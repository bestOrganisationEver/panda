import enum
import os
from queue import Empty, Queue
import sys
from time import sleep
from typing import Generator, Union
import lldb
from lldb.plugins.parsed_cmd import ParsedCommand, LLDBOptionValueParser

FILENAME = os.path.basename(__file__).removesuffix(".py")


# lldb.OptionArgParser
# used by lldb to initialize this module
def __lldb_init_module(debugger: lldb.SBDebugger, internal_dict):
    # ci = debugger.GetCommandInterpreter()
    DumpCType.register(debugger, __name__)
    # res = lldb.SBCommandReturnObject()
    # ci.HandleCommand("command script add -f %s.custom_ptype pptype" % FILENAME, res)
    # if not res.Succeeded():
    #     raise Exception("Could not register command")


def iter_queue(q):  # uses ducktyping
    while True:
        try:
            yield q.get(block=False)
        except Empty:
            break


class DepType(enum.IntEnum):
    # this dependency requires a complete definition of the dependency type
    # which is a product type, like a union or struct (or enum)
    # struct B {
    #   struct A a;
    # };
    StructBStructA = 0

    # this dependency requires only an (implicit) declaration of the dependency type
    # which is a product type, like a union or struct (or enum):
    # struct B {
    #   struct A* a;
    # };
    StructBStructAptr = 1

    # this dependency requires a typedef of the definition type
    # AND a definition of the type the typedef depends on, if the typedef
    # requires a definition of the type it depends on
    # typedef struct A A;
    # struct B {
    #   A a;
    # };
    StructBtypedefA = 2

    # this dependency requires a typedef of the definition type
    # but DOES NOT require a definition of the type the typedef depends on
    # typedef struct A A;
    # struct B {
    #   A *a;
    # };
    #
    # or
    #
    # typedef struct A *Astar;
    # struct B {
    #   Astar a;
    # };
    StructBPtrOfTypedefA = 3

    Typedef_A_B = 4
    Typedef_Aptr_B = 5
    Typedef_structA_B = 6
    Typedef_structAptr_B = 7
    Typedef_enumA_B_or_Typedef_enumAptr_B = 8
    Typedef_array_B = 9
    # # typedef A B;
    # TypedefDepInTypedef = 4

    # # typedef struct A B;
    # ProductDepInTypedef = 5


def get_sized_inner(lldbtype: lldb.SBType):
    """dereferences until it hits a type whose size cannot be known without
    extra information"""

    in_pointer = False
    in_array = False
    while True:
        ttype = lldbtype.type
        if ttype == lldb.eTypeClassArray:
            lldbtype = lldbtype.GetArrayElementType()
            in_array = True
        elif ttype == lldb.eTypeClassPointer:
            lldbtype = lldbtype.GetPointeeType()
            in_pointer = True
        else:
            return lldbtype, in_pointer, in_array


def break_type_down(lldbtype: lldb.SBType):
    """breaks down a type into the types it depends on. yields (dep_type, is_complete_dep)
    where is_complete_dep is a bool that indicates that the dependency needs a
    definition when True, and only an (implicit) declaration when False.
    Typedefs are counted as a definition."""

    assert type(lldbtype) == lldb.SBType

    to_resolve: TypeDepQueue = TypeDepQueue()
    ttype = lldbtype.type

    if ttype == lldb.eTypeClassTypedef:
        td_type: lldb.SBType
        in_pointer: bool
        td_type, in_pointer, in_array = get_sized_inner(lldbtype.GetTypedefedType())

        # to_resolve.put(
        #     td_type,
        #     (
        #         TypeDepState.NotInPointer
        #         if td_type.IsTypedefType()
        #         else TypeDepState.InPointer
        #     ),
        # )

        # if is_anonymous_type(td_type) or td_type.IsFunctionType():
        if is_anonymous_type(td_type):
            # TODO: unroll this. The dep types will be wrong as-is.
            # somehow it still works.
            for i in break_type_down(td_type):
                yield i
            return
        elif td_type.IsFunctionType():
            # TODO: unroll this. The dep types will be wrong as-is.
            # somehow it still works.
            for dep, dep_type in break_type_down(td_type):
                if dep_type == DepType.StructBStructA:
                    if in_pointer:
                        yield dep, DepType.Typedef_structAptr_B
                    else:
                        yield dep, DepType.Typedef_structA_B
                elif dep_type == DepType.StructBStructAptr:
                    yield dep, DepType.Typedef_structAptr_B
                elif dep_type == DepType.StructBtypedefA:
                    if in_pointer:
                        yield dep, DepType.Typedef_Aptr_B
                    else:
                        yield dep, DepType.Typedef_A_B
                elif dep_type == DepType.StructBPtrOfTypedefA:
                    yield dep, DepType.Typedef_Aptr_B
                    # raise Exception()
                else:
                    raise Exception()

            return
        elif in_array:
            if td_type.type != lldb.eTypeClassBuiltin:
                yield td_type, DepType.Typedef_array_B
                chain_len, tdtype = resolve_typedefs(lldbtype)
                assert chain_len != 0

                if tdtype.type != lldb.eTypeClassPointer:
                    for x in break_type_down_after_typedefs(tdtype):
                        yield x
            return

        else:
            if td_type.type == lldb.eTypeClassBuiltin:
                return

            if td_type.type == lldb.eTypeClassEnumeration:
                dt = DepType.Typedef_enumA_B_or_Typedef_enumAptr_B
            elif in_pointer and td_type.IsTypedefType():
                dt = DepType.Typedef_Aptr_B
            elif not in_pointer and td_type.IsTypedefType():
                dt = DepType.Typedef_A_B
            elif in_pointer and not td_type.IsTypedefType():
                dt = DepType.Typedef_structAptr_B
            elif not in_pointer and not td_type.IsTypedefType():
                dt = DepType.Typedef_structA_B
            else:
                raise Exception()

            yield td_type, dt
            return

    # we've handled the immediate typedef.
    for i in break_type_down_after_typedefs(lldbtype):
        yield i


def break_type_down_after_typedefs(lldbtype: lldb.SBType):
    assert type(lldbtype) == lldb.SBType
    assert lldbtype.type != lldb.eTypeClassTypedef

    to_resolve: TypeDepQueue = TypeDepQueue()
    ttype = lldbtype.type

    if ttype == lldb.eTypeClassStruct:
        for t in lldbtype.get_fields_array():
            to_resolve.put(t.GetType(), TypeDepState.NotInPointer)
    elif ttype == lldb.eTypeClassUnion:
        for t in lldbtype.get_fields_array():
            to_resolve.put(t.GetType(), TypeDepState.NotInPointer)
    else:
        to_resolve.put(lldbtype, TypeDepState.NotInPointer)

    for lldbtype, dep_state in iter_queue(to_resolve):
        ttype = lldbtype.type
        if ttype == lldb.eTypeClassArray:
            to_resolve.put(lldbtype.GetArrayElementType(), dep_state)
        elif ttype == lldb.eTypeClassPointer:
            to_resolve.put(lldbtype.GetPointeeType(), TypeDepState.InPointer)
        elif ttype == lldb.eTypeClassFunction:
            for t in lldbtype.GetFunctionArgumentTypes():
                to_resolve.put(t, dep_state)
            to_resolve.put(lldbtype.GetFunctionReturnType(), dep_state)
        elif ttype in (
            lldb.eTypeClassStruct,
            lldb.eTypeClassUnion,
            lldb.eTypeClassEnumeration,
        ):
            if is_anonymous_type(lldbtype):
                for t in lldbtype.get_fields_array():
                    to_resolve.put(t.GetType(), dep_state)
                continue

            if dep_state == TypeDepState.NotInPointer:
                yield lldbtype, DepType.StructBStructA
            elif dep_state == TypeDepState.InPointer:
                yield lldbtype, DepType.StructBStructAptr
            else:
                raise Exception()
        elif ttype == lldb.eTypeClassBuiltin:
            # don't even expose to the caller, we can skip this safely
            pass
        elif ttype == lldb.eTypeClassTypedef:
            if dep_state == TypeDepState.NotInPointer:
                yield lldbtype, DepType.StructBtypedefA
                chain_len, tdtype = resolve_typedefs(lldbtype)
                assert chain_len != 0

                if tdtype.type != lldb.eTypeClassPointer:
                    assert not tdtype.IsPointerType()

                    to_resolve.put(tdtype, dep_state)
            elif dep_state == TypeDepState.InPointer:
                yield lldbtype, DepType.StructBPtrOfTypedefA
            else:
                raise Exception()
        else:
            raise Exception()
            yield lldbtype, dep_state


# def type_c_decl(lldbtype: lldb.SBType) -> str:
#     ttype = lldbtype.type

#     if ttype == lldb.eTypeClassFunction:
#         raise NotImplementedError(
#             "Function type not implemented when not used to declare value", lldbtype
#         )

#     if ttype == lldb.eTypeClassArray:
#         raise RuntimeError("Array type not possible when not used to declare value")

#     if ttype == lldb.eTypeClassTypedef:
#         return "typedef " + type_value_c_repr(
#             lldbtype.GetTypedefedType(), lldbtype.name, indentation
#         )

#     if ttype == lldb.eTypeClassStruct:
#         if is_anonymous_type(lldbtype):
#             raise RuntimeError("Anonymous type cannot be declared.")
#         else:
#             return "struct " + lldbtype.name

#     if ttype == lldb.eTypeClassUnion:
#         if is_anonymous_type(lldbtype):
#             raise RuntimeError("Anonymous type cannot be declared.")
#         else:
#             return "union " + lldbtype.name

#     if ttype == lldb.eTypeClassEnumeration:
#         if is_anonymous_type(lldbtype):
#             raise RuntimeError("Anonymous type cannot be declared.")
#         else:
#             return "enum " + lldbtype.name

#     raise RuntimeError("wrong type", lldbtype)


def type_c_name_iw(lldbtype: lldb.SBType, iw: "IndentedWriter") -> None:
    assert type(iw) == IndentedWriter

    ttype = lldbtype.type
    if ttype == lldb.eTypeClassPointer:
        type_c_name_iw(lldbtype.GetPointeeType(), iw)
        iw.append_last_line("*")

    elif ttype == lldb.eTypeClassFunction:
        raise NotImplementedError(
            "Function type not implemented when not used to declare value", lldbtype
        )

    elif ttype == lldb.eTypeClassArray:
        raise RuntimeError("Array type not possible when not used to declare value")

    elif ttype == lldb.eTypeClassTypedef:
        iw.add_line(lldbtype.name)

    elif ttype == lldb.eTypeClassStruct:
        assert not is_anonymous_type(lldbtype), lldbtype
        # if is_anonymous_type(lldbtype):
        #     return get_type_definition(lldbtype, indentation)
        # else:
        #     return " " * indentation + "struct " + lldbtype.name
        iw.add_line("struct " + lldbtype.name)

    elif ttype == lldb.eTypeClassUnion:
        assert not is_anonymous_type(lldbtype)
        # if is_anonymous_type(lldbtype):
        #     return get_type_definition(lldbtype, indentation)
        # else:
        #     return " " * indentation + "union " + lldbtype.name
        iw.add_line("union " + lldbtype.name)

    elif ttype == lldb.eTypeClassEnumeration:
        assert not is_anonymous_type(lldbtype)
        # if is_anonymous_type(lldbtype):
        #     return get_type_definition(lldbtype, indentation)
        # else:
        #     return " " * indentation + "enum " + lldbtype.name
        iw.add_line("enum " + lldbtype.name)

    elif ttype == lldb.eTypeClassBuiltin:
        # Not .name, because _Bool becomes bool. Sigh.
        iw.add_line(lldbtype.__repr__())
    else:
        raise RuntimeError("wrong type", lldbtype, lldbtype.name, lldbtype.type)


def type_c_name(lldbtype: lldb.SBType) -> str:
    iw = IndentedWriter(0)
    type_c_name_iw(lldbtype, iw)
    return iw.read()


# HACK: due to a bug (?), if you move a (by lldb standards) non-anonymous field of a struct
# (SBTypeMember) of the following type:
# struct Parent {
#   struct { /* this field */
#     whatever_t a;
#   } Inner;
# }
#  to an SBType by calling GetType(), instead of making the new type anonymous
# (as the variable name is now dropped), clang will think it's still a non-anon
# struct. It seems like the only user-facing way to fix this through the python
# API is by looking at lldbtype.name and seeing if it ends with ::(unnamed struct)
# this is heavily leaning into terrible hack territory.
def is_anonymous_type(lldbtype: lldb.SBType) -> bool:
    assert type(lldbtype) == lldb.SBType, lldbtype
    unnamed_end = None
    if lldbtype.type == lldb.eTypeClassStruct:
        unnamed_end = ("::(unnamed struct)", "::(anonymous struct)")
    elif lldbtype.type == lldb.eTypeClassUnion:
        unnamed_end = ("::(unnamed union)", "::(anonymous union)")
    elif lldbtype.type == lldb.eTypeClassEnumeration:
        unnamed_end = ("::(unnamed enum)", "::(anonymous enum)")
    elif lldbtype.type == lldb.eTypeClassTypedef:
        return False

    if unnamed_end is not None:
        return lldbtype.IsAnonymousType() or lldbtype.name.endswith(unnamed_end)

    else:
        # raise NotImplementedError(
        #     "classes and stuff can probably be here too, just not implemented", lldbtype
        # )
        return lldbtype.IsAnonymousType()


def type_value_c_repr_iw(
    lldbtype: lldb.SBType, var_str: str, iw: Union["IndentedWriter", None]
):
    if iw is None:
        iw = IndentedWriter(0)
    assert type(iw) == IndentedWriter

    assert type(lldbtype) == lldb.SBType, lldbtype
    assert type(var_str) == str, (var_str, lldbtype)
    ttype = lldbtype.type
    if ttype == lldb.eTypeClassTypedef:
        iw.add_line(lldbtype.name + " " + var_str)
        return

    elif ttype == lldb.eTypeClassPointer:
        # TODO: does this work?
        # return type_value_c_repr(lldbtype.GetPointeeType(), "(*" + var_str + ")")
        return type_value_c_repr_iw(lldbtype.GetPointeeType(), "*" + var_str + "", iw)

    elif ttype == lldb.eTypeClassFunction:
        args: lldb.SBTypeList = lldbtype.GetFunctionArgumentTypes()
        args_str = "(" + ", ".join(type_c_name(arg) for arg in args) + ")"
        ret_type = type_c_name(lldbtype.GetFunctionReturnType())
        # print("FUNC YO", ret_type + " (" + var_str + ")" + args_str)
        iw.add_line(ret_type + " (" + var_str + ")" + args_str)
        return

    elif ttype == lldb.eTypeClassArray:
        inner: lldb.SBType = lldbtype.GetArrayElementType()
        if lldbtype.size and lldbtype.size != 0:
            outer_size = lldbtype.size
            inner_size = inner.GetByteSize()
            assert inner_size != 0
            assert outer_size % inner_size == 0

            size_str = str(lldbtype.size // inner_size)
        else:
            size_str = ""

        type_value_c_repr_iw(inner, "(" + var_str + ")[%s]" % size_str, iw)
        return

    elif ttype in (
        lldb.eTypeClassStruct,
        lldb.eTypeClassUnion,
        lldb.eTypeClassEnumeration,
    ):
        if is_anonymous_type(lldbtype):
            get_type_definition_iw(lldbtype, iw)
            if var_str != "":
                iw.append_last_line(" " + var_str)
            return
        else:
            type_c_name_iw(lldbtype, iw)
            if var_str != "":
                iw.append_last_line(" " + var_str)
            return

    elif ttype == lldb.eTypeClassBuiltin:
        # not .name, because _Bool becomes bool.
        iw.add_line(lldbtype.__repr__() + " " + var_str)
    else:
        raise RuntimeError(ttype, lldbtype)


def type_value_c_repr(lldbtype: lldb.SBType, var_str: str) -> str:
    iw = IndentedWriter(0)
    type_value_c_repr_iw(lldbtype, var_str, iw)
    return iw.read()


class TypeDepState(enum.IntEnum):
    InPointer = 0
    NotInPointer = 1


class IndentedWriter:
    def __init__(self, indent_level: int):
        self.lvl = indent_level
        self.lines: list[str] = []

    def set_indent(self, new_indent: int):
        self.lvl = new_indent

    def inc_indent(self, inc: int):
        self.lvl += inc

    def dec_indent(self, dec: int):
        self.lvl -= dec

    def add_line(self, line: str):
        assert type(line) == str
        self.lines.append(" " * self.lvl + line)

    def append_last_line(self, suf: str):
        assert len(self.lines) > 0
        self.lines[-1] += suf

    def read(self):
        return "\n".join(self.lines)

    def iterlines(self):
        for l in self.lines:
            yield l


class TypeDepQueue:
    def __init__(self):
        self.q: Queue[tuple[lldb.SBType, TypeDepState]] = Queue()
        # self.seen: set[str] = set()
        self.seen: set[tuple[str, int, TypeDepState]] = set()

    def put(self, lldbtype: lldb.SBType, type_dep_state: TypeDepState):
        assert type(lldbtype) == lldb.SBType, lldbtype
        # TODO: typename = type_c_repr(lldbtype)
        typename = (lldbtype.name, lldbtype.type, type_dep_state)
        if is_anonymous_type(lldbtype) or typename not in self.seen:
            self.seen.add(typename)
            self.q.put((lldbtype, type_dep_state))

    def get(self, block=True, timeout=None):
        return self.q.get(block=block, timeout=timeout)


class UnresolvedTypeQueue:
    def __init__(self):
        self.q: Queue[lldb.SBType] = Queue()
        # self.seen: set[str] = set()
        self.seen: set[tuple[str, int]] = set()

    def put(self, lldbtype: lldb.SBType):
        assert type(lldbtype) == lldb.SBType, lldbtype
        # TODO: typename = type_c_repr(lldbtype)
        typename = (lldbtype.name, lldbtype.type)
        if is_anonymous_type(lldbtype) or typename not in self.seen:
            self.seen.add(typename)
            self.q.put(lldbtype)

    def get(self, block=True, timeout=None):
        return self.q.get(block=block, timeout=timeout)


def get_type_definition_iw(lldbtype: lldb.SBType, iw: IndentedWriter):
    assert type(iw) == IndentedWriter

    ttype = lldbtype.type

    if ttype == lldb.eTypeClassStruct:
        typename = lldbtype.name if not is_anonymous_type(lldbtype) else ""
        print(lldbtype)
        if is_anonymous_type(lldbtype):
            iw.add_line("struct {")
        else:
            iw.add_line("struct " + lldbtype.name + " {")
        iw.inc_indent(4)
        for t in lldbtype.fields:
            type_value_c_repr_iw(t.type, t.name if t.name is not None else "", iw)
            if t.IsBitfield():
                iw.append_last_line(" : " + str(t.GetBitfieldSizeInBits()))
            iw.append_last_line(";")
        iw.dec_indent(4)
        iw.add_line("}")
        return

    elif ttype == lldb.eTypeClassUnion:
        typename = lldbtype.name if not is_anonymous_type(lldbtype) else ""
        if is_anonymous_type(lldbtype):
            iw.add_line("union {")
        else:
            iw.add_line("union " + lldbtype.name + " {")
        iw.inc_indent(4)
        for t in lldbtype.fields:
            type_value_c_repr_iw(t.type, t.name if t.name is not None else "", iw)
            if t.IsBitfield():
                iw.append_last_line(" : " + str(t.GetBitfieldSizeInBits()))
            iw.append_last_line(";")
        iw.dec_indent(4)
        iw.add_line("}")
        return
    elif ttype == lldb.eTypeClassEnumeration:
        typename = lldbtype.name if not is_anonymous_type(lldbtype) else ""
        if is_anonymous_type(lldbtype):
            iw.add_line("enum {")
        else:
            iw.add_line("enum " + lldbtype.name + " {")
        iw.inc_indent(4)
        for t in lldbtype.enum_members:
            iw.add_line(t.name + ",")
        iw.dec_indent(4)
        iw.add_line("}")

        return

    elif ttype == lldb.eTypeClassTypedef:
        assert iw.lvl == 0
        iw.add_line(
            "typedef " + type_value_c_repr(lldbtype.GetTypedefedType(), lldbtype.name)
        )
        return
    elif ttype == lldb.eTypeClassFunction:
        assert iw.lvl == 0
        iw.add_line("typedef " + type_value_c_repr(lldbtype, lldbtype.name))
        return
    else:
        raise RuntimeError(lldbtype, lldbtype.type == lldb.eTypeClassFunction)


def get_type_definition(lldbtype: lldb.SBType) -> str:
    iw = IndentedWriter(0)
    get_type_definition_iw(lldbtype, iw)
    return iw.read()


def str_to_type(
    target: lldb.SBTarget, type_str: str
) -> tuple[str, Union[lldb.SBType, None]]:
    type_str = type_str.strip()
    if type_str.startswith("struct ") or type_str.startswith("enum "):
        # Look up first definition of type.
        # ---
        # By C standard §69.420 all extern definitions of a type must consist of the same
        # tokens. Thus we can get away with using FindFirstType instead of FindTypes.
        # Maybe. I have severe brainrot and cannot possibly read through the C
        # standard to make sure this makes sense. Consider this a heuristic.
        lldbtype: lldb.SBType = target.FindFirstType(type_str)
        if not lldbtype.IsValid():
            return "%s is not a valid struct or enum" % type_str, None
        return "", lldbtype
    else:
        # lldb doesn't just search for typedefs when a non-primitive type without the
        # struct prefix is passed in. It will also search for type definitions for
        # "struct " + type_name. To stop this we need to explicitly say this is a typedef.
        type_typedef: lldb.SBType = target.FindFirstType("typedef " + type_str)
        if not type_typedef.IsValid():
            return "%s is not a valid typedef" % type_str, None
        return "", type_typedef


class DumpCTypeRecurseOption(enum.IntEnum):
    Dont = 0
    ToLeaf = 1
    ToPrimitives = 2


def resolve_typedefs(lldbtype: lldb.SBType) -> tuple[int, lldb.SBType]:
    i = 0
    while lldbtype.IsTypedefType():
        i += 1
        lldbtype = lldbtype.GetTypedefedType()
    return i, lldbtype


class TypeDepNode:
    def __init__(self, lldbtype: lldb.SBType):
        self.type: lldb.SBType = lldbtype


# class TypeBlockDepNode:
#     def __init__(self, lldbtype: lldb.SBType):
#         self.type: lldb.SBType = lldbtype
#         self.soft_deps: list[lldb.SBType] = []

#     def iter_deps(self):
#         for dep in self.hard_deps:
#             yield dep
#         for dep in self.soft_deps:
#             yield dep


class HardDepHeader:
    def __init__(self):
        self.nodes: list[lldb.SBType] = []
        self.nodes_names: set[tuple[str, int]] = set()
        self.outstanding_soft_deps = []
        # self.soft_deps_that_need_decl: list[lldb.SBType] = []

    def find_node(self, lldbtype: lldb.SBType):
        if lldbtype.IsAnonymousType():
            return -1

        for i, node in enumerate(self.nodes):
            if (node.name, node.type) == (lldbtype.name, lldbtype.type):
                return i
        return -1

    def add_typedef_type(self, lldbtype: lldb.SBType, need_complete: bool):
        print("add typedef type:", lldbtype, need_complete)
        assert lldbtype.IsTypedefType()
        if lldbtype in self.nodes:
            return None

        for dep, dep_type in break_type_down(lldbtype):
            print("  add_typedef_type dep:", dep.name)
            if dep.IsTypedefType():
                if dep_type == DepType.Typedef_array_B:
                    print("ARRAY2:", lldbtype, dep)
                    self.add_typedef_type(dep, need_complete=True)
                else:
                    self.add_typedef_type(dep, need_complete=need_complete)

            else:
                if dep_type == DepType.Typedef_enumA_B_or_Typedef_enumAptr_B:
                    self.add_type(dep)
                elif dep_type == DepType.Typedef_array_B:
                    print("ARRAY:", lldbtype, dep)
                    self.add_type(dep)
                elif need_complete:
                    if dep_type == DepType.Typedef_structA_B:
                        # print("need_complete", )
                        self.add_type(dep)
                    elif dep_type == DepType.Typedef_structAptr_B:
                        self.add_soft_dep(dep)
                    else:
                        raise Exception(
                            lldbtype,
                            dep,
                            dep_type,
                            get_sized_inner(lldbtype.GetTypedefedType()),
                            lldbtype.GetTypedefedType(),
                        )
                # else:
                #     raise Exception(
                #         lldbtype,
                #         dep,
                #         dep_type,
                #         get_sized_inner(lldbtype.GetTypedefedType()),
                #         lldbtype.GetTypedefedType(),
                #     )
        # if not tdtype.IsTypedefType():
        #     # print("leaf typedef:", lldbtype)
        #     # TODO pointer in typedefed type
        #     if need_complete:
        #         # print("need_complete:", lldbtype)
        #         self.add_type(tdtype)
        #         self.insert_after_deps_resolved(lldbtype)
        #         return
        #         # return
        #     # else:
        #     #     # print("not need_complete:", lldbtype)
        #     #     return None

        # # print("non-leaf typedef:", lldbtype)
        # self.add_typedef_type(tdtype, need_complete=need_complete)
        # print("end", lldbtype)
        self.insert_after_deps_resolved(lldbtype)

    def add_soft_dep(self, deptype: lldb.SBType):
        print("add_soft_dep:", deptype.name)
        assert deptype.type != lldb.eTypeClassPointer, deptype
        # if
        if deptype in self.nodes:
            return
        self.outstanding_soft_deps.append(deptype)

    def add_type(
        self,
        lldbtype: lldb.SBType,
        only_implicit_declaration=False,
    ):
        assert lldbtype.type != lldb.eTypeClassPointer
        if not only_implicit_declaration and lldbtype in self.nodes:
            print("  already in nodes, skipping:", lldbtype.name)
            return None

        if lldbtype.type == lldb.eTypeClassBuiltin:
            return None

        print("add_type:", lldbtype.name)
        if lldbtype.IsTypedefType():
            self.add_typedef_type(lldbtype, need_complete=False)
            return

        for dep, dep_type in break_type_down(lldbtype):
            print("  add_type dep:", lldbtype.name, dep.name)
            assert dep.type != lldb.eTypeClassBuiltin, (lldbtype, dep)
            if lldbtype == dep:
                continue
            if dep_type == DepType.StructBStructA:
                # if only_implicit_declaration:
                self.add_type(dep, only_implicit_declaration)
                # else:
                #     self.add_soft_dep(dep)
            elif dep_type == DepType.StructBStructAptr:
                self.add_soft_dep(dep)
            elif dep_type == DepType.StructBtypedefA:
                # td: lldb.SBType = dep.GetTypedefedType()
                # assert td.IsValid()
                self.add_typedef_type(dep, need_complete=True)
            elif dep_type == DepType.StructBPtrOfTypedefA:
                self.add_typedef_type(dep, need_complete=False)
            else:
                raise Exception()
        # self.print_defs()
        # input()
        self.insert_after_deps_resolved(lldbtype)

    def insert_after_deps_resolved(self, lldbtype: lldb.SBType):
        print("insert_after_deps_resolved:", lldbtype.name)

        last_index: Union[int, None] = None
        for dep, dep_type in break_type_down(lldbtype):
            if dep == lldbtype:
                continue
            # it might be possible to cache the index result from the dependencies
            # but it's tricky, so here we just loop over the list
            if dep_type in (
                DepType.StructBStructA,
                DepType.StructBtypedefA,
                DepType.StructBPtrOfTypedefA,
                DepType.Typedef_A_B,
                DepType.Typedef_Aptr_B,
                DepType.Typedef_array_B,
                DepType.Typedef_enumA_B_or_Typedef_enumAptr_B,
                # DepType.Typedef_structA_B,
            ):
                if dep_type == DepType.Typedef_array_B:
                    print("ARRAY!!", lldbtype, dep)
                assert (dep.name, dep.type) in self.nodes_names, (
                    self.nodes,
                    dep,
                    dep_type,
                    lldbtype,
                )
                if last_index == None:
                    last_index = self.find_node(dep)
                    assert last_index != -1
                else:
                    possibly = self.find_node(dep)
                    assert possibly != -1
                    last_index = max(possibly, last_index)
            else:
                self.add_soft_dep(dep)

        insert_index = last_index + 1 if last_index is not None else 0

        if not (
            lldbtype.type == lldb.eTypeClassTypedef
            and (lldbtype.name, lldbtype.type) in self.nodes_names
        ):
            # try:
            #     self.nodes.index(lldbtype)
            #     raise Exception()
            # except:
            #     pass
            self.nodes_names.add((lldbtype.name, lldbtype.type))
            self.nodes.insert(insert_index, lldbtype)
        # if lldbtype not in self.nodes:
        #     self.nodes.insert(insert_index, lldbtype)

        print("end insert_after_deps:", lldbtype.name, insert_index)
        # for dep in incomplete_dependencies(lldbtype):
        #     if dep != lldbtype:
        #         self.add_soft_dep(dep)
        #     # if dep not in self.nodes:
        #     #     self.add_soft_dep(dep)
        #     # self.soft_deps_that_need_decl.append(dep)

    def resolve_all_deps(self):
        print("resolve_all_deps:", self.outstanding_soft_deps)
        if not self.outstanding_soft_deps:
            return None

        while self.outstanding_soft_deps:
            # self.print_defs()
            # print([type_c_name(x) for x in self.outstanding_soft_deps])
            # input()
            t = self.outstanding_soft_deps[0]
            del self.outstanding_soft_deps[0]
            self.add_type(t, only_implicit_declaration=False)

    def print_defs(self):
        defs = "=======\n"
        for t in self.nodes:
            # print("assss")
            defs += get_type_definition(t) + ";\n"
        print(defs)
        return defs

    def generate(self):
        print("generating")
        self.resolve_all_deps()

        defs = ""
        # print(self.soft_deps_that_need_decl)
        for t in self.outstanding_soft_deps:
            # print(1, t.name)
            # if t.IsTypedefType():
            #     defs += get_type_definition(t) + ";\n"
            # else:
            defs += type_c_name(t) + ";\n"
        defs += "/* end decls */\n"
        for t in self.nodes:
            # print("assss")
            defs += get_type_definition(t) + ";\n"

        assert len(self.nodes_names) == len(self.nodes), (
            len(self.nodes_names),
            len(self.nodes),
        )
        print("====")
        print(defs)
        print("====")
        print([type_c_name(x) for x in self.outstanding_soft_deps])


def resolve_types(
    target: lldb.SBTarget,
    types: list[str],
    recurse_option: DumpCTypeRecurseOption,
):
    # print(recurse_option)
    if recurse_option == DumpCTypeRecurseOption.ToPrimitives:
        # use str instead of lldb.SBType for __in__. Not sure if __in__ works
        # in the expected way for SBType
        unres_q = Queue()
        # for forward declarations
        struct_typedefs_str: dict[int, str] = {}
        primitive_typedefs_str: dict[int, str] = {}
        res_str = ""

        # initialize the queue with all the types from the user
        for typename in types:
            err, lldbtype = str_to_type(target, typename)
            if err:
                res_str = "/* %s, skipping */\n" % err + res_str
                continue
            assert lldbtype is not None  # just to satisfy the type checker
            unres_q.put(lldbtype)

        h = HardDepHeader()
        for lldbtype in iter_queue(unres_q):
            # add the types we haven't seen into the queue
            h.add_type(lldbtype)
        # res_str = typedefs + res_str
        h.generate()
        # for type in unres_q.seen:
        #     type
    elif recurse_option == DumpCTypeRecurseOption.ToLeaf:
        res_str = ""
        for typename in types:
            type_str, new_type = get_type_definition_and_leaf(
                target, typename, to_leaf=True
            )
            res_str = type_str + "\n" + res_str
    elif recurse_option == DumpCTypeRecurseOption.Dont:
        res_str = ""
        for typename in types:
            type_str, new_type = get_type_definition_and_leaf(
                target, typename, to_leaf=False
            )
            res_str = type_str + "\n" + res_str

    return res_str


class DumpCType(ParsedCommand):
    program = "dump_ctype"

    def __init__(self, debugger, internal_dict):
        super().__init__(debugger, internal_dict)

    @classmethod
    def register(cls, debugger, module_name):
        # It seems like do_register_cmd should really be a classmethod, but
        # it's a staticmethod so we abstract over it for easier calling
        cls.do_register_cmd(cls, debugger=debugger, module_name=module_name)

    def setup_command_definition(self):
        parser = self.get_parser()

        parser.add_option(
            "l",
            "to-leaf",
            help="to_leaf = True. Recurses typedefs until a struct or enum is hit.",
            value_type=lldb.eArgTypeBoolean,
            dest="to_leaf",
            default=True,
        )

        parser.add_option(
            "p",
            "to_primitives",
            help="to_primitives = True. Recurses typedefs and definitions until all types other than primitives are exhausted. Implies --to-leaf.",
            value_type=lldb.eArgTypeBoolean,
            dest="to_primitives",
            default=True,
        )

        parser.add_argument_set(
            [
                parser.make_argument_element(
                    arg_type=lldb.eArgTypeTypeName, repeat="optional"
                )
            ]
        )

    def __call__(
        self,
        debugger: lldb.SBDebugger,
        args_array: Union[lldb.SBStructuredData, list[str]],
        exe_ctx: lldb.SBExecutionContext,
        result: lldb.SBCommandReturnObject,
    ):
        target: lldb.SBTarget = debugger.GetSelectedTarget()  # type: ignore
        assert target is not None, "no target :/"

        # docs say this is supposed to be iterable(list?) of str. Real world
        # experience says no. Handle both.
        if type(args_array) != lldb.SBStructuredData:
            # cast to list early in case it's a generator we won't be able to
            # rewind
            try:
                args_array = list(iter(args_array))  # type: ignore
            except TypeError:  # from iter
                raise RuntimeError("args_array isn't an expected type (list)")
            except:
                raise RuntimeError("unknown error when parsing args_array")

            if not all(type(x) == str for x in args_array):
                raise RuntimeError("args_array isn't an expected type (list of strs)")
            types = args_array
        else:
            assert type(args_array) == lldb.SBStructuredData
            types = []
            for i in range(args_array.GetSize()):
                item: lldb.SBStructuredData = args_array.GetItemAtIndex(i)

                # HACK: item.GetStringValue() takes a size for a buf it will malloc.
                # there is currently seemingly no good way to get the size of the
                # buffer we need, as GetSize isn't implemented for string types on
                # SBStructuredData. So instead we use GetAsJSON which isn't intended
                # to be used this way, but :whatevs-until-everything-explodes:.

                # The type of item.GetStringValue according to SWIG is wrong:
                # It seems like this method takes a char *dst (??what??).
                # This actually isn't the case due to this file:
                # lldb/bindings/python/python-typemaps.swig
                #
                # this file maps a (char *dst, size_t dst_len) argument pair to
                # a dst_len: PyLong.
                type_name = item.GetStringValue(1000)
                types.append(type_name)

        if len(types) == 0:
            raise RuntimeError("at least one type is needed")

        # resolve recurse option
        parser: LLDBOptionValueParser = self.get_parser()
        print(parser.to_primitives, parser.to_leaf)  # type: ignore
        if parser.to_primitives:  # type: ignore
            recurse_opt = DumpCTypeRecurseOption.ToPrimitives
        elif parser.to_leaf:  # type: ignore
            recurse_opt = DumpCTypeRecurseOption.ToLeaf
        else:
            recurse_opt = DumpCTypeRecurseOption.Dont
        print(recurse_opt)
        res = resolve_types(target, types, recurse_opt)
        print("===resolve_types output===")
        print(res)
        # result.AppendMessage(res)
