import enum
import os
from queue import Empty, Queue
import sys
from time import sleep
from typing import Union
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


def break_type_down(lldbtype: lldb.SBType):
    """breaks down a type into the types it depends on"""
    to_resolve: UnresolvedTypeQueue = UnresolvedTypeQueue()
    ttype = lldbtype.type

    if ttype == lldb.eTypeClassTypedef:
        to_resolve.put(lldbtype.GetTypedefedType())
    elif ttype == lldb.eTypeClassStruct:
        for t in lldbtype.get_fields_array():
            to_resolve.put(t.GetType())
    elif ttype == lldb.eTypeClassUnion:
        for t in lldbtype.get_fields_array():
            to_resolve.put(t.GetType())
    else:
        to_resolve.put(lldbtype)

    for lldbtype in iter_queue(to_resolve):
        ttype = lldbtype.type
        if ttype == lldb.eTypeClassArray:
            to_resolve.put(lldbtype.GetArrayElementType())
        elif ttype == lldb.eTypeClassPointer:
            to_resolve.put(lldbtype.GetPointeeType())
        elif ttype == lldb.eTypeClassFunction:
            for t in lldbtype.GetFunctionArgumentTypes():
                to_resolve.put(t)
            to_resolve.put(lldbtype.GetFunctionReturnType())
        elif ttype == lldb.eTypeClassStruct:
            yield lldbtype
        elif ttype == lldb.eTypeClassUnion:
            yield lldbtype
        elif ttype == lldb.eTypeClassBuiltin:
            # don't even expose to the caller, we can skip this safely
            pass
        else:
            yield lldbtype


def type_c_repr(lldbtype: lldb.SBType) -> str:
    ttype = lldbtype.type
    print(7, lldbtype)
    if ttype == lldb.eTypeClassPointer:
        return "" + type_c_repr(lldbtype.GetPointeeType()) + "*"

    if ttype == lldb.eTypeClassFunction:
        raise NotImplementedError(
            "Function type not implemented when not used to declare value"
        )

    if ttype == lldb.eTypeClassArray:
        raise RuntimeError("Array type not possible when not used to declare value")

    if ttype == lldb.eTypeClassTypedef:
        return lldbtype.name

    if ttype == lldb.eTypeClassStruct:
        if is_anonymous_type(lldbtype):
            return get_type_definition(lldbtype)
        else:
            return "struct " + lldbtype.name

    if ttype == lldb.eTypeClassUnion:
        if is_anonymous_type(lldbtype):
            return get_type_definition(lldbtype)
        else:
            return "union " + lldbtype.name

    if ttype == lldb.eTypeClassEnumeration:
        if is_anonymous_type(lldbtype):
            return get_type_definition(lldbtype)
        else:
            return "enum " + lldbtype.name

    if ttype == lldb.eTypeClassBuiltin:
        return lldbtype.name

    raise RuntimeError("wrong type", lldbtype)


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
    assert type(lldbtype) == lldb.SBType
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
        raise NotImplementedError(
            "classes and stuff can probably be here too, just not implemented", lldbtype
        )
        return lldbtype.IsAnonymousType()


def type_value_c_repr(lldbtype: lldb.SBType, var_str: str):
    ttype = lldbtype.type
    if ttype == lldb.eTypeClassTypedef:
        return lldbtype.name + " " + var_str

    if ttype == lldb.eTypeClassPointer:
        # TODO: does this work?
        # return type_value_c_repr(lldbtype.GetPointeeType(), "(*" + var_str + ")")
        return type_value_c_repr(lldbtype.GetPointeeType(), "*" + var_str + "")

    if ttype == lldb.eTypeClassFunction:
        args: lldb.SBTypeList = lldbtype.GetFunctionArgumentTypes()
        args_str = "(" + ", ".join(type_c_repr(arg) for arg in args) + ")"
        ret_type = type_c_repr(lldbtype.GetFunctionReturnType())

        return ret_type + " (" + var_str + ")" + args_str

    if ttype == lldb.eTypeClassArray:
        return type_value_c_repr(
            lldbtype.GetArrayElementType(),
            "(" + var_str + ")[%s]" % str(lldbtype.size) if lldbtype.size else "",
        )

    if ttype in (
        lldb.eTypeClassStruct,
        lldb.eTypeClassUnion,
        lldb.eTypeClassEnumeration,
    ):
        if is_anonymous_type(lldbtype):
            return get_type_definition(lldbtype) + " " + var_str
        else:
            return type_c_repr(lldbtype) + " " + var_str

    if ttype == lldb.eTypeClassBuiltin:
        return lldbtype.name + " " + var_str

    raise RuntimeError(ttype, lldbtype)


class UnresolvedTypeQueue:
    def __init__(self):
        self.q: Queue[lldb.SBType] = Queue()
        # self.seen: set[str] = set()
        self.seen: set[tuple[str, int]] = set()

    def put(self, lldbtype: lldb.SBType):
        assert type(lldbtype) == lldb.SBType, lldbtype
        # TODO: typename = type_c_repr(lldbtype)
        typename = (lldbtype.name, lldbtype.type)
        if typename not in self.seen:
            self.seen.add(typename)
            self.q.put(lldbtype)

    def get(self, block=True, timeout=None):
        return self.q.get(block=block, timeout=timeout)


def get_type_definition(lldbtype: lldb.SBType):
    ttype = lldbtype.type

    if ttype == lldb.eTypeClassStruct:
        typename = lldbtype.name if not is_anonymous_type(lldbtype) else ""
        return (
            "struct "
            + typename
            + " {\n  "
            + "\n  ".join(
                map(
                    lambda t: (
                        type_value_c_repr(t.type, t.name)
                        if t.name is not None
                        else type_c_repr(t.type)
                    )
                    + ";",
                    lldbtype.fields,
                )
            )
            + "\n}"
        )

    if ttype == lldb.eTypeClassUnion:
        typename = lldbtype.name if not is_anonymous_type(lldbtype) else ""
        return (
            "union "
            + typename
            + " {\n  "
            + "\n  ".join(
                map(
                    lambda t: (
                        type_value_c_repr(t.type, t.name)
                        if t.name is not None
                        else type_c_repr(t.type)
                    )
                    + ";",
                    lldbtype.fields,
                )
            )
            + "\n}"
        )
    if ttype == lldb.eTypeClassEnumeration:
        typename = lldbtype.name if not is_anonymous_type(lldbtype) else ""
        return (
            "enum "
            + typename
            + " {\n  "
            + "\n  ".join(
                map(
                    lambda t: (t.name) + ",",
                    lldbtype.enum_members,
                )
            )
            + "\n}"
        )
    if ttype == lldb.eTypeClassTypedef:
        return "typedef " + type_value_c_repr(
            lldbtype.GetTypedefedType(), lldbtype.name
        )

    raise RuntimeError(lldbtype)


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


def resolve_types(
    target: lldb.SBTarget,
    types: list[str],
    recurse_option: DumpCTypeRecurseOption,
):
    # print(recurse_option)
    if recurse_option == DumpCTypeRecurseOption.ToPrimitives:
        # use str instead of lldb.SBType for __in__. Not sure if __in__ works
        # in the expected way for SBType
        unres_q = UnresolvedTypeQueue()
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

        for lldbtype in iter_queue(unres_q):
            # add the types we haven't seen into the queue
            for t in break_type_down(lldbtype):
                unres_q.put(t)

            # if it's anon, printing it is already handled in the place it's
            # defined in
            if is_anonymous_type(lldbtype):
                continue

            type_str = get_type_definition(lldbtype)

            i, resolved_lldbtype = resolve_typedefs(lldbtype)

            if i != 0:  # is typedef
                if i not in struct_typedefs_str:
                    struct_typedefs_str[i] = ""
                if i not in primitive_typedefs_str:
                    primitive_typedefs_str[i] = ""

                if resolved_lldbtype.type in (
                    lldb.eTypeClassStruct,
                    lldb.eTypeClassUnion,
                ):
                    struct_typedefs_str[i] = type_str + ";\n" + struct_typedefs_str[i]
                elif all(
                    t.type == lldb.eTypeClassBuiltin
                    for t in break_type_down(resolved_lldbtype)
                ):
                    primitive_typedefs_str[i] = (
                        type_str + ";\n" + primitive_typedefs_str[i]
                    )
                else:
                    res_str = type_str + ";\n" + res_str
            else:
                res_str = type_str + ";\n" + res_str

        # print(primitive_typedefs_str)
        typedefs = "\n".join(
            map(
                lambda x: x[1],
                sorted(primitive_typedefs_str.items(), key=lambda x: x[0]),
            )
        ) + "\n".join(
            map(
                lambda x: x[1],
                sorted(struct_typedefs_str.items(), key=lambda x: x[0]),
            )
        )
        res_str = typedefs + res_str
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
