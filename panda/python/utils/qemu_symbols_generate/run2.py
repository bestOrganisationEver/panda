import os
from cffi import FFI
from sodoth.unified_interface import generate_header

# add manually. 1st field is the name for CPU*ARCH*State. 2nd is bits. 3rd is path to libpanda*.so
archs = [
    ("X86", 32, "/i386-softmmu/libpanda-i386.so"),
    ("X86", 64, "/x86_64-softmmu/libpanda-x86_64.so"),
    ("ARM", 32, "/arm-softmmu/libpanda-arm.so"),
    ("ARM", 64, "/aarch64-softmmu/libpanda-aarch64.so"),
    ("PPC", 32, "/ppc-softmmu/libpanda-ppc.so"),
    ("PPC", 64, "/ppc64-softmmu/libpanda-ppc64.so"),
]

panda_base = "../../../../build"


def validate_header(header_content: str, types_to_check: list[str]):
    ffi = FFI()
    try:
        ffi.cdef(header_content)
        for t in types_to_check:
            ffi.new(t + "*")
        return False
    except Exception as e:
        raise e


"""
This function attempts to create, validate, and write a header file based on the required information
"""


def generate_config(arch, bits, elf_file):
    # header = HeaderFile(arch, pahole_path, elf_file)
    # the truth of the matter is we don't need 1000s of QEMU structs. We need 3.
    # We also need the tree created by references to those.
    struct_list = [
        "QemuThread",
        "QemuCond",
        "struct qemu_work_item",
        "CPUAddressSpace",
        "GDBRegisterState",
        "CPUState",
        "TranslationBlock",
        "MachineState",
        "Monitor",
    ]

    h = generate_header(
        struct_list, elf_file, use_provider_executable_instead_of_api=True
    )

    # correction to make this not architecture neutral
    h = h.replace("void *env_ptr;", "CPU" + arch + "State *env_ptr;")

    # cffi doesn't support 128 bit
    # we can't just do the following:
    # h = "typedef char __int128[16];\n" + h
    # because pycparser errors on this. thus, we do:

    h = h.replace("__int128 ", "__int128_artificial ")
    h = "typedef char __int128_artificial[16];\n" + h

    # print(h)
    validate_header(h, types_to_check=struct_list)

    import os

    os.makedirs("./output", exist_ok=True)
    OUT_FILE_NAME = "./output/panda_datatypes_" + arch + "_" + str(bits) + ".h"
    with open(OUT_FILE_NAME, "w") as f:
        f.write(h)
    print("qemu_symbols_generate: Finished. Content written to " + OUT_FILE_NAME)


numgen = 0

for arch in archs:
    file_path = panda_base + arch[2]
    if os.path.exists(file_path):
        print("qemu_symbols_generate: %s found, generating..." % file_path)
        generate_config(arch=arch[0], bits=arch[1], elf_file=file_path)
        numgen += 1
    else:
        print("qemu_symbols_generate: %s doesn't exist. Skipping." % file_path)

print("Number of generated headers: " + str(numgen))
