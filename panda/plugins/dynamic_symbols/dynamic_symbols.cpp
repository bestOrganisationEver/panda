/* PANDABEGINCOMMENT
 * 
 * Authors:
 * Luke Craig               luke.craig@ll.mit.edu
 * 
 * This work is licensed under the terms of the GNU GPL, version 2. 
 * See the COPYING file in the top-level directory. 
 * 
PANDAENDCOMMENT */
// This needs to be defined before anything is included in order to get
// the PRIx64 macro
#define __STDC_FORMAT_MACROS

// elf.h uses this, important it comes first
#include <cstdint>

extern "C" {
#include "elf.h"
}

#include <iostream> 
#include <vector>
#include <string>
#include <iterator> 
#include <map> 
#include <set>
#include <algorithm>
#include "panda/plugin.h"
#include "osi/osi_types.h"
#include "osi/osi_ext.h"
#include <unordered_map>
#include "osi_linux/endian_helpers.h"


// These need to be extern "C" so that the ABI is compatible with
// QEMU/PANDA, which is written in C
extern "C" {

bool init_plugin(void *);
void uninit_plugin(void *);
#include "dynamic_symbols_int_fns.h"
#include "hooks/hooks_int_fns.h"
#include "syscalls2/syscalls_ext_typedefs.h"
#include "syscalls2/syscalls2_info.h"
#include "syscalls2/syscalls2_ext.h"
#include "proc_start_linux/proc_start_linux.h"
#include "proc_start_linux/proc_start_linux_ppp.h"

}
using namespace std;

map<target_ulong, map<string, target_ulong>> mapping;

#if TARGET_LONG_BITS == 32
#define ELF(r) Elf32_ ## r
#else
#define ELF(r) Elf64_ ## r
#endif

#define DT_INIT_ARRAY	   25		  ,  /* Array with addresses of init fct */
#define DT_FINI_ARRAY	   26		  ,  /* Array with addresses of fini fct */
#define DT_INIT_ARRAYSZ	   27		  ,  /* Size in bytes of DT_INIT_ARRAY */
#define DT_FINI_ARRAYSZ	   28		  ,  /* Size in bytes of DT_FINI_ARRAY */
#define DT_RUNPATH	       29		  ,  /* Library search path */
#define DT_FLAGS	      30		  ,  /* Flags for the object being loaded */
#define DT_PREINIT_ARRAY  32		  ,  /* Array with addresses of preinit fct*/
#define DT_PREINIT_ARRAYSZ 33		  ,  /* size in bytes of DT_PREINIT_ARRAY */
#define DT_NUM		      34		  ,  /* Number used */
#define DT_SUNW_RTLDINF 0x6000000e
#define DT_CONFIG 0x6ffffefa
#define DT_DEPAUDIT 0x6ffffefb
#define DT_AUDIT 0x6ffffefc
#define DT_PLTPAD 0x6ffffefd
#define DT_MOVETAB 0x6ffffefe
#define DT_SYMINFO 0x6ffffeff
#define DT_GNU_HASH 0x6FFFFEF5

vector<int> possible_tags{ DT_PLTGOT , DT_HASH , DT_STRTAB , DT_SYMTAB , DT_RELA , DT_INIT , DT_FINI , DT_REL , DT_DEBUG , DT_JMPREL, 25, 26, 32, DT_SUNW_RTLDINF , DT_CONFIG , DT_DEPAUDIT , DT_AUDIT , DT_PLTPAD , DT_MOVETAB , DT_SYMINFO , DT_VERDEF , DT_VERNEED };

inline bool operator<(const struct symbol& s, const struct symbol& p){
    return s.address < p.address;
}

inline bool operator<(const struct symbol& s, target_ulong p){
    return s.address < p;
}

unordered_map<target_ulong, unordered_map<string, set<struct symbol>>> symbols;
unordered_map<string, set<struct symbol>> unmodded_symbol_mapping;
extern bool panda_please_flush_tb;

vector<struct hook_symbol_resolve> hooks;

void hook_symbol_resolution(struct hook_symbol_resolve *h){
    //printf("adding hook %s %llx\n", h->name, (long long unsigned int) h->cb);
    hooks.push_back(*h);
}

void check_symbol_for_hook(CPUState* cpu, struct symbol s, char* procname, OsiModule *m){
    for (struct hook_symbol_resolve &hook_candidate : hooks){
        if (hook_candidate.enabled){
            if (hook_candidate.procname[0] == 0 || strncmp(procname, hook_candidate.procname, MAX_PATH_LEN -1) == 0){
                //printf("comparing \"%s\" and \"%s\"\n", hook_candidate.name, s.name);

                if (hook_candidate.name[0] == 0 || strncmp(s.name, hook_candidate.name, MAX_PATH_LEN -1) == 0){
                    //printf("name matches\n");
                    if (hook_candidate.section[0] == 0 || strstr(s.section, hook_candidate.section) != NULL){
                        (*(hook_candidate.cb))(cpu, &hook_candidate, s, m);
                    }
                }
            }
        }
    }
}

struct symbol resolve_symbol(CPUState* cpu, target_ulong asid, char* section_name, char* symbol){
    update_symbols_in_space(cpu);

    for (const auto& section : symbols[asid]){
        string n = section.first;
        auto section_vec = section.second;
        size_t found;
        if (section_name == NULL){
            found = 0;
        }else{
            found = n.find(section_name); 
        }
        //section name is A "does string exist in section"
        if (found != string::npos){
            for (auto &it: section_vec){
                struct symbol val = it;
                string val_str (val.name);
                // symbol resolves on exact equality
                if (val_str.compare(symbol) == 0){
                    //printf("result: %s %s\n", section.first.c_str(), val.name);
                    strncpy((char*) &val.section, section.first.c_str(), MAX_PATH_LEN -1);
                    return val;
                }
            }
        } 
    }
    struct symbol blank;
    blank.address = 0;
    memset((char*) & blank.name, 0, MAX_PATH_LEN);
    memset((char*) & blank.section, 0, MAX_PATH_LEN);
    return blank;
}

struct symbol get_best_matching_symbol(CPUState* cpu, target_ulong address, target_ulong asid){
    update_symbols_in_space(cpu);
    struct symbol address_container;
    address_container.address = address;
    struct symbol best_candidate;
    best_candidate.address = 0;
    memset((char*) & best_candidate.name, 0, MAX_PATH_LEN);
    memset((char*) & best_candidate.section, 0, MAX_PATH_LEN);
    for (const auto& section : symbols[asid]){
        set<struct symbol> section_symbols = section.second;
        set<struct symbol>::iterator it = section_symbols.lower_bound(address_container);
        if (it != section_symbols.end()){
            if (it->address == address){
                // if we found a match just break and move on.
                memcpy(&best_candidate, &*it, sizeof(struct symbol));
                break;
            }
            //check that there exists a lower value
            if (it != section_symbols.begin()){
                // get that lower value
                it--;
                // make comparison
                if (it->address > best_candidate.address){
                    //copy it
                    memcpy(&best_candidate, &*it, sizeof(struct symbol));
                }
            }
        }
    }
    return best_candidate;
}

string read_str(CPUState* cpu, target_ulong ptr){
    string buf = "";
    char tmp;
    while (true){
        if (panda_virtual_memory_read(cpu, ptr, (uint8_t*)&tmp,1) == MEMTX_OK){
            buf += tmp;
            if (tmp == '\x00'){
                break;
            }
            ptr+=1;
        }else{
            break;
        }
    }
    return buf;
}

int get_numelements_hash(CPUState* cpu, target_ulong dt_hash){
    //printf("in dt_hash_section 0x%llx\n", (long long unsigned int) dt_hash);
    struct dt_hash_section dt;

    if (panda_virtual_memory_read(cpu, dt_hash, (uint8_t*) &dt, sizeof(struct dt_hash_section))!= MEMTX_OK){
        //printf("got error 2\n");
        return -1;
        //goto nextloop;
    }
    fixupendian(dt.nbuckets);
    //printf("Nbucks: 0x%x\n", dt.nbuckets);
    return dt.nbuckets;
}

int get_numelements_gnu_hash(CPUState* cpu, target_ulong gnu_hash){
    //printf("Just DT_HASH with %s\n", name.c_str());
    // must do gnu_hash method
    // see the following for details:
    // http://deroko.phearless.org/dt_gnu_hash.txt
    // https://flapenguin.me/elf-dt-gnu-hash

    struct gnu_hash_table ght;
    if (panda_virtual_memory_read(cpu, gnu_hash, (uint8_t*)&ght, sizeof(ght))!=MEMTX_OK){
        //printf("got error in gnu_hash_table\n");
        return -1;
    }
    //printf("GNU numbucks: 0x%x, bloom_size 0x%x\n", ght.nbuckets, ght.bloom_size);
    uint32_t* buckets = (uint32_t*) malloc(ght.nbuckets*sizeof(uint32_t));
    assert(buckets != NULL);

    target_ulong bucket_offset = gnu_hash + sizeof(gnu_hash_table) + (ght.bloom_size*sizeof(target_ulong));

    if (panda_virtual_memory_read(cpu, bucket_offset, (uint8_t*) buckets, ght.nbuckets*sizeof(uint32_t)) != MEMTX_OK){
        //printf("Couldn't read buckets\n");
        free(buckets);
        return -1;
    }

    unsigned int last_sym = 0;
    int index = 0;
    for (index = 0; index < ght.nbuckets; index++){
        //printf("%d %x\n", index, buckets[index]);
        if (buckets[index] > last_sym){
            last_sym = buckets[index]; 
        }
    }
    //printf("last_sym %x index: %d\n", last_sym, index);
    
    free(buckets);
    
    uint32_t num = 0;

    uint32_t chain_index = last_sym - ght.symoffset;
    target_ulong chain_address = bucket_offset + (sizeof(uint32_t)*ght.nbuckets);

    while (!(num&1)){
        if (panda_virtual_memory_read(cpu, chain_address + (chain_index * sizeof(uint32_t)), (uint8_t*) &num, sizeof(uint32_t))!= MEMTX_OK){                                
            //printf("Failed loading chains\n");
            return -1;
        }
        chain_index++;
    }
    return chain_index + ght.symoffset;
}

int get_numelements_symtab(CPUState* cpu, target_ulong base, target_ulong dt_hash, target_ulong gnu_hash, target_ulong dynamic_section, target_ulong symtab, int numelements_dyn){
    //printf("Get numelembs symtab 0x%x, 0x%x\n", base, dt_hash);
    if (base != dt_hash){
        int result = get_numelements_hash(cpu, dt_hash);
        if (result != -1)
            return result;
    }
    if (base != gnu_hash){
        //printf("trying gnu_hash\n");
        int result = get_numelements_gnu_hash(cpu, gnu_hash);
        if (result != -1)
            return result;
    }
    // we don't actually have the size of these things 
    // (not included) so we find it by finding the next
    // closest section
    //  target_ulong strtab_min = strtab + 0x100000;
    //printf("continuing onto the end\n");
    target_ulong symtab_min = symtab + 0x100000;
    ELF(Dyn) tag;
    for (int j=0; j< numelements_dyn; j++){
        if (panda_virtual_memory_read(cpu, dynamic_section + j*sizeof(ELF(Dyn)), (uint8_t*)&tag, sizeof(ELF(Dyn))) != MEMTX_OK){
            return -1;
        }
        fixupendian(tag.d_tag);
        fixupendian(tag.d_un.d_ptr);
        if (find(begin(possible_tags), end(possible_tags), (int)tag.d_tag) != end(possible_tags)){
            uint32_t candidate = tag.d_un.d_ptr;
            if (candidate > symtab && candidate < symtab_min){
                symtab_min = candidate;
            }
        }
    }
    return (symtab_min - symtab)/(sizeof(ELF(Dyn)));
}


void find_symbols(CPUState* cpu, OsiProc *current, OsiModule *m){
    target_ulong asid = panda_current_asid(cpu);

    if (m->name == NULL){
        //printf("%s name is null\n", current->name);
        return;
    }
    string name(m->name);

    // we already read this one
    if (symbols[asid].find(name) != symbols[asid].end()){
        //printf("%s %s already exists \n", current->name, m->name);
        return;
    }
    // static variable to store first 4 bytes of mapping
    char elfhdr[4];

    // read first 4 bytes
    if (likely(panda_virtual_memory_read(cpu, m->base, (uint8_t*)elfhdr, 4) != MEMTX_OK)){
        // can't read page.
        return;
    }
    // is it an ELF header?
    if (unlikely(elfhdr[0] == '\x7f' && elfhdr[1] == 'E' && elfhdr[2] == 'L' && elfhdr[3] == 'F')){
        ELF(Ehdr) ehdr;
        // attempt to read memory allocation
        if (panda_virtual_memory_read(cpu, m->base, (uint8_t*)&ehdr, sizeof(ELF(Ehdr))) != MEMTX_OK){
            //printf("cant read elf header\n");
            return;
        }


        target_ulong phnum = ehdr.e_phnum;
        target_ulong phoff = ehdr.e_phoff;
        fixupendian(phnum);
        fixupendian(phoff);

        ELF(Phdr) dynamic_phdr;

        //printf("Read Phdr from 0x%x + 0x%x + j*0x%lx\n", m->base, phoff, (sizeof(ELF(Phdr))));

        for (int j=0; j<phnum; j++){
            if (panda_virtual_memory_read(cpu, m->base + phoff + (j*sizeof(ELF(Phdr))), (uint8_t*)&dynamic_phdr, sizeof(ELF(Phdr))) != MEMTX_OK){
                return;
            }

            fixupendian(dynamic_phdr.p_type)

            if (dynamic_phdr.p_type == PT_DYNAMIC){
                break;
            }else if (dynamic_phdr.p_type == PT_NULL){
                //printf("hit PT_NULL\n");
                return;
            }else if (j == phnum -1){
                //printf("hit phnum-1\n");
                return;
            }
        }
        fixupendian(dynamic_phdr.p_filesz);
        int numelements_dyn = dynamic_phdr.p_filesz / sizeof(ELF(Dyn));
        // iterate over dynamic program headers and find strtab
        // and symtab
        ELF(Dyn) tag;
        target_ulong strtab = 0, symtab = 0, strtab_size = 0, dt_hash = 0, gnu_hash = 0;
        int j = 0;

        fixupendian(dynamic_phdr.p_vaddr);
        while (j < numelements_dyn){
            //printf("Read Dyn PHDR from 0x%x + 0x%x + j*0x%lx\n", m->base, dynamic_phdr.p_vaddr, (sizeof(ELF(Phdr))));
            if (panda_virtual_memory_read(cpu, m->base + dynamic_phdr.p_vaddr + (j*sizeof(ELF(Dyn))), (uint8_t*)&tag, sizeof(ELF(Dyn))) != MEMTX_OK){
                //printf("%s:%s Failed to read entry %d\n", name.c_str(), current->name, j);
                return;
            }

            fixupendian(tag.d_tag);
            fixupendian(tag.d_un.d_ptr);

            if (tag.d_tag == DT_STRTAB){
                //printf("Found DT_STRTAB\n");
                strtab = tag.d_un.d_ptr;
            }else if (tag.d_tag == DT_SYMTAB){
                //printf("Found DT_SYMTAB\n");
                symtab = tag.d_un.d_ptr;
            }else if (tag.d_tag == DT_STRSZ ){
                //printf("Found DT_STRSZ\n");
                strtab_size = tag.d_un.d_ptr;
            }else if (tag.d_tag == DT_HASH){
                //printf("Found DT_HASH\n");
                dt_hash = tag.d_un.d_ptr;
            }else if (tag.d_tag == DT_GNU_HASH){
                //printf("Found DT_GNU_HASH\n");
                gnu_hash = tag.d_un.d_ptr;
            }else if (tag.d_tag == DT_NULL){
                //printf("Found DT_NULL \n");
                j = numelements_dyn;
                //break;
            }

            j++;
        }  

        // some of these are offsets. some are fully qualified
        // addresses. this is a gimmick that can sort-of tell.
        // probably better to replace this at some point
        if (strtab < m->base){
            strtab += m->base;
        }
        if (symtab < m->base){
            symtab += m->base;
        }
        if (dt_hash < m->base){
            dt_hash += m->base;
        }
        if (gnu_hash < m->base){
            gnu_hash += m->base;
        }

        //printf("strtab: %llx symtab: %llx hash: %llx\n", (long long unsigned int) strtab, (long long unsigned int)symtab, (long long unsigned int) dt_hash);

        int numelements_symtab = get_numelements_symtab(cpu,m->base, dt_hash, gnu_hash, m->base + dynamic_phdr.p_vaddr, symtab, numelements_dyn);
        if (numelements_symtab == -1){
            //printf("numelements_symtab not working\n");
            return;
        }

        target_ulong symtab_size = numelements_symtab * sizeof(ELF(Sym));

        //printf("symtab_size %llx strtab_size %llx\n",(long long unsigned int)symtab_size, (long long unsigned int)strtab_size);

        char* symtab_buf = (char*)malloc(symtab_size);
        char* strtab_buf = (char*)malloc(strtab_size);

        //printf("symtab %llx\n", (long long unsigned int) symtab);
        //printf("symtab: 0x" TARGET_FMT_lx "  0x" TARGET_FMT_lx "\n", symtab, strtab);
        if (panda_virtual_memory_read(cpu, symtab, (uint8_t*)symtab_buf, symtab_size) == MEMTX_OK &&
            panda_virtual_memory_read(cpu, strtab, (uint8_t*) strtab_buf, strtab_size) == MEMTX_OK){
            int i = 0; 
            //for (int idx =0; idx < strtab_size; idx++)
            //  printf("Strtab[%d]: %c\n", idx, strtab_buf[idx]);

            for (;i<numelements_symtab; i++){
                ELF(Sym)* a = (ELF(Sym)*) (symtab_buf + i*sizeof(ELF(Sym)));
                fixupendian(a->st_name);
                fixupendian(a->st_value);
                if (a->st_name < strtab_size && a->st_value != 0){
                    struct symbol s;
                    strncpy((char*)&s.name, &strtab_buf[a->st_name], MAX_PATH_LEN-1);
                    strncpy((char*)&s.section, m->name, MAX_PATH_LEN-1);
                    s.address = m->base + a->st_value;
                    //printf("found symbol %s %s 0x%llx\n",s.section, &strtab_buf[a->st_name],(long long unsigned int)s.address);
                    symbols[asid][name].insert(s);
                    check_symbol_for_hook(cpu, s, current->name, m);
                }
            }
        }
        free(symtab_buf);
        free(strtab_buf);
    }
}


void update_symbols_in_space(CPUState* cpu){
    if (panda_in_kernel(cpu)){
        return;
    }
    OsiProc *current = get_current_process(cpu);
    GArray *ms = get_mappings(cpu, current);
    if (ms == NULL) {
        return;
    } else {
        //iterate over mappings
        for (int i = 0; i < ms->len; i++) {
            OsiModule *m = &g_array_index(ms, OsiModule, i);
            find_symbols(cpu, current, m);
        }
    }
}

void* self_ptr;
panda_cb pcb_asid;
panda_cb pcb_btc;
panda_cb pcb_btc_execve;


void btc(CPUState *env, TranslationBlock *tb){
    if (!panda_in_kernel(env)){
        update_symbols_in_space(env);
        panda_disable_callback(self_ptr, PANDA_CB_BEFORE_TCG_CODEGEN, pcb_btc);
    }
}

bool asid_changed(CPUState *env, target_ulong old_asid, target_ulong new_asid) {
    //panda_please_flush_tb = true;
    panda_enable_callback(self_ptr, PANDA_CB_BEFORE_TCG_CODEGEN, pcb_btc);
    return false;
}

void hook_program_start(CPUState *env, TranslationBlock* tb, struct hook* h){
    //printf("got to program start 0x%llx\n", (long long unsigned int)rr_get_guest_instr_count());
    update_symbols_in_space(env);
    h->enabled = false;
}

void (*dlsym_add_hook)(struct hook*);

void recv_auxv(CPUState *env, TranslationBlock *tb, struct auxv_values av){
    struct hook h;
    h.addr = av.entry;
    h.asid = panda_current_asid(env);
    h.type = PANDA_CB_BEFORE_TCG_CODEGEN;
    h.cb.before_tcg_codegen = hook_program_start;
    h.km = MODE_USER_ONLY;
    h.enabled = true;
    dlsym_add_hook(&h);
}

bool init_plugin(void *self) {
    self_ptr = self;
    pcb_asid.asid_changed = asid_changed;
    panda_register_callback(self, PANDA_CB_ASID_CHANGED, pcb_asid);
    pcb_btc.before_tcg_codegen = btc;
    panda_register_callback(self, PANDA_CB_BEFORE_TCG_CODEGEN, pcb_btc);
    panda_disable_callback(self, PANDA_CB_BEFORE_TCG_CODEGEN, pcb_btc);
    panda_require("osi");
    assert(init_osi_api());
    panda_require("proc_start_linux");
    PPP_REG_CB("proc_start_linux",on_rec_auxv, recv_auxv);
    void* hooks = panda_get_plugin_by_name("hooks");
    if (hooks == NULL){
        panda_require("hooks");
        hooks = panda_get_plugin_by_name("hooks");
    }
    if (hooks != NULL){
        dlsym_add_hook = (void(*)(struct hook*)) dlsym(hooks, "add_hook");
        if ((void*)dlsym_add_hook == NULL) {
            printf("couldn't load add_hook from hooks\n");
            return false;
        }
    }
    return true;
}

void uninit_plugin(void *self) { 
}
