from __future__ import print_function
import sys

sys.path[0:0] = ['.', '..']

from elftools.common.py3compat import bytes2str
from elftools.elf.elffile import ELFFile
from elftools.elf.sections import SymbolTableSection

def process_file(filename):
    """ Maps names to addresses using ELF data and names to types
        using DWARF data.
    """
    print('Processing file:', filename)
    with open(filename, 'rb') as f:
        elf_entries = get_ELF_entries(f)
        get_DWARF_entries(f, elf_entries)
        
def get_ELF_entries(stream):
    """ Creates dictionaries of object, variable, and file names to
        memory addresses using ELF data.
    """
    elffile = ELFFile(stream)
    section = elffile.get_section_by_name(b'.symtab')

    entries = {'OBJECTS':dict(), 'FUNCTIONS':dict(), 'FILES':dict()}
    if not section:
        print('  No symbol table found. Perhaps this ELF has been stripped?')
        return
    if isinstance(section, SymbolTableSection):

        for i in section.iter_symbols():
            if 'STT_OBJECT' == i.entry['st_info']['type']:
                entries['OBJECTS'][i.name] = "0x%x"%(i.entry['st_value'],)
            elif 'STT_FUNC' == i.entry['st_info']['type']:
                entries['FUNCTIONS'][i.name] = "0x%x"%(i.entry['st_value'],)
            elif 'STT_FILE' == i.entry['st_info']['type'] and i.name != "":
                entries['FILES'][i.name] = "0x%x"%(i.entry['st_value'],) 
        print("\n_____________\n\nELF INFO\n_____________")
        print('\nFiles:')
        for fn in entries['FILES']:
            print(fn, entries['FILES'][fn])       
        print('\nFunctions:') 
        for fn in entries['FUNCTIONS']:
            print(fn, entries['FUNCTIONS'][fn])
        print('\nObjects:') 
        for fn in entries['OBJECTS']:
            print(fn, entries['OBJECTS'][fn])
        return entries

def get_DWARF_entries(stream, elf_entries):
    """ Prints variable names and types and function names determined by DWARF 
        data and addresses from the ELF dictionaries.
    """
    elffile = ELFFile(stream)
    if not elffile.has_dwarf_info():
        print('  file has no DWARF info')
        return
    dwarfinfo = elffile.get_dwarf_info()
    print("\n_____________\n\nDWARF INFO\n_____________")

    for compile_unit in dwarfinfo.iter_CUs():
        print("\nCOMPILE UNIT: ", compile_unit.get_top_DIE().get_full_path())
        entries = make_entry_dictionaries(compile_unit)
        print("Variables:")
        for offset in entries['VARIABLES']:
            type_offset = entries['VARIABLES'][offset].attributes['DW_AT_type'].value
            type_name = find_data_type(entries, type_offset, 0)
            name = entries['VARIABLES'][offset].attributes['DW_AT_name'].value
            address = ""
            try:
                address = elf_entries['OBJECTS'][name]
            except:
                pass
            print("\t", type_name, name, address)
        print("Functions:")
        for offset in entries['FUNCTIONS']:
            name = entries['FUNCTIONS'][offset].attributes['DW_AT_name'].value
            address = ""
            try:
                address = elf_entries['FUNCTIONS'][name]
            except:
                pass
            print("\t", name, address) 
        print("_____________")
    return None

def make_entry_dictionaries(compile_unit):
    """ Creates dictionaries for mapping DIE entries to their type references.
    """
    cu_offset = compile_unit.cu_offset
    entries = {'FUNCTIONS':dict(), 'VARIABLES':dict(), 'TYPES':dict(), 'OTHER':dict()}

    for DIE in compile_unit.iter_DIEs():
        try:
            offset = DIE.offset - cu_offset
            if DIE.tag == 'DW_TAG_subprogram':
                entries['FUNCTIONS'][offset] = DIE
            elif DIE.tag == 'DW_TAG_variable':
                entries['VARIABLES'][offset] = DIE
            elif DIE.tag == 'DW_TAG_base_type':
                entries['TYPES'][offset] = DIE
            else:
                entries['OTHER'][offset] = DIE
        except KeyError:
            continue
    return entries

def find_data_type(entries, reference, depth):
    """ Recursively follows DIE entries' type references to a basic type and returns
        a string description of the type.
    """
    try:
        type_name = entries['TYPES'][reference].attributes['DW_AT_name'].value
        return type_name
    except KeyError:
        try: 
            points_to = entries['OTHER'][reference].attributes['DW_AT_type'].value
            if depth > 10:
                return ""
            if entries['OTHER'][reference].tag == 'DW_TAG_pointer_type':
                return find_data_type(entries, points_to, depth + 1) + "*"
            else: 
                tag = entries['OTHER'][reference].tag
                other_type = tag.replace("DW_TAG_", "").replace("_type", "")
                return other_type + " " + find_data_type(entries, points_to, depth + 1)
        except:
            return ""

if __name__ == '__main__':
    for filename in sys.argv[1:]:
        process_file(filename)

