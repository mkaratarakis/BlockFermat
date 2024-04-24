import re
import os

def get_defs(lean_code):

    defs = r"def\s[\s\S]*?#.+"
    structures = r"structure\s[\s\S]*?#.+"

    defs_list = re.findall(defs, lean_code)
    structures_list = re.findall(structures, lean_code)

    # Merge the lists of definitions and structures
    merged_code = "\n\n".join(defs_list + structures_list)

    return merged_code

def apply_script_to_imports(imports_set):
    # Iterate over each file path in the set of imports
    for file_path in imports_set:
        print(file_path)
        file_name = os.path.basename(file_path)

        with open(file_path, "r") as file:
            original_code = file.read()

        modified_code = get_defs(original_code)

        modified_file_name = f"modified_{file_name}"
        with open(modified_file_name, "w") as file:
            file.write(modified_code)

        print(f"Modified code has been written to {modified_file_name}")

imports_set = {
'/home/michail/blockchain/.lake/packages/mathlib/Mathlib/FieldTheory/Finite/Basic.lean',
'/home/michail/blockchain/.lake/packages/mathlib/Mathlib/FieldTheory/Finite/Polynomial.lean'
}

apply_script_to_imports(imports_set)

