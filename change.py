import os
import re
import pprint

pp = pprint.PrettyPrinter()

# Global list to store accessed imports
accessed_imports = []

# Global dictionary to store imports for each imported file
imports_dict = {}

def remove_align(lean_code):
    # Define a regular expression pattern to match "align" lines
    align_pattern = r"#align.*|set_option linter.uppercaseLean3 false.*"
    # Use re.sub to remove all "align" lines from the code
    modified_code = re.sub(align_pattern, "", lean_code)

    return modified_code

# Function to process imports in a Lean file and store them in a list
def process_imports(lean_code, base_dir, excluded_prefixes, processed_files):
    imports = re.findall(r'import\s+([^#\s]+)', lean_code)
    imports_list = []
    for import_stmt in imports:
        if any(import_stmt.startswith(prefix) for prefix in excluded_prefixes):
            #print("Stopping at import:", import_stmt)
            return False, []
        import_parts = import_stmt.split('.')
        # Capitalize the first letter of each directory name after "Mathlib"
        import_parts[0] = import_parts[0].replace("Mathlib", "", 1).capitalize()  
        import_file_path = os.path.join(base_dir, *import_parts[:-1], import_parts[-1] + ".lean")
        import_file_path = os.path.normpath(import_file_path)  # Normalize the file path
        if not os.path.exists(import_file_path):
            #print("File not found:", import_file_path)
            continue
        if import_file_path in processed_files:
            #print("Already processed:", import_file_path)
            continue
        #print("Processing import:", import_file_path)
        accessed_imports.append(import_file_path)
        processed_files.add(import_file_path)
        with open(import_file_path, 'r') as file:
            imported_lean_code = file.read()
        # Remove aligns
        #modified_imported_code = remove_align(imported_lean_code)
        modified_imported_code = imported_lean_code
        with open(import_file_path, 'w') as file:
            file.write(modified_imported_code)
        continue_processing, imported_imports = process_imports(modified_imported_code, base_dir, excluded_prefixes, processed_files)
        if continue_processing:
            imports_list.append(import_file_path)
            imports_dict[import_file_path] = imported_imports
    return True, imports_list

# Main function to process Lean files recursively
def main():
    base_dir = "/home/michail/blockchain/.lake/packages/mathlib/Mathlib/"  # Base directory path
    main_file = "deligne.lean"  # Main Lean file name
    excluded_prefixes = ["Mathlib.Data", "Mathlib.Control",
                         "Mathlib.Init", "Mathlib.Lean", 
                         "Mathlib.Mathport", 
                          "Mathlib.Tactic", 
                         "Mathlib.Testing", "Mathlib.Util", 
                         "Lean.", "Qq", "Mathlib.util",
                         "Init", "Std", "Aesop"]
    main_file_path = os.path.join(base_dir, main_file)
    with open(main_file_path, 'r') as file:
        main_lean_code = file.read()
    processed_files = set()
    continue_processing, main_imports = process_imports(main_lean_code, base_dir, excluded_prefixes, processed_files)

    # Print the list of accessed imports with no duplicates
    unique_accessed_imports = list(set(accessed_imports))

    # Print the list of all imports
    print("\nList of all imports:")
    pp.pprint(set(unique_accessed_imports))

    # Print the length of the final list of unique imports
    print("\nLength of the final list of unique imports:", len(set(unique_accessed_imports)))

if __name__ == "__main__":
    main()
