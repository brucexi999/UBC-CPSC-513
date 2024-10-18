import re


def extract_variables(c_code):
    """Extracts the variable declarations from the C code."""
    match = re.search(r'int\s+(\w+)\s*\[(\d+)\]', c_code)
    if match:
        arr_name = match.group(1)
        arr_size = int(match.group(2))
        return arr_name, arr_size
    else:
        return None, 0


def convert_c_to_smt(c_code):
    smt_script = "(set-logic ALL)\n(set-option :produce-models true)\n(set-option :incremental true)\n(set-option :produce-unsat-cores true)\n(set-option :print-cores-full true)\n\n"

    # Extract array name and size from the C code
    arr_name, arr_size = extract_variables(c_code)

    if not arr_name or arr_size == 0:
        print("No array variables found in the code.")
        return ""

    # Declare variables for each element in the array
    smt_script += "; Declare array elements as symbolic variables\n"
    for i in range(arr_size):
        smt_script += f"(declare-const x{i} Int)\n"

    smt_script += "\n; Sorting logic\n"

    # Declare variables for the intermediate sorted positions
    for i in range(arr_size-1):  # You need n-1 iterations in the outer loop to complete the sorting
        for j in range(arr_size):
            smt_script += f"(declare-const arr{i}_{j} Int)\n"

        if (i > 0):
            smt_script += "\n"
            for j in range(i):
                smt_script += f"(assert (= arr{i}_{j} arr{j}_{j}))\n"

            smt_script += "\n(assert (or \n"

            for j in range(i, arr_size):
                smt_script += f" (and (= arr{i}_{i} arr{i-1}_{j})"
                for k in range(i, arr_size):
                    if (k != j):
                        smt_script += f" (<= arr{i-1}_{j} arr{i-1}_{k})"
                smt_script += ")\n"

            smt_script += "))\n\n"

        else:
            smt_script += "\n(assert (or \n"

            for j in range(arr_size):
                smt_script += f" (and (= arr{i}_{i} x{j})"
                for k in range(arr_size):
                    if (k != j):
                        smt_script += f" (<= x{j} x{k})"
                smt_script += f") ; if x{j} is min\n"

            smt_script += "))\n\n"

    # Postcondition: Array should be sorted
    smt_script += "\n; Check if the array is sorted\n"

    smt_script += "(assert (and"
    for i in range(arr_size - 1):
        smt_script += f" (<= arr{arr_size - 2}_{i} arr{arr_size - 2}_{i+1})"
    smt_script += "))\n"

    smt_script += "\n(assert (not (and"
    for i in range(arr_size - 1):
        smt_script += f" (<= arr{arr_size - 2}_{i} arr{arr_size - 2}_{i+1})"

    smt_script += ")))\n"

    # Check satisfiability
    smt_script += "(check-sat)\n"

    # Get the counter example
    smt_script += "(get-model)	; See the counter-example"

    return smt_script


c_code_path = "selection_sort.c"
with open(c_code_path, "r") as f:
    c_code = f.read()

# Convert the sorting C code to SMT-LIBv2
smt_script = convert_c_to_smt(c_code)
with open("smt_instance.smt2", "w") as f:
    f.write(smt_script)
