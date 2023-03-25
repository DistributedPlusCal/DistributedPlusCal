import glob
import shutil
import sys
import json
import os
import subprocess
from pathlib import Path
import shutil


# jar location for parsing test
jar_parse = "tlatools/dist/tla2tools.jar"

# jar location for checking test
jar_check =  "tlatools/dist/tla2tools.jar"

# jar location for sanity test
jar_sanity =  "tlatools/dist/tla2tools.jar"

# path where all the tests are located
main_path = "tlatools/test-distpcal"
# path where all pre-compiled specifications are located
compare_path = "tlatools/test-compare"
# path where all result are saved
result_path = "tlatools/test-result"
# path where all compiled specifications are saved
compile_path = "tlatools/test-compile"

# Do we do model checking ?
do_check = True

# Do we compare to existing results ?
do_compare = True

output_to_file = False

# Remove generated files: MtestXXX, .old, .cfg
delete_generated = False
# Max time in second before timeout of a test
TIMEOUT_TIME = 60

# 0 = print nothing
# 1 = print summary
# 2 = print summary of each test
# 3 = print all
# 4 = print all + more output
verbose_level = 1

# generated file prefix
GEN_FILE_PREFIX = "Mtest"

# - - - - - - - - - - - - - - - - - - - - -
# run a pluscal parsing test test
def run_parsing(tla_file_path):

    # run the command
    try:
        cmd = ["java", "-cp", jar_parse, "pcal.trans", "-label", tla_file_path]
        output = subprocess.run(cmd, capture_output=True,
                                text=True, timeout=TIMEOUT_TIME)
    except:
        if verbose_level >= 3:
            print(output.stderr)
        output = "timeout"
    return output


# - - - - - - - - - - - - - - - - - - - - -
# run tlc checking parse test
def run_checking(tla_file_path, args):

    # create the command
    cmd = ["java", "-XX:+UseParallelGC", "-jar", jar_check, "-metadir", tla_file_path+"_metadir/", tla_file_path]
    for a in args:
        cmd.append(a)

    # run the command
    try:
        output = subprocess.run(cmd, capture_output=True,
                                text=True, timeout=TIMEOUT_TIME)
    except:
        output = "timeout"
    return output

# - - - - - - - - - - - - - - - - - - - - -
# run tlc sanity test
def run_sanity(tla_file_path, args):

    # create the command
    cmd = ["java", "-cp", jar_sanity, "tla2sany.SANY", tla_file_path]
    for a in args:
        cmd.append(a)

    # run the command
    try:
        output = subprocess.run(cmd, capture_output=True,
                                text=True, timeout=TIMEOUT_TIME)
    except:
        if verbose_level >= 3:
            print(output.stderr)
        output = "timeout"
    return output

# - - - - - - - - - - - - - - - - - - - - -
# run parse and compare test
def run_compare_parse(tla_file_path_1, tla_file_path_2):
    # parse the 2 files
    run_parsing(tla_file_path_1)
    run_parsing(tla_file_path_2)
    return run_compare(tla_file_path_1, tla_file_path_2)


# - - - - - - - - - - - - - - - - - - - - -
# run compare test
def run_compare(tla_file_path_1_in, tla_file_path_2_in):
    # read the first file
    str_1 = ""
    f1 = open(tla_file_path_1_in, "r")
    line = f1.readline()
    while line:
        if line.startswith("\\* BEGIN TRANSLATION"):
            line = f1.readline()
            while line and not line.startswith("\\* END TRANSLATION"):
                str_1 += line
                line = f1.readline()
        line = f1.readline()
    f1.close()

    # read the second file
    str_2 = ""
    f2 = open(tla_file_path_2_in, "r")
    line = f2.readline()
    while line:
        if line.startswith("\\* BEGIN TRANSLATION"):
            line = f2.readline()
            while line and not line.startswith("\\* END TRANSLATION"):
                str_2 += line
                line = f2.readline()
        line = f2.readline()
    f2.close()

    # compare the two files
    return str_1 == str_2

# - - - - - - - - - - - - - - - - - - - - -
# Create the .cfg and .tla test files from a spec file
def create_cfg(path, file_name, constants):
    test_file_name = GEN_FILE_PREFIX + file_name

    # write tla file
    test_file_tla = open(os.path.join(path, test_file_name + ".tla"), "w")

    # write start of module
    test_file_tla.write("---- MODULE " + test_file_name + " ----\n")
    test_file_tla.write("EXTENDS " + file_name + "\n\n")

    # write each constant
    for k, v in constants.items():
        test_file_tla.write("Const" + str(k) + " == " + str(v) + "\n\n")

    # write end of module
    test_file_tla.write("====\n")
    test_file_tla.close()

    # write cfg file
    test_file_cfg = open(os.path.join(path, test_file_name + ".cfg"), "w")
    # write each constant
    for k, v in constants.items():
        test_file_cfg.write("CONSTANT\n" + str(k) + " <- Const" + str(k) + "\n")
    # write specification
    test_file_cfg.write("SPECIFICATION\nSpec\n")
    test_file_cfg.close()


# - - - - - - - - - - - - - - - - - - - - -
# Remove the generated .cfg and .tla test files
def remove_cfg(path, file_name):
    # remove original TLA file (copied from test directory)
    try: 
        os.remove(os.path.join(path, file_name + ".tla"))
    except:
        if verbose_level >= 2:
            print("\n    Warning: Missing otiginal TLA file in compile directory")

    # remove files generated for model-checking 
    test_file_name = GEN_FILE_PREFIX + file_name
    try: 
        os.remove(os.path.join(path, test_file_name + ".tla"))
        os.remove(os.path.join(path, test_file_name + ".cfg"))
        shutil.rmtree(os.path.join(path, test_file_name + ".tla_metadir/"))
    except:
        if verbose_level >= 2:
            print("\n    Warning: Missing generated",GEN_FILE_PREFIX,"(OLD,CFG) files ")

# - - - - - - - - - - - - - - - - - - - - -
# Remove the generated .cfg and .old files
def remove_gen(path, file_name):
    try: 
        os.remove(os.path.join(path, file_name + ".old"))
        os.remove(os.path.join(path, file_name + ".cfg"))
    except:
        if verbose_level >= 2:
            print("\n    Warning: Missing generated OLD,CFG files ")

# - - - - - - - - - - - - - - - - - - - - -
# Print the message and add to file if applicable
def output_message(file,message):
    print(message)
    if file != None:
        file.write(message + "\n")

# - - - - - - - - - - - - - - - - - - - - -
# Print json options
def print_json(options):
    print("    ", options)

# - - - - - - - - - - - - - - - - - - - - -
# Process results of execution
def process_result(test_name,completed_process,phase,need_error):
    ok = phase+'_ok';
    error = phase+'_error';
    detail = phase+'_detail';
    
    if completed_process == "timeout":
        tests[test_name][ok] = False
        tests[test_name][error] = "Timeout"
    else:
        code = completed_process.returncode
        if code == 0: # process succeeded 
            if need_error: # but error was expected (instead of correct behaviour)
                tests[test_name][ok] = False
                tests[test_name][error] = "noerror"
            else:
                tests[test_name][ok] = True
                tests[test_name][error] = "ok"
                nb_test[ok] += 1
        else: # process failed
            if need_error: # and this was expected
                tests[test_name][ok] = True
                tests[test_name][error] = "errorWasExpected"
                nb_test[ok] += 1
            else:
                tests[test_name][ok] = False
                tests[test_name][error] = completed_process.stderr
                tests[test_name][detail] = completed_process.stdout
    if verbose_level >= 2:
        if tests[test_name][ok]:
            print('  :: ',phase,' OK')
        else:
            print('  :: ',phase,' ERROR')

# - - - - - - - - - - - - - - - - - - - - -
# Check command line arguments
def check_args():
    global jar_parse, jar_check, verbose_level, main_path, do_check, do_compare, delete_generated, output_to_file
    i = 0
    while i < len(sys.argv):
        if sys.argv[i] in ('-h', "--help"):
            print(sys.argv[0], "[-h] [-jp <jar_path>] [-jc <jar_path>] [-v <0..3>] [-tp <test_path>] [-dc] [-o]")
            exit()
        elif sys.argv[i] in ("-jp", "--jar_parse"):
            if i+1 >= len(sys.argv):
                print("error: need value after option", sys.argv[i])
                exit()
            i += 1
            jar_parse = sys.argv[i]
        elif sys.argv[i] in ("-jc", "--jar_check"):
            if i+1 >= len(sys.argv):
                print("error: need value after option", sys.argv[i])
                exit()
            i += 1
            jar_check = sys.argv[i]
        elif sys.argv[i] in ("-v", "--verbose"):
            if i+1 >= len(sys.argv):
                print("error: need value after option", sys.argv[i])
                exit()
            i += 1
            verbose_level = int(sys.argv[i])
        elif sys.argv[i] in ("-tp", "--test_path"):
            if i+1 >= len(sys.argv):
                print("error: need value after option", sys.argv[i])
                exit()
            i += 1
            main_path = sys.argv[i]
        elif sys.argv[i] in ("-o", "--output"):
            output_to_file = True
        elif sys.argv[i] in ("-dck", "--disable_check"):
            do_check = False
            print("No model-check")
        elif sys.argv[i] in ("-dco", "--disable_compare"):
            do_compare = False
            print("No compare")
        elif sys.argv[i] in ("-dg", "--delete_generated"):
            delete_generated = True
        i += 1

# - - - - - - - - - - - - - - - - - - - - -
# Main
check_args()

# setup path variables
jar_file = os.path.join(os.getcwd(), jar_parse)
test_path = os.path.join(os.getcwd(), main_path)

nb_test = {}
nb_test['comp'] = 0
nb_test['comp_ok'] = 0
nb_test['check'] = 0
nb_test['check_ok'] = 0
nb_test['compare'] = 0
nb_test['compare_ok'] = 0

# get all tla test files
tests = {}
tmp_files = sorted(glob.glob(os.path.join(test_path, "**/*.tla"), recursive = True))
for f in tmp_files:
    base_name = os.path.basename(f)
    if not base_name.startswith(GEN_FILE_PREFIX) and os.path.isfile(f):
        relpath = os.path.relpath(f, test_path)
        path = os.path.join(compile_path, relpath)
        try:
            os.makedirs(os.path.dirname(path))
        except:
            pass
        shutil.copy(f, path)
        tests[base_name] = {"path": path}

# print test find
if verbose_level >= 3:
    print("--- Test find ---")
    for test in tests.values():
        print(" ", test["path"])

# - - - - -
# Init phase
if verbose_level >= 1:
    print('--- Init ---')
for t in tests:
    test = tests[t]
    
    if verbose_level >= 2:
        print(" ", t, end="", flush=True)

    # read json from tla file
    try:
        json_str = ""
        f = open(test["path"], "r")
        line = f.readline()
        while line:
            if line.startswith("===="):
                line = f.readline()
                while line and not line.startswith("===="):
                    json_str += line
                    line = f.readline()
            line = f.readline()
        if json_str:
            test["json"] = json.loads(json_str)
        else:
            # default options
            test["json"] = json.load("{'need-error-parse': False,'need-error-check': False}")
    except:
        test["json"] = "{'error':true}"

    if verbose_level >= 2:
        print('  :: parse JSON done')
        if verbose_level >= 3:
            print_json(test["json"])

# - - - - -
# Translate  phase
if verbose_level >= 1:
    print('--- Translate  ---')
for t in tests:
    test = tests[t]
    if verbose_level >= 2:
        print(" ", t, end="", flush=True)
    # run test
    completed_process = run_parsing(test["path"])
    nb_test['comp'] += 1
    # check if an error is expected 
    need_error = False
    if "need-error-parse" in test["json"]:
        need_error = test["json"]["need-error-parse"]
    # process the result of the command
    process_result(t,completed_process,'comp',need_error)

# - - - - -
# Checking phase
if do_check:
    if verbose_level >= 1:
        print('--- TLC ---')
    for t in tests:
        test = tests[t]
        # only files that compiled correctly (not those for which a parse error was expected)
        if test["comp_ok"] and test['comp_error']=="ok":
            if verbose_level >= 2:
                print(" ", t, end="", flush=True)
            # create cfg and tla files
            constants = {}
            if "model-checking-args" in test["json"]:
                constants = test["json"]["model-checking-args"]
            file_dir = os.path.dirname(test["path"])
            file_name = os.path.splitext(os.path.basename(test["path"]))[0]
            create_cfg(file_dir, file_name, constants)
            # run test
            args = []
            if "args-check" in test["json"]:
                args = test["json"]["args-check"]
            test_file_name = os.path.join(file_dir, GEN_FILE_PREFIX + file_name + ".tla")
            if "just-sanity" in test["json"]:
                completed_process = run_sanity(test["path"], args)
            else:
                completed_process = run_checking(test_file_name, args)
            nb_test['check'] += 1
            # check if an error is expected 
            need_error = False
            if "need-error-check" in test["json"]:
                need_error = test["json"]["need-error-check"]
            # process the result of the command
            process_result(t,completed_process,'check',need_error)
        else:
            test['check_ok'] = False
            test['check_error'] = "Not parsed"
            test['check_detail'] = ""

# - - - - -
# Compare phase
if do_compare:
    if verbose_level >= 1:
        print('--- Compare ---')
    for t in tests: 
        test = tests[t]
        if verbose_level >= 2:
            print(" ", t, end="", flush=True)
        if "compare_to" in test["json"]:
            compare_name = test["json"]["compare_to"]
            # if other path than the default one, compare_path
            current_compare_path = os.path.join(os.getcwd(), compare_path)
            if "compare_path" in test["json"]: 
                if test["json"]["compare_path"] == "compile":
                    current_compare_path = os.path.join(os.getcwd(), compile_path)
            compare_file = os.path.join(current_compare_path,compare_name)
            nb_test['compare'] += 1
            if verbose_level >= 2:
                print(" to ", compare_name, end="", flush=True)
            if os.path.exists(compare_file):
                completed_process = run_compare(test["path"], compare_file)
                if completed_process:
                    test['compare_ok'] = True
                    nb_test['compare_ok'] += 1
                    test['compare_error'] = "ok"
                else:
                    test['compare_ok'] = False
                    test['compare_error'] = "file different"
            else:
                test['compare_ok'] = False
                test['compare_error'] = "file "+compare_file+" doesn't exist"
        else:
            test['compare_ok'] = True
            test['compare_error'] = "errorWasExpected"

        if verbose_level >= 2:
            if test['compare_ok']:
                print('  :: compare :: OK')
            else:
                print('  :: compare :: ERROR')

# - - - - -
# Cleaning phase
if delete_generated:
    for t in tests:
        test = tests[t]
        file_dir = os.path.dirname(test["path"])
        file_name = os.path.splitext(os.path.basename(test["path"]))[0]
        # remove generated files 
        remove_gen(file_dir, file_name)
        # remove generated files if flag
        remove_cfg(file_dir, file_name)
                
# - - - - -
# Display result
if verbose_level >= 1:
    print('--- STATS ---')
if verbose_level >= 2:
    for t in tests:
        out_file = None
        if output_to_file:
            relpath = os.path.relpath(tests[t]["path"], compile_path)
            dir = os.path.join(result_path, relpath)
            try:
                os.makedirs(dir)
            except:
                pass
            name = os.path.splitext(os.path.basename(tests[t]["path"]))[0]
            out_file = open(os.path.join(dir, name) + ".out", "w")
        print("============================================")
        print(t)
        # result for compilation
        comp = tests[t]["comp_ok"]
        if comp:
            result_message = "OK"
            if tests[t]['comp_error'] == "errorWasExpected":
                result_message = result_message + " (doesn't translate)"
                comp = False # compilation failed, in fact
            output_message(out_file,"  Compilation: " + result_message)
        else:
            result_message = "Error"
            output_message(out_file,"  Compilation: " + result_message)
            if verbose_level >= 3:
                output_message(out_file,"    Error: " + tests[t]["comp_error"])
                if verbose_level >= 4:
                    output_message(out_file,"    " + tests[t]["comp_detail"])
        # continue only if compilation succeeded
        if comp:
            # result for model-checking
            if do_check:
                mc = tests[t]["check_ok"]
                if mc:
                    result_message = "OK"
                    if tests[t]['check_error'] == "errorWasExpected":
                        result_message = result_message + " (doesn't model-check)"
                        mc = False # model-checking failed, in fact
                    output_message(out_file,"  Model checking: " + result_message)
                else:
                    result_message = "Error"
                    output_message(out_file,"  Model checking: " + result_message)
                    if verbose_level >= 3:
                        output_message(out_file,"    Error: " + tests[t]["check_error"])
                        if verbose_level >= 4:
                            output_message(out_file,"    " + tests[t]["check_detail"])                      
            # result for comparison
            if do_compare:
                compare = tests[t]["compare_ok"]
                if compare:
                    result_message = "OK"
                    if tests[t]['compare_error'] == "errorWasExpected":
                        result_message = result_message + " (no file)"
                    output_message(out_file,"  Compare: " + result_message)
                else:
                    result_message = "Error"
                    output_message(out_file,"  Compare: " + result_message)
                    if verbose_level >= 3:
                        output_message(out_file,"    Error: " + tests[t]["compare_error"])

        if output_to_file:
            out_file.close()

    print("============================================")

if verbose_level >= 1:
    print("Parse test: ", nb_test['comp_ok'], "/", nb_test['comp'])
    print("Check test: ", nb_test['check_ok'], "/", nb_test['check'])
    print("Compare test: ", nb_test['compare_ok'], "/", nb_test['compare'])

if verbose_level >= 1:
    print('--- DONE ---')

if not nb_test['comp_ok'] == nb_test['comp']:
    exit(1)
if not nb_test['check_ok'] == nb_test['check']:
    exit(1)
if not nb_test['compare_ok'] == nb_test['compare']:
    exit(1)
