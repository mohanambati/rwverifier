import sys, os, subprocess, platform
from os import listdir
from os.path import isfile, isdir, join

# settings

CLINGO_PATH = "/home/mambati/Documents/clingo-5.2.1-linux-x86_64"
PLATFORM = None
MAINSTR = "//"
COMPLETE = False
CLINGO_OUTPUT = []

# This function captures and displays runtime exception
def displayerrormsg():
    print ("""usage: python verifier.py [options] original_input re-written_input [instance_directory]

              options:

              verify single example
                -s (relative_path original_input) (relative_path re-written_input) (relative_path instance_directory)
                -ns (relative_path original_input) (relative_path re-written_input)

              verify all examples
                None relative_path_directory_name

              """)
    print ("Error : ", sys.exc_info())
    return


# this function reads a file
def read_file(filename):
    f = open(filename, 'r')
    program = f.read()
    f.close()
    return program


# this function writes a file
def write_file(filename, data):
    f = open(filename, 'w')
    f.write(data)
    f.close()
    return filename


# This fuction retuns the exact path of the files.

def getpaths(inputfile, rewrittenfile, randominstance=None):
    currentpath = os.path.dirname(os.path.abspath(__file__))
    inputfile = currentpath + MAINSTR + inputfile
    rewrittenfile = currentpath + MAINSTR + rewrittenfile
    if randominstance:
        randominstance = currentpath + MAINSTR + randominstance
        return inputfile, rewrittenfile, randominstance
    else:
        return inputfile, rewrittenfile


# This function removes the aggregate functions in ASP program.
def parse(program):
    return '.'.join([predicate for predicate in program.split(".") if "#show" not in predicate])


# This function captures the signature elements in the grounded ASP program.
def parse_ground(ground_program):
    return [line.split(' ')[2] for line in ground_program.split("\n") if line.split(' ')[0] == '4']


# This function preprocess the ASP program.
def preprocess(filename, randominstance=None):
    temp = ''
    if type(filename) == list:
        for f in filename:
            temp += read_file(f)
        return parse(temp)
    elif randominstance:
        temp = randominstance + read_file(filename)
        return parse(temp)
    return parse(read_file(filename))


# This function grounds the ASP program.
def gringo(filename, randominstance=None):
    if randominstance:
        grounded_program = subprocess.check_output(
            CLINGO_PATH + "gringo " + write_file("preprocssed.lp", preprocess(filename, randominstance)), shell=True)
        os.system(
            CLINGO_PATH + "clingo --models 0 " + write_file("preprocssed.lp", preprocess(filename, randominstance))+" --outf=2 > temp.JSON")
    else:
        grounded_program = subprocess.check_output(
            CLINGO_PATH + "gringo " + write_file("preprocssed.lp", preprocess(filename)),
            shell=True)
        os.system(
            CLINGO_PATH + "clingo --models 0 " + write_file("preprocssed.lp", preprocess(filename))+" --outf=2 > temp.JSON")
    CLINGO_OUTPUT.append(eval(read_file("temp.JSON")))
    os.remove("preprocssed.lp")
    os.remove("temp.JSON")
    return grounded_program

# This function returns the answersets of programs.
def compute_answersets():
    answersets = []
    for prg_out in CLINGO_OUTPUT:
        assert prg_out['Result'] == "SATISFIABLE",\
         "Program Not Satisfied."
        answersets.append([prg_out["Models"]["Number"], prg_out["Call"][0]["Witnesses"]])
    return answersets

# This function checks for one to one correspondence of answer sets.
def check_correspondence(answersets, extrapredicates):
    assert answersets[0][0] == answersets[1][0],\
                "Number of answersets are not same. Solving test failed."

    original= [model['Value'] for model in answersets[0][1]]
    temp_rewrite = [model['Value'] for model in answersets[1][1]]
    rewrite = []
    for model in temp_rewrite:
        cleanmodel = [ansset for ansset in model if ansset not in extrapredicates]
        rewrite.append(cleanmodel)
    # print original, rewrite
    return sorted(original) == sorted(rewrite)

# This function verfies all the examples.
def verifyall(directoryname):
    currentpath = os.path.dirname(os.path.abspath(__file__))
    examplepath = currentpath + MAINSTR + directoryname
    examples = [f for f in listdir(examplepath) if isdir(join(examplepath, f))]
    for example in examples:
        print ("\n")
        print (example)
        print ("\n")
        currentpath = examplepath
        correspondence = True
        currentpath += MAINSTR + example
        inpath = currentpath
        files = [f for f in listdir(currentpath) if isfile(join(currentpath, f))]
        dirs = [f for f in listdir(currentpath) if isdir(join(currentpath, f))]
        if dirs:
            currentpath += MAINSTR + dirs[0]
            instances = [f for f in listdir(currentpath) if isfile(join(currentpath, f))]
        else:
            instances = None

        for file in files:
            if 'example' in file:
                inputfile = file
                break

        for file in files:
            if 'rewrite' in file:
                rewrittenfile = file
                break

        if instances:
            for instancefile in instances:
                print ("instance : ", instancefile)
                instance = read_file(currentpath + MAINSTR + instancefile)
                print (inpath)
                if not verify_specific(inpath + MAINSTR + inputfile, inpath + MAINSTR + rewrittenfile, instance):
                    correspondence = False
                    break
        else:
            if not verify_specific(inpath + MAINSTR + inputfile, inpath + MAINSTR + rewrittenfile, ''):
                correspondence = False

        if correspondence:
            print ("Answer sets of both programs are in one to one correspondence")
        else:
            print ("Answer sets of both programs are not in one to one correspondence")

# This function starts the tests for clingo output.
def solvertest(old_signature,new_signature):
    global COMPLETE
    assert len(old_signature) > 0 or len(new_signature) > 0,\
        "Empty signature sets. Ground test failed."
    if not old_signature == (old_signature & new_signature):
        print ("Grounding test failed.")
        COMPLETE = True
        return False
    else:
        print ("Grounding test completed.")
        extrapredicates = new_signature - (old_signature & new_signature)
        assert check_correspondence(compute_answersets(), extrapredicates),\
        "Failed in solving test."
        print("Solving test completed.")
    COMPLETE = True
    return True

# this function verifies the input and rewritten files for a given specific random instance.
def verify_specific(inputfile, rewrittenfile, randominstance=None):
    global CLINGO_PATH, CLINGO_OUTPUT
    CLINGO_PATH = ''
    CLINGO_OUTPUT = []
    old_signature = set(parse_ground(gringo(inputfile, randominstance)))
    new_signature = set(parse_ground(gringo(rewrittenfile, randominstance)))
    #print ("old signature : ", old_signature)
    #print ("new signature : ", new_signature)
    return solvertest(old_signature, new_signature)

# this function verifies the input and rewritten files for a directory of instances.
def verify_seperate(inputfile, rewrittenfile, randominstance=None):
    global CLINGO_OUTPUT
    print ("\n")
    print (inputfile)
    print ("\n")
    inputfile, rewrittenfile, randominstance = getpaths(inputfile, rewrittenfile, randominstance)

    instancefiles = [f for f in listdir(randominstance) if isfile(join(randominstance, f))]

    for file in instancefiles:
        CLINGO_OUTPUT = []
        if '.lp' in file:
            print ("Instance : ", file)
            instance = read_file(randominstance + '/' + file)
            old_signature = set(parse_ground(gringo(inputfile, instance)))
            new_signature = set(parse_ground(gringo(rewrittenfile, instance)))
            if not solvertest(old_signature, new_signature):
                return False
    return True

# this function verifies the input and rewritten files without instance files.
def verify_nonseperate(inputfile, rewrittenfile):
    global CLINGO_OUTPUT 
    CLINGO_OUTPUT = []
    inputfile, rewrittenfile = getpaths(inputfile, rewrittenfile)
    old_signature = set(parse_ground(gringo(inputfile)))
    new_signature = set(parse_ground(gringo(rewrittenfile)))
    #print ("old signature : ", old_signature)
    #print ("new signature : ", new_signature)
    return solvertest(old_signature, new_signature)

# The program starts here. this part of code checks the usauge of tool and handles it.
if __name__ == "__main__":
    PLATFORM = platform.system()
    if PLATFORM == "Windows":
        MAINSTR = "\\"
        CLINGO_PATH = ''
    elif PLATFORM == "Linux":
        MAINSTR = "/"
        assert CLINGO_PATH, \
            "Please enter you gringo executable path in CLINGO_PATH variable."
        CLINGO_PATH = CLINGO_PATH.strip()
        CLINGO_PATH = CLINGO_PATH + '/' if CLINGO_PATH[len(CLINGO_PATH) - 1] != '/' else CLINGO_PATH

    assert PLATFORM in ["Windows", "Linux"], \
        "Platform not supported."

    if len(sys.argv) == 2:
        verifyall(sys.argv[1])
    else:
        if sys.argv[1] == "-s":
            assert verify_seperate(sys.argv[2], sys.argv[3], sys.argv[4]), \
                "Answer sets of both programs are NOT in one to one correspondence"
        elif sys.argv[1] == "-ns":
            assert verify_nonseperate(sys.argv[2], sys.argv[3]), \
                "Answer sets of both programs are NOT in one to one correspondence"
        assert COMPLETE, \
            "Process not completed due to errors."
        print("Answer sets of both programs are in one to one correspondence")



