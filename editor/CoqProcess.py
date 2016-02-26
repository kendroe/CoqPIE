#
# PIE - Python based IDe for Coq
#
# CoqProcess.py
#
# (C) 2015, 2016 Kenneth Roe
# All rights reserved
#
# This file contains code for managing the coqtop process
#
from subprocess import Popen, PIPE
from time import sleep
from fcntl import fcntl, F_GETFL, F_SETFL
from os import O_NONBLOCK, read
import os

coqtop = None

def processSize(pid):
    ps = Popen(['ps', 'aulx'], stdout=PIPE).communicate()[0]
    processes = ps.split('\n')
    # this specifies the number of splits, so the splitted lines
    # will have (nfields+1) elements
    nfields = len(processes[0].split()) - 1
    for row in processes[1:]:
        x = row.split(None, nfields)
        if len(x) > 1 and x[1]==str(pid):
            return str(x[5])
    return None

def compile(name, source, objName):
    print "Source "+source+"\n"
    print "Obj "+objName+"\n"
    coqCompile = Popen(['coqc','-R', '.', name,source],stdin = PIPE, stdout = PIPE, stderr = PIPE, shell = False)
    # set the O_NONBLOCK flag of p.stdout file descriptor:
    flags = fcntl(coqCompile.stdout, F_GETFL) # get current p.stdout flags
    fcntl(coqCompile.stdout, F_SETFL, flags | O_NONBLOCK)
    flags = fcntl(coqCompile.stderr, F_GETFL) # get current p.stderr flags
    fcntl(coqCompile.stderr, F_SETFL, flags | O_NONBLOCK)
    sleep(0.1)
    c = True
    while (c):
        print "Cycle"
        try:
            l = read(coqCompile.stdout.fileno(), 4096)
            print "stdout "+str(len(l))+" "+l
            if len(l)>0:
                coqCompile.wait()
                return False
            c = False
        except OSError:
            pass
        try:
            x = read(coqCompile.stderr.fileno(), 4096)
            print "stderr "+str(len(x))+" "+x
            if len(x)>0:
                coqCompile.wait()
                return False
        except OSError:
            print "No output"
            sleep(0.1)
            print "Wait done"
    print "CompileSize "+source+" size "+str(processSize(coqCompile.pid))
    coqCompile.wait()
    print "Final CompileSize "+source+" size "+str(processSize(coqCompile.pid))
    #os.rename(source+'o',objName+".vo")
    #os.rename(source[0:len(source)-2]+".glob",objName+".glob")
    return True

currentState = -1

script = ""

def coqTopSize():
    return processSize(coqtop.pid)

def startCoq(name):
    global currentState
    global coqtop
    global script
    script = ""
    currentState = 1
    if (coqtop!=None):
        coqtop.terminate()

    coqtop = Popen(['coqtop','-emacs','-R','.',name],
                   stdin = PIPE, stdout = PIPE, stderr = PIPE, shell = False)
    # set the O_NONBLOCK flag of p.stdout file descriptor:
    flags = fcntl(coqtop.stdout, F_GETFL) # get current p.stdout flags
    fcntl(coqtop.stdout, F_SETFL, flags | O_NONBLOCK)
    flags = fcntl(coqtop.stderr, F_GETFL) # get current p.stderr flags
    fcntl(coqtop.stderr, F_SETFL, flags | O_NONBLOCK)
    sleep(0.1)
    r = ""
    c= True
    while (c):
        try:
           l = read(coqtop.stdout.fileno(), 4096)
           r += l
        except OSError:
            try:
                x = read(coqtop.stderr.fileno(), 4096)
                c = False
            except OSError:
                sleep(0.1)

def commandCycle(command):
    global currentState
    global coqtop
    global script
    coqtop.stdin.write(command)
    script = script + command
    #print "COMMAND"
    #print command
    #res = coqtop.communicate(command)
    #print "RES"
    #print res
    #print "END RES"
    #x = res[1]
    c = True
    sleep(0.1)
    r = ""
    while (c):
        try:
           #l = read(coqtop.stdout.fileno(), 540960)
           l = coqtop.stdout.read()
           r += l
        except IOError:
            try:
                #x = read(coqtop.stderr.fileno(), 540960)
                x = coqtop.stderr.read()
                try:
                    #l = read(coqtop.stdout.fileno(), 540960)
                    l = coqtop.stdout.read()
                    r += l
                except IOError:
                    pass
                print "COQ PROMPT "+x
                while len(x) > 0 and (x[0]<'0' or x[0]>'9'):
                    while len(x) > 0 and not(x[0]==' '):
                        x = x[1:]
                    x = x[1:]
                if len(x)>0:
                    xx = 0
                    while xx < len(x) and x[xx]>='0' and x[xx]<='9':
                        xx = xx+1
                    x = x[0:xx]
                    currentState = int(x)
                    print "Current State = "+x
                c = False
            except IOError:
                sleep(0.1)
    return r

def backTo(step):
    commandCycle("BackTo "+str(step)+".\n")

#startCoq()

#print commandCycle("Definition x := 5.\n")
#print commandCycle("Definition y := 5.\n")

class ActiveProcess:
    def __init__(self, f, d):
        self.files = f
        self.defs = d
        self.currentFile = None
        for x in self.files:
            for dd in self.defs[x]:
                dd.currentFile = False
                dd.processed = False

    def moveToDefPosition(self, definition, pos):
        pass

    def markDefEdited(self, d):
        pass

