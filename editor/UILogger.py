#
# PIE - Python based IDe for Coq
#
# UI.py
#
# This file contains the front end for putting up windows in PIE
#
# (C) 2015, 2016 Kenneth Roe
# All rights reserved
#

files = {}
log = []

def logKeyPress(file,text,fr,to,srow,scol,erow,ecol,erowNew,ecolNew):
    if not(file in files.keys()):
        files[file] = text
    log.append((file,fr,to,srow,scol,erow,ecol,erowNew,ecolNew))

def dumpLog(file):
    ff = open(file, "w")
    for f in files.keys():
        ff.write("**** FILE: "+f+" ****\n")
        ff.write(files[f]+"\n")
        ff.write("**** END FILE: "+f+" ****\n")
    for l in log:
        (file,fr,to,srow,scol,erow,ecol,erowNew,ecolNew) = l
        ff.write("*** ORIGINAL: "+f+" "+str(srow)+" "+str(scol)+" "+str(erow)+" "+str(ecol)+" "+str(erowNew)+" "+str(ecolNew)+" ***\n")
        ff.write("#"+fr+"#\n")
        ff.write("*** TO: ***\n")
        ff.write("#"+to+"#\n")
        ff.write("*** DONE ***\n")
    ff.close()

