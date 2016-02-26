#
# PIE - Python based IDe for Coq
#
# Collect.py
#
# This file contains code to run coqtop and collect data from the derivation
#
# (C) 2015, 2016 Kenneth Roe
# All rights reserved
#
import CoqProcess
import CoqLex
import os

def errorResult(text):
    if len(text) > 8 and text[0:8]=='Toplevel':
        return True
    if len(text) > 5 and text[0:6]=='Error:':
        return True
    return ("\n>" in text) and ("^" in text)

def collectData(project, name, definitions, text):
    text = text.split("\n")
    os.chdir(project)
    CoqProcess.startCoq(name)

    for d in definitions:
        p = d.getCoqPrefix(text)
        x = p.split("\n")
        pp = " ".join(x)
        proof = d.getProof()
        s = d.getCoqSuffix(text)

        print "**** def ****"
        print d.__coqstr__()
        #print d.tokens[0]
        #print d.tokens[len(d.tokens)-1]
        print "**** Command ****"
        print pp
        print "**** Result ****"
        #if d.isBad():
        #r = "Bad\n \n^"
        #else:
        r = CoqProcess.commandCycle(pp+"\n")
        print r
        d.result = r
        d.old_result = r
        if errorResult(r):
            print "**ERROR CASE "+d.__coqstr__()
            d.needsReplay = 4
        if True:
        #try:
            if (s != ""):
                tg = CoqLex.tokenize(r)
                tokens = []
                for t in tg:
                    tokens.append(t)
                if (len(tokens)>0 and tokens[0].typ=='NUMBER'):
                    d.subgoals = int(tokens[0].value)
                if (len(tokens)>0 and tokens[0].value=='No'):
                    d.subgoals = 0
                cgoals = 1
                ugoals = 0
                for t in d.getProof():
                    print "**** Tactic ****"
                    t.full = True
                    print t
                    print t.getSegment(text)[0]
                    print t.getSegment(text)[1]
                    print "**** Result ****"
                    r = CoqProcess.commandCycle(t.getSegment(text)[0]+"\n")
                    print r
                    t.result = r
                    t.old_result = r
                    tg = CoqLex.tokenize(r)
                    tokens = []
                    for tt in tg:
                        tokens.append(tt)
                    if len(tokens)>6 and tokens[1].value=='focused':
                        t.unfocused = int(tokens[6].value)
                        ugoals = t.unfocused
                        t.unfocused = int(tokens[6].value)
                        p = 7
                        while tokens[p].value=='-':
                            t.unfocused = t.unfocused + int(tokens[p+1].value)
                            p = p + 2
                        ugoals = t.unfocused
                    #elif len(tokens)==0:
                        #t.unfocused = ugoals
                    #else:
                        #t.unfocused = ugoals
                        #t.unfocused = 0
                        #ugoals = 0
                    print "UGOALS"
                    print ugoals
                    if (len(tokens)>0 and tokens[0].typ=='NUMBER'):
                        t.subgoals = int(tokens[0].value)
                        cgoals = t.subgoals
                        t.unfocused = 0
                        ugoals = 0
                    #elif len(tokens)==0:
                    else:
                        t.subgoals = cgoals
                        t.unfocused = ugoals
                        #cgoals = 0
                        #t.subgoals = 0
                print "**** Suffix ****"
                print s
                print "**** Result ****"
                r = CoqProcess.commandCycle(s+"\n")
                print r
                d.qed = r
        #except RuntimeError:
            #print "**** SCRIPT ****"
            #print CoqProcess.script
            #exit()
    os.chdir("..")
    print "CoqSize "+name+" "+CoqProcess.coqTopSize()
