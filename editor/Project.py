#
# PIE - Python based IDe for Coq
#
# Project.py
#
# This file contains code for the Coq Lexer
#
# (C) 2015, 2016 Kenneth Roe
# All rights reserved
#
import collections
import re
import CoqLex
import CoqParse
from optparse import OptionParser
import sys
import UI
import Collect
import CoqProcess
import os
import shutil
import time

try:
    import Tkinter
    import tkFont
except ImportError:
    import tkinter as Tkinter
    import tkinter.font as tkFont

import ttk

CoqLex.initLex()

class Project:
    def __init__(self):
        self.files = []
        self.defs = {}
        self.resultFile = {}
        self.loaded = {}
        self.text = {}
        self.libraryTerms = []
        self.definedTerms = []
        self.instantiations = {}
        self.projectFile = None
        self.populated = {}
        self.updateStatus = {}
        self.fileDependencies = {}
        self.needsReplay = {}
        self.registeredUI = []
        self.root = "."
        self.overrideRoot = False
        self.projectName = "Main"
    #
    # Dependency stuff
    #

    def findDef(self, name):
        for f in self.files:
            for d in self.defs[f]:
                for n in d.definedNames():
                    if n==name:
                        return d
        return None

    def buildFileDependencies(self):
       #print "*** startBuild ***"
       for f in self.files:
           self.fileDependencies[f] = []
           for d in self.defs[f]:
               d.containingFile = f
       for f in self.files:
           for d in self.defs[f]:
               #print "Dependencies "+str(d)
               for c in d.children:
                   #print "Parent child"
                   #print "     "+str(d)
                   #print "     "+str(c)
                   ff = c.containingFile
                   if not(f in self.fileDependencies[ff]):
                       #print "    added dependency " + str(ff) + " " +str(f)
                       self.fileDependencies[ff].append(f)
       addedFile = True
       while (addedFile):
           addedFile = False
           for f in self.files:
               for ff in self.fileDependencies[f]:
                   for fff in self.fileDependencies[ff]:
                       if not(fff in self.fileDependencies[f]):
                           addedFile = True
                           self.fileDependencies[f].append(fff)

    def doMarkNeedsReplay(self, d, n):
        #print "    Marking "+str(d)+" "+str(d.needsReplay)
        if d.needsReplay < n:
            #print "        Marked"
            d.needsReplay = n
            for x in d.getProof():
                if n>1:
                    x.needsReplay = 2
                else:
                    x.needsReplay = 1
            for x in d.children:
                self.doMarkNeedsReplay(x, n)
    def markNeedsReplay(self, d):
        for x in d.children:
            self.doMarkNeedsReplay(x, d.needsReplay-1)

    def dummyDependencies(self):
        #print "Here0"
        prev_defs = []
        for f in self.files:
            #print "FILE "+str(f)
            for d in self.defs[f]:
                #print "Here2 "+str(d)
                d.children = []
                d.parents = []

    def buildDependencies(self):
        #print "Here0"
        prev_defs = []
        for f in self.files:
            #print "FILE "+str(f)
            for d in self.defs[f]:
                #print "Here2 "+str(d)
                d.children = []
                d.parents = []
	        #for x in d.definedNames():
	            #print "    NAME "+str(x)
	        #for x in d.dependencies():
	            #print "    DEPENDENCY "+str(x)
                #print d.dependencies()
                #print "Here4"
                for x in prev_defs:
                    dep = False
                    for bb in d.dependencies():
                        for aa in x.definedNames():
                            if aa==bb[0] and len(d.definedNames())>0:
                                dep = True
                    if dep:
                        x.children.append(d)
                        d.parents.append(x)
                prev_defs.append(d)
        #print "********************** FOUND DEPENDENCIES **********************"
        #for f in self.files:
            #for d in self.defs[f]:
	        #print "NAMES"
                #for x in d.definedNames():
	            #print "    "+str(x)
                #print "    BUILD CHILDREN"
                #for x in d.children:
                    #print "        "+str(x.definedNames())
                #print "    BUILD PARENTS"
                #print d.parents
                #for x in d.parents:
                    #print "        "+str(x.definedNames())
  
    #
    # Coq process control
    #
    def extractText(self, lines, d):
        lines = ['']+lines
        ft = d.tokens[0]
        lt = d.tokens[len(d.tokens)-1]
        if len(d.getProof())>0 and d.isProof():
            t1 = d.getProof()[0].tokens[0]
            ll = d.getProof()[len(d.getProof())-1]
            t2 = ll.tokens[len(ll.tokens)-1]
            if ft.line==t1.line:
                l1 = [lines[ft.line][ft.column:t1.column]]
            else:
                l1 = [lines[ft.line][ft.column:]]+lines[ft.line+1:t1.line]+[lines[t1.line][0:t1.column]]
            if lt.line==t2.line:
                l2 = [lines[t2.line][t2.column+len(t2.value):lt.column+len(lt.value)]]
            else:
                l2 = [lines[t2.line][t2.column+len(t2.value):]]+lines[t2.line+1:lt.line]+[lines[lt.line][0:lt.column+len(lt.value)]]
            return l1+["admit."]+l2
        else:
            if ft.line==lt.line:
                return [lines[ft.line][ft.column:lt.column+len(lt.value)]]
            else:
                return [lines[ft.line][ft.column:]]+lines[ft.line+1:lt.line]+[lines[lt.line][0:lt.column+len(lt.value)]]

    def extractFullText(self, lines, d):
        lines = ['']+lines
        ft = d.tokens[0]
        lt = d.tokens[len(d.tokens)-1]
        if ft.line==lt.line:
            return [lines[ft.line][ft.column:lt.column+len(lt.value)]]
        else:
            return [lines[ft.line][ft.column:]]+lines[ft.line+1:lt.line]+[lines[lt.line][0:lt.column+len(lt.value)]]

    def extractBeforeText(self, lines, d):
        lines = ['']+lines
        ft = d.tokens[0]
        lt = d.tokens[len(d.tokens)-1]
        if len(d.getProof())>0:
            t1 = d.getProof()[0].tokens[0]
            if ft.line==t1.line:
                l1 = [lines[ft.line][ft.column:t1.column]]
            else:
                l1 = [lines[ft.line][ft.column:]]+lines[ft.line+1:t1.line]+[lines[t1.line][0:t1.column]]
            return l1
        else:
            return []

    def extractTactic(self, lines, d, n):
        lines = ['']+lines
        ll = d.getProof()[n]
        ft = ll.tokens[0]
        lt = ll.tokens[len(ll.tokens)-1]
        if ft.line==lt.line:
            return [lines[ft.line][ft.column:lt.column+len(lt.value)]]
        else:
            return [lines[ft.line][ft.column:]]+lines[ft.line+1:lt.line]+[lines[lt.line][0:lt.column+len(lt.value)]]

    def buildPath(self, file):
        l = file.split("/")
        path = "."
        print l
        while (len(l) > 1):
            path = path + "/" + l[0]
            print "Building "+path
            l = l[1:]
            try:
                os.stat(path)
            except:
                os.mkdir(path)

    def compileFile(self, file):
        pos = 0
        print "COMPILE' "+file
        f = file[0:len(file)-2]
        print "COMPILE'' "+f
        os.chdir(self.projectFile)
        self.buildPath(f)
        lines = []
        l = self.text[file].split("\n")
        for d in self.defs[file]:
            lines = lines+self.extractText(l, d)
        ff = open(f+".v","w")
        ff.write("\n".join(lines))
        ff.close()
        if CoqProcess.compile(self.projectName,f+".v",f+".vo"):
            #print "Good"
            self.updateStatus[file] = 0
            for x in self.defs[file]:
                if len(x.getProof())>0:
                    if x.needsReplay>2:
                        x.needsReplay = 2
                        for t in x.getProof():
                            t.needsReplay = 2
        else:
            #print "Bad"
            self.updateStatus[file] = 4
        #os.remove(f+".v")
	os.chdir("..")

    def compileFullFile(self, file):
        pos = 0
        for i in range(0,len(file)):
            if file[i]=='/':
                pos = i+1
        f = file[pos:]
        f = file[0:len(f)-2]
        os.chdir(self.projectFile)
        lines = []
        l = self.text[file].split("\n")
        for d in self.defs[file]:
            lines = lines+self.extractfullText(l, d)
        ff = open("thetmp.v","w")
        ff.write("\n".join(lines))
        ff.close()
        if CoqProcess.compile(self.projectName,"thetmp.v",f):
            self.updateStatus[file] = 0
            for x in self.defs[file]:
                x.needsReplay = 0
                for t in x.getProof():
                    t.needsReplay = 0
        else:
            self.updateStatus[file] = 4
        os.remove("thetmp.v")
	os.chdir("..")

    def updateUserInterface(self, status):
       #print "***** UPDATE ***** " + str(self.registeredUI)
       for x in self.registeredUI:
           x.colorReplay()
           if not(status==None):
               x.showStatus(status)

    def compileDependentFiles(self, file):
       self.buildFileDependencies()
       rebuild = self.fileDependencies[file]
       #print "*** rebuild ***"
       #print rebuild
       for x in rebuild:
          self.managementState[x] = -1
       self.updateUserInterface("Compiling")
       for x in self.files:
          if x in rebuild and not(x==file):
              nc = False
              for y in self.defs[x]:
                  if y.needsReplay > 2:
                      nc = True
              if nc:
                  self.managementState[x] = 2
                  self.updateUserInterface("Compiling "+x)
                  self.compileFile() 
              self.managementState[x] = 1
              self.updateUserInterface("Ready")

    def initializeCoqManagement(self):
        self.managementState = {}
        self.currentFileIndex = -1
        self.currentDefIndex = -1
        self.currentStepIndex = -1
        for f in self.files:
            self.managementState[f] = 0
            for d in self.defs[f]:
                d.managementState = 0
                for p in d.getProof():
                    p.managementState = 0

    def backupMarker(self,nf,nd):
        print "**** BACKUP MARKER ****"
        #print "Current "+str(self.currentFileIndex)+" "+str(self.currentDefIndex)+" "+str(self.currentStepIndex)
        print "New "+str(nf)+" "+str(nd)
        print self.currentFileIndex
        print self.currentDefIndex
        print self.currentStepIndex
        if (nf < self.currentFileIndex) or ((nf==self.currentFileIndex) and (nd < self.currentDefIndex)) or ((nf==self.currentFileIndex) and (nd==self.currentDefIndex) and (self.currentStepIndex != None or self.currentStepIndex >= 0)):
            self.moveToPosition(nf,nd,None)
            #self.moveMarker(self.defs[self.files[nf]][nd],None)
        print self.currentFileIndex
        print self.currentDefIndex
        print self.currentStepIndex

    def backupMarkerStep(self,nf,nd,ns):
        print "**** BACKUP MARKER ****"
        print nf
        print nd
        print ns
        print self.currentDefIndex
        print self.currentStepIndex
        print "backupMarkerStep"
        print "Current "+str(self.currentFileIndex)+" "+str(self.currentDefIndex)+" "+str(self.currentStepIndex)
        print "New "+str(nf)+" "+str(nd)+" "+str(ns)
        if (nf < self.currentFileIndex) or ((nf==self.currentFileIndex) and (nd < self.currentDefIndex)) or ((nf==self.currentFileIndex) and (nd==self.currentDefIndex) and (ns < self.currentStepIndex)):
            self.moveToPosition(nf,nd,ns)
            #self.moveMarker(self.defs[self.files[nf]][nd],
                            #self.defs[self.files[nf]][nd].getProof()[ns])
        print self.currentFileIndex
        print self.currentDefIndex
        print self.currentStepIndex

    def moveMarker(self,d,p):
        newFile = -1
        newDef = -1
        newStep = -1
        #print "++++++++++++++++++ STEP 1 ++++++++++++++++++ "+str(d)
        for fn in range(0,len(self.files)):
            for dn in range(0,len(self.defs[self.files[fn]])):
                if d==self.defs[self.files[fn]][dn]:
                    newFile = fn
                    newDef = dn
                    if p==True:
                        newStep = len(d.getProof())
                    else:
		        for pn in range(0,len(d.getProof())):
			    if d.getProof()[pn]==p:
                                newStep = pn
        moveToPosition(newFile,newDef,newStep)

    def errorResult(self, text):
        if len(text) > 8 and text[0:8]=='Toplevel':
            return True
        if len(text) > 5 and text[0:6]=='Error:':
            return True
        return ("\n>" in text) and ("^" in text)

    def moveToPosition(self,newFile,newDef,newStep):
        for fn in range(0,len(self.files)):
            if newFile==self.files[fn]:
                newFile = fn
        print "HERE0.5 "+str(newDef)+" "+str(newStep)+" "+str(newFile)
        if self.currentFileIndex > -1 and self.currentDefIndex < len(self.defs[self.files[newFile]]) and self.currentDefIndex > -1 and (newDef != self.currentDefIndex or newFile != self.currentFileIndex):
            d = self.defs[self.files[self.currentFileIndex]][self.currentDefIndex]
            if newFile > self.currentFileIndex or (newFile==self.currentFileIndex and newDef > self.currentDefIndex):
                for p in d.getProof():
                    p.old_result = p.result
                d.old_result = d.result
        if newDef > -1 and newDef < len(self.defs[self.files[newFile]]):
            d = self.defs[self.files[newFile]][newDef]
        else:
            d = None
        p = None
        if newFile==self.currentFileIndex and ((newDef > self.currentDefIndex and self.currentStepIndex != None) or (newDef==self.currentDefIndex and ((newStep != None and self.currentStepIndex == None) or (newStep == None and self.currentStepIndex != None)))):
            if self.currentDefIndex > 0:
                dd = self.defs[self.files[self.currentFileIndex]][self.currentDefIndex]
                self.currentStepIndex = None
                self.currentDefIndex = self.currentDefIndex-1
                print "**** Backup 1 ****"
                print dd.coqCycle
                CoqProcess.backTo(dd.coqCycle)
                self.currentCoqCycle = dd.coqCycle
            else:
                self.currentDefIndex = -1
                self.currentStepIndex = None
        if not(newStep==None) and newStep > -1:
            if not(d==None):
               #print newStep
               #print d.getProof()
               if newStep < len(d.getProof()):
                   p = d.getProof()[newStep]
               else:
                   p = None
        if self.currentFileIndex==newFile and self.currentDefIndex>= 0:
            st = self.currentDefIndex+1
        else:
            st = 0
        print "st = "+str(st)
        for x in range(st,newDef+1):
            self.defs[self.files[newFile]][x].managementState = -1
        if newStep >= 0:
            self.defs[self.files[newFile]][newDef].managementState = -1
            st = 0
            if newDef==self.currentDefIndex and newFile==self.currentFileIndex:
                st = self.currentStepIndex
            for y in range(st,newStep+1):
                self.defs[self.files[newFile]][newDef].getProof()[y].managementState = -1

        print "++++++++++++++++++ STEP 2 ++++++++++++++++++"
        print d
        print p
        if newFile >= 0:
            print "++++++++++++++++++ STEP 3 ++++++++++++++++++ "+str(newFile)+" "+str(self.currentFileIndex)+" "+str(newDef)+" "+str(self.currentDefIndex)+" "+str(newStep)+" "+str(self.currentStepIndex)
            if not(newFile==self.currentFileIndex):
                if (self.currentFileIndex >= 0):
                    for d in self.defs[self.files[self.currentFileIndex]]:
                        d.managementState = 0
                        for p in d.getProof():
                            p.managementState = 0
                self.compileDependentFiles(self.files[newFile])
                self.currentFileIndex = newFile
                self.currentDefIndex = -1
                self.currentStepIndex = None
            self.managementState[self.files[newFile]] = 1
            if not(newDef == self.currentDefIndex):
                if newDef > self.currentDefIndex:
                    self.managementState[self.currentFileIndex] = 2
                    if self.currentDefIndex < 0:
                        self.updateUserInterface("Starting Coq")
                        os.chdir(self.projectFile)
                        CoqProcess.startCoq(self.projectName)
                        os.chdir("..")
                        self.currentCoqCycle = -1
                        self.currentDefIndex = -1
                    text = self.text[self.files[self.currentFileIndex]].split("\n")
                    ee = newDef+1
                    if newStep!=None:
                        ee = newDef
                    for x in range(self.currentDefIndex+1,ee):
                       print "Processing "+str(x)
                       d = self.defs[self.files[self.currentFileIndex]][x]
                       p = d.getCoqPrefix(text)
                       xx = p.split("\n")
                       pp = " ".join(xx)
                       proof = d.getProof()
                       s = d.getCoqSuffix(text)

                       d.managementState = 2
                       self.updateUserInterface("Definition "+str(d.header()))
                       print "Saving cycle "+str(self.currentCoqCycle)
                       d.coqCycle = self.currentCoqCycle
                       r = CoqProcess.commandCycle(pp+"\n")
                       d.managementState = 1
                       print "****** COMMAND *****"
                       print pp
                       print "****** RESULT *****"
                       print r
                       print "****** DONE *****"
                       d.result = r
                       self.currentCoqCycle = CoqProcess.currentState
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
                           d.managementState = 2
                           self.updateUserInterface("Proving "+str(d.header()))
                           r = CoqProcess.commandCycle("admit.\n")
                           self.currentCoqCycle = CoqProcess.currentState
                           print "**** Command1 ****\nadmit.\n*** Result ****"
                           print r
                           print "**** Done ****"
                           print "**** Suffix ****"
                           print "**** Command2 ****"
                           print s
                           r = CoqProcess.commandCycle(s+"\n")
                           d.managementState = 1
                           print "**** Result ****"
                           print r
                           print "**** Done ****"
                           d.qed = r
                           self.currentCoqCycle = CoqProcess.currentState
                           if d.needsReplay > 2:
                               if len(d.getProof())==0:
                                   d.needsReplay = 0
                               else:
                                   d.needsReplay = 2
                       else:
                           if self.errorResult(d.result):
                               d.needsReplay = 4
                               d.managementState = 0
                               self.currentDefIndex = x-1
                               self.currentStepIndex = None
                               self.updateUserInterface("Ready")
                               self.writeProverFile()
                               print "Here0"
                               for y in range(x,newDef):
                                   print "Here1 "+str(y)
                                   d = self.defs[self.files[self.currentFileIndex]][y]
                                   print "Here2"
                                   d.managementState = 0
                                   print "Here3"
                               print "Here3.5"
                               if newDef < len(self.defs[self.files[self.currentFileIndex]]):
                                   print "Here4"
                                   d = self.defs[self.files[self.currentFileIndex]][newDef]
                                   print "Here5"
                                   d.managementState = 0
                                   print "Here6"
                                   if newStep != None:
                                       for y in range(0,newStep):
                                           d.getProof()[y].managementState = 0
                                   print "Here7"
                               print "Final "+str(x)
                               return
                           d.needsReplay = 0
                    self.currentDefIndex = ee-1
                    self.currentStepIndex = None
                elif newDef < self.currentDefIndex:
                    if newStep != None:
                        newDef = newDef-1
                    nn = self.currentDefIndex+1
                    if nn > len(self.defs[self.files[self.currentFileIndex]]):
                        nn = len(self.defs[self.files[self.currentFileIndex]])
                    for x in range(newDef+1,nn):
                        self.defs[self.files[self.currentFileIndex]][x].managementState = 0
                        for p in self.defs[self.files[self.currentFileIndex]][x].getProof():
                            p.managementState = 0
                    self.updateUserInterface("Backing up Coq")
                    if newDef < 0:
                        CoqProcess.startCoq(self.projectName)
                        self.currentCoqCycle = -1
                    else:
                        CoqProcess.backTo(self.defs[self.files[self.currentFileIndex]][newDef+1].coqCycle)
                        self.currentCoqCycle = self.defs[self.files[self.currentFileIndex]][newDef+1].coqCycle
                    print "***** Backup 3 *****"
                    print self.defs[self.files[self.currentFileIndex]][newDef+1].coqCycle
                    self.currentDefIndex = newDef
                    self.currentStepIndex = None
            print "Second step check "+str(newStep)+" "+str(self.currentStepIndex)
            if newStep != None and newStep != self.currentStepIndex:
                print "Here1"
                if self.currentStepIndex==None:
                    print "++++++++++++++++++ STEP 4 ++++++++++++++++++ "+str(newStep)
                    d = self.defs[self.files[self.currentFileIndex]][self.currentDefIndex+1]
                    text = self.text[self.files[self.currentFileIndex]].split("\n")
                    p = d.getCoqPrefix(text)
                    xx = p.split("\n")
                    pp = " ".join(xx)
                    proof = d.getProof()
                    s = d.getCoqSuffix(text)

                    d.managementState = 2
                    self.updateUserInterface("Definition "+str(d.header()))
                    print "Saving cycle "+str(self.currentCoqCycle)
                    d.coqCycle = self.currentCoqCycle
                    r = CoqProcess.commandCycle(pp+"\n")
                    d.managementState = 1
                    print "****** COMMAND *****"
                    print pp
                    print "****** RESULT *****"
                    print r
                    print "****** DONE *****"
                    d.result = r
                    try:
                        tg = CoqLex.tokenize(r)
                        tokens = []
                        for tt in tg:
                            tokens.append(tt)
                    except RuntimeError:
                        d.managementState = 0
                        d.needsReplay = 4
                        i = 0
                        while i < len(d.getProof()):
                            d.getProof()[i].managementState = 0
                            i = i+1
                        self.updateUserInterface("Ready")
                        return
                    if d.needsReplay > 2:
                        d.needsReplay = 2
                    self.currentStepIndex = -1
                    self.currentDefIndex = self.currentDefIndex+1
                    self.currentCoqCycle = CoqProcess.currentState
                if newStep > self.currentStepIndex:
                    print "Here2"
                    text = self.text[self.files[self.currentFileIndex]].split("\n")
                    #if self.currentStepIndex < 0:
                        #print "++++++++++++++++++ STEP 4 ++++++++++++++++++ "+str(newStep)
                        #d = self.defs[self.files[self.currentFileIndex]][self.currentDefIndex]
                        #p = d.getCoqPrefix(text)
                        #x = p.split("\n")
                        #pp = " ".join(x)
                        #proof = d.getProof()
                        #s = d.getCoqSuffix(text)

                        #d.managementState = 2
                        #self.updateUserInterface("Tactic "+d.header())
                        #d.coqCycle = self.currentCoqCycle
                        #r = CoqProcess.commandCycle(pp+"\n")
                        #print "**** Command3 ****"
                        #print pp+"\n"
                        #print "**** Result ****"
                        #print r
                        #print "**** Done ****"
                        #d.result = r
                        #try:
                            #tg = CoqLex.tokenize(r)
                            #tokens = []
                            #for tt in tg:
                                #tokens.append(tt)
                        #except RuntimeError:
                            #d.managementState = 0
                            #d.needsReplay = 4
                            #i = 0
                            #while i < len(d.getProof()):
                                #d.getProof()[i].managementState = 0
                                #i = i+1
                            #self.updateUserInterface("Ready")
                            #return
                        #if d.needsReplay > 2:
                            #d.needsReplay = 2
                        #self.currentCoqCycle = CoqProcess.currentState
                        #self.currentStepIndex = 0
                    if self.currentStepIndex < 0:
                       ugoals = 0
                       cgoals = 1
                    else:
                        ugoals = d.getProof()[self.currentStepIndex].unfocused
                        cgoals = d.getProof()[self.currentStepIndex].subgoals
                    self.currentStepIndex = self.currentStepIndex+1
                    while self.currentStepIndex < newStep+1:
                        print "++++++++++++++++++ STEP 5 ++++++++++++++++++ "+str(self.currentStepIndex)
                        t = d.getProof()[self.currentStepIndex]
                        print "Saving cycle "+str(self.currentCoqCycle)
                        print "**** Tactic ****"
                        print t
                        print "**** Result ****"
                        t.coqCycle = self.currentCoqCycle
                        t.managementState = 2
                        d.managementState = 2
                        print "Here 1"
                        self.updateUserInterface("Tactic "+t.__coqstr__())
                        print "Here 2"
                        print t.getSegment(text)[0]
                        r = CoqProcess.commandCycle(t.getSegment(text)[0]+"\n")
                        print "**** Command4 ****"
                        print t.getSegment(text)[0]+"\n"
                        print "**** Result ****"
                        print r
                        print "**** Done ****"
                        t.managementState = 1
                        d.managementState = 1
                        t.needsReplay = 0
                        self.currentCoqCycle = CoqProcess.currentState
                        #print r
                        #if not(t.old_result==None):
                            #t.old_result = t.result
                        t.result = r
                        print "Here 3"
                        try:
                            tg = CoqLex.tokenize(r)
                            tokens = []
                            for tt in tg:
                                tokens.append(tt)
                            if len(tokens)>6 and tokens[1].value=='focused':
                                t.unfocused = int(tokens[6].value)
                                p = 7
                                while tokens[p].value=='-':
                                    t.unfocused = t.unfocused + int(tokens[p+1].value)
                                    p = p + 2
                                ugoals = t.unfocused
                            elif len(tokens)==0:
                                raise RuntimeError("xxx")
                                #t.unfocused = ugoals
                            else:
                                t.unfocused = 0
                                ugoals = 0
                            print "UGOALS"
                            print ugoals
                            if (len(tokens)>0 and tokens[0].typ=='NUMBER'):
                                t.subgoals = int(tokens[0].value)
                                cgoals = t.subgoals
                            elif len(tokens) > 1 and tokens[0].value=="No" and tokens[1].value=="more":
                                t.unfocused = 0
                                t.subgoals = 0
                                cgoals = 0
                                ugoals = 0
                            #elif len(tokens)==0:
                                #t.subgoals = cgoals
                            else:
                                raise RuntimeError("xxx")
                                #cgoals = 0
                                #t.subgoals = 0
                        except RuntimeError:
                            t.managementState = 0
                            t.needsReplay = 4
                            i = self.currentStepIndex + 1
                            while i < len(d.getProof()):
                                d.getProof()[i].managementState = 0
                                i = i+1
                            self.updateUserInterface("Ready")
                            return
                        self.currentStepIndex = self.currentStepIndex + 1
                    self.currentStepIndex = self.currentStepIndex - 1
                    if self.currentStepIndex==len(d.getProof())-1:
                        d.needsReplay = 0
                elif newStep < self.currentStepIndex:
                    print d
                    print newStep
                    #print "Here3 "+str(d.getProof()[newStep].coqCycle)+" "+str(d.coqCycle)
                    #print d.getProof()
                    #print d.getProof()[newStep]
                    d = self.defs[self.files[self.currentFileIndex]][self.currentDefIndex]
                    for p in range(newStep+1,self.currentStepIndex+1):
                        d.getProof()[p].managementState = 0
                    self.updateUserInterface("Backing up Coq")
                    CoqProcess.backTo(d.getProof()[newStep+1].coqCycle)
                    self.currentCoqCycle = d.getProof()[newStep+1].coqCycle
                    print "**** Backup 2 ****"
                    print d.getProof()[newStep].coqCycle
                    self.currentStepIndex = newStep
        self.updateUserInterface("Ready")
        self.writeProverFile()

    def retokenize(self, d, text, start_line, start_col, end_line, end_col):
        if start_line==end_line:
            ttt = [text[start_line-1][start_col:end_col+1]]
        else:
            ttt = [text[start_line-1][start_col:]]+text[start_line:end_line-1]+[text[end_line-1][0:end_col+1]]
        pt = "\n".join(ttt)
        program = []
        for token in CoqLex.tokenize(pt):
            l = token.line+start_line-1
            c = token.column
            if token.line==1:
                c = c + start_col
            program.append(CoqLex.Token(token.typ,token.value,l,c))
        d.tokens = program
    #
    # File modification stuff
    #
    def updateFileText(self, file, first_def, last_def, first_step, last_step, start_line, start_col, end_line_old, end_col_old, end_line_new, end_col_new, new_text):
        print "**** Updating file text ****"
        print new_text
        print "**** Updating file text ****"
        print first_def
        program = []
        fn = -1
        for xx in range(0,len(self.files)):
            if self.files[xx]==file:
                fn = xx
        if first_step==None:
            if first_def==None:
                self.backupMarker(fn,last_def)
            else:
                self.backupMarker(fn,first_def-1)
        else:
            self.backupMarkerStep(fn,first_def,first_step-1)
        #print "updateFileText"
        if first_def==None:
            head = self.defs[file][0:last_def+1]
            tail = self.defs[file][last_def+1:]
            deleted = []
        else:
            head = self.defs[file][0:first_def]
            tail = self.defs[file][last_def+1:]
            deleted = self.defs[file][first_def:last_def+1]
        #print "Here 2"
        saveResult = False
        #print "Here 4"
        t = new_text.split("\n")
        if start_line==end_line_new:
            ttt = [t[start_line-1][start_col:end_col_new]]
        else:
            ttt = [t[start_line-1][start_col:]]+t[start_line:end_line_new-1]+[t[end_line_new-1][0:end_col_new]]
        nt = "\n".join(ttt)
        for token in CoqLex.tokenize(nt):
            l = token.line+start_line-1
            c = token.column
            if token.line==1:
                c = c + start_col
            program.append(CoqLex.Token(token.typ,token.value,l,c))
        print "**** def range ****"
        print first_def
        print last_def
        print first_step
        print last_step
        print "**** Text range ****"
        print start_col
        print start_line
        print end_col_old
        print end_line_old
        print end_col_new
        print end_line_new
        if len(t) > end_line_new-1:
            print t[end_line_new-1]
        if len(t) > end_line_new:
            print t[end_line_new]
        if len(t) > end_line_new+1:
            print t[end_line_new+1]
        print "**** New Text ****"
        print nt
        print "**** End new Text ****"
        #print program
        if first_step==None and last_step==None:
            try:
                result = CoqParse.parseCoqProgram(program)
                #print "parsed"
                #print result
                for i in range(len(head),len(self.defs[file])-len(tail)):
                    self.defs[file][i].needsReplay = 4
                    self.markNeedsReplay(self.defs[file][i])
                self.defs[file] = head+result+tail
                self.buildDependencies()
                for r in result:
                    print "Processing"
                    print r
                    print "Start"
                    r.needsReplay = 4
                    self.markNeedsReplay(r)
                    print r.__coqstr__()
                    print "Done"
                    if len(r.getProof())>0:
                        print "Here1"
                        print deleted
                        for z in deleted:
                            print "Here2"
                            if z.definedNames()==r.definedNames():
                                print "Here3"
                                pos = 0
                                while pos < len(z.getProof()) and pos < len(r.getProof()):
                                    x = z.getProof()[pos]
                                    y = r.getProof()[pos]
                                    if x.__coqstr__()==y.__coqstr__():
                                        y.result = x.result
                                        y.old_result = x.old_result
                                    else:
                                        pos = len(z.getProof())
                                    pos = pos+1
            except CoqParse.ParseError as e:
                print "Cannot parse "+str(e)
                if len(e.tokens)==0:
                    return (end_line_new, end_col_new)
                else:
                    return (e.tokens[0].line,e.tokens[0].column)
        else:
            d = self.defs[file][first_def]
            tail = self.defs[file][first_def+1:]
            try:
                result = CoqParse.topParseCoqTactic(program)
                #print "parsed"
                #print result
                if first_step==None:
                    d.proof = d.proof[0:last_step]+result+d.proof[last_step:]
                    first_step = last_step
                else:
                    fs = first_step
                    for r in result:
                        r.subgoals = d.proof[fs].subgoals
                        r.unfocused = d.proof[fs].unfocused
                        r.result = d.proof[fs].result
                        r.old_result = d.proof[fs].old_result
                        r.needsReplay = 2
                        r.managementState = 0
                        if fs < last_step-1:
                            fs = fs+1
                    d.proof = d.proof[0:first_step]+result+d.proof[last_step+1:]
                for dd in d.proof[first_step+len(result):]:
                    #print "Here aa"
                    dd.editUpdateTokens(start_line,start_col,end_line_old,end_col_old,end_line_new,end_col_new)
                    dd.needsReplay = 2
                    #print "Here bbb"
                #self.buildDependencies()
                #print d
                #print "Start"
                d.needsReplay = 2 
                self.markNeedsReplay(d)
                l = len(d.tokens)
                el = d.tokens[l-1].line
                ec = d.tokens[l-1].column+len(d.tokens[l-1].value)
                el = el+end_line_new-end_line_old
                if el==end_line_new:
                    ec = ec+end_col_new-end_col_old
                self.retokenize(d,t,d.tokens[0].line,d.tokens[0].column,el,ec)
            except CoqParse.ParseError as e:
                #print "Cannot parse"
                #print e
                try:
                    if len(e[1])==0:
                        return (end_line_new, end_col_new)
                    else:
                        return (e[1][0].line,e[1][0].column)
                except IndexError:
                    return (end_line_new, end_col_new)
        self.text[file] = new_text
        saveResult = True
        for dd in tail:
            #print "Here aa"
            dd.editUpdateTokens(start_line,start_col,end_line_old,end_col_old,end_line_new,end_col_new)
            #print "Here bbb"
        #print "*** NEW TEXT ***"
        #print self.text[file]
        #print "*** DONE NEW TEXT ***"
        #saveResult = False
        if saveResult:
            print "Saving"
            #self.buildDependencies()
            self.writeProverFile()
            print self.root
            print file
            ff = open(self.root+"/"+file,"w")
            ff.write(self.text[file])
            ff.close()
        #print "**** RETURNING ****"
        return None

    def insertTactic(self, d, n, new_text):
        #print "**** INSERTING TACTIC ****"
        #print new_text
        program = []
        saveResult = True
        #print "Here 1"
        file = None
        for f in self.files:
            i = -1
            for x in range(0,len(self.defs[f])):
                if self.defs[f][x]==d:
                    i = x
            #print "i = " + str(i)
            if i > -1:
                fn = -1
                for xx in range(0,len(self.files)):
                    if self.files[xx]==f:
                        fn = xx
                self.backupMarkerStep(fn,pos,n)
                #print "Inserting " + str(i) + " in " + f + " " + str(n)
                head = self.defs[f][0:i]
                tail = self.defs[f][i+1:]
                if n < len(d.proof):
                    nt = d.proof[n].tokens[0]
                    start_line = nt.line
                    start_column = nt.column
                    i = 0
                    while i < len(d.tokens) and d.tokens[i]!=nt:
                        i = i+1
                    tok = d.tokens[i-1]
                else:
                    ttt = d.proof[n-1].tokens
                    tok = ttt[len(ttt)-1]
                    start_line = tok.line
                    start_column = tok.column+len(tok.value)
                    while i < len(d.tokens) and d.tokens[i]!=tok:
                        i = i+1
                    nt = d.tokens[i+1]
                #print "Tokens"
                #print tok
                #print nt
                add_extra_break = (tok.line == nt.line)
                t = d.proof[n].tokens
                end_line = t[len(t)-1].line
                for token in CoqLex.tokenize(new_text):
                    if add_extra_break:
                        l = token.line+start_line
                    else:
                        l = token.line+start_line-1
                    c = token.column
                    if token.line==1 and not(add_extra_break):
                        c = c + start_column
                    program.append(CoqLex.Token(token.typ,token.value,l,c))
                #print "Here 2"
                #print "Here 3"
                #print "Here 3b"
                saveResult = False
                #print "Here 4"
                #print program
                try:
                    result = CoqParse.topParseCoqTactic(program)
                    #print "parsed"
                    for r in result:
                        r.subgoals = d.proof[n].subgoals
                        r.unfocused = d.proof[n].unfocused
                        r.result = d.proof[n].result
                        r.needsReplay = 2
                        r.managementState = 0
                    #print result
                except CoqParse.ParseError as e:
                    #print "Cannot parse"
                    saveResult = False
                    result = CoqErrorDeclaration(program,e.message,len(tokens)-len(e.tokens))
                    #print result
                    new_text = result.insertMessage(new_text)
                line = nt.line
                column = nt.column
                #print "Here 1"
                if len(result)==0:
                    line2 = line
                    column2 = column
                else:
                    #print "Here 1a"
                    r = result[len(result)-1]
                    #print r.tokens
                    #print "Here 1b"
                    t = r.tokens[len(r.tokens)-1]
                    line2 = t.line+1
                    #print "Here 1c"
                    column2 = 0
                    #print line2
                    #print column2
                #print "Here 2"
                #if add_extra_break:
                    #line2 = line2+1
                #print line2
                #print column2
                for i in range(n,len(d.proof)):
                    d.proof[i].editUpdateTokens(start_line,start_column,line,column,line2,column2)
                    d.proof[i].needsReplay = 3
                #print "Here 3"
                d.proof = d.proof[0:n]+result+d.proof[n:]
                d.editUpdateTokens(start_line,start_column,line,column,line2,column2)
                for dd in tail:
                    #print "Here aa"
                    dd.editUpdateTokens(start_line,start_column,line,column,line2,column2)
                    #print "Here bbb"
                #print "Here3b"
                #print len(self.defs[f])
                t = self.text[f].split("\n")
                before_text = t[0:start_line-1]
                #print "Here4"
                after_text = t[start_line-1:]
                if add_extra_break:
                    before_text.append(t[start_line-1][0:start_column])
                    after_text[0] = t[start_line-1][start_column:]
                #print len(self.text[f])
                while len(new_text)>0 and new_text[len(new_text)-1]=='\n':
                    new_text = new_text[0:len(new_text)-1]
                self.text[f] = "\n".join(before_text+new_text.split("\n")+after_text)
                #print len(self.text[f])
                #print "*** NEW TEXT ***"
                #print self.text[f]
                #print "*** DONE NEW TEXT ***"
                #print start_line
                #print start_column
                #print line
                #print column
                #print line2
                #print column2
                #print add_extra_break
                file = f
                self.buildDependencies()
                #print d
                #print "Start"
                d.needsReplay = 2 
                self.markNeedsReplay(d)
                #print "Done"
        #print "Here1"
        if saveResult:
            self.writeProverFile()
            ff = open(file,"w")
            ff.write(self.text[f])
            ff.close()
        #print "**** RETURNING ****"

    def replaceTactic(self, d, n, new_text):
        #print "**** REPLACING TACTIC ****"
        #print new_text
        program = []
        saveResult = True
        #print "Here 1"
        file = None
        for f in self.files:
            i = -1
            for x in range(0,len(self.defs[f])):
                if self.defs[f][x]==d:
                    i = x
            #print "file i = " + file + " " + str(i)
            if i > -1:
                fn = -1
                for xx in range(0,len(self.files)):
                    if self.files[xx]==f:
                        fn = xx
                self.backupMarkerStep(fn,pos,n)
                #print "Replacing " + str(i) + " in " + f
                head = self.defs[f][0:i]
                tail = self.defs[f][i+1:]
                start_line = d.proof[n].tokens[0].line
                start_column = d.proof[n].tokens[0].column
                t = d.proof[n].tokens
                end_line = t[len(t)-1].line
                if n==0:
                    if i==0:
                        break_before = False
                    else:
                        t = head[len(head)-1].tokens
                        break_before = (t[len(t)-1].line==start_line)
                else:
                    t = d.proof[n-1].tokens
                    break_before = (t[len(t)-1].line==start_line)
                if n==len(d.proof)-1:
                    if len(tail)==0:
                        break_after = False
                    else:
                        break_after = (tail[0].tokens[0].line==end_line)
                else:
                    break_after = (d.proof[n+1].tokens[0].line==end_line)
                for token in CoqLex.tokenize(new_text):
                    if break_before:
                        l = token.line+start_line
                    else:
                        l = token.line+start_line-1
                    c = token.column
                    if token.line==1 and not(break_before):
                        c = c + start_column
                    program.append(CoqLex.Token(token.typ,token.value,l,c))
                #print "Here 2"
                #print "Here 3"
                #print "Here 3b"
                saveResult = False
                #print "Here 4"
                #print program
                try:
                    result = CoqParse.topParseCoqTactic(program)
                    #print "parsed"
                    for r in result:
                        r.subgoals = d.proof[n].subgoals
                        r.unfocused = d.proof[n].unfocused
                        r.result = d.proof[n].result
                        r.needsReplay = 1
                        r.managementState = 0
                    #print result
                except CoqParse.ParseError as e:
                    #print "Cannot parse"
                    saveResult = False
                    result = CoqErrorDeclaration(program,e.message,len(tokens)-len(e.tokens))
                    #print result
                    new_text = result.insertMessage(new_text)
                line = d.proof[n].tokens[len(d.proof[n].tokens)-1].line
                column = d.proof[n].tokens[len(d.proof[n].tokens)-1].column+len(d.proof[n].tokens[len(d.proof[n].tokens)-1].value)
                print "Here 1"
                if len(result)==0:
                    line2 = line
                    column2 = column
                else:
                    #print "Here 1a"
                    r = result[len(result)-1]
                    #print r.tokens
                    #print "Here 1b"
                    t = r.tokens[len(r.tokens)-1]
                    line2 = t.line
                    #print "Here 1c"
                    column2 = t.column+len(t.value)
                #print "Here 2"
                if break_after:
                    line2 = line2+1
                    column2 = 0
                for i in range(n+1,len(d.proof)):
                    d.proof[i].editUpdateTokens(start_line,start_column,line,column,line2,column2)
                    d.proof[i].needsReplay = 3
                #for dd in d.proof[n+1:]:
                    #print "Here aa"
                    #dd.editUpdateTokens(start_line,start_column,line,column,line2,column2)
                    #print "Here bbb"
                #print "Here 3"
                d.proof = d.proof[0:n]+result+d.proof[n+1:]
                d.editUpdateTokens(start_line,start_column,line,column,line2,column2)
                for dd in tail:
                    #print "Here aa"
                    dd.editUpdateTokens(start_line,start_column,line,column,line2,column2)
                    #print "Here bbb"
                #print "Here3b"
                #print len(self.defs[f])
                t = self.text[f].split("\n")
                before_text = t[0:start_line-1]
                #print "Here4"
                if start_column>0:
                    new_text = t[start_line-1][0:start_column]+new_text
                if column < len(t[line-1]):
                    new_text = new_text+t[line-1][column:]
                #print "Here5"
                after_text = t[line:]
                #print len(self.text[f])
                while len(new_text)>0 and new_text[len(new_text)-1]=='\n':
                    new_text = new_text[0:len(new_text)-1]
                self.text[f] = "\n".join(before_text+new_text.split("\n")+after_text)
                #print len(self.text[f])
                #print "*** NEW TEXT ***"
                #print self.text[f]
                #print "*** DONE NEW TEXT ***"
                #print start_line
                #print start_column
                #print line
                #print column
                #print line2
                #print column2
                #print break_before
                #print break_after
                file = f
                self.buildDependencies()
                #print d
                #print "Start"
                d.needsReplay = 2 
                self.markNeedsReplay(d)
                #print "Done"
        #print "Here1"
        if saveResult:
            self.writeProverFile()
            ff = open(file,"w")
            ff.write(self.text[f])
            ff.close()
        #print "**** RETURNING ****"

    def replaceDeclaration(self, d, new_text):
        #print "**** REPLACING DECLARATION ****"
        #print new_text
        program = []
        saveResult = True
        #print "Here 1"
        file = None
	for f in self.files:
	    i = -1
            for x in range(0,len(self.defs[f])):
                if self.defs[f][x]==d:
                    i = x
            #print "i = " + str(i)
            if i > -1:
                fn = -1
                for xx in range(0,len(self.files)):
                    if self.files[xx]==f:
                        fn = xx
                self.backupMarker(fn,i)
                #print "Replacing " + str(i) + " in " + f
                head = self.defs[f][0:i]
                tail = self.defs[f][i+1:]
                start_line = d.tokens[0].line
                start_column = d.tokens[0].column
                if len(head)==0:
                    break_before = False
                else:
                    head_tokens = head[len(head)-1].tokens
                    break_before = (head_tokens[len(head_tokens)-1].line==d.tokens[0].line)
                if len(tail)==0:
                    break_after = False
                else:
                    tail_tokens = tail[0].tokens
                    break_after = (tail_tokens[len(tail_tokens)-1].line==d.tokens[len(d.tokens)-1].line)
                for token in CoqLex.tokenize(new_text):
                    if break_before:
                        l = token.line+start_line
                    else:
                        l = token.line+start_line-1
                    c = token.column
                    if token.line==1:
                        c = c + start_column
                    program.append(CoqLex.Token(token.typ,token.value,l,c))
                #print "Here 2"
                saveResult = False
                #print "Here 4"
                #print program
                try:
                    result = CoqParse.parseCoqProgram(program)
                    #print "parsed"
                    #print result
                except CoqParse.ParseError as e:
                    #print "Cannot parse"
                    saveResult = False
                    result = [CoqErrorDeclaration(program,e.message,len(tokens)-len(e.tokens))]
                    #print result[0]
                    new_text = result[0].insertMessage(new_text)
                line = d.tokens[len(d.tokens)-1].line
                column = d.tokens[len(d.tokens)-1].column+len(d.tokens[len(d.tokens)-1].value)
                #print "Here1 "+str(len(result))
                if len(result)>0:
                    r = result[len(result)-1]
                    line2 = r.tokens[len(r.tokens)-1].line
                    column2 = r.tokens[len(r.tokens)-1].column
                    if break_after:
                        line2 = line2+1
                        column2 = 0
                else:
                    line2 = start_line
                    column2 = start_column
                    if break_before or break_after:
                        line2 = line2+1
                        column2 = 0
                for dd in tail:
                    #print "Here aa"
                    dd.editUpdateTokens(start_line,start_column,line,column,line2,column2)
                    #print "Here bbb"
                #print "Here3"
                #print len(self.defs[f])
                self.defs[f] = head+result+tail
                #print len(head)
                #print len(result)
                #print len(tail)
                t = self.text[f].split("\n")
                before_text = t[0:start_line-1]
                #print "Here4"
                if break_before:
                    new_text = t[start_line-1][0:start_column]+"\n"+new_text
                if break_after:
                    new_text = new_text+"\n"+t[line-1][column:]
                #print "Here5"
                after_text = t[line:]
                #print len(self.text[f])
                while len(new_text)>0 and new_text[len(new_text)-1]=='\n':
                    new_text = new_text[0:len(new_text)-1]
                self.text[f] = "\n".join(before_text+new_text.split("\n")+after_text)
                #print len(self.text[f])
                #print "*** NEW TEXT ***"
                #print self.text[f]
                #print "*** DONE NEW TEXT ***"
                #print start_line
                #print start_column
                #print line
                #print column
                #print line2
                #print column2
                #print break_before
                #print break_after
                file = f
                self.buildDependencies()
                for r in result:
                    #print r
                    #print "Start"
                    r.needsReplay = 4
                    self.markNeedsReplay(r)
                    #print "Done"
        #print "Here1"
        #print "Here2"
        #print "Here3"
        if saveResult:
            self.writeProverFile()
            ff = open(file,"w")
            ff.write(self.text[f])
            ff.close()
        #print "**** RETURNING ****"

    def insertDeclaration(self, file, pos, new_text):
        f = file
        #print "**** INSERTING DECLARATION ****"
        #print new_text
        program = []
        saveResult = True
        #print "Here 1"
        if pos < len(self.defs[file]):
            d = self.defs[file][pos]
            start_line = d.tokens[0].line
            start_column = d.tokens[0].column
        else:
            d = None
            start_line = len(self.text[file])+1
            start_column = 0
        for token in CoqLex.tokenize(new_text):
            l = token.line+start_line-1
            c = token.column
            if token.line==1:
                c = c + start_column
            program.append(CoqLex.Token(token.typ,token.value,l,c))
        saveResult = False
        #print "Here 4"
        try:
            result = CoqParse.parseCoqProgram(program)
            #print "parsed"
            #print result
        except CoqParse.ParseError as e:
            #print "Cannot parse"
            saveResult = False
            result = [CoqErrorDeclaration(program,e.message,len(tokens)-len(e.tokens))]
            #print result[0]
            new_text = result[0].insertMessage(new_text)
        file = None
        #print "inserting " + str(pos) + " in " + f
        fn = -1
        for xx in range(0,len(self.files)):
            if self.files[xx]==f:
                fn = xx
        self.backupMarker(fn,pos)
        head = self.defs[f][0:pos]
        if d==None:
            tail = []
        else:
            tail = self.defs[f][pos:]
        if d==None:
            line = len(self.text[file])+1
            column = 0
        else:
            line = d.tokens[0].line
            column = d.tokens[0].column
        #print "Here1 "+str(len(result))
        #print line
        #print column
        #print "Here2"
        #print result
        r = result[len(result)-1]
        line2 = r.tokens[len(r.tokens)-1].line+2
        column2 = r.tokens[len(r.tokens)-1].column
        #print line2
        #print column2
        #for dd in tail:
            #print dd.tokens[0]
        for dd in tail:
            #print "Here aa"
            #print dd.tokens[0]
            dd.editUpdateTokens(start_line,start_column,line-1,column,line2-1,column2)
            #print dd.tokens[0]
            #print "Here bbb"
        #print "Here3"
        #print len(head)
        #print len(result)
        #print len(tail)
        #print len(self.defs[f])
        for r in result:
            r.managementState = 0
            r.needsReplay = 4
        self.defs[f] = head+result+tail
        t = self.text[f].split("\n")
        before_text = t[0:start_line-1]
        #print "Here4"
        if start_column>0:
            new_text = t[start_line-1][0:start_column]+new_text
        if column < len(t[line-1]):
            new_text = new_text+t[line-1][column:]
        #print "Here5"
        after_text = t[start_line:]
        #print len(self.text[f])
        #print "*** BEFORE TEXT ***"
        #print before_text
        #print "*** AFTER TEXT ***"
        #print after_text
        #print "*** OLD TEXT ***"
        #print self.text[f]
        #print "*** DONE OLD TEXT ***"
        #print len(self.text[f])
        while len(new_text)>0 and new_text[len(new_text)-1]=='\n':
            new_text = new_text[0:len(new_text)-1]
        self.text[f] = "\n".join(before_text+new_text.split("\n")+after_text)
        #print len(self.text[f])
        #print "*** NEW TEXT ***"
        #print self.text[f]
        #print "*** DONE NEW TEXT ***"
        #print start_line
        #print start_column
        #print line
        #print column
        #print line2
        #print column2
        #print f
        file = f
        #print "Here1"
        self.buildDependencies()
        #print "Here3"
        if saveResult:
            self.writeProverFile()
            ff = open(file,"w")
            ff.write(self.text[f])
            ff.close()
        #print "**** RETURNING ****"

    def readCoqFile(self, coqSource):
        self.populated[coqSource] = True
        print self.root
        print coqSource
        f = open(self.root+"/"+coqSource)

        statements = f.read()
        self.text[coqSource] = statements

        program = []
        for token in CoqLex.tokenize(statements):
            program.append(token)

        #try:
        p = CoqParse.parseCoqProgram(program)
        #except CoqParse.ParseError:
            #print coqSource
            #exit()

        self.defs[coqSource] = []
        for x in p:
            #print x
            #print x.name
            self.defs[coqSource].append(x)
            for t in x.definedNames():
                self.definedTerms.append(t)
            #print "#### START ####"
            #print self.extractText(self.text[coqSource].split("\n"), x)
            #print "#### END ####"
            #for n in range(0,len(x.getProof())):
                #print self.extractTactic(self.text[coqSource].split("\n"), x, n)
                #print "########"

    def instantiateCoqFile(self, coqSource):
        try:
            x = self.loaded[coqSource]
            return
        except KeyError:
            pass
        self.loaded[coqSource] = True
        old_defs = self.defs[coqSource]
        self.readCoqFile(coqSource)
        new_defs = self.defs[coqSource]
	for i in range(0,len(new_defs)):
            print "Processing element"
            print old_defs[i]
            print "Needs replay"
            print old_defs[i].needsReplay
            #print new_defs[i]
            self.instantiations[old_defs[i]] = new_defs[i]
            new_defs[i].result = old_defs[i].result
            new_defs[i].old_result = old_defs[i].old_result
            new_defs[i].inFile = old_defs[i].inFile
            new_defs[i].needsReplay = old_defs[i].needsReplay
            new_defs[i].insertParent = old_defs[i].insertParent
            new_defs[i].insertItem = old_defs[i].insertItem
            new_defs[i].parents = []
            new_defs[i].children = []
            parents = old_defs[i].parents
            for p in parents:
                new_defs[i].parents.append(p)
                try:
                    p.children.remove(old_defs[i])
                except ValueError:
                    pass
                p.children.append(new_defs[i])
            children = old_defs[i].children
            for c in children:
                new_defs[i].children.append(c)
                #print "Processing child"
                #print c
                #print c.parents
                try:
                    c.parents.remove(old_defs[i])
                except ValueError:
                    pass
                c.parents.append(new_defs[i])
            for j in range(0,len(new_defs[i].getProof())):
                print i
                print j
                print len(new_defs[i].getProof())
                print len(old_defs[i].getProof())
                if j < len(new_defs[i].getProof()):
                    if j >= len(old_defs[i].getProof()):
                        new_defs[i].getProof()[j].result = ""
                        new_defs[i].getProof()[j].old_result = ""
                        new_defs[i].getProof()[j].needsReplay = 0
                        new_defs[i].getProof()[j].subgoals = 0
                        new_defs[i].getProof()[j].unfocused = 0
                    else:
                        new_defs[i].getProof()[j].result = old_defs[i].getProof()[j].result
                        try:
                            new_defs[i].getProof()[j].old_result = old_defs[i].getProof()[j].old_result
                        except AttributeError:
                            pass
                        new_defs[i].getProof()[j].needsReplay = old_defs[i].getProof()[j].needsReplay
                        new_defs[i].getProof()[j].subgoals = old_defs[i].getProof()[j].subgoals
                        new_defs[i].getProof()[j].unfocused = old_defs[i].getProof()[j].unfocused
        for f in self.files:
            for d in self.defs[f]:
                for p in range(0,len(d.parents)):
                    for n in range(0,len(old_defs)):
                        if d.parents[p]==old_defs[n]:
                            d.parents[p] = new_defs[n]
                for c in range(0,len(d.children)):
                    for n in range(0,len(old_defs)):
                        if d.children[c]==old_defs[n]:
                            d.children[c] = new_defs[n]
        return (old_defs,new_defs)

    def initiateProverFile(self, pname):
        if not(self.projectFile==None):
            return
        #print "&&&&&&&&&&& Resetting project &&&&&&&&&"
        try:
            shutil.rmtree(pname)
        except OSError:
            pass
        os.mkdir(pname)
        self.projectFile = pname

    def writeProverFile(self):
        f = open(self.projectFile+"/files","w")
        f.write(self.root+"\n")
        f.write(self.projectName+"\n")
        f.write(str(len(self.files))+"\n")
        n = 1
        for ff in self.files:
            f.write(ff+"\n")
            dd = self.defs[ff]
            subf = open(self.projectFile+"/file"+str(n),"w")
            f.write(str(len(dd))+"\n")
            n = n+1
            for d in dd:
                q = d.definedNames()
                f.write(str(len(q))+"\n")
                #print "WRITE NAME"
                for x in q:
                    #print "    "+str(x)
                    f.write(str(x) + "\n")
                #print "DEF "+str(d)
                f.write(d.header()+"\n")
                f.write(str(len(d.parents))+"\n")
                #print "    WRITE PARENTS"
                for x in d.parents:
                    #print "        "+str(x.definedNames()[0])
                    f.write(x.definedNames()[0]+"\n")
                f.write(str(len(d.children))+"\n")
                #print "    WRITE CHILDREN"
                for x in d.children:
                    #print "        "+str(x.definedNames()[0])
                    #print "Child "+str(x)
                    f.write(x.definedNames()[0]+"\n")
                f.write(str(d.needsReplay)+"\n")
                x = len(d.result.split("\n"))
                subf.write(str(x)+"\n")
                subf.write(d.result+"\n")
                try:
                    if d.old_result==None:
                        subf.write("0\n")
                    else:
                        x = len(d.old_result.split("\n"))
                        subf.write(str(x)+"\n")
                        subf.write(d.old_result+"\n")
                except AttributeError:
                    subf.write("0\n")
                if d.indent():
                    f.write("1\n")
                else:
                    f.write("0\n")
                if d.undent():
                    f.write("1\n")
                else:
                    f.write("0\n")
                l = len(d.getProof())
                f.write(str(l)+"\n")
                for t in d.getProof():
                    #print t
                    f.write(str(t.subgoals)+"\n")
                    f.write(str(t.unfocused)+"\n")
                    f.write(str(t.needsReplay)+"\n")
                    x = len(t.result.split("\n"))
                    subf.write(str(x)+"\n")
                    subf.write(t.result+"\n")
                    try:
                        if t.old_result==None:
                            subf.write("0\n")
                        else:
                            x = len(t.old_result.split("\n"))
                            subf.write(str(x)+"\n")
                            subf.write(t.old_result+"\n")
                    except AttributeError:
                        subf.write("0\n")
            subf.close()
        f.close()

    def getLines(self, lines):
        count = int(lines[0])
        text = "\n".join(lines[1:count+1])
        lines = lines[count+1:]
        return (text,lines)

    def readProverProject(self, f):
        self.defs = {}
        self.text = {}
        self.files = []
        self.projectFile = f
        ff = open(f+"/files")
        lines = ff.read().split("\n")
        if not(self.overrideRoot):
            self.root = lines[0]
        self.projectName = lines[1]
        count = int(lines[2])
        lines = lines[3:]
        for i in range(0,count):
            file = lines[0]
            self.resultFile[file] = "file"+str(i+1)
            self.files.append(file)
            c2 = int(lines[1])
            lines = lines[2:]
            dd = []
            #print "Processing file "+file
            for i in range(0,c2):
                d = CoqParse.CoqPlaceHolderDeclaration([],"",[],[],[],file,False,False)
                dd.append(d)
                rl = self.getLines(lines)
                lines = rl[1]
                #print "DECL "+str(rl[0])
                d.decl_list = rl[0].split("\n")
                #print "NAME "+str(d.definedNames())
                d.defn = lines[0]
                rl = self.getLines(lines[1:])
                d.temp_parents = rl[0].split("\n")
                lines = rl[1]
                rl = self.getLines(lines)
                d.temp_children = rl[0].split("\n")
                #print "READ PARENTS"
                #for x in d.temp_parents:
                    #print "    "+str(x)
                #print "READ CHILDREN"
                #for x in d.temp_children:
                    #print "    "+str(x)
                lines = rl[1]
                d.needsReplay = int(lines[0])
                d.result = ""
                d.indent_val = int(lines[1])>0
                d.undent_val = int(lines[2])>0
                c3 = int(lines[3])
                lines = lines[4:]
                pp = dd[i].getProof()
                for i in range(0,c3):
                    #print "    Tactic "+str(i)+" "+str(c3)
                    p = CoqParse.CoqPlaceHolderTactic([]);
                    pp.append(p)
                    p.subgoals = int(lines[0])
                    p.unfocused = int(lines[1])
                    p.needsReplay = int(lines[2])
                    lines = lines[3:]
                    p.result = ""
            self.defs[file] = dd
            self.populated[file] = False
        for f in self.files:
            #print f
            for d in self.defs[f]:
                d.parents = []
                for x in d.temp_parents:
                    if not(x==''):
                        z = self.findDef(x)
                        #print "TEMP "+str(x)
                        #print "FINAL "+str(z)
                        if z!=None:
                            d.parents.append(z)
                d.children = []
                for x in d.temp_children:
                    if not(x==''):
                        z = self.findDef(x)
                        #print "TEMPc "+str(x)
                        #print "FINALc "+str(z)
                        if z!=None:
                            d.children.append(z)
        print "Building dependencies"
        self.buildDependencies()
        print "After building dependencies"

    def populateFile(self, f):
        if self.projectFile==None:
            return
        #print self.populated
        if self.populated[f]:
            return
        self.populated[f] = True
        print "POPULATE FILE "+f
        ff = open(self.projectFile + "/" + self.resultFile[f])
        lines = ff.read().split("\n")
        for d in self.defs[f]:
            rl = self.getLines(lines)
            d.result = rl[0]
            lines = rl[1]
            rl = self.getLines(lines)
            d.old_result = rl[0]
            lines = rl[1]
            pp = d.getProof()
            for p in pp:
                rl = self.getLines(lines)
                lines = rl[1]
                p.result = rl[0]
                rl = self.getLines(lines)
                lines = rl[1]
                p.old_result = rl[0]

def readData(prover,root,override,name,args):
    print "&&&Root "+str(root)
    proj = Project()
    proj.root = root
    proj.overrideRoot = override
    proj.projectName = name
    doWrite = False
    if len(args) > 0:
        for f in args:
            print "@@@@@@@@@@@@@@@ Parsing "+f
            proj.initiateProverFile(prover)
            proj.files.append(f)
            proj.readCoqFile(f)
            Collect.collectData(proj.projectFile, proj.projectName, proj.defs[f], proj.text[f])
            doWrite = True
            proj.compileFile(f)
    else:
        proj.readProverProject(prover)
    if doWrite:
        #proj.buildDependencies()
        proj.dummyDependencies()
        proj.writeProverFile()
        #for f in proj.files:
            #proj.compileFile(f)
    return proj

#f = open('../Coq4/SfLib.v')
#statements = f.read()

#initLex()

#for token in tokenize(statements):
#    print(token)


def main(argv):
    parser = OptionParser()
    #parser.add_option("-h", "--help", dest="help",
    #                   help="show help message and exit", metavar="HELP")
    parser.add_option("-r", "--root", dest="root",
                       help="Specify the root of the project", metavar="ROOT")
    parser.add_option("-n", "--name", dest="name",
                       help="Specify the Coq project name", metavar="NAME")
    parser.add_option("-p", "--prover", dest="prover",
                       help="Specify the name of the project file", metavar="PROVER")
    (options, args) = parser.parse_args(argv)
    print options
    print args
    root = options.root
    override = True
    if root==None:
        override = False
        root = "."

    prover = options.prover
    if prover==None:
        prover = "prover.pp"
        if os.path.exists("prover.pp"):
            print "Error: 'prover.pp' exists--must use -p to specify project file."
            exit()

    name = options.name
    if name==None:
        name = "Main"

    args = args[1:]

    print "**** START TIME ****"
    print (time.strftime("%H:%M:%S"))

    proj = readData(prover,root,override,name,args)

    print "**** FINISH TIME ****"
    print (time.strftime("%H:%M:%S"))

    root = Tkinter.Tk()
    root.wm_title("CoqPIE")
    root.wm_iconname("PIE")

    #import plastik_theme
    #plastik_theme.install('~/tile-themes/plastik/plastik')

    app = UI.App(root,proj)
    app.populate_tree()
    root.mainloop()
    UI.UILogger.dumpLog("CoqPIE.log")

if __name__ == "__main__":
    main(sys.argv)

