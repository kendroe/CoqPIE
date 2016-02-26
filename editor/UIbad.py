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
try:
    import Tkinter
    import tkFont
except ImportError:
    import tkinter as Tkinter
    import tkinter.font as tkFont

import ttk
import CoqLex
import CoqParse
import UILogger

def donothing():
   filewin = Toplevel(root)
   button = Button(filewin, text="Do nothing button")
   button.pack()

current = None
reference = None
 
def makeReference():
   global current
   global reference
   reference = current

thekeywords = ['Require', 'Export' ,'Opaque', 'Fixpoint', 'match', 'with', 'end',
            'if', 'then', 'else', 'Fixpoint', 'Implicit', 'Arguments', 'fun',
            'Definition', 'forall', 'exists', 'fix', 'In', 'Function',
            'Theorem', 'Proof', 'Qed', 'Open', 'Scope', 'Ltac',
            'move', 'after', 'goal', 'try', 'before',
            'after', 'at', 'top', 'bottom', 'Tactic', 'Notation',
            'let', 'in', 'as', 'by', 'Inductive', 'return',
            'if', 'then', 'else', 'andb', 'true', 'false',
            'repeat', 'context', 'inversion', 'simpl', 'length',
            'reflexivity', 'clear', 'destruct', 'fresh', 'option', 'nat', 'None',
            'Some', 'apply', 'eapply', 'solve', 'compute', 'list', 'cons', 'nil' ]

class App(object):
    def __init__(self,r,proj):
        self.idn = 0
        self.updateNumber = 0
        self.project = proj
        self.tree = None
        self.root = r
        self._setup_widgets()
        self._build_tree()
        self.widgetMap = {}
        self.widgetFile = {}
        self.text = {}
        self.code_tags = []
        self.proof_tags = []
        self.proofMap = {}
        print "currentDefn none"
        self.currentDefn = None
        self.currentStepn = None
        self.parseCache = {}
        self.knownTerms = proj.libraryTerms+proj.definedTerms
        self.selectDefTag = None
        proj.registeredUI.append(self)
        proj.initializeCoqManagement()
        self.highlightMap = {}

    def get_keyword_placements(self,tokens):
        goodWords = []
        badWords = []
        numbers = []
        quotes = []
        comments = []
        symbols = []
        keywords = []
        for t in tokens:
            if t.typ=='ID' or t.typ=='_':
                if t.value in thekeywords:
                    keywords.append((t.line,t.column,t.line,t.column+len(t.value)))
                elif t.value in self.knownTerms:
                    goodWords.append((t.line,t.column,t.line,t.column+len(t.value)))
                else:
                    badWords.append((t.line,t.column,t.line,t.column+len(t.value)))
            elif t.typ=='QUOTATION' or t.typ=='SQUOTATION':
                x = t.value.split("\n")
                if len(x)==1:
                    el = t.line
                    ec = t.column + len(t.value)
                else:
                    el = t.line + len(x)-1
                    ec = len(x[len(x)-1])
                quotes.append((t.line,t.column,el,ec))
            elif t.typ=='COMMENT' or t.typ=='SEPERATOR':
                x = t.value.split("\n")
                if len(x)==1:
                    el = t.line
                    ec = t.column = len(t.value)
                else:
                    el = t.line + len(x)-1
                    ec = len(x[len(x)-1])
                comments.append((t.line,t.column,el,ec))
            elif t.typ=='NUMBER':
                numbers.append((t.line,t.column,t.line,t.column+len(t.value)))
            elif t.value in thekeywords:
                keywords.append((t.line,t.column,t.line,t.column+len(t.value)))
            elif t.typ!='leftParen' and t.typ!='rightParen' and t.typ!='leftBrace' and t.typ!='rightBrace' and t.typ!='leftBracket' and t.typ!='rightBracket':
                symbols.append((t.line,t.column,t.line,t.column+len(t.value)))

        return (keywords,goodWords,badWords,quotes,comments,numbers,symbols)

    def filter_tuples(self, tuples):
        z = []
        for x in tuples:
            if x[0]<=1 and x[2]<=1:
                z.append(x)
        return z

    def get_keyword_placements1(self, tokens):
        p = self.get_keyword_placements(tokens)
        return (self.filter_tuples(p[0]), self.filter_tuples(p[1]), self.filter_tuples(p[2]), self.filter_tuples(p[3]), self.filter_tuples(p[4]), self.filter_tuples(p[5]), self.filter_tuples(p[6]))

    def inDiff(self, tuple, diffs):
        for d in diffs:
            if (d[0]< tuple[0] or (d[0]==tuple[0] and d[1]<=tuple[1])) and (d[2]>tuple[2] or (d[2]==tuple[2] and d[3]>=tuple[3])):
                return True
        return False

    def modeAtPosition(self, line, col):
        #print "^^^ GETTING STATE "+str(line)+" "+str(col)
        try:
            for d in self.project.defs[self.displayedFile]:
                t = d.tokens[len(d.tokens)-1]
                l = t.line
                c = t.column+len(t.value)
                if line < l or (line==l and col < c):
                    p = d.getProof()
                    try:
                        if len(p) > 0:
                            l = p[0].tokens[0].line
                            c = p[0].tokens[0].column
                            #print "Testing begin"
                            if line < l or (line==l and col < c):
                                return d.managementState
                            for pp in p:
                                #print "Testing tok"
                                t = pp.tokens[len(pp.tokens)-1]
                                l = t.line
                                c = t.column+len(t.value)
                                #print "Testing tok2 "+str(l)+" "+str(c)
                                if line < l or (line==l and col < c):
                                    try:
                                        #print "Returning state for "+str(pp)+" "+str(pp.managementState)
                                        return pp.managementState
                                    except AttributeError:
                                        #print "Returning state for "+str(pp)+" zero"
                                        return 0
                    except AttributeError:
                        pass
                    #print "Def return state for "+str(d)
                    return d.managementState
        except AttributeError:
            return 0

    def defTagText(self, textView):
        textView.tag_delete(Tkinter.ALL)
        textView.tag_delete('gray')
        textView.tag_delete('lightgray')
        textView.tag_delete('blue')
        textView.tag_delete('yellow')
        textView.tag_configure('gray', background = 'gray')
        textView.tag_configure('lightgray', background = 'lightgray')
        textView.tag_configure('blue', background = 'lightblue')
        textView.tag_configure('yellow', background="yellow")
        line = 1
        column = 0
        self.tag = 0
        for d in self.project.defs[self.displayedFile]:
            p = d.getProof()
            if len(p) > 0:
                t = p[0].tokens[0]
                nl = t.line
                nc = t.column
                try:
                    if d.managementState == 2:
                        textView.tag_add('gray',str(line)+"."+str(column),str(nl)+"."+str(nc))
                    elif d.managementState == 1:
                        textView.tag_add('lightgray',str(line)+"."+str(column),str(nl)+"."+str(nc))
                    elif d.managementState == -1:
                        textView.tag_add('blue',str(line)+"."+str(column),str(nl)+"."+str(nc))
                except AttributeError:
                    pass
                line = nl
                column = nc
                for x in range(0,len(p)-1):
                    pp = p[x]
                    t = pp.tokens[len(pp.tokens)-1]
                    nl = t.line
                    nc = t.column+len(t.value)
                    try:
                        if pp.managementState == 2:
                            textView.tag_add('gray',str(line)+"."+str(column),str(nl)+"."+str(nc))
                        elif pp.managementState == 1:
                            textView.tag_add('lightgray',str(line)+"."+str(column),str(nl)+"."+str(nc))
                        elif pp.managementState == -1:
                            textView.tag_add('blue',str(line)+"."+str(column),str(nl)+"."+str(nc))
                    except AttributeError:
                        pass
                    line = nl
                    column = nc
                pp = p[len(p)-1]
                t = pp.tokens[len(pp.tokens)-1]
                nl = t.line
                nc = t.column+len(t.value)
                try:
                    if pp.managementState == 2:
                        textView.tag_add('gray',str(line)+"."+str(column),str(nl)+"."+str(nc))
                    elif pp.managementState == 1:
                        textView.tag_add('lightgray',str(line)+"."+str(column),str(nl)+"."+str(nc))
                    elif pp.managementState == -1:
                        textView.tag_add('blue',str(line)+"."+str(column),str(nl)+"."+str(nc))
                except AttributeError:
                    pass
                line = nl
                column = nc
            else:
                t = d.tokens[len(d.tokens)-1]
                nl = t.line
                nc = t.column+len(t.value)
                try:
                    #print "COLORING"
                    if d.managementState == 2:
                        textView.tag_add('gray',str(line)+"."+str(column),str(nl)+"."+str(nc))
                    elif d.managementState == 1:
                        textView.tag_add('lightgray',str(line)+"."+str(column),str(nl)+"."+str(nc))
                    elif d.managementState == -1:
                        textView.tag_add('blue',str(line)+"."+str(column),str(nl)+"."+str(nc))
                    #print "    Done "+str(d.managementState)
                except AttributeError:
                    #print "    None"
                    pass
                line = nl
                column = nc

    def tagText(self, textView, keywords, diffs, df, lines, use_mode):
        #print "^^^^^^^^^ tagText "+str(lines)
        #textView.tag_delete('blue_f')
        #textView.tag_delete('magenta_f')
        #textView.tag_delete('cyan_f')
        #textView.tag_delete('red_f')
        #textView.tag_delete('green_f')
        #textView.tag_delete('black_f')
        #textView.tag_configure('blue_f', foreground="blue")
        #textView.tag_configure('magenta_f', foreground="magenta")
        #textView.tag_configure('red_f', foreground="red")
        #textView.tag_configure('green_f', foreground="green")
        #textView.tag_configure('cyan_f', foreground="cyan")
        #textView.tag_configure('black_f', foreground="black")
        line = 1
        column = 0
        #print "Tag 2"
        #print "Tag 3"
        for d in diffs:
            tagn = "tag"+str(self.tag)
            textView.tag_add(tagn,str(d[0])+"."+str(d[1]),str(d[2])+"."+str(d[3]))
            textView.tag_config(tagn, foreground="black", background="yellow")
            self.tag = self.tag+1
            self.code_tags.append(tagn)
        #print "Tag 4"
        m = 0
        for k in keywords[0]:
            if lines==None or k[0] in lines:
                tagn = "tag"+str(self.tag)
                textView.tag_add(tagn,str(k[0])+"."+str(k[1]),str(k[2])+"."+str(k[3]))
                if use_mode:
                    m = self.modeAtPosition(k[0],k[1])
                if self.inDiff(k,diffs):
                    textView.tag_config(tagn, foreground="blue", background="yellow")
                elif m==2:
                    textView.tag_config(tagn, foreground="blue", background="gray")
                elif m==1:
                    textView.tag_config(tagn, foreground="blue", background="lightgray")
                elif m==-1:
                    textView.tag_config(tagn, foreground="blue", background="lightblue")
                else:
                    textView.tag_config(tagn, foreground="blue", background="white")
                self.tag = self.tag+1
                self.code_tags.append(tagn)
        #print "Tag 5"
        for k in keywords[1]:
            if lines==None or k[0] in lines:
                tagn = "tag"+str(self.tag)
                textView.tag_add(tagn,str(k[0])+"."+str(k[1]),str(k[2])+"."+str(k[3]))
                if use_mode:
                    m = self.modeAtPosition(k[0],k[1])
                if self.inDiff(k,diffs):
                    textView.tag_config(tagn, foreground="magenta", background="yellow")
                elif m==2:
                    textView.tag_config(tagn, foreground="magenta", background="gray")
                elif m==1:
                    textView.tag_config(tagn, foreground="magenta", background="lightgray")
                elif m==-1:
                    textView.tag_config(tagn, foreground="magenta", background="lightblue")
                else:
                    textView.tag_config(tagn, foreground="magenta", background="white")
                self.tag = self.tag+1
                self.code_tags.append(tagn)
        #print "Tag 6"
        for k in keywords[2]:
            if lines==None or k[0] in lines:
                tagn = "tag"+str(self.tag)
                textView.tag_add(tagn,str(k[0])+"."+str(k[1]),str(k[2])+"."+str(k[3]))
                if use_mode:
                    m = self.modeAtPosition(k[0],k[1])
                if self.inDiff(k,diffs):
                    textView.tag_config(tagn, foreground="red", background="yellow")
                elif m==2:
                    textView.tag_config(tagn, foreground="red", background="gray")
                elif m==1:
                    textView.tag_config(tagn, foreground="red", background="lightgray")
                elif m==-1:
                    textView.tag_config(tagn, foreground="red", background="lightblue")
                else:
                    textView.tag_config(tagn, foreground="red", background="white")
                self.tag = self.tag+1
                self.code_tags.append(tagn)
        #print "Tag 7"
        for k in keywords[3]:
            if lines==None or k[0] in lines:
                tagn = "tag"+str(self.tag)
                textView.tag_add(tagn,str(k[0])+"."+str(k[1]),str(k[2])+"."+str(k[3]))
                if use_mode:
                    m = self.modeAtPosition(k[0],k[1])
                if self.inDiff(k,diffs):
                    textView.tag_config(tagn, foreground="green", background="yellow")
                elif m==2:
                    textView.tag_config(tagn, foreground="green", background="gray")
                elif m==1:
                    textView.tag_config(tagn, foreground="green", background="lightgray")
                elif m==-1:
                    textView.tag_config(tagn, foreground="green", background="lightblue")
                else:
                    textView.tag_config(tagn, foreground="green", background="white")
                self.tag = self.tag+1
                self.code_tags.append(tagn)
        #print "Tag 8"
        for k in keywords[4]:
            if lines==None or k[0] in lines:
                tagn = "tag"+str(self.tag)
                textView.tag_add(tagn,str(k[0])+"."+str(k[1]),str(k[2])+"."+str(k[3]))
                if use_mode:
                    m = self.modeAtPosition(k[0],k[1])
                if self.inDiff(k,diffs):
                    textView.tag_config(tagn, foreground="#888", background="yellow")
                elif m==2:
                    textView.tag_config(tagn, foreground="#888", background="gray")
                elif m==1:
                    textView.tag_config(tagn, foreground="#888", background="lightgray")
                elif m==-1:
                    textView.tag_config(tagn, foreground="#888", background="lightblue")
                else:
                    textView.tag_config(tagn, foreground="#888", background="white")
                self.tag = self.tag+1
                self.code_tags.append(tagn)
        #print "Tag 9"
        for k in keywords[5]:
            if lines==None or k[0] in lines:
                tagn = "tag"+str(self.tag)
                textView.tag_add(tagn,str(k[0])+"."+str(k[1]),str(k[2])+"."+str(k[3]))
                if use_mode:
                    m = self.modeAtPosition(k[0],k[1])
                if self.inDiff(k,diffs):
                    textView.tag_config(tagn, foreground="green", background="yellow")
                elif m==2:
                    textView.tag_config(tagn, foreground="green", background="gray")
                elif m==1:
                    textView.tag_config(tagn, foreground="green", background="lightgray")
                elif m==-1:
                    textView.tag_config(tagn, foreground="green", background="lightblue")
                else:
                    textView.tag_config(tagn, foreground="green", background="white")
                self.tag = self.tag+1
                self.code_tags.append(tagn)
        #print "Tag 10"
        for k in keywords[6]:
            if lines==None or k[0] in lines:
                tagn = "tag"+str(self.tag)
                textView.tag_add(tagn,str(k[0])+"."+str(k[1]),str(k[2])+"."+str(k[3]))
                if use_mode:
                    m = self.modeAtPosition(k[0],k[1])
                if self.inDiff(k,diffs):
                    textView.tag_config(tagn, foreground="cyan", background="yellow")
                elif m==2:
                    textView.tag_config(tagn, foreground="cyan", background="gray")
                elif m==1:
                    textView.tag_config(tagn, foreground="cyan", background="lightgray")
                elif m==-1:
                    textView.tag_config(tagn, foreground="cyan", background="lightblue")
                else:
                    textView.tag_config(tagn, foreground="cyan", background="white")
                self.tag = self.tag+1
                self.code_tags.append(tagn)
        #print "Tag 11"
        if not(self.firstLine==None):
            tagn = "tag"+str(self.tag)
            self.tag = self.tag+1
            textView.tag_add(tagn,str(self.firstLine)+"."+str(self.firstCol),str(self.lastLine)+"."+str(self.lastCol))
            textView.tag_config(tagn, foreground="black", background="yellow")
            self.code_tags.append(tagn)
            if self.errorLine != None:
                tagn = "tag"+str(self.tag)
                self.code.tag_add(tagn,str(self.errorLine)+"."+str(self.errorCol),str(self.lastLine)+"."+str(self.lastCol))
                self.code.tag_config(tagn, foreground="black", background="red")
                self.code_tags.append(tagn)
                self.tag = self.tag+1
        elif not(df==None):
            tagn = "tag"+str(self.tag)
            self.tag = self.tag+1
            strow = df.tokens[0].line
            stcol = df.tokens[0].column
            enrow = df.tokens[len(df.tokens)-1].line
            encol = df.tokens[len(df.tokens)-1].column+len(df.tokens[len(df.tokens)-1].value)
            textView.tag_add(tagn,str(strow)+"."+str(stcol),str(enrow)+"."+str(encol))
            textView.tag_config(tagn, foreground="black", background="orange")
            self.code_tags.append(tagn)
        self.highlightSelection()

    def highlight_proof_keywords(self,tokens):
        for x in self.proof_tags:
            self.response.tag_delete(x)
        self.proof_tags = []
        n = 0
        for t in tokens:
            if t.typ!='ID' and t.value==t.typ:
                tagn = "tag"+str(n)
                self.proof_tags.append(tagn)
                n = n+1
                self.response.tag_add(tagn,str(t.line)+"."+str(t.column),str(t.line)+"."+str(t.column+len(t.value)))
                self.response.tag_config(tagn, foreground="blue", background="white")

    def highlight_keywords_new_position(self):
        #print self.code.yview()
        try:
            count = len(self.text[self.displayedFile])
        except KeyError:
            print "Count error"
            return
        start_line = int(self.code.yview()[0]*count)
        end_line = int(self.code.yview()[1]*count+25)
        if start_line < 1:
            start_line = 1
        lines_to_process = []
        new_highlighted = []
        st = 0
        l = len(self.highlightedLines)
        while st < l and self.highlightedLines[st] < start_line:
            new_highlighted.append(self.highlightedLines[st])
            st = st+1
        x = start_line
        while x <= end_line:
            if st < l and self.highlightedLines[st]==x:
                st = st + 1
            else:
                lines_to_process.append(x)
            new_highlighted.append(x)
            x = x+1
        while st < l:
            new_highlighted.append(self.highlightedLines[st])
            st = st+1
        self.highlightedLines = new_highlighted
        #print "Start line "+str(start_line)
        #print "End line "+str(end_line)
        #print "Process "+str(lines_to_process)
        self.tagText(self.code,self.placements,[],self.hdef,lines_to_process,True)

    def highlight_keywords(self,tokens,diffs,df):
        self.highlightedLines = []
        self.placements = self.get_keyword_placements(tokens)
        #print "highlight 1"
        self.hdef = df
        self.placements = (self.update_keywords(self.placements[0]),
                           self.update_keywords(self.placements[1]),
                           self.update_keywords(self.placements[2]),
                           self.update_keywords(self.placements[3]),
                           self.update_keywords(self.placements[4]),
                           self.update_keywords(self.placements[5]),
                           self.update_keywords(self.placements[6]))
        #print "highlight 2"
        for x in self.code_tags:
            self.code.tag_delete(x)
        #print "highlight 3"
        self.code_tags = []
        self.defTagText(self.code)
        self.highlight_keywords_new_position()
        #print "highlight 4"
        #n = 0
        #for t in tokens:
            #if t.typ!='ID' and t.value==t.typ:
                #tagn = "tag"+str(n)
                #self.code_tags.append(tagn)
                #n = n+1
                #self.code.tag_add(tagn,str(t.line)+"."+str(t.column),str(t.line)+"."+str(t.column+len(t.value)))
                #self.code.tag_config(tagn, foreground="blue", background="white")

    def toggle_showOld(self):
       print "Toggle show old"
       print self.showOldVar.get()
       x = self.proofMap[self.savedTag]
       self.selectProofNode(self.savedTag)

    def diff_changed(self,val):
       print "Diff changed"
       print val
       print self.diff_value.get()
       self.selectProofNode(self.savedTag)

    def toggle_hyp(self):
        #print "Toggle hyp"
        for key in self.info.hypothesisVars.keys():
            #print "Hypothesis"
            #print key
            #print self.info.hypothesisVars[key].get()
            self.info.open_dict[key] = self.info.hypothesisVars[key].get()
        self.selectDef(self.selectDefTag)

    def moveTextCursor(self):
        print "HERE"
        self.doMoveDeclaration = True
        self.selectTreeItem()
        #self.root.after(30000,self.moveDeclaration())
        print "HERE 2"
        #if self.savedTag != None:
            #step = self.info
            #df = self.info.parent
            #self.project.moveMarker(self.currentDef,step)

    def getGoalOld(self,info):
        try:
            return self.parseCache[info.old_result]
        except KeyError:
            try:
                try:
                    #print info
                    #print info.old_result
                    if info.old_result==None:
                        return None
                    else:
                        t = CoqLex.tokenize(info.old_result)
                    tokens = []
                    for x in t:
                        tokens.append(x)
                except RuntimeError:
                    l = info.old_result.split("\n")
                    res = []
                    for ll in l:
                        while len(ll) > 80:
                            res.append(ll[0:80])
                            ll = ll[80:]
                        res.append(ll)
                    hlabel = Tkinter.Text(self.response, width=90,height=len(res)*2)
                    self.response.create_window(0,0,window=hlabel, anchor=Tkinter.NW)
                    hlabel.insert(Tkinter.INSERT, "\n".join(res))
                    return

                #self.highlight_proof_keywords(tokens)
                cg = CoqParse.parseCoqGoal(tokens)
                self.parseCache[info.old_result] = (cg,tokens)
                return (cg,tokens)
            except CoqParse.ParseError:
                #print "RESULT"
                #print info.old_result
                #print "DONE RESULT"
                return None

    def getGoal(self,info):
        try:
            return self.parseCache[info.result]
        except KeyError:
            try:
                try:
                    t = CoqLex.tokenize(info.result)
                    tokens = []
                    for x in t:
                        tokens.append(x)
                except RuntimeError:
                    l = info.result.split("\n")
                    res = []
                    for ll in l:
                        while len(ll) > 80:
                            res.append(ll[0:80])
                            ll = ll[80:]
                        res.append(ll)
                    hlabel = Tkinter.Text(self.response, width=90,height=len(res)*2)
                    self.response.create_window(0,0,window=hlabel, anchor=Tkinter.NW)
                    hlabel.insert(Tkinter.INSERT, "\n".join(res))
                    return

                #self.highlight_proof_keywords(tokens)
                cg = CoqParse.parseCoqGoal(tokens)
                self.parseCache[info.result] = (cg,tokens)
                return (cg,tokens)
            except CoqParse.ParseError:
                #print "RESULT"
                #print info.result
                #print "DONE RESULT"
                return None

    def insertResponseText(self,text):
        print "RESPONSE TEXT"
        print text
        print "END RESPONSE TEXT"
        #self.response.tag_delete(Tkinter.ALL)
        x = text.split("\n")
        l = len(x)
        self.response.configure(scrollregion=(0,0,4000,200000)) 
        self.response.update_idletasks()
        self.response.delete(Tkinter.ALL)
        hlabel = Tkinter.Text(self.response, width=80,height=l+200)
        self.response.create_window(0,0,window=hlabel, anchor=Tkinter.NW)
        i = 0
        tags = []
        print x
        while i < len(x)-1:
            print x[i]
            if len(x[i])>0 and x[i][0]=='>' and len(x[i+1])>0 and x[i+1][0]=='>':
                st = x[i+1].find('^')
                if st > -1:
                    en = len(x[i+1])
                    if en <= len(x[i]):
                        print "HERE "+str(i)
                        x = x[0:i+1]+x[i+2:]
                        tags.append((i+1,st,en))
            i = i+1
        text = "\n".join(x)
        print "RESPONSE TEXT"
        print text
        print "END RESPONSE TEXT"
        print text
        hlabel.insert(Tkinter.INSERT, text)
        for q in tags:
            tagn = "tag"+str(self.tag)
            self.tag = self.tag+1
            hlabel.tag_add(tagn,str(q[0])+"."+str(q[1]),str(q[0])+"."+str(q[2]))
            hlabel.tag_config(tagn, foreground="black", background="red")
   
    def selectProofNode(self,tag):
        self.response.configure(scrollregion=(0,0,4000,200000)) 
        self.response.update_idletasks()
        self.savedTag = tag
        n = tag
        #print "SELECTING " + str(n)
	#self.tactic.delete("1.0",Tkinter.END)
	current = self.proofMap[n]
        self.currentDef = current
        #print current
        #print self.proofFile[n]
        info = self.proofMap[n].getSegment(self.text[self.proofFile[n]])
        #self.tactic.insert(Tkinter.INSERT, info[0])
        self.tacticText = info[0]
        try:
            self.tacticNum = self.proofNum[n]
        except KeyError:
            return True
        self.response.delete(Tkinter.ALL)
        info = self.proofMap[n]
        self.info = info
        #self.response.insert(Tkinter.INSERT, info.result)
        #print "Here1"
        #print info.result
        #print "Here2"
        if self.showOldVar.get()>0:
            r = self.getGoalOld(info)
        else:
            r = self.getGoal(info)
        if r==None:
            return True
        (cg,tokens) = r
        cgp = None
        diff_hyp = False
        diff_old = False
        if self.diff_value.get()==self.diff['values'][2]:
            diff_hyp = True
            r = None
        elif self.diff_value.get()==self.diff['values'][1]:
            diff_old = True
            if self.showOldVar.get()>0:
                r = self.getGoal(info)
            else:
                r = self.getGoalOld(info)
        elif info.parent != None:
            if self.showOldVar.get()>0:
                r = self.getGoalOld(info.parent)
            else:
                r = self.getGoal(info.parent)
            if r != None:
                (cgp,tokens) = r
        #print "Here1"
        try:
            od = info.open_dict
        except AttributeError:
            od = {}
            info.open_dict = od
        #print cg
        if self.showOldVar.get()>0:
            if info.parent != None:
                old_text = info.parent.old_result.split("\n")
            text = info.old_result.split("\n")
        else:
            if info.parent != None:
                old_text = info.parent.result.split("\n")
            text = info.result.split("\n")
        #for t in cg.hypotheses:
            #print "Hypothesis Name"
            #print t[0]
            #print "Hypothesis"
            #print t[1]
            #print "Hypotheses segment"
            #print t[1].getSegment(text)[0]
        #print "Goal"
        #print cg.goal
        #print "Goal segment"
        #print cg.goal.getSegment(text)[0]
        #print cg.subgoals
        #print cg.unfocused_subgoals
        if cg.unfocused_subgoals==0 or cg.unfocused_subgoals==None:
            if cg.subgoals==1:
                goal = "1 subgoal"
            elif cg.subgoals==0:
                goal = "No subgoals"
            else:
                goal = "%d subgoals"%cg.subgoals
        else:
            goal = "%d focused subgoals (unfocused: %d)"%(cg.subgoals,cg.unfocused_subgoals)
        goal_label = Tkinter.Label(self.response, text=goal, font=24, bg='white')
        self.response.create_window(0, 0, window=goal_label, anchor=Tkinter.NW) 
        ypos = 35
        #print "ypos"
        #print ypos
        if len(cg.hypotheses)>0:
            if len(cg.hypotheses)==1:
                t = 'Hypothesis'
            else:
                t = 'Hypotheses'
            hyp_label = Tkinter.Label(self.response, text=t, font=24, bg='white')
            self.response.create_window(0, ypos, window=hyp_label, anchor=Tkinter.NW) 
            #print "Self.topic_label size"
            ypos = ypos + 24
            #print "ypos"
            #print ypos
        info.hypothesisVars = {}
        n = 0
        for h in cg.hypotheses:
            ph = None
            if cgp != None:
                for x in cgp.hypotheses:
                    if x[0]==h[0]:
                        ph = x
            elif diff_hyp:
                ph = ('xx',cg.goal,'yy')
            var = Tkinter.IntVar()
            hcheck_box = Tkinter.Checkbutton(self.response, text=h[0], command=self.toggle_hyp, variable=var)
            info.hypothesisVars[h[0]] = var
            self.response.create_window(0,ypos, window=hcheck_box, anchor=Tkinter.NW)
            try:
                open = od[h[0]]
            except KeyError:
                od[h[0]] = 0
                open = 0
            var.set(open)
            tokens = None
            if h[2]==None:
                x = h[1].getSegment(text)
                tt = x[0]
                tokens = x[1]
            else:
                tt = h[2].getSegment(text)[0]+" : " + h[1].getSegment(text)[0]
            t = tt.split("\n")
            diffs = []
            if tokens != None and ph != None:
                d = CoqParse.diffs(h[1],ph[1])
                for x in d:
                    if open or (x[0][0][0]<=1 and x[1][0][0]<=1):
                        diffs.append((x[0][0][0],x[0][0][1],x[0][1][0],x[0][1][1]))
            if open:
                hlabel = Tkinter.Text(self.response, width=80,height=len(t))
                self.response.create_window(100,ypos,window=hlabel, anchor=Tkinter.NW)
                hlabel.insert(Tkinter.INSERT, tt)
                if tokens != None:
                    p = self.get_keyword_placements(tokens)
                    self.tagText(hlabel,p,diffs,None,None, False)
                hlabel.configure(state=Tkinter.DISABLED)
                ypos = ypos + 24*len(t)
            else:
                hlabel = Tkinter.Text(self.response,width=80,height=1)
                self.response.create_window(100,ypos,window=hlabel, anchor=Tkinter.NW)
                hlabel.insert(Tkinter.INSERT, t[0])
                if tokens != None:
                    p = self.get_keyword_placements1(tokens)
                    self.tagText(hlabel,p,diffs,None,None, False)
                hlabel.configure(state=Tkinter.DISABLED)
                ypos = ypos + 24
            if ph==None and not(diff_hyp) and not(diff_old):
                hcheck_box.configure(bg='yellow')
                tagn = "ptag"+str(n)
                self.code_tags.append(tagn)
                n = n+1
            #print "ypos"
            #print ypos
        deleted_hyps = []
        if cgp != None:
            for h in cgp.hypotheses:
                ph = None
                for x in cg.hypotheses:
                    if x[0]==h[0]:
                        ph = x
                if ph==None:
                    deleted_hyps.append(h)
        if len(deleted_hyps) > 0:
            ypos = ypos + 11
            if len(deleted_hyps)==1:
                t = 'Deleted hypothesis'
            else:
                t = 'Deleted hypotheses'
            hyp_label = Tkinter.Label(self.response, text=t, font=24, fg='#888')
            self.response.create_window(0, ypos, window=hyp_label, anchor=Tkinter.NW) 
            ypos = ypos + 24
            #print "ypos"
            #print ypos
            for h in deleted_hyps:
                var = Tkinter.IntVar()
                hcheck_box = Tkinter.Checkbutton(self.response, text=h[0], command=self.toggle_hyp, variable=var, fg='#888')
                info.hypothesisVars[h[0]] = var
                self.response.create_window(0,ypos, window=hcheck_box, anchor=Tkinter.NW)
                try:
                    open = od[h[0]]
                except KeyError:
                    od[h[0]] = 0
                    open = 0
                var.set(open)
                tokens = None
                if h[2]==None:
                    x = h[1].getSegment(old_text)
                    tt = x[0]
                    #tokens = x[1]
                else:
                    tt = h[2].getSegment(old_text)[0]+" : " + h[1].getSegment(old_text)[0]
                t = tt.split("\n")
                if open:
                    hlabel = Tkinter.Text(self.response, width=80,height=len(t),fg='#888')
                    if tokens != None:
                        p = self.get_keyword_placements(tokens)
                        self.tagText(hlabel,p,[],None, None, False)
                    self.response.create_window(100,ypos,window=hlabel, anchor=Tkinter.NW)
                    hlabel.insert(Tkinter.INSERT, tt)
                    hlabel.configure(state=Tkinter.DISABLED)
                    ypos = ypos + 24*len(t)
                else:
                    hlabel = Tkinter.Text(self.response,width=80,height=1,fg='#888')
                    if tokens != None:
                        p = self.get_keyword_placements1(tokens)
                        self.tagText(hlabel,p,[],None,None, False)
                    self.response.create_window(100,ypos,window=hlabel, anchor=Tkinter.NW)
                    hlabel.insert(Tkinter.INSERT, t[0])
                    hlabel.configure(state=Tkinter.DISABLED)
                    ypos = ypos + 24
                #print "ypos"
                #print ypos

        x = cg.goal.getSegment(text)
        gg = x[0]
        g = gg.split("\n")
        var = Tkinter.IntVar()
        try:
            open = od['.goal']
        except KeyError:
            od['.goal'] = 1
            open = 1
        diffs = []
        if cgp!=None:
            d = CoqParse.diffs(cg.goal,cgp.goal)
            for xx in d:
                if open or (xx[0][0][0]<=1 and xx[1][0][0]<=1):
                    diffs.append((xx[0][0][0],xx[0][0][1],xx[0][1][0],xx[0][1][1]))
        ypos += 16
        hcheck_box = Tkinter.Checkbutton(self.response, text='MAIN GOAL', command=self.toggle_hyp, variable=var)
        info.hypothesisVars['.goal'] = var
        var.set(open)
        self.response.create_window(0,ypos, window=hcheck_box, anchor=Tkinter.NW)
        ypos += 24
        if open:
            hlabel = Tkinter.Text(self.response, width=200,height=len(g))
            self.response.create_window(0,ypos,window=hlabel, anchor=Tkinter.NW)
            hlabel.insert(Tkinter.INSERT, gg)
            p = self.get_keyword_placements(x[1])
            self.tagText(hlabel,p,diffs,None,None, False)
            hlabel.configure(state=Tkinter.DISABLED)
            ypos = ypos + 15*len(g)+50
        else:
            hlabel = Tkinter.Text(self.response,width=80,height=1)
            self.response.create_window(0,ypos,window=hlabel, anchor=Tkinter.NW)
            hlabel.insert(Tkinter.INSERT, g[0])
            p = self.get_keyword_placements1(x[1])
            self.tagText(hlabel,p,diffs,None,None,False)
            hlabel.configure(state=Tkinter.DISABLED)
            ypos = ypos + 24
        n = 1
        #print "Other goals"
        for og in cg.otherGoals:
            #print "Other goal"
            #print n
            #print ypos
            n = n+1
            x = og.getSegment(text)
            gg = x[0]
            g = gg.split("\n")
            var = Tkinter.IntVar()
            try:
                open = od['.goal'+str(n)]
            except KeyError:
                od['.goal'+str(n)] = 0
                open = 0
            ypos += 16
            hcheck_box = Tkinter.Checkbutton(self.response, text='GOAL '+str(n), command=self.toggle_hyp, variable=var)
            info.hypothesisVars['.goal'+str(n)] = var
            var.set(open)
            #print "Here"
            self.response.create_window(0,ypos, window=hcheck_box, anchor=Tkinter.NW)
            ypos += 24
            if open:
                hlabel = Tkinter.Text(self.response, width=200,height=len(g))
                self.response.create_window(0,ypos,window=hlabel, anchor=Tkinter.NW)
                hlabel.insert(Tkinter.INSERT, gg)
                p = self.get_keyword_placements(x[1])
                self.tagText(hlabel,p,[],None,None,False)
                hlabel.configure(state=Tkinter.DISABLED)
                ypos = ypos + 15*len(g)+50
            else:
                hlabel = Tkinter.Text(self.response,width=80,height=1)
                self.response.create_window(0,ypos,window=hlabel, anchor=Tkinter.NW)
                hlabel.insert(Tkinter.INSERT, g[0])
                p = self.get_keyword_placements(x[1])
                self.tagText(hlabel,p,[],None,None,False)
                hlabel.configure(state=Tkinter.DISABLED)
                ypos = ypos + 24
        #print ypos
        self.response.configure(scrollregion=(0,0,4000,ypos+100)) 
        self.response.update_idletasks()

        #print info.parent
        #print info.parent.result
        return False

    def selectTactic(self,tag):
        self.response.configure(scrollregion=(0,0,4000,200000)) 
        self.response.update_idletasks()
        self.savedTag = tag
        n = tag.widget.selection()[0]
        #print "SELECTING " + n
	#self.tactic.delete("1.0",Tkinter.END)
	current = self.proofMap[n]
        info = self.proofMap[n].getSegment(self.text[self.proofFile[n]])
        #self.tactic.insert(Tkinter.INSERT, info[0])
        self.tacticText = info[0]
        self.tacticNum = self.proofNum[n]
        self.response.delete(Tkinter.ALL)
        info = self.proofMap[n]
        self.info = info
        #self.response.insert(Tkinter.INSERT, info.result)
        try:
            (cg,tokens) = self.parseCache[info.result]
        except KeyError:
            try:
                t = CoqLex.tokenize(info.result)
                tokens = []
                for x in t:
                    tokens.append(x)
                #self.highlight_proof_keywords(tokens)
                cg = CoqParse.parseCoqGoal(tokens)
                self.parseCache[info.result] = (cg,tokens)
            except CoqParse.ParseError:
                pass
                #print "RESULT"
                #print info.result
                #print "DONE RESULT"
        cgp = None
        if info.parent != None:
            old_text = info.parent.result.split("\n")
            try:
                (cgp,tokens) = self.parseCache[info.parent.result]
            except KeyError:
                t = CoqLex.tokenize(info.parent.result)
                tokens = []
                for x in t:
                    tokens.append(x)
                #print "PARENT RESULT"
                #print info.parent.result
                #print "DONE RESULT"
                #self.highlight_proof_keywords(tokens)
                cgp = CoqParse.parseCoqGoal(tokens)
                self.parseCache[info.parent.result] = (cgp,tokens)
        #print "Here1"
        try:
            od = info.open_dict
        except AttributeError:
            od = {}
            info.open_dict = od
        #print cg
        text = info.result.split("\n")
        #for t in cg.hypotheses:
            #print "Hypothesis Name"
            #print t[0]
            #print "Hypothesis"
            #print t[1]
            #print "Hypotheses segment"
            #print t[1].getSegment(text)[0]
        #print "Goal"
        #print cg.goal
        #print "Goal segment"
        #print cg.goal.getSegment(text)[0]
        #print cg.subgoals
        #print cg.unfocused_subgoals
        if cg.unfocused_subgoals==0 or cg.unfocused_subgoals==None:
            if cg.subgoals==1:
                goal = "1 subgoal"
            elif cg.subgoals==0:
                goal = "No subgoals"
            else:
                goal = "%d subgoals"%cg.subgoals
        else:
            goal = "%d focused subgoals (unfocused: %d)"%(cg.subgoals,cg.unfocused_subgoals)
        goal_label = Tkinter.Label(self.response, text=goal, font=24, bg='white')
        self.response.create_window(0, 0, window=goal_label, anchor=Tkinter.NW) 
        ypos = 35
        #print "ypos"
        #print ypos
        if len(cg.hypotheses)>0:
            if len(cg.hypotheses)==1:
                t = 'Hypothesis'
            else:
                t = 'Hypotheses'
            hyp_label = Tkinter.Label(self.response, text=t, font=24, bg='white')
            self.response.create_window(0, ypos, window=hyp_label, anchor=Tkinter.NW) 
            #print "Self.topic_label size"
            ypos = ypos + 24
            #print "ypos"
            #print ypos
        info.hypothesisVars = {}
        n = 0
        for h in cg.hypotheses:
            ph = None
            if cgp != None:
                for x in cgp.hypotheses:
                    if x[0]==h[0]:
                        ph = x
            var = Tkinter.IntVar()
            hcheck_box = Tkinter.Checkbutton(self.response, text=h[0], command=self.toggle_hyp, variable=var)
            info.hypothesisVars[h[0]] = var
            self.response.create_window(0,ypos, window=hcheck_box, anchor=Tkinter.NW)
            try:
                open = od[h[0]]
            except KeyError:
                od[h[0]] = 0
                open = 0
            var.set(open)
            tokens = None
            if h[2]==None:
                x = h[1].getSegment(text)
                tt = x[0]
                tokens = x[1]
            else:
                tt = h[2].getSegment(text)[0]+" : " + h[1].getSegment(text)[0]
            t = tt.split("\n")
            diffs = []
            if tokens != None and ph != None:
                d = CoqParse.diffs(h[1],ph[1])
                for x in d:
                    if open or (x[0][0][0]<=1 and x[1][0][0]<=1):
                        diffs.append((x[0][0][0],x[0][0][1],x[0][1][0],x[0][1][1]))
            if open:
                hlabel = Tkinter.Text(self.response, width=80,height=len(t))
                self.response.create_window(100,ypos,window=hlabel, anchor=Tkinter.NW)
                hlabel.insert(Tkinter.INSERT, tt)
                if tokens != None:
                    p = self.get_keyword_placements(tokens)
                    self.tagText(hlabel,p,diffs,None,None,False)
                hlabel.configure(state=Tkinter.DISABLED)
                ypos = ypos + 24*len(t)
            else:
                hlabel = Tkinter.Text(self.response,width=80,height=1)
                self.response.create_window(100,ypos,window=hlabel, anchor=Tkinter.NW)
                hlabel.insert(Tkinter.INSERT, t[0])
                if tokens != None:
                    p = self.get_keyword_placements1(tokens)
                    self.tagText(hlabel,p,diffs,None,None,False)
                hlabel.configure(state=Tkinter.DISABLED)
                ypos = ypos + 24
            if ph==None:
                hcheck_box.configure(bg='yellow')
                tagn = "ptag"+str(n)
                self.code_tags.append(tagn)
                n = n+1
            #print "ypos"
            #print ypos
        deleted_hyps = []
        if cgp != None:
            for h in cgp.hypotheses:
                ph = None
                for x in cg.hypotheses:
                    if x[0]==h[0]:
                        ph = x
                if ph==None:
                    deleted_hyps.append(h)
        if len(deleted_hyps) > 0:
            ypos = ypos + 11
            if len(deleted_hyps)==1:
                t = 'Deleted hypothesis'
            else:
                t = 'Deleted hypotheses'
            hyp_label = Tkinter.Label(self.response, text=t, font=24, fg='#888')
            self.response.create_window(0, ypos, window=hyp_label, anchor=Tkinter.NW) 
            ypos = ypos + 24
            #print "ypos"
            #print ypos
            for h in deleted_hyps:
                var = Tkinter.IntVar()
                hcheck_box = Tkinter.Checkbutton(self.response, text=h[0], command=self.toggle_hyp, variable=var, fg='#888')
                info.hypothesisVars[h[0]] = var
                self.response.create_window(0,ypos, window=hcheck_box, anchor=Tkinter.NW)
                try:
                    open = od[h[0]]
                except KeyError:
                    od[h[0]] = 0
                    open = 0
                var.set(open)
                tokens = None
                if h[2]==None:
                    x = h[1].getSegment(old_text)
                    tt = x[0]
                    #tokens = x[1]
                else:
                    tt = h[2].getSegment(old_text)[0]+" : " + h[1].getSegment(old_text)[0]
                t = tt.split("\n")
                if open:
                    hlabel = Tkinter.Text(self.response, width=80,height=len(t),fg='#888')
                    if tokens != None:
                        p = self.get_keyword_placements(tokens)
                        self.tagText(hlabel,p,[],None,None,False)
                    self.response.create_window(100,ypos,window=hlabel, anchor=Tkinter.NW)
                    hlabel.insert(Tkinter.INSERT, tt)
                    hlabel.configure(state=Tkinter.DISABLED)
                    ypos = ypos + 24*len(t)
                else:
                    hlabel = Tkinter.Text(self.response,width=80,height=1,fg='#888')
                    if tokens != None:
                        p = self.get_keyword_placements1(tokens)
                        self.tagText(hlabel,p,[],None,None,False)
                    self.response.create_window(100,ypos,window=hlabel, anchor=Tkinter.NW)
                    hlabel.insert(Tkinter.INSERT, t[0])
                    hlabel.configure(state=Tkinter.DISABLED)
                    ypos = ypos + 24
                #print "ypos"
                #print ypos

        x = cg.goal.getSegment(text)
        gg = x[0]
        g = gg.split("\n")
        var = Tkinter.IntVar()
        try:
            open = od['.goal']
        except KeyError:
            od['.goal'] = 1
            open = 1
        diffs = []
        if cgp!=None:
            d = CoqParse.diffs(cg.goal,cgp.goal)
            for xx in d:
                if open or (xx[0][0][0]<=1 and xx[1][0][0]<=1):
                    diffs.append((xx[0][0][0],xx[0][0][1],xx[0][1][0],xx[0][1][1]))
        ypos += 16
        hcheck_box = Tkinter.Checkbutton(self.response, text='MAIN GOAL', command=self.toggle_hyp, variable=var)
        info.hypothesisVars['.goal'] = var
        var.set(open)
        self.response.create_window(0,ypos, window=hcheck_box, anchor=Tkinter.NW)
        ypos += 24
        if open:
            hlabel = Tkinter.Text(self.response, width=200,height=len(g))
            self.response.create_window(0,ypos,window=hlabel, anchor=Tkinter.NW)
            hlabel.insert(Tkinter.INSERT, gg)
            p = self.get_keyword_placements(x[1])
            self.tagText(hlabel,p,diffs,None,None,False)
            hlabel.configure(state=Tkinter.DISABLED)
            ypos = ypos + 15*len(g)+50
        else:
            hlabel = Tkinter.Text(self.response,width=80,height=1)
            self.response.create_window(0,ypos,window=hlabel, anchor=Tkinter.NW)
            hlabel.insert(Tkinter.INSERT, g[0])
            p = self.get_keyword_placements1(x[1])
            self.tagText(hlabel,p,diffs,None,None,False)
            hlabel.configure(state=Tkinter.DISABLED)
            ypos = ypos + 24
        n = 1
        #print "Other goals"
        for og in cg.otherGoals:
            #print "Other goal"
            #print n
            #print ypos
            n = n+1
            x = og.getSegment(text)
            gg = x[0]
            g = gg.split("\n")
            var = Tkinter.IntVar()
            try:
                open = od['.goal'+str(n)]
            except KeyError:
                od['.goal'+str(n)] = 0
                open = 0
            ypos += 16
            hcheck_box = Tkinter.Checkbutton(self.response, text='GOAL '+str(n), command=self.toggle_hyp, variable=var)
            info.hypothesisVars['.goal'+str(n)] = var
            var.set(open)
            #print "Here"
            self.response.create_window(0,ypos, window=hcheck_box, anchor=Tkinter.NW)
            ypos += 24
            if open:
                hlabel = Tkinter.Text(self.response, width=200,height=len(g))
                self.response.create_window(0,ypos,window=hlabel, anchor=Tkinter.NW)
                hlabel.insert(Tkinter.INSERT, gg)
                p = self.get_keyword_placements(x[1])
                self.tagText(hlabel,p,[],None,None,False)
                hlabel.configure(state=Tkinter.DISABLED)
                ypos = ypos + 15*len(g)+50
            else:
                hlabel = Tkinter.Text(self.response,width=80,height=1)
                self.response.create_window(0,ypos,window=hlabel, anchor=Tkinter.NW)
                hlabel.insert(Tkinter.INSERT, g[0])
                p = self.get_keyword_placements(x[1])
                self.tagText(hlabel,p,[],None,None,False)
                hlabel.configure(state=Tkinter.DISABLED)
                ypos = ypos + 24
        #print ypos
        self.response.configure(scrollregion=(0,0,4000,ypos+100)) 
        self.response.update_idletasks()

        #print info.parent
        #print info.parent.result

    def insertDeclaration(self,text):
        pos = -1
        f = self.currentDef.inFile
        for x in range(0,len(self.project.defs[f])):
            if self.project.defs[f][x]==self.currentDef:
                pos = x
        self.project.insertDeclaration(f, pos, text)
        self.text[f] = self.project.text[f].split("\n")
        self.update_tree(self.currentDef.insertParent,None,f,pos,1,self.project.defs[f])

    def insertDefinition(self):
        self.insertDeclaration('Definition x := 0.\n\n')

    def insertTheoremStep(self):
        pos = -1
        f = self.currentDef.inFile
        for x in range(0,len(self.project.defs[f])):
            if self.project.defs[f][x]==self.currentDef:
                pos = x
        p = self.currentDef.getProof()
        posb = -1
        for i in range(0,len(p)):
            if p[i]==self.info:
                posb = i
        #print "******* Here1"
        self.project.insertTactic(self.currentDef, posb, "admit.")
        #print "******* Here2"
        self.text[f] = self.project.text[f].split("\n")
        #print "******* Here3"
        self.selectTactic(self.savedTag)
        #print "******* Here4"

    def insertTheorem(self):
        self.insertDeclaration('Theorem x : 1=1.\nProof.\n    reflexivity.\nQed.\n\n')

    def insertFunction(self):
        self.insertDeclaration('Function x := 0.\n\n')

    def insertFixpoint(self):
        self.insertDeclaration('Fixpoint x := 0.\n\n')

    def insertTactic(self):
        self.insertDeclaration('Ltac x := simpl.\n\n')

    def colorReplay(self):
        self.highlight_keywords(self.toks,[],None)
        #print "********* COLOR *************"
        self.tree.tag_configure('yellowb', background = 'yellow')
        self.tree.tag_configure('yellow', foreground = 'darkgray')
        self.tree.tag_configure('red', foreground = 'red')
        self.tree.tag_configure('orange', foreground = 'orange')
        self.tree.tag_configure('green', foreground = 'orange')
        self.tree.tag_configure('gray', background = 'gray')
        self.tree.tag_configure('lightgray', background = 'lightgray')
        self.tree.tag_configure('blue', background = 'lightblue')
        name = self.search.get()
        for x in self.widgetMap:
            #print "testing "+str(x)
            try:
                try:
                    w = self.widgetMap[x]
                    #print w
                    highlight = False
                    if w==None:
                        try:
                            mode = self.project.managementState[self.widgetFile[x]]
                        except KeyError:
                            mode = 0
                        try:
                            replay = self.project.needsReplay[self.widgetFile[x]]
                        except KeyError:
                            replay = 0
                        if len(name)>0:
                            for d in self.project.defs[self.widgetFile[x]]:
                                for n in d.definedNames():
                                    if n==name:
                                        highlight = True
                    else:
                        try:
                            mode = w.managementState
                        except AttributeError:
                            mode = 0
                        try:
                            replay = w.needsReplay
                        except AttributeError:
                            replay = 0
                        if len(name)>0:
                            for n in w.definedNames():
                                if n==name:
                                    highlight = True
                    if highlight:
                        self.tree.item(x, tags=('yellowb'))
                    elif replay==4:
                        if mode==2:
                            self.tree.item(x, tags=('red','lightgray'))
                        elif mode==1:
                            self.tree.item(x, tags=('red','gray'))
                        elif mode==-1:
                            self.tree.item(x, tags=('red','blue'))
                        else:
                            self.tree.item(x, tags=('red'))
                    elif replay==3:
                        if mode==2:
                            self.tree.item(x, tags=('orange','lightgray'))
                        elif mode==1:
                            self.tree.item(x, tags=('orange','gray'))
                        elif mode==-1:
                            self.tree.item(x, tags=('orange','blue'))
                        else:
                            self.tree.item(x, tags=('orange',))
                    elif replay==2:
                        if mode==2:
                            self.tree.item(x, tags=('yellow','lightgray'))
                        elif mode==1:
                            self.tree.item(x, tags=('yellow','gray'))
                        elif mode==-1:
                            self.tree.item(x, tags=('yellow','blue'))
                        else:
                            self.tree.item(x, tags=('yellow',))
                    elif replay==1:
                        if mode==2:
                            self.tree.item(x, tags=('green','lightgray'))
                        elif mode==1:
                            self.tree.item(x, tags=('green','gray'))
                        elif mode==-1:
                            self.tree.item(x, tags=('green','blue'))
                        else:
                            self.tree.item(x, tags=('green',))
                    else:
                        if mode==2:
                            self.tree.item(x, tags=('lightgray'))
                        elif mode==1:
                            self.tree.item(x, tags=('gray'))
                        elif mode==-1:
                            self.tree.item(x, tags=('blue'))
                        else:
                            self.tree.item(x, tags=())
                except Tkinter.TclError:
                    pass
            except AttributeError:
                pass
        for x in self.proofMap:
            #print "testing "+str(x)
            try:
                try:
                    w = self.proofMap[x]
                    #print w
                    if w==None:
                        try:
                            mode = self.project.managementState[self.proofFile[x]]
                        except KeyError:
                            mode = 0
                        try:
                            replay = self.project.needsReplay[self.proofFile[x]]
                        except KeyError:
                            replay = 0
                    else:
                        try:
                            mode = w.managementState
                        except AttributeError:
                            mode = 0
                        try:
                            replay = w.needsReplay
                        except AttributeError:
                            replay = 0
                    if replay==4:
                        if mode==2:
                            self.tree.item(x, tags=('red','lightgray'))
                        elif mode==1:
                            self.tree.item(x, tags=('red','gray'))
                        elif mode==-1:
                            self.tree.item(x, tags=('red','blue'))
                        else:
                            self.tree.item(x, tags=('red'))
                    elif replay==3:
                        if mode==2:
                            self.tree.item(x, tags=('orange','lightgray'))
                        elif mode==1:
                            self.tree.item(x, tags=('orange','gray'))
                        elif mode==-1:
                            self.tree.item(x, tags=('orange','blue'))
                        else:
                            self.tree.item(x, tags=('orange',))
                    elif replay==2:
                        if mode==2:
                            self.tree.item(x, tags=('yellow','lightgray'))
                        elif mode==1:
                            self.tree.item(x, tags=('yellow','gray'))
                        elif mode==-1:
                            self.tree.item(x, tags=('yellow','blue'))
                        else:
                            self.tree.item(x, tags=('yellow',))
                    elif replay==1:
                        if mode==2:
                            self.tree.item(x, tags=('green','lightgray'))
                        elif mode==1:
                            self.tree.item(x, tags=('green','gray'))
                        elif mode==-1:
                            self.tree.item(x, tags=('green','blue'))
                        else:
                            self.tree.item(x, tags=('green',))
                    else:
                        if mode==2:
                            self.tree.item(x, tags=('lightgray'))
                        elif mode==1:
                            self.tree.item(x, tags=('gray'))
                        elif mode==-1:
                            self.tree.item(x, tags=('blue'))
                        else:
                            self.tree.item(x, tags=())
                except AttributeError:
                    pass
            except Tkinter.TclError:
                pass
        #print "********* DONE COLOR *************"
        self.tree.update_idletasks()
        #self.proof.update_idletasks()

    def acceptEdit(self):
        print "Accept edit"
        self.saveChanges()

    def selectLeft(self):
        print self.currentDefn
        print self.currentStepn
        defs = self.project.defs[self.displayedFile]
        if self.currentStepn==None or self.currentStepn==-1:
            if self.currentDefn > 0:
                self.currentDefn = self.currentDefn-1
                self.currentStepn = len(defs[self.currentDefn].getProof())-1
        else:
            self.currentStepn = self.currentStepn-1
        print self.currentDefn
        print self.currentStepn
        if (self.currentStepn < 0):
            self.currentStepn = None
        print "*** DONE ***"
        try:
            self.doSelecting(defs[self.currentDefn],self.currentStepn)
        except TypeError:
            self.showStatus("Select definition first.")

    def selectRight(self):
        print self.currentDefn
        print self.currentStepn
        defs = self.project.defs[self.displayedFile]
        if self.currentStepn==None and len(defs[self.currentDefn].getProof()) > 0:
            self.currentStepn = 0
        elif self.currentStepn != None and self.currentStepn < len(defs[self.currentDefn].getProof())-1:
            self.currentStepn = self.currentStepn+1
        elif self.currentDefn < len(defs)-1:
            self.currentDefn = self.currentDefn+1
        print self.currentDefn
        print self.currentStepn
        print "*** DONE ***"
        try:
            self.doSelecting(defs[self.currentDefn],self.currentStepn)
        except TypeError:
            self.showStatus("Select definition first.")

    def selectTreeItem(self):
        print self.code.yview()
        loc = self.code.index('insert').split(".")
        row = int(loc[0])
        col = int(loc[1])
        print "Loc "+str(row)+" "+str(col)
        self.saveChanges()
        def_to_select = None
        step_to_select = None
        for i in range(0,len(self.project.defs[self.displayedFile])):
            try:
                d = self.project.defs[self.displayedFile][i]
                print "CHECKING "+str(d.tokens[0])+" "+str(d.tokens[len(d.tokens)-1])
                if self.covers_definition(d, row, col, row, col):
                    def_to_select = d
                    print "HAVE DEF"
                    for i in range(0,len(d.getProof())):
                        if self.covers_step(d, i, row, col, row, col):
                            step_to_select = i
            except:
                print "Unexpected error:", sys.exc_info()[0]
        print "HERE1"
        print def_to_select
        print step_to_select
        print "HERE2"
        self.doSelecting(def_to_select,step_to_select)

    def doSelecting(self, def_to_select, step_to_select):
        tag = None
        for x in self.widgetMap:
            print x
            print self.widgetMap[x]
            if self.widgetMap[x]==def_to_select and def_to_select.insertItem==x:
                print "HAVE DEF"
                try:
                    if step_to_select==None:
                        print "HERE3 "+str(x)
                        self.tree.see(x)
                        self.tree.selection_set(x)
                        return
                except Tkinter.TclError:
                    pass
        if not(step_to_select==None) and step_to_select > -1:
            for x in self.proofMap:
                if self.proofMap[x]==def_to_select.getProof()[step_to_select] and def_to_select.getProof()[step_to_select].insertItem==x:
                    try:
                        self.tree.see(x)
                        self.tree.selection_set(x)
                        return
                    except Tkinter.TclError:
                        pass

    def moveDeclaration(self):
        print "moveDeclaration"
        print self.currentDefn
        print self.currentStepn
        print self.project.currentFileIndex
        print self.project.currentDefIndex
        print self.project.currentStepIndex
        self.saveChanges()
        print "Here "+str(self.savedTag)+" "+str(self.selectDefTag)
        print self.currentDefn
        print self.currentStepn
        if self.savedTag == None and self.selectDefTag != None:
            try:
                self.project.moveToPosition(self.displayedFileIndex,self.currentDefn,None)
            except TypeError:
                self.showStatus("Select definition first.")
            self.tree.delete(self.currentDef.insertItem)
            try:
                del self.widgetMap[self.currentDef.insertItem]
            except KeyError:
                pass
            try:
                del self.proofMap[self.currentDef.insertItem]
            except KeyError:
                pass
            try:
                del self.widgetFile[self.currentDef.insertItem]
            except KeyError:
                pass
            try:
                del self.proofFile[self.currentDef.insertItem]
            except KeyError:
                pass
            parent = self.project.defs[self.displayedFile][0].insertParent
            id = "i"+str(self.idn)
            print "id (c) = " + str(id)
            self.idn = self.idn + 1
            xx = self.tree.insert(parent,self.currentDefn,id,text=self.currentDef.header())
            self.currentDef.insertItem = xx
            self.widgetMap[xx] = self.currentDef
            self.widgetFile[xx] = self.displayedFile
            self.proofFile[xx] = self.displayedFile
            self.proofMap[xx] = self.currentDef
            print "Building proof tree 1"
            self.buildProofTree(xx,self.currentDef)
            #self.tree.see(self.selectDefTag)
            #self.tree.selection_set(self.selectDefTag)
            self.selectDef(id)
            self.colorReplay()
            self.tree.selection_set(id)
        elif self.savedTag != None:
            try:
                step = self.info
            except AttributeError:
                step = -1
            df = step
            print "Moving through parents"
            print df
            print df.insertItem
            while (df.parent != None):
                df = df.parent
                print df.insertItem
                print df
            print "*** DONE ***"
            n = -1
            for x in range(0,len(self.project.defs[self.displayedFile])):
                if df==self.project.defs[self.displayedFile][x]:
                    n = x
            print "Attributes"
            attr = self.tree.item(df.insertItem)
            print attr
            if self.currentStepn==None:
                print "!!!!!!! Moving marker + "+str(self.displayedFile)+" "+str(n)+" None"
                self.project.moveToPosition(self.displayedFileIndex,n,-1)
            else:
                print "!!!!!!! Moving marker + "+str(self.displayedFile)+" "+str(n)+" "+str(self.currentStepn+1)
                self.project.moveToPosition(self.displayedFileIndex,n,self.currentStepn)
            self.tree.delete(df.insertItem)
            try:
                del self.widgetMap[df.insertItem]
            except KeyError:
                pass
            try:
                del self.proofMap[df.insertItem]
            except KeyError:
                pass
            try:
                del self.widgetFile[df.insertItem]
            except KeyError:
                pass
            try:
                del self.proofFile[df.insertItem]
            except KeyError:
                pass
            parent = self.project.defs[self.displayedFile][0].insertParent
            id = "i"+str(self.idn)
            print "id (d) = " + str(id)
            self.idn = self.idn + 1
            if self.currentDefn==None:
                defs = self.project.defs[self.displayedFile]
                for i in range(0,len(defs)):
                    if defs[i]==df:
                        self.currentDefn = i
            #xx = self.tree.insert(parent,self.currentDefn,self.displayedFile+"."+df.header(),text=df.header())
            print self.currentDefn
            print df.header()
            xx = self.tree.insert(parent,self.currentDefn,id,text=df.header())
            df.insertItem = xx
            self.proofMap[xx] = df
            self.proofFile[xx] = self.displayedFile
            self.widgetMap[xx] = df
            self.widgetFile[xx] = self.displayedFile
            print "Info"
            print "xx = "+str(xx)
            print self.proofMap[xx]
            print "Building proof tree 2"
            self.buildProofTree(df.insertItem,df)
            self.colorReplay()
            self.tree.see(step.insertItem)
            self.tree.selection_set(step.insertItem)

    def buildProofTree(self,rt,df):
        print "*** buildProofTree ***"
        print rt
        print df
        pl = df.getProof()
        if len(pl)>0:
            goals = 1
	    ugoals = 0
	    r = rt
            self.proofMap[r] = self.widgetMap[r]
            self.proofNum[r] = -1
            self.proofMap[r].parent = None
            self.proofFile[r] = self.widgetFile[r]
            rl = [r]
            gl = [0]
            gp = [0]
            fl = []
            parent = self.proofMap[r]
            print "ROOT PARENT "+str(parent.insertItem)
            print parent
            backFill = None
            count = -1
            for x in pl:
                count = count+1
                if backFill != None:
                    self.proofMap[backFill] = x
                    self.proofFile[backFill] = self.widgetFile[r]
                    backFill = None
                print "Adding "+x.__coqstr__()
                print "goals "+str(goals)
		print "subgoals "+str(x.subgoals)
                print "UGOALS"
		print "ugoals "+str(ugoals)
		print "nugoals "+str(x.unfocused)
                print "fl" + str(fl)
                print "gl" + str(gl)
                print "gp" + str(gp)
                nn = self.tree.insert(r,'end',text=x.__coqstr__())
                x.insertItem = nn
                self.proofMap[nn] = x
                self.proofFile[nn] = self.widgetFile[rt]
                self.proofNum[nn] = count
                x.parent = parent
                print "Parent of "+str(x.insertItem)+" is "+str(x.parent.insertItem)
                ngoals = x.subgoals
                nugoals = x.unfocused
                print "Goals "+str(ngoals)+" "+str(nugoals)
                if ngoals==0 and nugoals==0:
                    print "*** Output ***"
                    print x.result
                    print "*** Done Output ***"
                parent = x
                print "Needs replay "+str(x.needsReplay)
                if x.needsReplay<2:
                    print "Here1"
                    if nugoals < ugoals:
                        print len(fl)
                        xx = fl[len(fl)-1]
                        fl = fl[0:len(fl)-1]
                        #print "Removing focus"
                        r = rl[xx-1]
                        parent = self.proofMap[r]
                        rl = rl[0:xx]
                        gl = gl[0:xx]
                        gp = gp[0:xx]
                    elif ngoals > goals:
                        rl.append(nn)
                        gl.append(ngoals-goals+1)
                        gp.append(1)
                        parent = x
                        r = nn
                    elif nugoals > ugoals:
                        fl.append(len(rl))
                        rl.append(nn)
                        gl.append(1)
                        gp.append(1)
                        r = nn
                        parent = x
                    elif ngoals < goals and len(rl)>1:
                        xx = len(rl)-1
                        r = rl[xx]
                        sgc = gl[xx]
                        sgn = gp[xx]
                        while sgn==sgc and len(rl)>1:
                            rl = rl[0:xx]
                            gl = gl[0:xx]
                            gp = gp[0:xx] 
                            xx = xx-1
                            r = rl[xx]
                            sgc = gl[xx]
                            sgn = gp[xx]
                        if sgn<sgc:
                            r = self.tree.insert(rl[xx-1],'end',text='SUBGOAL '+str(sgn+1))
                            self.proofMap[r] = x
                            self.proofFile[r] = self.widgetFile[rt]
                            self.proofNum[r] = count
                            rl[xx] = r
                            gp[xx] = sgn+1
                goals = ngoals
                ugoals = nugoals

    def deleteItem(self):
	self.code.delete("1.0",Tkinter.END)
        self.saveChanges()

    def selectDef(self,tag):
        loc = self.code.index('insert').split(".")
        row = int(loc[0])
        col = int(loc[1])
        self.showStatus("Ready row:"+str(row)+" col:"+str(col))
        print "selectDef"
        self.response.delete(Tkinter.ALL)
        self.selectDefTag = tag
        self.savedTag = None
        self.saveChanges()
        new_text = self.code.get("1.0",Tkinter.END)
        self.text[self.displayedFile] = new_text.split("\n")
        self.highlightMap[self.displayedFile] = (self.errorLine,self.errorCol,self.firstLine,self.firstCol,self.lastLine,self.lastCol,self.originalLastLine,self.originalLastCol,self.firstChangedDef,self.lastChangedDef,self.firstChangedStep,self.lastChangedStep)
        self.originalText = None
        self.currentDef = None
        self.currentDefn = None
        self.currentStepn = None
        global current
        global reference
        try:
            if len(tag.widget.selection())<1:
                return
            n = tag.widget.selection()[0]
        except AttributeError:
            n = tag
        print "***** HERE 1 ******"
        print "Selecting "+str(n)
        print self.tree.item(n)
        p = self.tree.parent(n)
        print p
        print len(p)
        doColor = False
        if len(p)==0:
            try:
                self.showStatus("Loading meta-data")
                self.project.populateFile(self.widgetFile[n])
                print "***** HERE 1a ******"
                r = self.project.instantiateCoqFile(self.widgetFile[n])
                print "***** HERE 1b ******"
                for q in self.widgetMap:
                    try:
                        nd = self.project.instantiations[self.widgetMap[q]]
                        self.widgetMap[q] = nd
                        print "Build proof tree 3"
                        self.buildProofTree(q,nd)
                        print "***** HERE 1c ******"
                    except KeyError:
                        pass
                        # for i in range(0,len(r[0])):
                            #if self.widgetMap[q]==r[0][i]:
                                #self.widgetMap[q] = r[1][i]
                self.showStatus("Ready")
                doColor = True
            except KeyError:
                self.showStatus("Ready")
                pass
        print "***** HERE 2 ******"
        try:
            f = self.widgetFile[n]
            try:
                zzz = self.text[f]
            except KeyError:
                self.text[f] = self.project.text[f].split("\n")
            if self.widgetMap[n] == None:
                info = None
            else:
                info = self.widgetMap[n].getSegment(self.text[f])
                #print "Proof size "+str(len(self.widgetMap[n].getProof()))
            #print "Here1"
        except KeyError:
            try:
                f = self.widgetFile[n]
                self.text[f] = self.project.text[f].split("\n")
                info = self.widgetMap[n].getSegment(self.text[self.widgetFile[n]])
                #print "Here2"
            except KeyError:
                #print "Here3"
                pass
        print "***** HERE 3 ******"
        haveProof = False
        try:
            zzz = self.proofMap[n]
            haveProof = True
            print "Here 3b"
            zz = self.widgetMap[n]
            attr = self.tree.item(n)
            print "Here 3c"
            if attr['open']==0:
                print "Here 3d"
                haveProof = False
        except KeyError:
            pass
        print "***** HERE 4 ******"
        try:
            f = self.widgetFile[n]
        except KeyError:
            f = self.proofFile[n]
        try:
            current = self.widgetMap[n]
            for dd in range(0,len(self.project.defs[f])):
                d = self.project.defs[f][dd]
                if d.insertItem==n:
                    self.currentDefn = dd
                    self.currentStepn = None
        except KeyError:
            f = self.proofFile[n]
            current = self.proofMap[n]
            info = self.proofMap[n].getSegment(self.text[f])
        print "***** HERE 4.5 ******"
        if haveProof:
            print "PROVING"
            self.showStatus("Parsing goal info")
            if self.selectProofNode(n):
	        c = self.proofMap[n]
                try:
                    self.insertResponseText(c.result)
                except AttributeError:
                    pass
            for dd in range(0,len(self.project.defs[f])):
                d = self.project.defs[f][dd]
                for pp in range(0,len(d.getProof())):
                    if d.getProof()[pp].insertItem==n:
                        self.currentDefn = dd
                        self.currentStepn = pp
            self.showStatus("Ready")
        else:
            try:
                print current
                if len(current.getProof())>0:
                    self.insertResponseText(current.qed)
                else:
                    self.insertResponseText(current.result)
            except AttributeError:
                pass
        print "***** HERE 5 ******"
        #print f
        #print self.displayedFile
	if f != self.displayedFile:
            self.code.delete("1.0",Tkinter.END)
            print f
            try:
                print "Here1"
                self.code.insert(Tkinter.INSERT, "\n".join(self.text[f]))
            except KeyError:
                print "Here2"
                self.project.populateFile(f)
                r = self.project.instantiateCoqFile(f)
                self.text[f] = self.project.text[f].split("\n")
                for q in self.widgetMap:
                    try:
                        nd = self.project.instantiations[self.widgetMap[q]]
                        self.widgetMap[q] = nd
                        print "Build proof tree 3"
                        self.buildProofTree(q,nd)
                        print "***** HERE 1c ******"
                    except KeyError:
                        pass
                        # for i in range(0,len(r[0])):
                            #if self.widgetMap[q]==r[0][i]:
                                #self.widgetMap[q] = r[1][i]
                self.code.insert(Tkinter.INSERT, "\n".join(self.text[f]))
            print n
            print self.widgetMap[n]
            if self.widgetMap[n] == None:
                info = None
            else:
                info = self.widgetMap[n].getSegment(self.text[f])
            self.lastKeypressText = self.code.get("1.0",Tkinter.END)
            for x in range(0,len(self.project.files)):
                if self.project.files[x]==f:
                    self.displayedFileIndex = x
            self.displayedFile = f
            try:
                (self.errorLine,self.errorCol,self.firstLine,self.firstCol,self.lastLine,self.lastCol,self.originalLastLine,self.originalLastCol,self.firstChangedDef,self.lastChangedDef,self.firstChangedStep,self.lastChangedStep) = self.highlightMap[self.displayedFile]
            except KeyError:
                self.errorLine = None
                self.errorCol = None
                self.firstLine = None
                self.firstCol = None
                self.lastLine = None
                self.lastCol = None
                self.originalLastLine = None
                self.originalLastCol = None
                self.firstChangedDef = None
                self.lastChangedDef = None
                self.firstChangedStep = None
                self.lastChangedStep = None
        
        print "***** HERE 6 ******"
        if info != None:
            self.originalText = info[0]
            self.tacticText = None
            self.currentDef = current
            start = current.tokens[0].line - 30.0
            if start < 0:
                start = 0.0
            self.code.yview_moveto(start / (len(self.text[f])+0.0))
        print "***** HERE 7 ******"
        diffs = []
        if reference != None:
            #print "Reference"
            #print current
            #print reference
            #print current.getListRepr()
            #print reference.getListRepr()
            d = CoqParse.diffs(current,reference)
            #print d
            for x in d:
                diffs.append((x[0][0][0],x[0][0][1],x[0][1][0],x[0][1][1]))
        print "***** HERE 8 ******"
        toks = []
        for x in self.project.defs[f]:
            toks = toks+x.tokens
        self.toks = toks
        self.highlight_keywords(toks,diffs,current)
        #for x in self.proof.get_children():
            #self.proof.delete(x)
        #pl = self.widgetMap[n].getProof()
        print "***** HERE 9 ******"
        try:
            print self.doMoveDeclaration
            if self.doMoveDeclaration:
                self.doMoveDeclaration = False
                print "Moving declaration"
                self.moveDeclaration()
            self.doMoveDeclaration = False
        except AttributeError:
            pass
        print "***** HERE 10 ******"
        if doColor:
            self.colorReplay()
        loc = self.code.index('insert').split(".")
        row = int(loc[0])
        col = int(loc[1])
        self.showStatus("Ready row:"+str(row)+" col:"+str(col))

    def deleteItem(self):
	self.code.delete("1.0",Tkinter.END)
        self.saveChanges()

    def updateValue(self, old_line, old_col, new_line, new_col, line, col):
        if line < old_line:
            return (line,col)
        line = line + new_line - old_line
        if line==new_line:
            if col >= old_col:
                col = col + new_col - old_col
        return (line,col)

    def update_keywords(self, keywords):
        if self.firstLine==None:
            return keywords
        res = []
        for k in keywords:
            x = self.updateValue(self.originalLastLine, self.originalLastCol, self.lastLine,self.lastCol,k[0],k[1])
            y = self.updateValue(self.originalLastLine, self.originalLastCol, self.lastLine,self.lastCol,k[2],k[3])
            res.append((x[0],x[1],y[0],y[1]))
        return res

    def saveChanges(self):
        print "Saving changes"
        if not(self.firstLine==None):
            new_text = self.code.get("1.0",Tkinter.END)
            items_to_delete = []
            if self.firstChangedDef != None:
                for i in range(self.firstChangedDef, self.lastChangedDef+1):
                    d = self.project.defs[self.displayedFile][i]
                    items_to_delete.append(d.insertItem)
                    #print "Deleting "+str(i)+" "+str(d.insertItem)
                    #self.tree.delete(d.insertItem)
            l = len(self.project.defs[self.displayedFile])
            parent = self.project.defs[self.displayedFile][0].insertParent
            print "DEFS"
            print self.firstChangedDef
            print self.lastChangedDef
            print self.firstChangedStep
            print self.lastChangedStep
            r = self.project.updateFileText(self.displayedFile, self.firstChangedDef, self.lastChangedDef, self.firstChangedStep, self.lastChangedStep, self.firstLine, self.firstCol, self.originalLastLine, self.originalLastCol, self.lastLine, self.lastCol, new_text)
            if r != None:
                self.errorLine = r[0]
                self.errorCol = r[1]
                #self.code.insert(str(r[0])+"."+str(r[1]),"<ERROR>")
                tagn = "tag"+str(self.tag)
                self.tag = self.tag+1
                self.code.tag_add(tagn,str(self.errorLine)+"."+str(self.errorCol),str(self.lastLine)+"."+str(self.lastCol))
                self.code.tag_config(tagn, foreground="black", background="red")
                self.code_tags.append(tagn)
                self.showStatus("Parsing error, please correct.")
                return
            for x in items_to_delete:
                self.tree.delete(x)
                try:
                    del self.widgetMap[x]
                except KeyError:
                    pass
                try:
                    del self.proofMap[x]
                except KeyError:
                    pass
                try:
                    del self.widgetFile[x]
                except KeyError:
                    pass
                try:
                    del self.proofFile[x]
                except KeyError:
                    pass
            f = self.firstChangedDef
            print "FIRST CHANGED "+str(f)
            incr = 1
            if f==None:
                incr = 1
                f = self.lastChangedDef+1
            for x in range(f,self.lastChangedDef+incr+len(self.project.defs[self.displayedFile])-l):
                d = self.project.defs[self.displayedFile][x]
                print "PROCESSING "+str(x)+" "+str(d)
                id = "i"+str(self.idn)
                print "id (a) = " + str(id)
                self.idn = self.idn + 1
                #xx = self.tree.insert(parent,x,self.displayedFile+"."+d.header(),text=d.header())
                xx = self.tree.insert(parent,x,id,text=d.header())
                d.insertItem = xx
                d.inFile = self.displayedFile
                d.insertParent = parent
                self.widgetFile[xx] = self.displayedFile
                self.widgetMap[xx] = d
                print "Build proof tree 4"
                self.buildProofTree(xx,d)
            self.text[self.displayedFile] = new_text.split("\n")
            toks = []
            for x in self.project.defs[self.displayedFile]:
                toks = toks+x.tokens
            self.toks = toks
            #print "Doing highlighting"
            self.highlight_keywords(toks,[],None)
            self.errorLine = None
            self.errorCol = None
            self.firstLine = None
            self.firstCol = None
            self.lastLine = None
            self.lastCol = None
            self.originalLastLine = None
            self.originalLastCol = None
            self.firstChangedDef = None
            self.lastChangedDef = None
            self.firstChangedStep = None
            self.lastChangedStep = None
            self.colorReplay()
            #print str(self.currentDefn)+" "+str(self.currentStepn)
            if self.currentDefn != None:
                if len(self.project.defs[self.displayedFile])>self.currentDefn:
                    d = self.project.defs[self.displayedFile][self.currentDefn]
                    if self.currentStepn != None:
                        if self.currentStepn < len(d.getProof()):
                            s = d.getProof()[self.currentStepn]
                            self.tree.see(s.insertItem)
                            self.tree.selection_set(s.insertItem)
                    else:
                        self.tree.see(d.insertItem)
                        self.tree.selection_set(d.insertItem)
        return
        #print "********* SAVING CHANGES ************"
        new_text = self.code.get("1.0",Tkinter.END)
        #print new_text
        #print "*********"
        try:
            if self.originalText==None:
                return
            #print self.originalText
            #print "*********"
            if new_text!=self.originalText and new_text!=self.originalText+"\n":
                #print "Text has changed"
                #print len(new_text)
                #print len(self.originalText)
                #print new_text
                #print self.originalText
                #print "Here0"
                #print self.currentDef.inFile
                od = self.project.defs[self.currentDef.inFile]
                #print "here1"
                oc = len(self.project.defs[self.currentDef.inFile])
                #print "here2"
                self.project.replaceDeclaration(self.currentDef, new_text)
                #print "--------- DONE REPLACE -----------"
                self.text[self.currentDef.inFile] = self.project.text[self.currentDef.inFile].split("\n")
                #print "Here a"
                #print self.currentDef
                #print "Here aa"
                parent = self.currentDef.insertParent
                #print "Here b"
                new_defs = self.project.defs[self.currentDef.inFile]
                #print "Here c"
                pos = -1
                #print "Here1"
                for q in range(0,len(od)):
                    if od[q]==self.currentDef:
                        pos = q
                count = len(new_defs)-oc+1
                #print "Here2"
                #print pos
                #print count
                #print oc
                #print len(new_defs)
                self.update_tree(parent,self.currentDef.insertItem,self.currentDef.inFile,pos,count,new_defs)
                #print "Here3a"
                self.colorReplay()
                #print "Here3"
                #self.populate_tree()
                self.originalText = None
            elif self.tacticText!=None:
                new_text = self.tactic.get("1.0",Tkinter.END)
                if self.tacticText!=new_text and new_text!=self.tacticText+"\n":
                    self.project.replaceTactic(self.currentDef, self.tacticNum, new_text)
                    self.text[self.currentDef.inFile] = self.project.text[self.currentDef.inFile].split("\n")
	            self.original_text = None
                    self.tacticText = None
                    self.selectDef(self.selectDefTag)

        except AttributeError:
            print "No previous definition"

    def in_definition(self, d, line, col):
        st_line = d.tokens[0].line
        st_col = d.tokens[0].column
        l = len(d.tokens)-1
        en_line = d.tokens[l].line
        en_col = d.tokens[l].column+len(d.tokens[l].value)
        if line < st_line:
            return False
        if line == st_line and col < st_col:
            return False
        if line > en_line:
            return False
        if line == en_line and col > en_col:
            return False
        return True

    def covers_definition(self, d, sline, scol, eline, ecol):
        st_line = d.tokens[0].line
        st_col = d.tokens[0].column
        l = len(d.tokens)-1
        en_line = d.tokens[l].line
        en_col = d.tokens[l].column+len(d.tokens[l].value)
        #print "    covers_definition "+str(sline)+" "+str(scol)+" "+str(eline)+" "+str(ecol)+" "+str(st_line)+" "+str(st_col)+" "+str(en_line)+" "+str(en_col)
        if eline < st_line:
            return False
        if eline == st_line and ecol < st_col:
            return False
        if sline > en_line:
            return False
        if sline == en_line and scol > en_col:
            return False
        #print "    YES"
        return True

    def after_definition(self, d, line, col):
        l = len(d.tokens)-1
        eline = d.tokens[l].line
        ecol = d.tokens[l].column+len(d.tokens[l].value)
        #print "    covers_definition "+str(sline)+" "+str(scol)+" "+str(eline)+" "+str(ecol)+" "+str(st_line)+" "+str(st_col)+" "+str(en_line)+" "+str(en_col)
        if line < eline:
            return False
        if line == eline and col < ecol:
            return False
        #print "    YES"
        return True

    def covers_step(self, d, i, sline, scol, eline, ecol):
        if len(d.getProof())==0:
            return False
        p = d.getProof()[i]
        if i==0:
            st_line = p.tokens[0].line
            st_col = p.tokens[0].column
        else:
            p1 = d.getProof()[i-1]
            l = len(p1.tokens)-1
            st_line = p1.tokens[l].line
            st_col = p1.tokens[l].column+len(p1.tokens[l].value)
        l = len(p.tokens)-1
        en_line = p.tokens[l].line
        en_col = p.tokens[l].column+len(p.tokens[l].value)-1
        #print "    covers_step "+str(sline)+" "+str(scol)+" "+str(eline)+" "+str(ecol)+" "+str(st_line)+" "+str(st_col)+" "+str(en_line)+" "+str(en_col)
        if eline < st_line:
            return False
        if eline == st_line and ecol < st_col:
            return False
        if sline > en_line:
            return False
        if sline == en_line and scol > en_col:
            return False
        #print "    YES"
        return True

    def before_step(self, d, i, line, col):
        if len(d.getProof())==0:
            return False
        p = d.getProof()[i]
        if i==0:
            st_line = p.tokens[0].line
            st_col = p.tokens[0].column
        else:
            p1 = d.getProof()[i-1]
            l = len(p1.tokens)-1
            st_line = p1.tokens[l].line
            st_col = p1.tokens[l].column+len(p1.tokens[l].value)-1
        l = len(p.tokens)-1
        if line > st_line:
            return False
        if line == st_line and col > st_col:
            return False
        #print "    YES"
        return True

    def after_step(self, d, i, line, col):
        if len(d.getProof())==0:
            return False
        p = d.getProof()[i]
        l = len(p.tokens)-1
        en_line = p.tokens[l].line
        en_col = p.tokens[l].column+len(p.tokens[l].value)
	if eline > line:
	    return False
        if eline == line and ecol > col:
            return False
        #print "    YES"
        return True

    def covers_postfix(self, d, sline, scol, eline, ecol):
        if len(d.getProof())==0:
            return False
        p = d.getProof()[len(d.getProof())-1]
        l = len(p.tokens)-1
        st_line = p.tokens[l].line
        st_col = p.tokens[l].column
        l = len(d.tokens)-1
        en_line = d.tokens[l].line
        en_col = d.tokens[l].column+len(d.tokens[l].value)
        if eline < st_line:
            return False
        if eline == st_line and ecol <= st_col:
            return False
        if sline > en_line:
            return False
        if sline == en_line and scol > en_col:
            return False
        #print "    YES"
        return True

    def before_postfix(self, d, line, col):
        if len(d.getProof())==0:
            return False
        p = d.getProof()[len(d.getProof())-1]
        l = len(p.tokens)-1
        st_line = p.tokens[l].line
        st_col = p.tokens[l].column
        if line > st_line:
            return False
        if line == st_line and col >= st_col:
            return False
        #print "    YES"
        return True

    def covers_prefix(self, d, sline, scol, eline, ecol):
        if len(d.getProof())==0:
            return False
        p = d.getProof()[0]
        en_line = p.tokens[0].line
        en_col = p.tokens[0].column
        st_line = d.tokens[0].line
        st_col = d.tokens[0].column
        #print "    covers_prefix "+str(sline)+" "+str(scol)+" "+str(eline)+" "+str(ecol)+" "+str(st_line)+" "+str(st_col)+" "+str(en_line)+" "+str(en_col)
        if eline < st_line:
            return False
        if eline == st_line and ecol < st_col:
            return False
        if sline > en_line:
            return False
        if sline == en_line and scol >= en_col:
            return False
        #print "    YES"
        return True

    def before_position(self, line1, col1, line2, col2):
        if line1 < line2:
            return True
        if line1 > line2:
            return False
        return col1 < col2

    def expandDefRange(self, start_line, start_col, end_line, end_col):
        print "expandDefRange "+str(start_line)+" "+str(start_col)+" "+str(end_line)+" "+str(end_col)
        scol = None
        sline = None
        ecol = None
        eline = None
        for i in range(0,len(self.project.defs[self.displayedFile])):
            #print "    Testing_er "+str(i)
            d = self.project.defs[self.displayedFile][i]
            if self.covers_definition(d, start_line, start_col, end_line, end_col):
                #print "Covers definition "+str(i)
                if self.firstChangedDef==None or i < self.firstChangedDef:
                    self.firstChangedDef = i
                if self.lastChangedDef==None or i > self.lastChangedDef:
                    self.lastChangedDef = i
        print "New range "+str(self.firstChangedDef)+" "+str(self.lastChangedDef)
        if self.firstChangedDef == None:
           for i in range(0,len(self.project.defs[self.displayedFile])):
               d = self.project.defs[self.displayedFile][i]
               if self.after_definition(d, start_line, start_col):
                   self.lastChangedDef = i
           if self.lastChangedDef==None:
               self.lastChangedDef = -1
               d = self.project.defs[self.displayedFile][0]
               sline = 1
               scol = 0
               eline = d.tokens[0].line
               ecol = d.tokens[0].column
           elif self.lastChangedDef < len(self.project.defs[self.displayedFile])-1:
               d = self.project.defs[self.displayedFile][self.lastChangedDef+1]
               eline = d.tokens[0].line
               ecol = d.tokens[0].column
               d = self.project.defs[self.displayedFile][self.lastChangedDef]
               t = d.tokens[len(d.tokens)-1]
               sline = t.line
               scol = t.column+len(t.value)
           else:
               d = self.project.defs[self.displayedFile][self.lastChangedDef]
               t = d.tokens[len(d.tokens)-1]
               sline = t.line
               scol = t.column+len(t.value)
               eline = end_line
               ecol = end_col
        else:
           sline = self.project.defs[self.displayedFile][self.firstChangedDef].tokens[0].line
           scol = self.project.defs[self.displayedFile][self.firstChangedDef].tokens[0].column
           tl = len(self.project.defs[self.displayedFile][self.lastChangedDef].tokens)-1
           eline = self.project.defs[self.displayedFile][self.lastChangedDef].tokens[tl].line
           ecol = self.project.defs[self.displayedFile][self.lastChangedDef].tokens[tl].column+len(self.project.defs[self.displayedFile][self.lastChangedDef].tokens[tl].value)
           if self.firstChangedDef==self.lastChangedDef:
               d = self.project.defs[self.displayedFile][self.firstChangedDef]
               for i in range(0,len(d.getProof())):
                   #print "    Testing step "+str(i)
                   if self.covers_step(d, i, start_line, start_col, end_line, end_col):
                       #print "    Covered"
                       if self.firstChangedStep==None or i < self.firstChangedStep:
                           self.firstChangedStep = i
                       self.lastChangedStep = i
                   if self.firstChangedStep==None:
                      if i > 0 and self.before_step(d, i, eline, ecol) and self.after_step(d,i-1, sline, scol):
                          self.lastChangedStep = i
               if len(d.getProof()) > 0 and self.before_postfix(d, eline, ecol) and self.after_step(d, len(d.getProof())-1, sline, scol):
                   self.lastChangedStep = len(d.getProof)
               if self.covers_prefix(d, start_line, start_col, end_line, end_col):
                   self.firstChangedStep = None
                   self.lastChangedStep = None
               if self.covers_postfix(d, start_line, start_col, end_line, end_col):
                   if len(d.getProof())>0:
                       self.firstChangedStep = len(d.getProof())-1
                       self.lastChangedStep = len(d.getProof())-1
                   else:
                       self.firstChangedStep = None
                       self.lastChangedStep = None
               if not(self.firstChangedStep==None):
                   sline = d.getProof()[self.firstChangedStep].tokens[0].line
                   scol = d.getProof()[self.firstChangedStep].tokens[0].column
                   tl = len(d.getProof()[self.lastChangedStep].tokens)-1
                   eline = d.getProof()[self.lastChangedStep].tokens[tl].line
                   ecol = d.getProof()[self.lastChangedStep].tokens[tl].column+len(d.getProof()[self.lastChangedStep].tokens[tl].value)
               elif not(self.lastChangedStep==None):
                   tl = len(d.getProof()[self.lastChangedStep-1].tokens)-1
                   sline = d.getProof()[self.lastChangedStep-1].tokens[tl].line
                   scol = d.getProof()[self.lastChangedStep-1].tokens[tl].column+len(d.getProof()[self.lastChangedStep-1].tokens[tl].value)
                   if self.lastChangedStep < len(d.getProof()):
                       eline = d.getProof()[self.lastChangedStep].tokens[0].line
                       ecol = d.getProof()[self.lastChangedStep].tokens[0].column
                   else:
                       sline = eline
                       scol = ecol
        print "expandDefRange "+str(self.firstChangedDef)+" "+str(self.lastChangedDef)+" "+str(self.firstChangedStep)+" "+str(self.lastChangedStep)
        print "    "+str(sline)+" "+str(scol)+" "+str(eline)+" "+str(ecol)
        return (sline,scol,eline,ecol)

    def searchChange(self, key):
        #print "search change"
        #print key
        #print self.search.get()
        self.colorReplay()

    def highlightSelection(self):
        try:
            self.code.tag_delete("select",Tkinter.SEL_FIRST,Tkinter.SEL_LAST)
            #tagn = "tag"+str(self.tag)
            #self.tag = self.tag+1
            self.code.tag_add("select",Tkinter.SEL_FIRST,Tkinter.SEL_LAST)
            self.code.tag_config("select", foreground="lightblue", background="black")
        except Tkinter.TclError:
            pass

    def codeSelect(self, key):
        self.highlightSelection()
        loc = self.code.index('insert').split(".")
        row = int(loc[0])
        col = int(loc[1])
        self.showStatus("Ready row:"+str(row)+" col:"+str(col))
        #self.code.tag_config('sel', foreground="black", background="blue")
        pass
        #print "codeSelect"
        #print key
        #print self.code.index('current')
        #print self.code.yview()

    def codeChange(self, key):
        self.highlightSelection()
        self.errorCol = None
        self.errorLine = None
        loc = self.code.index('insert').split(".")
        row = int(loc[0])
        col = int(loc[1])
        self.showStatus("Ready row:"+str(row)+" col:"+str(col))
        nt = self.code.get("1.0",Tkinter.END)
        if nt==self.lastKeypressText:
            return
        firstChange = 0
        start_line = 1
        start_col = 0
        while firstChange < len(nt) and firstChange < len(self.lastKeypressText) and nt[firstChange]==self.lastKeypressText[firstChange]:
            if nt[firstChange]=='\n':
                start_line = start_line + 1
                start_col = 0
            else:
                start_col = start_col + 1
            firstChange = firstChange+1
        last_change_old = len(self.lastKeypressText)-1
        last_change_new = len(nt)-1
        while self.lastKeypressText[last_change_old]==nt[last_change_new] and last_change_old >= firstChange and last_change_new >= firstChange:
            last_change_old = last_change_old - 1
            last_change_new = last_change_new - 1
        last_change_old = last_change_old+1
        last_change_new = last_change_new+1
        end_line_old = start_line
        end_col_old = start_col
	x = firstChange
        while x < last_change_old:
            if self.lastKeypressText[x]=='\n':
                end_line_old = end_line_old + 1
                end_col_old = 0
            else:
                end_col_old = end_col_old + 1
            x = x + 1
        end_line_new = start_line
        end_col_new = start_col
        x = firstChange
        while x < last_change_new:
            if nt[x]=='\n':
                end_line_new = end_line_new + 1
                end_col_new = 0
            else:
                end_col_new = end_col_new + 1
            x = x + 1
        UILogger.logKeyPress(self.displayedFile,self.project.text[self.displayedFile],self.lastKeypressText[firstChange:last_change_old],nt[firstChange:last_change_new],start_line,start_col,end_line_old,end_col_old,end_line_new,end_col_new)
        #print "Key pressed "+str(len(self.lastKeypressText))+" "+str(len(nt))+" "+str(firstChange) + " " + str(last_change_old)+" "+str(last_change_new)+" " + str(start_line) + " " + str(start_col)+" "+str(end_line_old)+" "+str(end_col_old)+" "+str(end_line_new)+" "+str(end_col_new)
        #print "****************************"
        #print self.lastKeypressText[firstChange:]
        #print "****************************"
        #print nt[firstChange:]
        #print "****************************"
        #print self.lastKeypressText[last_change_old:]
        #print "****************************"
        #print nt[last_change_new:]
        #print "****************************"
        self.lastKeypressText = nt
        #print key
        #print self.displayedFile
        #self.project.defs
        #self.text
        #self.project.text
        print self.firstLine
        print self.firstCol
        print self.lastLine
        print self.lastCol
        print self.originalLastLine
        print self.originalLastCol
        print self.firstChangedDef
        print self.lastChangedDef
        print self.firstChangedStep
        print self.lastChangedStep
        print "Change position"
        print start_line
        print start_col
        print end_line_old
        print end_col_old
        print end_line_new
        print end_col_new
        if self.firstLine==None:
            print "Here0"
            self.originalLastLine = end_line_old
            self.originalLastCol = end_col_old
            self.firstLine = start_line
            self.firstCol = start_col
            self.lastLine = end_line_new
            self.lastCol = end_col_new
            #print "Covers test"
            (sline,scol,eline,ecol) = self.expandDefRange(self.firstLine,self.firstCol,self.originalLastLine,self.originalLastCol)
            if sline != None:
               print "CASE 0"
               if self.before_position(sline,scol,self.firstLine, self.firstCol):
                   print "CASE 0A"
                   self.firstLine = sline
                   self.firstCol = scol
               if self.before_position(self.originalLastLine, self.originalLastCol,eline,ecol):
                   print "CASE 0B"
                   self.originalLastLine = eline
                   self.originalLastCol = ecol
                   (l,c) = self.updateValue(end_line_old, end_col_old, end_line_new, end_col_new, eline, ecol)
                   self.lastLine = l
                   self.lastCol = c
        else:
            if start_line > self.firstLine or (start_line==self.firstLine and start_col >= self.firstCol):
                if end_line_old < self.lastLine or (end_line_old==self.lastLine and end_col_old <= self.lastCol):
                    print "CASE 1"
                    (l,c) = self.updateValue(end_line_old, end_col_old, end_line_new, end_col_new, self.lastLine, self.lastCol)
                    self.lastLine = l
                    self.lastCol = c
                else:
                    print "CASE 2"
                    (l,c) = self.updateValue(self.lastLine, self.lastCol, self.originalLastLine, self.originalLastCol, end_line_old, end_col_old)
                    (sline,scol,eline,ecol) = self.expandDefRange(self.firstLine, self.firstCol, l, c)
                    if scol != None:
                        print "Here0"
                        if self.before_position(self.originalLastLine, self.originalLastCol, eline, ecol):
                            print "Here1"
                            (l,c) = self.updateValue(self.originalLastLine, self.originalLastCol, self.lastLine, self.lastCol, eline, ecol)
                            (l,c) = self.updateValue(end_line_old, end_col_old, end_line_new, end_col_new, l, c)
                            self.originalLastLine = eline
                            self.originalLastCol = ecol
                            self.lastLine = l
                            self.lastCol = c
                        if self.before_position(self.lastLine, self.lastCol, end_line_old, end_col_old):
                            print "Here2"
                            (l,c) = self.updateValue(self.originalLastLine, self.originalLastCol, self.lastLine, self.lastCol, end_line_old, end_col_old)
                            self.lastLine = end_line_new
                            self.lastCol = end_col_new
                            self.originalLastLine = l
                            self.originalLastCol = c
                        if self.before_position(sline,scol,self.firstLine,self.firstCol):
                            self.firstLine = sline
                            self.firstCol = scol
                    else:
                        print "Here3"
                        self.originalLastLine = l
                        self.originalLastCol = c
                        self.lastLine = end_line_new
                        self.lastCol = end_col_new
            else:
                if end_line_old < self.lastLine or (end_line_old==self.lastLine and end_col_old <= self.lastCol):
                    print "CASE 3"
                    (l,c) = self.updateValue(self.lastLine, self.lastCol, self.originalLastLine, self.originalLastCol, end_line_old, end_col_old)
                    (sline,scol,eline,ecol) = self.expandDefRange(start_line, start_col, l, c)
                    print "l, c"
                    print l
                    print c
                    print "Def range"
                    print sline
                    print scol
                    print eline
                    print ecol
                    self.firstLine = start_line
                    self.firstCol = start_col
                    if self.before_position(sline, scol, self.firstLine, self.firstCol):
                        print "Before stuff"
                        self.firstLine = sline
                        self.firstCol = scol
                    if self.firstChangedDef != None:
                        if self.before_position(self.originalLastLine, self.originalLastCol, eline, ecol):
                            print "Here1"
                            (l,c) = self.updateValue(self.originalLastLine, self.originalLastCol, self.lastLine, self.lastCol, eline, ecol)
                            (l,c) = self.updateValue(end_line_old, end_col_old, end_line_new, end_col_new, l, c)
                            self.originalLastLine = eline
                            self.originalLastCol = ecol
                            self.lastLine = l
                            self.lastCol = c
                        elif self.before_position(self.lastLine, self.lastCol, end_line_old, end_col_old):
                            print "Here2"
                            (l,c) = self.updateValue(self.originalLastLine, self.originalLastCol, self.lastLine, self.lastCol, end_line_old, end_col_old)
                            self.lastLine = end_line_new
                            self.lastCol = end_col_new
                            self.originalLastLine = l
                            self.originalLastCol = c
                        else:
                            if self.before_position(sline,scol,self.firstLine, self.firstCol):
                                print "Here3"
                                self.firstLine = sline
                                self.firstCol = scol
                            print "Default updating"
                            print end_line_old
                            print end_col_old
                            print end_line_new
                            print end_col_new
                            print self.lastLine
                            print self.lastCol
                            (self.lastLine,self.lastCol) = self.updateValue(end_line_old, end_col_old, end_line_new, end_col_new, self.lastLine, self.lastCol)
                else:
                    print "CASE 4"
                    (l,c) = self.updateValue(self.lastLine, self.lastCol, self.originalLastLine, self.originalLastCol, end_line_old, end_col_old)
                    (sline,scol,eline,ecol) = self.expandDefRange(start_line, start_col, l, c)
                    self.firstLine = start_line
                    self.firstCol = start_col
                    if self.firstChangedDef != None:
                        sline = self.firstChangedDef.tokens[0].line
                        scol = self.firstChangedDef.tokens[0].column
                        tl = len(self.lastChangedDef.tokens)-1
                        eline = self.lastChangedDef.tokens[tl].line
                        ecol = self.lastChangedDef.tokens[tl].column+len(self.lastChangedDef.tokens[tl].value)
                        if self.before_position(self.originalLastLine, self.originalLastCol, eline, ecol):
                            (l,c) = self.updateValue(self.originalLastLine, self.originalLastCol, self.lastLine, self.lastCol, eline, ecol)
                            (l,c) = self.updateValue(end_line_old, end_col_old, end_line_new, end_col_new, l, c)
                            self.originalLastLine = eline
                            self.originalLastCol = ecol
                            self.lastLine = l
                            self.lastCol = c
                        if self.before_position(self.lastLine, self.lastCol, end_line_old, end_col_old):
                            (l,c) = self.updateValue(self.originalLastLine, self.originalLastCol, self.lastLine, self.lastCol, end_line_old, end_col_old)
                            self.lastLine = end_line_new
                            self.lastCol = end_col_new
                            self.originalLastLine = l
                            self.originalLastCol = c
                        if self.before_position(sline,scol,self.firstLine, self.firstCol):
                            self.firstLine = sline
                            self.firstCol = scol
                    else:
                        self.originalLastLine = l
                        self.originalLastCol = c
                        self.lastLine = end_line_new
                        self.lastCol = end_col_new
        #print "Computing tokens"
        toks = []
        for x in self.project.defs[self.displayedFile]:
            toks = toks+x.tokens
        self.toks = toks
        #print "Doing highlighting"
        self.highlight_keywords(toks,[],None)
        print "Press Done"
        print "firstLine "+str(self.firstLine)
        print "firstCol "+str(self.firstCol)
        print "lastLine "+str(self.lastLine)
        print "lastCol "+str(self.lastCol)
        print "originalLastLine "+str(self.originalLastLine)
        print "originalLastCol "+str(self.originalLastCol)
        print "firstChangedDef "+str(self.firstChangedDef)
        print "lastChangedDef "+str(self.lastChangedDef)
        print "firstChangedStep "+str(self.firstChangedStep)
        print "lastChangedStep "+str(self.lastChangedStep)
        loc = self.code.index('insert').split(".")
        row = int(loc[0])
        col = int(loc[1])
        self.showStatus("Ready row:"+str(row)+" col:"+str(col))

    def updateKeywords(self):
        n = self.updateNumber
        def updateK():
            if n==self.updateNumber:
                self.highlight_keywords_new_position()
        return updateK

    def codevsbset(self, s, e):
        #print "Scroll " + str(s) + " " + str(e)
        self.needUpdate = True
        self.updateNumber = self.updateNumber+1
        self.root.after(300,self.updateKeywords())
        return self.vsb.set(s, e)

    def showStatus(self, s):
        self.status.configure(text=s)
        self.status.update_idletasks()

    def existentialInstantiations(self,text,exp1,exp2):
        #print exp1.__class__.__name__
        #print exp2.__class__.__name__
        if exp1.__class__.__name__=='CoqApplExpr' and exp2.__class__.__name__=='CoqApplExpr':
            return self.existentialInstantiations(text,exp1.fun,exp2.fun)+self.existentialInstantiations(text,exp1.param,exp2.param)
        elif exp1.__class__.__name__=='CoqForallExpr' and exp2.__class__.__name__=='CoqForallExpr':
            return self.existentialInstantiations(text,exp1.expr,exp2.expr)
        elif exp1.__class__.__name__=='CoqQuestionNameExpr':
            return [(exp1.name,exp2.getSegment(text))]
        else:
            return []

    def insertText(self, text, rows, cols, rowe, cole, insert):
        t = text.split("\n")
        print "*** INSERT ***"
        print insert
        print "*** TEXT ***"
        print text
        print "*** TEXT ***"
        print len(t)
        print rows
        print cols
        print rowe
        print cole
        nt = t[0:rows-1]+[t[rows-1][0:cols]]+insert[0].split("\n")+[t[rowe-1][cole:]]+t[rowe+1:]
        return "\n".join(nt)

    def replaceExistentials(self, text, startl, startc, g, m):
        if g.__class__.__name__=='CoqApplExpr':
            text = self.replaceExistentials(text,startl, startc, g.param, m)
            text = self.replaceExistentials(text,startl, startc, g.fun, m)
        elif g.__class__.__name__=='CoqQuestionNameExpr':
            for x in m:
                if x[0]==g.name:
                    line_s = g.tokens[0].line
                    col_s = g.tokens[0].column
                    line_e = g.tokens[len(g.tokens)-1].line
                    col_e = g.tokens[len(g.tokens)-1].column+len(g.tokens[len(g.tokens)-1].value)
                    line_s = line_s - startl+1
                    if line_s==1:
                        col_s = col_s - startc
                    line_e = line_e - startl+1
                    if line_e==1:
                        col_e = col_e - startc
                    text = self.insertText(text, line_s, col_s, line_e, col_e, x[1])
        return text

    def selectItem(self, defn, stepn):
        def_to_select = self.project.defs[self.displayedFile][defn]
        if stepn==None:
            step_to_select = None
        else:
            step_to_select = def_to_select.getProof()[stepn]
        for x in self.widgetMap:
            print x
            print self.widgetMap[x]
            if self.widgetMap[x]==def_to_select and def_to_select.insertItem==x:
                print "HAVE DEF"
                try:
                    if step_to_select==None:
                        print "HERE3 "+str(x)
                        self.tree.see(x)
                        self.tree.selection_set(x)
                        return
                except Tkinter.TclError:
                    pass
        if not(step_to_select==None):
            for x in self.proofMap:
                if self.proofMap[x]==def_to_select.getProof()[stepn] and x==def_to_select.getProof()[stepn].insertItem:
                    try:
                        self.tree.see(x)
                        self.tree.selection_set(x)
                        return
                    except Tkinter.TclError:
                        pass

    def moveLeft(self):
        print self.currentDefn
        print self.currentStepn
        if self.currentDefn==None:
            self.showStatus("Must select def or proof step first")
            return
        defs = self.project.defs[self.displayedFile]
        if self.currentStepn==None or self.currentStepn==-1:
            if self.currentDefn > 0:
                self.currentDefn = self.currentDefn-1
                self.currentStepn = len(defs[self.currentDefn].getProof())-1
        else:
            self.currentStepn = self.currentStepn-1
        print self.currentDefn
        print self.currentStepn
        if (self.currentStepn < 0):
            self.currentStepn = None
        print "*** DONE ***"
        self.doMoveDeclaration = True
        try:
            self.selectItem(self.currentDefn,self.currentStepn)
        except TypeError:
            self.doMoveDeclaration = False
            self.showStatus("Select definition first.")

    def moveRight(self):
        print self.currentDefn
        print self.currentStepn
        if self.currentDefn==None:
            self.showStatus("Must select def or proof step first")
            return
        defs = self.project.defs[self.displayedFile]
        if self.currentStepn==None and len(defs[self.currentDefn].getProof()) > 0:
            self.currentStepn = 0
        elif self.currentStepn != None and self.currentStepn < len(defs[self.currentDefn].getProof())-1:
            self.currentStepn = self.currentStepn+1
        elif self.currentDefn < len(defs)-1:
            self.currentDefn = self.currentDefn+1
            self.currentStepn = None
        print self.currentDefn
        print self.currentStepn
        print "*** DONE ***"
        self.doMoveDeclaration = True
        try:
            self.selectItem(self.currentDefn,self.currentStepn)
        except TypeError:
            self.doMoveDeclaration = False
            self.showStatus("Select definition first.")

    def moveCursor(self):
        pass

    def replaceStep(self, defn, stepn, text):
        def_to_select = self.project.defs[self.displayedFile][defn]
        step = def_to_select.getProof()[stepn]
        if step < len(def_to_select.getProof())-1:
            step1 = def_to_select.getProof()[stepn+1]
        else:
            step1 = None
        step1 = def_to_select.getProof()[stepn]
        startl = step.tokens[0].line
        startc = step.tokens[0].column
        endl = step.tokens[len(step.tokens)-1].line
        endc = step.tokens[len(step.tokens)-1].column+len(step.tokens[len(step.tokens)-1].value)
        self.code.delete(str(startl)+"."+str(startc),str(endl)+"."+str(endc))
        self.code.insert(str(startl)+"."+str(startc), text)
        self.codeChange("")
        self.acceptEdit()
        newStep = def_to_select.getProof()[stepn]
        newStep.result = step.result
        newStep.old_result = step.old_result
        if step1 != None:
            newStep1 = def_to_select.getProof()[stepn+1]
            newStep1.result = step1.result
            newStep1.old_result = step1.old_result

    def matchExpScore(self, e1, e2):
        if e1==None and e2==None:
            return 1
        if e1.__class__==CoqParse.CoqNameExpr and e2.__class__==CoqParse.CoqNameExpr:
            if e1.name==e2.name:
                return 1
            else:
                return 0
        if e1.__class__==CoqParse.CoqApplExpr and e2.__class__==CoqParse.CoqApplExpr:
            return self.matchExpScore(e1.fun,e2.fun)+self.matchExpScore(e1.param,e2.param)+1
        if e1.__class__==CoqParse.CoqForallExpr and e2.__class__==CoqParse.CoqForallExpr:
            return self.matchExpScore(e1.var,e2.var)+self.matchExpScore(e1.var_type,e2.var_type)+self.matchExpScore(e1.expr,e2.expr)
        if e1.__class__==CoqParse.CoqExistsExpr and e2.__class__==CoqParse.CoqExistsExpr:
            return self.matchExpScore(e1.var,e2.var)+self.matchExpScore(e1.vtype,e2.vtype)+self.matchExpScore(e1.exp,e2.exp)
        return 0

    def matchHypScore(self, h1, h2):
        if h1[2]==None and h2[2]==None:
            return 2+self.matchExpScore(h1[1],h2[1])
        elif h1[2] != None and h2[2] != None:
            return 2+self.matchExpScore(h1[1],h2[1])+self.matchExpScore(h1[2],h2[2])
        else:
            return 0
        return 0

    def updateTactic(self, tactic, oldGoal, newGoal):
        #print "Update Tactic"
        #print tactic
        l = tactic.getExpressions()
        #print l
        nl = []
        for x in l:
            #print "Processing step "+str(x)
            for h in oldGoal.hypotheses:
                #print "    Checking hyp "+str(h)
                #print "    "+str(x.__class__==CoqParse.CoqNameExpr)
                #print "    "+str(x.name)
                #print "    "+str(h[0])
                #print "    "+str(x.name==h[0])
                #print "    "+str(len(x.name))
                if x.__class__==CoqParse.CoqNameExpr and len(x.name)==1 and x.name[0]==h[0]:
                    #print "        GOT IT"
                    pos = -1
                    score = -1
                    for i in range(0,len(newGoal.hypotheses)):
                        sc = self.matchHypScore(h,newGoal.hypotheses[i])
                        #print "            Scoring "+str(h)+" "+str(newGoal.hypotheses[i])+" "+str(sc)
                        if sc>score:
                            score = sc
                            pos = i
                    nl.append(CoqParse.CoqNameExpr(x.tokens,[newGoal.hypotheses[pos][0]]))
        if len(nl) != len(l):
            return None
        #print nl
        #print pos
        #print "BEFORE update"
        #print tactic
        for x in range(0,len(nl)):
            if l[0] != nl[0]:
                return tactic.updateWithExpressions(nl)
        return tactic

    def replayStep(self):
        print "Replay step"
        print self.currentDef
        print self.displayedFile
        print self.currentDefn
        print self.currentStepn
        print self.project.currentFileIndex
        print self.project.files[self.project.currentFileIndex]
        print self.project.currentDefIndex
        print self.project.currentStepIndex
        if self.project.currentFileIndex > -1 and self.project.files[self.project.currentFileIndex]==self.displayedFile and self.currentDefn==self.project.currentDefIndex and self.project.currentStepIndex > -1 and self.currentStepn==self.project.currentStepIndex:
            print "Good replay"
            #self.doMoveDeclaration = True
            print self.currentDefn
            print self.currentStepn
            #self.selectItem(self.currentDefn,self.currentStepn+1)
            print "XXXXXXXX"
            print self.currentDefn
            print self.currentStepn
            tactic = self.project.defs[self.displayedFile][self.currentDefn].getProof()[self.currentStepn]
            nextTactic = self.project.defs[self.displayedFile][self.currentDefn].getProof()[self.currentStepn+1]
            print "JUST GOTTEN"
            print nextTactic
            g = self.getGoal(tactic)[0]
            og = self.getGoalOld(tactic)[0]
            r = self.updateTactic(nextTactic,og,g)
            print r
            if r==None:
                r = nextTactic
            if r!=nextTactic:
                self.replaceStep(self.currentDefn,self.currentStepn+1,r.__coqstr__()+".")
                self.acceptEdit()
            self.doMoveDeclaration = True
            self.selectItem(self.currentDefn,self.currentStepn+1)
            #print tactic 
            #print tactic.__coqstr__()
            #print r
            #print r.__coqstr__()

    def extractLemma(self):
        print self.code.index('current')
        print "extract lemma"
        self.saveChanges()
        print "Here "+str(self.savedTag)+" "+str(self.selectDefTag)
        if self.currentStepn != None and self.currentDefn != None:
           d = self.project.defs[self.displayedFile][self.currentDefn]
           p = d.getProof()[self.currentStepn]
           text = p.result.split("\n")
           goals = p.subgoals+p.unfocused
           x = self.currentStepn
           e = p
           print goals
           while x < len(d.getProof()) and goals <= e.subgoals + e.unfocused:
               x = x + 1
               if x < len(d.getProof()):
                   e = d.getProof()[x]
           print p
           print e
           (g1,_) = self.getGoal(p)
           (g2,_) = self.getGoal(e)
           print "GOAL 1"
           print g1.goal.__coqstr__()
           print "OTHER GOAL 1[0]"
           print g1.otherGoals[0].__coqstr__()
           print "GOAL 2"
           print g2.goal.__coqstr__()
           repl = self.existentialInstantiations(e.result.split("\n"),g1.otherGoals[0],g2.goal)
           if p==e:
               proof_text = "\n    admit."
           else:
               l = len(p.tokens)-1
               st_line = p.tokens[l].line
               st_col = p.tokens[l].column+len(p.tokens[l].value)
               l = len(e.tokens)-1
               en_line = e.tokens[l].line
               en_col = e.tokens[l].column+len(e.tokens[l].value)
               tl = self.text[self.displayedFile][st_line-1:en_line]
               tl[0] = tl[0][st_col:]
               if st_line==en_line:
                   tl[0] = tl[0][0:en_col-st_col]
               else:
                   tl[en_line-st_line] = tl[en_line-st_line][0:en_col]
               proof_text = "\n".join(tl)
           (cg,tokens) = self.parseCache[p.result]
           name = "newThm"
           appl = "apply "+name+"."
           vars = []
           hypBody = ""
           intro_h = ""
           intro_v = ""
           for x in cg.hypotheses:
               if (x[1].__class__==CoqParse.CoqNameExpr) or (x[1].__class__==CoqParse.CoqApplExpr and x[1].fun.__class__==CoqParse.CoqNameExpr and x[1].fun.name==['list']):
                   vars.append(x[0])
                   intro_v = intro_v+" "+str(x[0])
               else:
                   h = x[1].getSegment(text)
                   appl = appl + " apply "+x[0]+"."
                   hypBody = hypBody + h[0]+" -> "
                   intro_h = intro_h+" "+str(x[0])
           if (len(vars) > 0):
               fa = "forall"
               for v in vars:
                   fa = fa+" "+v
               fa = fa + ", "
           else:
               fa = ""
           hyp = "Theorem "+name+" : " + fa + hypBody
           appl = appl + "\n"
           g = cg.goal.getSegment(text)
           goal_line = cg.goal.tokens[0].line
           goal_col = cg.goal.tokens[0].column
           g = self.replaceExistentials(g[0], goal_line, goal_col, cg.goal, repl)
           intros = ""
           if len(intro_h)>0 or len(intro_v)>0:
               intros = "    intros"+intro_v+intro_h+".\n"
           hyp = hyp + g + ".\nProof.\n"+intros+proof_text+"\nQed."
           print "Theorem"
           print hyp
           print "Apply"
           print appl
           print "Def insert"
           print d.tokens[0].line
           print d.tokens[0].column
           print "Token insert"
           l = len(p.tokens)-1
           print p.tokens[l].line
           print p.tokens[l].column+len(p.tokens[l].value)
           if p != e:
               self.code.insert(str(en_line)+"."+str(en_col), "\n*)\n")
               self.code.insert(str(p.tokens[l].line)+"."+str(p.tokens[l].column+len(p.tokens[l].value)),"\n(*")
           self.code.insert(str(p.tokens[l].line)+"."+str(p.tokens[l].column+len(p.tokens[l].value)),"\n"+appl+"\n")
           self.code.insert(str(d.tokens[0].line)+"."+str(d.tokens[0].column),"\n"+hyp+"\n\n")
           self.codeChange("")

    def _setup_widgets(self):

        menubar = Tkinter.Menu(self.root)
        filemenu = Tkinter.Menu(menubar, tearoff=0)
        filemenu.add_command(label="New", command=donothing)
        filemenu.add_command(label="Open", command=donothing)
        filemenu.add_command(label="Save", command=donothing)
        filemenu.add_command(label="Save as...", command=donothing)
        filemenu.add_command(label="Close", command=donothing)

        filemenu.add_separator()

        filemenu.add_command(label="Exit", command=donothing)
        menubar.add_cascade(label="File", menu=filemenu)
        editmenu = Tkinter.Menu(menubar, tearoff=0)
        editmenu.add_command(label="Undo", command=donothing)

        editmenu.add_separator()

        editmenu.add_command(label="Cut", command=donothing)
        editmenu.add_command(label="Copy", command=donothing)
        editmenu.add_command(label="Paste", command=donothing)
        editmenu.add_command(label="Delete", command=self.deleteItem)
        editmenu.add_command(label="Select All", command=donothing)

        menubar.add_cascade(label="Edit", menu=editmenu)
        insertmenu = Tkinter.Menu(menubar, tearoff=0)

        insertmenu.add_command(label="Tactic", command=self.insertTactic)
        insertmenu.add_command(label="Notation", command=donothing)
        insertmenu.add_command(label="Tactic Notation", command=donothing)
        insertmenu.add_command(label="Fixpoint", command=self.insertFixpoint)
        insertmenu.add_command(label="Definition", command=self.insertDefinition)
        insertmenu.add_command(label="Function", command=self.insertFunction)
        insertmenu.add_command(label="Theorem", command=self.insertTheorem)
        insertmenu.add_command(label="Theorem Step", command=self.insertTheoremStep)
        insertmenu.add_command(label="Other", command=donothing)

        #menubar.add_cascade(label="Insert", menu=insertmenu)

        deletemenu = Tkinter.Menu(menubar, tearoff=0)

        deletemenu.add_command(label="Declaration", command=donothing)
        deletemenu.add_command(label="Tactic", command=donothing)

        #menubar.add_cascade(label="Delete", menu=deletemenu)
        coqmenu = Tkinter.Menu(menubar, tearoff=0)

        coqmenu.add_command(label="Move to selected declaration", command=self.moveDeclaration)
        coqmenu.add_command(label="Move to text cursor position", command=self.moveTextCursor)
        coqmenu.add_command(label="Full compile", command=donothing)

        menubar.add_cascade(label="Coq Control", menu=coqmenu)

        viewmenu = Tkinter.Menu(menubar, tearoff=0)

        viewmenu.add_command(label="Make reference", command=makeReference)
	viewmenu.add_command(label="Select Tree item", command=self.selectTreeItem)
	viewmenu.add_command(label="Parse Edit", command=self.acceptEdit)

        menubar.add_cascade(label="View", menu=viewmenu)

        macromenu = Tkinter.Menu(menubar, tearoff=0)
	macromenu.add_command(label="Extract lemma", command=self.extractLemma)
	macromenu.add_command(label="Replay step", command=self.replayStep)
        menubar.add_cascade(label="Macros", menu=macromenu)

        helpmenu = Tkinter.Menu(menubar, tearoff=0)
        helpmenu.add_command(label="Help Index", command=donothing)
        helpmenu.add_command(label="About...", command=donothing)
        menubar.add_cascade(label="Help", menu=helpmenu)

        self.root.config(menu=menubar)

        #menubar.pack(fill='both', expand=True, side="bottom")
        #menubar.pack(fill='x')

        pane1 = Tkinter.PanedWindow()
        pane1.pack(fill='both',expand=True,side="bottom")

        container = ttk.Frame()
        pane1.add(container, width=300)
        #container.pack(fill='both', expand=True, side="left")

        # XXX Sounds like a good support class would be one for constructing
        #     a treeview with scrollbars.
        self.tree = ttk.Treeview(selectmode="browse")
        vsb = ttk.Scrollbar(orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        self.tree.bind("<<TreeviewSelect>>",self.selectDef)
        self.tree.grid(column=0, row=2, sticky='nsew', in_=container)
        vsb.grid(column=1, row=2, sticky='ns', in_=container)
        hsb.grid(column=0, row=3, sticky='ew', in_=container)
        self.status = Tkinter.Label(container, text="Ready", justify="left")
        self.status.configure()
        self.status.grid(column=0,row=4,sticky='ew', in_=container)
        bcontainer = ttk.Frame()
        bcontainer.grid(column=0,row=0,sticky='ew',in_=container)
        l = Tkinter.Label(bcontainer, text="Coq")
        l.grid_configure(column=0,row=0,sticky='ew',in_=bcontainer)
        b = Tkinter.Button(bcontainer, text="Left", command=self.moveLeft)
        b.grid_configure(column=1,row=0,sticky='ew',in_=bcontainer)
        b = Tkinter.Button(bcontainer, text="Selected", command=self.moveDeclaration)
        b.grid_configure(column=2,row=0,sticky='ew',in_=bcontainer)
        b = Tkinter.Button(bcontainer, text="Right", command=self.moveRight)
        b.grid_configure(column=3,row=0,sticky='ew',in_=bcontainer)
        b = Tkinter.Button(bcontainer, text="Replay", command=self.replayStep)
        b.grid_configure(column=4,row=0,sticky='ew',in_=bcontainer)
        bcontainer.grid_columnconfigure(1, weight=1)
        bcontainer = ttk.Frame()
        bcontainer.grid(column=0,row=1,sticky='ew',in_=container)
        searchlabel = Tkinter.Label(bcontainer, text="Find:")
        searchlabel.grid(column=0,row=0,sticky='ew',in_=bcontainer)
        self.search = Tkinter.Entry(bcontainer)
        self.search.grid(column=1,row=0,sticky='ew', in_=bcontainer)
        self.search.bind('<KeyRelease>',self.searchChange)

        container.grid_columnconfigure(0, weight=1)
        bcontainer.grid_columnconfigure(1, weight=1)
        container.grid_rowconfigure(2, weight=1)
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
                    if self.currentStepIndex==len(d.getProof)-1:
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


        #container = ttk.Frame()
        #container.pack(fill='both', expand=True)
        #pane1.add(container)

        # XXX Sounds like a good support class would be one for constructing
        #     a treeview with scrollbars.
        #self.proof = ttk.Treeview()
        #vsb = ttk.Scrollbar(orient="vertical", command=self.proof.yview)
        #hsb = ttk.Scrollbar(orient="horizontal", command=self.proof.xview)
        #self.proof.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        #self.proof.bind("<<TreeviewSelect>>",self.selectTactic)
        #self.proof.grid(column=0, row=0, sticky='nsew', in_=container)
        #vsb.grid(column=1, row=0, sticky='ns', in_=container)
        #hsb.grid(column=0, row=1, sticky='ew', in_=container)

        #container.grid_columnconfigure(0, weight=1)
        #container.grid_rowconfigure(0, weight=1)

        #pane2 = Tkinter.PanedWindow(orient=Tkinter.VERTICAL)
        #pane1.add(pane2)

        container = ttk.Frame()
        #container.pack(fill='both', expand=True, side="bottom")
        pane1.add(container, width=600)

        # XXX Sounds like a good support class would be one for constructing
        #     a treeview with scrollbars.
        self.code = Tkinter.Text(height=50)
        self.code.bind('<KeyRelease>',self.codeChange)
        self.code.bind('<ButtonRelease>',self.codeSelect)
        self.code.bind('<ButtonPress>',self.codeSelect)
        self.code.bind('<Motion>',self.codeSelect)

        self.vsb = ttk.Scrollbar(orient="vertical", command=self.code.yview)
        hsb = ttk.Scrollbar(orient="horizontal", command=self.code.xview)
        self.code.configure(yscrollcommand=self.codevsbset, xscrollcommand=hsb.set)
        self.code.grid(column=0, row=1, sticky='nsew', in_=container)
        self.vsb.grid(column=1, row=1, sticky='ns', in_=container)
        hsb.grid(column=0, row=2, sticky='ew', in_=container)

        bcontainer = ttk.Frame()
        bcontainer.grid(column=0,row=0,sticky='ew',in_=container)
        l = Tkinter.Label(bcontainer, text="Navigation")
        l.grid_configure(column=0,row=0,sticky='ew',in_=bcontainer)
        b = Tkinter.Button(bcontainer, text="Left", command=self.selectLeft)
        b.grid_configure(column=1,row=0,sticky='ew',in_=bcontainer)
        b = Tkinter.Button(bcontainer, text="Tree item", command=self.selectTreeItem)
        b.grid_configure(column=2,row=0,sticky='ew',in_=bcontainer)
        b = Tkinter.Button(bcontainer, text="Right", command=self.selectRight)
        b.grid_configure(column=3,row=0,sticky='ew',in_=bcontainer)
        b = Tkinter.Button(bcontainer, text="Parse", command=self.acceptEdit)
        b.grid_configure(column=4,row=0,sticky='ew',in_=bcontainer)

        container.grid_columnconfigure(0, weight=1)
        container.grid_rowconfigure(0, weight=1)
        bcontainer.grid_columnconfigure(4, weight=1)

        #container = ttk.Frame()
        #container.pack(fill='both', expand=True, side="bottom")
        #pane2.add(container, height=100)

        # XXX Sounds like a good support class would be one for constructing
        #     a treeview with scrollbars.
        #self.tactic = Tkinter.Text(height=50)

        #vsb = ttk.Scrollbar(orient="vertical", command=self.tactic.yview)
        #hsb = ttk.Scrollbar(orient="horizontal", command=self.tactic.xview)
        #self.tactic.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        #self.tactic.grid(column=0, row=0, sticky='nsew', in_=container)
        #vsb.grid(column=1, row=0, sticky='ns', in_=container)
        #hsb.grid(column=0, row=1, sticky='ew', in_=container)

        #container.grid_columnconfigure(0, weight=1)
        #container.grid_rowconfigure(0, weight=1)

        container = ttk.Frame()
        #container.pack(fill='both', expand=True, side="bottom")
        pane1.add(container, width=700)

        # XXX Sounds like a good support class would be one for constructing
        #     a treeview with scrollbars.
        self.response = Tkinter.Canvas(container, width=300,height=300,scrollregion=(0,0,4000,200000))
        vsb = ttk.Scrollbar(container, orient="vertical", command=self.response.yview)
        hsb = ttk.Scrollbar(container, orient="horizontal", command=self.response.xview)
        hsb.config(command=self.response.xview)
        vsb.config(command=self.response.yview)
        self.response.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        self.response.grid(column=0, row=1, sticky='nsew', in_=container)
        vsb.grid(column=1, row=1, sticky='ns', in_=container)
        hsb.grid(column=0, row=2, sticky='ew', in_=container)
        bcontainer = ttk.Frame()
        bcontainer.grid(column=0,row=0,sticky='ew',in_=container)
        self.showOldVar = Tkinter.IntVar()
        self.showOld = Tkinter.Checkbutton(bcontainer, text="Show previous output", command=self.toggle_showOld, variable=self.showOldVar)
        self.showOld.grid(column=0,row=0,sticky='ew',in_=bcontainer)
        self.diff_value = Tkinter.StringVar()
        self.diff = ttk.Combobox(bcontainer, textvariable=self.diff_value)
        self.diff['values'] = ('Prev step', 'Old result', 'Hyp application')
        self.diff.current(0)
        self.diff.grid(column=1, row=0, sticky='ew', in_=bcontainer)
        self.diff.bind('<<ComboboxSelected>>',self.diff_changed)
        bcontainer.grid_columnconfigure(1, weight=1)

        container.grid_columnconfigure(0, weight=1)
        container.grid_rowconfigure(1, weight=1)

        self.displayedFile = None
        self.displayedFileIndex = -1

    def _build_tree(self):
        #self.proof.heading("#0", text="Proof")
        self.tree.heading("#0", text="Definitions")

    def populate_tree(self):
        self.firstLine = None
        self.firstCol = None
        self.errorLine = None
        self.errorCol = None
        self.lastLine = None
        self.lastCol = None
        self.originalLastLine = None
        self.originalLastCol = None
        self.firstChangedDef = None
        self.lastChangedDef = None
        self.firstChangedStep = None
        self.lastChangedStep = None
        try:
            for x in self.treeItems:
                self.tree.delete(x)
                try:
                    del self.widgetMap[x]
                except KeyError:
                    pass
                try:
                    del self.proofMap[x]
                except KeyError:
                    pass
                try:
                    del self.widgetFile[x]
                except KeyError:
                    pass
                try:
                    del self.proofFile[x]
                except KeyError:
                    pass
        except AttributeError:
            pass
        self.treeItems = []
        self.proofMap = {}
        self.proofFile = {}
        self.proofNum = {}
        for f in self.project.files:
            ss = self.tree.insert('','end',f,text=f)
            #self.tree.tag_configure('yellow', background = 'yellow')
            #self.tree.item(ss, tags=('yellow',))
            self.treeItems.append(ss)
            #print ss
            self.widgetMap[ss] = None
            self.widgetFile[ss] = f
            #self.text[f] = self.project.text[f].split("\n")
            c = 0
            stack = []
            for d in self.project.defs[f]:
                if d.undent() and len(stack)>0:
                    ss = stack[len(stack)-1]
                    stack = stack[0:len(stack)-1]
                d.inFile = f
                id = "i"+str(self.idn)
                print "id (b) = " + str(id)
                self.idn = self.idn + 1
                #xx = self.tree.insert(ss,'end',f+"."+d.header(),text=d.header())
                xx = self.tree.insert(ss,'end',id,text=d.header())
                d.insertParent = ss
                d.insertItem = xx
                c = c+1
                #print type(xx)
                #print "Adding "+xx
                self.widgetFile[xx] = f
                self.widgetMap[xx] = d
                #self.buildProofTree(xx,d)
                if d.indent():
                    stack.append(ss)
                    ss = xx

    def update_tree(self,parent,del_item,file,pos,count,new_defs):
        if del_item != None:
            self.tree.delete(del_item)
            try:
                del self.widgetMap[del_item]
            except KeyError:
                pass
            try:
                del self.proofMap[del_item]
            except KeyError:
                pass
            try:
                del self.widgetFile[del_item]
            except KeyError:
                pass
            try:
                del self.proofFile[del_item]
            except KeyError:
                pass
        while count > 0:
            d = new_defs[pos]
            xx = self.tree.insert(parent,pos,file+"."+d.header(),text=d.header())
            d.insertParent = parent
            d.insertItem = xx
            d.inFile = file
            self.widgetFile[xx] = file
            self.widgetMap[xx] = d
            pos = pos + 1
            count = count - 1

    def test_populate_tree(self):
        ss = self.tree.insert('','end',values=('SatSolver.v',''))
        self.tree.insert(ss,'end',values=('    Exports',''))
        self.tree.insert(ss,'end',values=('    Notations',''))
        self.tree.insert(ss,'end',values=('    var_count','Definition'))
        self.tree.insert(ss,'end',values=('    next_offset','Definition'))
        self.tree.insert(ss,'end',values=('    positive_lit_offset','Definition'))
        self.tree.insert(ss,'end',values=('    negative_lit_offset','Definition'))
        self.tree.insert(ss,'end',values=('    invariant','Definition'))
        self.tree.insert(ss,'end',values=('    invariant1','Definition'))
        self.tree.insert(ss,'end',values=('    finalState','Definition'))
        self.tree.insert(ss,'end',values=('    Program','Definition'))
        self.tree.insert(ss,'end',values=('    Set Printing Depth 200','Command'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux8','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux7','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux6','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux5','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux4','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux4b','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux3','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux2','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux1','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux9','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1Aux9b','Theorem'))
        self.tree.insert(ss,'end',values=('    MergeTheorem1','Theorem'))
        self.tree.insert(ss,'end',values=('    SatProgramWorks','Theorem'))

        self.proof.insert('','end',values=('intros'))
        ss = self.proof.insert('','end',values=('inversion_H6'))
        self.proof.insert(ss,'end',values=('____subst'))
        self.proof.insert(ss,'end',values=('____clear_H6'))
        ss = self.proof.insert('','end',values=('inversion_H15'))
        self.proof.insert(ss,'end',values=('____subst'))
        self.proof.insert(ss,'end',values=('____clear_H15'))
	ss = self.proof.insert('','end',values=('inversion_H6'))
	self.proof.insert(ss,'end',values=('____subst'))
        self.proof.insert(ss,'end',values=('____clear_H6'))
        self.proof.insert(ss,'end',values=('____Transparent_basicEval'))
        self.proof.insert(ss,'end',values=('________simpl_in_H12'))
        self.proof.insert(ss,'end',values=('____Opaque_basicEval'))
        ss = self.proof.insert('','end',values=('inversion_H12'))
        self.proof.insert(ss,'end',values=('____subst'))
        self.proof.insert(ss,'end',values=('____clear_H12'))
        ss = self.proof.insert('','end',values=('inversion_H10'))
        self.proof.insert(ss,'end',values=('____subst'))
        self.proof.insert(ss,'end',values=('____clear_H10'))
        ss = self.proof.insert('','end',values=('eapply_concreteComposeEmpty_in_H16'))
        self.proof.insert(ss,'end',values=('____inversion_H16'))
        self.proof.insert(ss,'end',values=('____subst'))
        self.proof.insert(ss,'end',values=('____clear_H16'))
        self.proof.insert('','end',values=('simpl_in_H12'))
        self.proof.insert('','end',values=('simpl_in_H13'))
        ss = self.proof.insert('','end',values=('inversion_H13'))
        self.proof.insert(ss,'end',values=('____subst'))
        self.proof.insert(ss,'end',values=('____clear_H13'))
        self.proof.insert(ss,'end',values=('____Transparent_basicEval'))
        self.proof.insert(ss,'end',values=('________simpl_in_H14'))
        self.proof.insert(ss,'end',values=('____Opaque_basicEval'))
        ss = self.proof.insert('','end',values=('inversion_H14'))
        self.proof.insert(ss,'end',values=('____subst'))
        self.proof.insert(ss,'end',values=('____clear_H14'))
        ss = self.proof.insert('','end',values=('eapply_mapSumExists_in_H7'))
        self.proof.insert(ss,'end',values=('____inversion_H7'))
        self.proof.insert(ss,'end',values=('____subst'))
        self.proof.insert(ss,'end',values=('____clear_H7'))
        ss = self.proof.insert('','end',values=('inversion_H6'))
        self.proof.insert(ss,'end',values=('____subst'))
        self.proof.insert(ss,'end',values=('____clear_H6'))
        self.proof.insert('','end',values=('simplifyHyp_H10'))
        self.proof.insert('','end',values=('simplifyHyp_H10'))
	ss = self.proof.insert('','end',values=('eapply_RSExists'))
	sg = self.proof.insert(ss,'end',values=('____SUBGOAL_1'))
        self.proof.insert(sg,'end',values=("________Transparent_basicEval"))
        self.proof.insert(sg,'end',values=('________simpl'))
        self.proof.insert(sg,'end',values=('________Opaque_basicEval'))
        self.proof.insert(sg,'end',values=('________reflexivity'))
        sg = self.proof.insert(ss,'end',values=('____SUBGOAL_2'))
        self.proof.insert(sg,'end',values=('________reflexivity'))

def main():
    root = Tkinter.Tk()
    root.wm_title("CoqPIE")
    root.wm_iconname("PIE")

    #import plastik_theme
    #plastik_theme.install('~/tile-themes/plastik/plastik')

    app = App(root)
    root.mainloop()
    #print "HERE"
    app.saveChanges()

if __name__ == "__main__":
    main()


