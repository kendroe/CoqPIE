# ****************************************************************************
#
# PIE - Python based IDe for Coq
#
# CoqParse.py
#
# This file contains code for the Coq Lexer
#
# (C) 2015, 2016 Kenneth Roe
# All rights reserved
#
# ****************************************************************************

import CoqLex
import types

# ****************************************************************************

class ParseError(Exception):
    def __init__(self, e, t):
        self.error = e
        self.tokens = t
    def __str__(self):
        return repr(self.error)

# ****************************************************************************

def pname(n):
    x = n[0]
    for i in range(1,len(n)):
        x = x + "." + n[i]
    return x

# ****************************************************************************

indent = 0

def spaces(n):
    r = ""
    while n > 0:
        n = n-1
        r = r+" "
    return r

# ****************************************************************************

class CoqParseObject:
    def __init__(self,t):
        self.needsReplay = 0
        #if len(t)==0:
            #print "Error"
        #print spaces(indent)+"Enumerating"
        #for x in t:
            #print spaces(indent+2)+str(x)
            #z = x.line
        self.tokens = t
        self.text = ""
    def __str__(self):
        return "Coq('"+self.__coqstr__()+"')"
    def __coqstr__(self):
        return "<Coq>"
    def getListRepr(self):
        return (["Parse"])
    @classmethod
    def create(cls,l,tokens):
        return CoqParseObject(tokens)
    def buildFromList(self,l):
        return CoqParseObject(l[1])
    def updateTokens(self,line,col,tokens):
        res = []
        for t in tokens:
            l = t.line-line+1
            c = t.column
            if l==1:
                c = c-col
            res.append(CoqLex.Token(t.typ,t.value,l,c))
        return res
    def editUpdateTokens(self,line_s, col_s, line_oe, col_oe, line_ne, col_ne):
        t2 = []
        for t in self.tokens:
            if t.line < line_s or (t.line==line_s and t.column < col_s):
                t2.append(t)
            elif t.line==line_oe:
                t2.append(CoqLex.Token(t.typ,t.value,line_ne,t.column-col_oe+col_ne))
            else:
                x = CoqLex.Token(t.typ,t.value,t.line+line_ne-line_oe,t.column)
                t2.append(x)
        self.tokens = t2
    def getSegment(self,text):
        #print "Tokens"
        #print self.tokens
        #print "End Tokens"
        if len(self.tokens)==0:
            return ""
        l1 = self.tokens[0].line
        c1 = self.tokens[0].column
        l2 = self.tokens[len(self.tokens)-1].line
        c2 = self.tokens[len(self.tokens)-1].column+len(self.tokens[len(self.tokens)-1].value)
        tl = text[l1-1:l2]
        if (len(tl)==0):
            return ("",self.updateTokens(l1,c1,self.tokens))
        if c1 >= len(tl[0]):
            tl[0] = ""
        else:
            tl[0] = tl[0][c1:]
        if l2==l1:
            tl[0] = tl[0][0:c2-c1]
        else:
            tl[l2-l1] = tl[l2-l1][0:c2]
        #print self.tokens
        #print l1
        #print c1
        #print l2
        #print c2
        return ("\n".join(tl),self.updateTokens(l1,c1,self.tokens))

# ****************************************************************************

class CoqExpr(CoqParseObject):
    def __init__(self):
        pass
    def dependencies(self):
        return []
    def __repr__(self):
        return "class CoqExpr"
    def __coqstr__(self):
        return "<CoqExpr>"

class CoqStarExpr(CoqExpr):
    def __init__(self,tokens):
        CoqParseObject.__init__(self,tokens)
    def getListRepr(self):
        return (["StarExpr"])
    @classmethod
    def create(cls,l,tokens):
        return CoqStarExpr(tokens)
    def __repr__(self):
        return "class CoqStarExpr "
    def __coqstr__(self):
        return "*"

class CoqNumberExpr(CoqExpr):
    def __init__(self,tokens,f):
        CoqParseObject.__init__(self,tokens)
        self.number = f
    def getListRepr(self):
        return (["Number",self.number])
    @classmethod
    def create(cls,l,tokens):
        return CoqNumberExpr(tokens,l[1])
    def __repr__(self):
        return "class CoqNumberExpr "+str(self.number)
    def __coqstr__(self):
        return str(self.number)

class CoqNameExpr(CoqExpr):
    def __init__(self,tokens,f):
        CoqParseObject.__init__(self,tokens)
        self.name = f
    def dependencies(self):
        return [self.name]
    def getListRepr(self):
        return (["Name",self.name])
    @classmethod
    def create(cls,l,tokens):
        return CoqNameExpr(tokens,l[1])
    def __repr__(self):
        x = ""
        first = True
        for z in self.name:
            if not(first):
                x = x + "."
            first = False
            x = x + z
        return "CoqNameExpr "+x
    def __coqstr__(self):
        x = ""
        first = True
        for z in self.name:
            if not(first):
                x = x + "."
            first = False
            x = x + z
        return x

class CoqQuestionNameExpr(CoqExpr):
    def __init__(self,tokens,f):
        CoqParseObject.__init__(self,tokens)
        self.name = f
    def getListRepr(self):
        return (["QuestionName",self.name])
    @classmethod
    def create(cls,l,tokens):
        return CoqQuestionNameExpr(tokens,l[1])
    def __repr__(self):
        return "class CoqQuestionNameExpr "+self.name
    def __coqstr__(self):
        return "?"+self.name

class CoqQuotationExpr(CoqExpr):
    def __init__(self,tokens,f):
        CoqParseObject.__init__(self,tokens)
        self.text = f
    def getListRepr(self):
        return (["Quotation",self.name])
    @classmethod
    def create(cls,l,tokens):
        return CoqQuotationExpr(tokens,l[1])
    def __repr__(self):
        return "class CoqQuotationExpr "+self.text
    def __coqstr__(self):
        return '"'+self.text+'"'

class CoqAtNameExpr(CoqExpr):
    def __init__(self,tokens,f):
        CoqParseObject.__init__(self,tokens)
        self.name = f
    def dependencies(self):
        return [self.name]
    def getListRepr(self):
        return (["AtName",self.name])
    @classmethod
    def create(cls,l,tokens):
        return CoqAtNameExpr(tokens,l[1])
    def __repr__(self):
        x = "classCoqAtNameExpr "
        first = True
        for z in self.name:
            if not(first):
                x = x + "."
            first = False
            x = x + z
        return x
    def __coqstr__(self):
        x = "@"
        first = True
        for z in self.name:
            if not(first):
                x = x + "."
            first = False
            x = x + z
        return x

class CoqDotDotExpr(CoqExpr):
    def __init__(self,tokens):
        CoqParseObject.__init__(self,tokens)
    def dependencies(self):
        return []
    def getListRepr(self):
        return (["DotDot"])
    @classmethod
    def create(cls,l,tokens):
        return CoqDotDotExpr(tokens)
    def __repr__(self):
        return "class CoqDotDotExpr"
    def __coqstr__(self):
        return ".."

class CoqUnderscoreExpr(CoqExpr):
    def __init__(self,tokens):
        CoqParseObject.__init__(self,tokens)
    def getListRepr(self):
        return (["Underscore"])
    @classmethod
    def create(cls,l,tokens):
        return CoqUnderscoreExpr(tokens)
    def __repr__(self):
        return "class CoqUnderscoreExpr"
    def __coqstr__(self):
        return "_"

class CoqApplExpr(CoqExpr):
    def __init__(self,tokens,f,p):
        CoqParseObject.__init__(self,tokens)
        self.fun = f
        self.param = p
    def dependencies(self):
        return self.fun.dependencies()+self.param.dependencies()
    def getListRepr(self):
        return (["Appl",self.fun,self.param])
    @classmethod
    def create(cls,l,tokens):
        return CoqApplExpr(tokens,l[1],l[2])
    def __repr__(self):
        return "class CoqApplExpr"
    def __coqstr__(self):
        return "(" + self.fun.__coqstr__()+" "+self.param.__coqstr__() + ")"

class CoqContextExpr(CoqExpr):
    def __init__(self,tokens,e):
        CoqParseObject.__init__(self,tokens)
        self.expr = e
    def dependencies(self):
        return self.expr.dependencies()
    def getListRepr(self):
        return (["ContextExpr",self.expr])
    @classmethod
    def create(cls,l,tokens):
        return CoqContextExpr(tokens,l[1])
    def __repr__(self):
        return "class CoqContextExpr"
    def __coqstr__(self):
        return "context [" + self.expr.__coqstr__() + "]"

class CoqBraceExpr(CoqExpr):
    def __init__(self,tokens,e,t,c):
        CoqParseObject.__init__(self,tokens)
        self.expr = e
        self.exprType = t
        self.exprCond = c
    def dependencies(self):
        return self.expr.dependencies()
    def getListRepr(self):
        return (["BraceExpr",self.expr,self.exprType,self.exprCond])
    @classmethod
    def create(cls,l,tokens):
        return CoqBraceExpr(tokens,l[1],l[2],l[3])
    def __repr__(self):
        return "class CoqBraceExpr"
    def __coqstr__(self):
        x = "{" + self.expr.__coqstr__()
        if (self.exprType != None):
            x = x + ":"+self.exprType.__coqstr__()
        if (self.exprCond != None):
            x = x + "|"+self.exprCond.__coqstr__()
        x = x + "}"
        return x

class CoqRecordExpr(CoqExpr):
    def __init__(self,tokens,m):
        CoqParseObject.__init__(self,tokens)
        self.maps = m
    def dependencies(self):
        x = []
        for m in maps:
            x = x + m[1].dependencies()
        return x
    def getListRepr(self):
        return (["RecordExpr",self.maps])
    @classmethod
    def create(cls,l,tokens):
        return CoqRecordExpr(tokens,l[1])
    def __repr__(self):
        return "class CoqRecordExpr"
    def __coqstr__(self):
        x = "{| "
        first = True
        for m in self.maps:
            if not(first):
                x = x + "; "
            x = m[0] + " := " + m[1].__coqstr__()
            first = True
        x = x + "|}"
        return x

class CoqFunExpr(CoqExpr):
    def __init__(self,tokens,v,b):
        CoqParseObject.__init__(self,tokens)
        self.vars = v
        self.body = b
    def dependencies(self):
        d = []
        x = self.body.dependencies()
        for v in self.vars:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    while (v[0] in x):
                        x.remove(v[0])
            except ValueError:
                pass
        return d+x
    def getListRepr(self):
        x = ["Fun"]
        for v in self.vars:
            x.append(v[0])
            x.append(v[1])
        x.append(self.body)
        return x
    @classmethod
    def create(cls,l,tokens):
        vars = []
        body = l[len(l)-2]
        for i in range(0,len(l)/2-1):
            vars.append(l[i*2+1],l[i*2+2])
        return CoqFunExpr(tokens,vars,body)
    def __repr__(self):
        return "class CoqFunExpr"
    def __coqstr__(self):
        x = "fun"
        for v in self.vars:
            if v[1]==None:
                x = x + " " + v[0]
            else:
                xx = ""
                for vv in v[0]:
                    xx = xx + " " + vv
                xx = xx[1:]
                x = x + " (" + xx + " : " + v[1].__coqstr__() + ")"
        return x+" => " + self.body.__coqstr__()

class CoqTupleExpr(CoqExpr):
    def __init__(self,tokens,l):
        CoqParseObject.__init__(self,tokens)
        self.terms = l
    def dependencies(self):
        d = []
        for t in self.terms:
            d = d+t.dependencies()
        return d
    def getListRepr(self):
        x = ["Tuple"]
        for t in self.terms:
            x.append(t)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqTupleExpr(tokens,l[1:])
    def __repr__(self):
        return "class CoqTupleExpr"
    def __coqstr__(self):
        x = "("
        comma = False
        for q in self.terms:
            if comma:
                x = x+", "
            comma = True
            x = x+q.__coqstr__()
        return x + ")"

class CoqExistsExpr(CoqExpr):
    def __init__(self,tokens,v,t,e):
        CoqParseObject.__init__(self,tokens)
        self.var = v
        self.vtype = t
        self.exp = e
    def dependencies(self):
        if self.vtype==None:
            d = []
        else:
            d = self.vtype.dependencies()
        if d==None:
            d = []
        z = self.exp.dependencies()
        if z==None:
            z = []
        try:
            try:
                x = d+z.remove(self.var)
            except TypeError:
                x = d+z
        except ValueError:
            x = d+z
        return x
    def getListRepr(self):
        return ["Exists",self.var,self.vtype,self.exp]
    @classmethod
    def create(cls,l,tokens):
        return CoqExistsExpr(tokens,l[1],l[2],l[3])
    def __repr__(self):
        return "class CoqExistsExpr"
    def __coqstr__(self):
        x = "exists "+self.var
        if (self.vtype != None):
            x = x + " : " + self.vtype.__coqstr__()
        return x + ", "+self.exp.__coqstr__()

# ****************************************************************************

class CoqForallExpr(CoqExpr):
    def __init__(self,tokens,v,t,e,cb):
        CoqParseObject.__init__(self,tokens)
        self.var = v
        self.var_type = t
        self.expr = e
        self.brace = cb
    def dependencies(self):
        if self.var_type==None:
            d = []
        else:
            d = self.var_type.dependencies()
        x = self.expr.dependencies()
        try:
            while self.var in x:
                while (self.var in x):
                    x.remove(self.var)
        except ValueError:
            pass
        #print "FORALL dependencies "+str(self.var)+" "+str(self.var_type)+" "+str(d)+" "+str(x)
        return d+x
    def getListRepr(self):
        return ["Forall",self.var,self.var_type,self.expr,self.brace]
    @classmethod
    def create(cls,l,tokens):
        return CoqForallExpr(tokens,l[1],l[2],l[3],l[4])
    def __repr__(self):
        return "class CoqMatchExpr"
    def __coqstr__(self):
        x = "forall "
        if self.var_type==None:
            x = x+self.var
        else:
            x = x+"("+self.var+":"+self.var_type.__coqstr__()+")"
        return x+", "+self.expr.__coqstr__()

def parseCoqForallExpr(tokens,blocks):
    #print "Parsing forall"
    tt = tokens
    if len(tokens)<5 or tokens[0].typ!='forall':
        raise ParseError('cannot parse match',tokens)
    vars = []
    tokens = tokens[1:]
    while len(tokens)>1 and (tokens[0].typ=='leftParen' or tokens[0].typ=='ID' or tokens[0].typ=='leftBrace' or tokens[0].typ=='_'):
        cb = False
        if tokens[0].typ=='ID' or tokens[0].typ=='_':
            t = None
            n = tokens[0].value
            if len(tokens)>2 and tokens[1].typ=='colon':
                x = parseCoqExpr(tokens[2:],[])
                tokens = x[1]
                t = x[0]
            else:
                tokens = tokens[1:]
            vars.insert(0,(n,t,cb))
        else:
            if tokens[0].typ=='leftBrace':
                cb = True
            ln = []
            tokens = tokens[1:]
            while len(tokens)>1 and (tokens[0].typ=='ID' or tokens[0].typ=='_'):
                ln.append(tokens[0].value)
                tokens = tokens[1:]
            if len(tokens)<3 or (tokens[0].typ!='colon' and tokens[0].typ!='rightBrace'):
                print tokens[0]
                print tokens[1]
                print tokens[2]
                raise ParseError('cannot parse forall',tokens)
            typ = None
            if (tokens[0].typ=='colon'):
                x = parseCoqExpr(tokens[1:],[])
                tokens = x[1]
                typ = x[0]
            if len(tokens)==0 or (tokens[0].typ != 'rightParen' and tokens[0].typ != 'rightBrace'):
                print tokens[0]
                print tokens[1]
                print tokens[2]
                print tokens[3]
                raise ParseError('cannot parse forall',tokens)
            tokens = tokens[1:]
            for n in ln:
                vars.insert(0,(n,typ,cb))
    #print "Got params"
    #print tokens[0]
    if len(tokens)==0 or tokens[0].typ != 'comma':
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError('cannot parse forall',tokens)
    x = parseCoqExpr(tokens[1:],blocks)
    r = x[0]
    tokens = x[1]
    #print "Done forall"
    #print tokens[0]
    for v in vars:
        r = CoqForallExpr(tt[0:len(tt)-len(tokens)],v[0],v[1],r,v[2])
    return (r,tokens)

class CoqMatchExpr(CoqExpr):
    def __init__(self,tokens,e,r,c):
        CoqParseObject.__init__(self,tokens)
        self.exp = e
        self.return_type = r
        self.cases = c
    def dependencies(self):
        if self.return_type==None:
            x = []
        else:
            x = self.return_type.dependencies()
        for e in self.exp:
            x = x + e[0].dependencies()
        for c in self.cases:
            d = c[1].dependencies()
            for p in c[0]:
                for v in p.dependencies():
                    try:
                        d.remove(v)
                    except ValueError:
                        pass
            x = x+d
        return d
    def getListRepr(self):
        return ["Match",self.exp,self.return_type,self.cases]
    @classmethod
    def create(cls,l,tokens):
        return CoqMatchExpr(tokens,l[1],l[2],l[3])
    def __repr__(self):
        return "class CoqMatchExpr"
    def __coqstr__(self):
        x = "match"
        pcomma = False
        for z in self.exp:
            if pcomma:
                x = x+","
            pcomma = True
            x = x + " "+z[0].__coqstr__()
            if z[1]!=None:
               x = x + " as "+z[1]
            if z[2]!=None:
               x = x + " in "+z[2].__coqstr__()
        if self.return_type!=None:
            x = x+" return "+self.return_type.__coqstr__()
        x = x + " with"
        for p in self.cases:
            x = x + " | "
            pcomma = False
            for q in p[0]:
                if pcomma:
                    x = x + ", "
                pcomma = True
                x = x+q.__coqstr__()
            x = x + " => " + p[1].__coqstr__()
        return x+" end"

def parseCoqMatchExpr(tokens):
    tt = tokens
    if len(tokens)<7 or tokens[0].typ!='match':
        raise ParseError('cannot parse match',tokens)
    x = parseCoqExpr(tokens[1:],[])
    tokens = x[1]
    ee = x[0]
    n = None
    t = None
    if len(tokens)>1 and tokens[0].typ=='as' and tokens[1].typ=='ID':
        n = tokens[1].value
        tokens = tokens[2:]
    if tokens[0].typ=='in':
        x = parseCoqExpr(tokens[1:],[])
        tokens = x[1]
        t = x[0]
    e = [(ee,n,t)]
    while len(tokens)>1 and tokens[0].typ=='comma':
        x = parseCoqExpr(tokens[1:],[])
        ee = x[0]
        tokens = x[1]
        if len(tokens)>1 and tokens[0].typ=='as' and tokens[1].typ=='ID':
            n = tokens[1].value
            tokens = tokens[2:]
        if tokens[0].typ=='in':
            x = parseCoqExpr(tokens[1:],[[CoqLex.Token('bar','|',0,0)]])
            tokens = x[1]
            t = x[0]
        e.append((ee,n,t))
    r = None
    if len(tokens)>1 and tokens[0].typ=='return':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('bar','|',0,0)]])
        r = x[0]
        tokens = x[1]
    if len(tokens)<3 or tokens[0].typ!='with':
        raise ParseError('cannot parse match',tokens)
    tokens = tokens[1:]
    first = True
    p = []
    while first or tokens[0].typ != 'end':
        if first==False and tokens[0].typ !='bar':
            #print tokens[0]
            #print tokens[1]
            #print tokens[2]
            #print tokens[3]
            raise ParseError('cannot parse match',tokens)
        if tokens[0].typ=='bar':
            tokens = tokens[1:]
        first = False
        pats = []
        x = parseCoqExpr(tokens,[])
        l = [x[0]]
        tokens = x[1]
        while len(tokens)>1 and tokens[0].typ=='comma':
            x = parseCoqExpr(tokens[1:],[[CoqLex.Token('bar','|',0,0)]])
            l.append(x[0])
            tokens = x[1]
        pats.append(l)
        while len(tokens)>1 and tokens[0].typ=='bar':
            x = parseCoqExpr(tokens,[[CoqLex.Token('equalGreater','=>',0,0)]])
            l = [x[0]]
            tokens = x[1]
            while len(tokens)>1 and tokens[0].typ=='comma':
                x = parseCoqExpr(tokens[1:],[[CoqLex.Token('equalGreater','=>',0,0)]])
                l.append(x[0])
                tokens = x[1]
            pats.append(l)
        if len(tokens)<2 or tokens[0].typ!='equalGreater':
            raise ParseError('cannot parse match',tokens)
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('bar','|',0,0)]])
        pp = x[0]
        tokens = x[1]
        for q in pats:
            p.append((q,pp))
    if len(tokens)<1 or tokens[0].typ!='end':
        raise ParseError('cannot parse match',tokens)
    return (CoqMatchExpr(tt[0:len(tt)-len(tokens)],e,r,p),tokens[1:])

class CoqLetExpr(CoqExpr):
    def __init__(self,tokens,p,b,w,e):
        CoqParseObject.__init__(self,tokens)
        self.pat = p
        self.bind = b
        self.exp = e
        self.wit = w
        self.exp = e
    def dependencies(self):
        if self.return_type==None:
            x = []
        else:
            x = self.return_type.dependencies()
        for e in self.exp:
            x = x + e[0].dependencies()
        for c in self.cases:
            d = c[1].dependencies()
            for p in c[0]:
                for v in p.dependencies():
                    try:
                        d.remove(v)
                    except ValueError:
                        pass
            x = x+d
        return d
    def getListRepr(self):
        return ["Let",self.pat,self.bind,self.wit,self.exp]
    @classmethod
    def create(cls,l,tokens):
        return CoqMatchExpr(tokens,l[1],l[2],l[3],l[4])
    def __repr__(self):
        return "class CoqLetExpr"
    def __coqstr__(self):
        x = "let "+self.pat.__coqstr__()
        if self.wit != None:
            x = x + " with " + self.wit.__coqstr__()
        x = x + " := " + self.bind.__coqstr__() + " in "+self.exp.__coqstr__()
        return x

def parseCoqLetExpr(tokens,terminals):
    tt = tokens
    if len(tokens)<3 or tokens[0].typ!='let':
        print tokens[0]
        raise ParseError('cannot parse let',tokens)
    x = parseCoqExpr(tokens[1:],[])
    tokens = x[1]
    p = x[0]
    w = None
    if len(tokens)>0 and tokens[0].typ=='with':
        w = parseCpqExpr(tokens[1:],[])
        w = x[0]
        tokens = x[1]
    if len(tokens)>0 and tokens[0].typ=='colonEqual':
        x = parseCoqExpr(tokens[1:],[])
        tokens = x[1]
        b = x[0]
    else:
        print tokens[0]
        raise ParseError('cannot parse let',tokens)
    if len(tokens)>0 and tokens[0].typ=='in':
        x = parseCoqExpr(tokens[1:],terminals)
        tokens = x[1]
        e = x[0]
    else:
        print tokens[0]
        raise ParseError('cannot parse let',tokens)
    return (CoqLetExpr(tt[0:len(tt)-len(tokens)],p,b,w,e),tokens)

class CoqFixExpr(CoqExpr):
    def __init__(self,tokens,n,ip,p,t,b,o):
        CoqParseObject.__init__(self,tokens)
        self.name = n
        self.implicit_params = ip
        self.params = p
        self.returnType = t
        self.order = o
        self.body = b
    def dependencies(self):
        d = []
        x = self.body.dependencies()
        for v in self.params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        for v in self.implicit_params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        if self.returnType!=None:
            x = x+self.returnType.dependencies()
        return d+x
    def getListRepr(self):
        return ["Fix",self.name,(["params"]+self.implicit_params),(["params"]+self.params),self.returnType,self.order,self.body]
    @classmethod
    def create(cls,l,tokens):
        return CoqFixExpr(tokens,l[1],l[2][1:],l[3][1:],l[4],l[5],l[6])
    def header(self):
        return "FixExpr " + self.name
    def __repr__(self):
        return "class CoqFixExpr "+self.name
    def __coqstr__(self):
        x = "fix "+self.name
        for i in self.implicit_params:
            if i[1]==None:
                x = x + " {"+i[0]+"}"
            else:
                x = x + " {"+i[0]+":"+i[1].__coqstr__()+"}"
        for i in self.params:
            if i[1]==None:
                x = x + " "+i[0]
            else:
                x = x + " ("+i[0]+":"+i[1].__coqstr__()+")"
        if self.order != None:
            x = x + " {struct "+self.order+"}"
        if self.returnType != None:
            x = x + ": "+self.returnType.__coqstr__()
        return x + " := "+self.body.__coqstr__()

def parseCoqFixExpr(tokens,blocks):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'fix' or tokens[1].typ != 'ID':
        raise ParseError("Cannot parse Fixpoint",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    implicit_params = []
    while tokens[0].typ=='leftBrace':
        if len(tokens)<4 or tokens[1].typ!='ID':
            raise ParseError("Cannot parse Fixpoint",tokens)
        n = []
        pos = 1
        while (len(tokens)>pos and tokens[pos].typ=='ID'):
            n.append(tokens[pos].value)
            pos = pos+1
        if tokens[pos].typ=='colon':
           x = parseCoqExpr(tokens[pos+1:],[])
           tokens = x[1]
           t = x[0]
        else:
           tokens = tokens[pos:]
           t = None
        if (tokens[0].typ!="rightBrace"):
            raise ParseError("Cannot parse Fixpoint",tokens)
        tokens=tokens[1:]
        for nn in n:
            implicit_params.append((nn,t))
    params = []
    while tokens[0].typ=='leftParen' or tokens[0].typ=='ID':
        if tokens[0].typ=='ID':
            params.append((tokens[0].value,None))
            tokens = tokens[1:]
        else:
            if len(tokens)<4 or tokens[1].typ!='ID':
                raise ParseError("Cannot parse Fixpoint",tokens)
            pos = 1
            n = []
            while (len(tokens)>pos and tokens[pos].typ=='ID'):
                n.append(tokens[pos].value)
                pos = pos+1
            if tokens[pos].typ=='colon':
               x = parseCoqExpr(tokens[pos+1:],[])
               tokens = x[1]
               t = x[0]
            else:
               tokens = tokens[pos:]
               t = None
            if (tokens[0].typ!="rightParen"):
                 raise ParseError("Cannot parse Fixpoint",tokens)
            tokens=tokens[1:]
            for nn in n:
                implicit_params.append((nn,t))
    order = None
    if len(tokens)>4 and tokens[0].typ=='leftBrace' and tokens[1].value=='struct' and tokens[2].typ=='ID' and tokens[3].typ=='rightBrace':
        order = tokens[2].value
        tokens = tokens[4:]
    return_type = None
    if len(tokens)>2 and tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[])
        tokens = x[1]
        return_type = x[0]
    if (len(tokens)<3 or tokens[0].typ!="colonEqual"):
        raise ParseError("Cannot parse Fixpoint",tokens)
    x = parseCoqExpr(tokens[1:],blocks)
    body = x[0]
    tokens = x[1]
    return (CoqFixExpr(tt[0:len(tt)-len(tokens)],name,implicit_params,params,return_type,body,order),tokens)

# ****************************************************************************

infixParses = [
    (1,[1,":",1],"colon"),
    (2,[1,"->",3],"dashGreater"),
    (2,[1,"<->",3],"lessDashGreater"),
    (5,[6,"|->",6],"cell"),
    (7,[7,"-->>",8],"imply"),
    (8,[8,"\\\\",9],"or"),
    (10,[10,"\/",11],"or"),
    (10,[10,"\\/",11],"or"),
    (110,[110,"||",111],"or"),
    (110,[110,"\\\\//",111],"and"),
    (20,[20,"/\\",21],"and"),
    (20,[20,"&&",21],"and"),
    (120,[20,"/\\\\",121],"and"),
    (120,[20,"//\\\\",121],"and"),
    (50,[51,"=",51],"equal"),
    (50,[51,"===",51],"equalprog"),
    (50,[51,"<<=",51],"lessprog"),
    (50,[51,"<>",51],"not_equal"),
    (50,[51,">=",49],"greater_equal"),
    (50,[51,"<=",49],"less_equal"),
    (50,[51,"<",49],"less"),
    (50,[51,">",49],"greater"),
    (55,[56,"++",56],"append"),
    (60,[60,"+",61],"plus"),
    (60,[60,"-",61],"minus"),
    (60,[60,"++++",61],"plus"),
    (60,[60,"+++",61],"plus"),
    (60,[60,"---",61],"minus"),
    (70,[70,"*",71],"times"),
    (70,[70,"***",71],"times"),
    (70,[70,"****",71],"times"),
    (75,[75,"%",76],"percent"),
    (80,["~",80],"sneg"),
    (210,["#",211],"pound"),
    (150,["~~",101],"neg"),
    (200,[201,"::",199],"cons"),

    (30,[30,";",31],"seq"),
    (40,["WHILE",0,"DO",0,"LOOP"],"WHILE"),
    (40,["IF",0,"THEN",0,"ELSE",0,"FI"],"IF"),
    (40,["DELETE",0,",",0,],"DELETE"),
    (40,[40,"::=",40],"assign"),
    (40,["NEW",0,",",0],"NEW"),
    (200,["!",200],"ref"),
    (170,["TREE","(",0,",",0,",",0,",",0,")"],"TREE"),
    (170,["SUM","(",0,",",0,",",0,")"],"SUM"),
    (170,["ite","(",0,",",0,",",0,")"],"ite"),
    (170,["if",0,"then",0,"else",0],"if"),
    (170,["Path","(",0,",",0,",",0,",",0,",",0,")"],"Path"),
    (170,["ARRAY","(",0,",",0,",",0,")"],"ARRAY"),
    #(1000,["nth","(",0,",",0,")"],"nth"),
    (1000,["{","{",0,"}","}",0,"{","{",0,",",0,"}","}" ],"hoare"),
    (1000,["replacenth","(",0,",",0,",",0,")"],"replacenth"),
    (1000,["find","(",0,",",0,")"],"find"),
    (1000,["range","(",0,",",0,")"],"range"),
    (1000,["TreeRecords","(",0,")"],"TreeRecords"),
    (1000,["ANum","(",0,")"],"ANum"),
    (1000,["v","(",0,")"],"v"),
    (998,[998,".",999],"period"),
    (300,["!!",301],"envRef"),
    (105,[105,"*\/*",106],"sepOrStar"),
    (105,[105,"*\\/*",106],"sepOrStar"),
    (110,[110,"**",111],"sepStar"),
    (150,[150,"====",151],"expEqual"),
    (150,[150,"<<<<",151],"expLess"),
    (160,[160,"++++",161],"expPlus"),
    (170,["--","(",0,",",0,")","-->",171],"arrow"),
    (170,["--","(",0,",",0,")","--->",171],"arrowb"),
    #(165,["[",0,"]"],"predicate")
]

def getPrefixes(prefixes,token,level):
    res = []
    for x in prefixes:
        if x[0]>=level and len(x[1])>0 and type(x[1][0])==types.StringType:
            #print spaces(indent)+str(x)
            if token.value==x[1][0]:
                res.append((x[0],x[1][1:],x[2]))
    return res

def getInfixes(prefixes,token,retLevel,level):
    res = []
    for x in prefixes:
        if x[0]>=level and len(x[1])>1 and type(x[1][0])!=types.StringType and x[1][0]<=retLevel and x[1][1]==token.value:
            #print "Appending"
            res.append((x[0],x[1][1:],x[2]))
    return res

def matchBlock(tokens,blocks):
    for b in blocks:
        if len(tokens)>=len(b):
             is_match = True
             bb = b
             tt = tokens
             while is_match and len(bb)>0:
                 f = bb[0]
                 t = tt[0]
                 if f.typ!=t.typ or (len(f.value)>0 and f.value!=t.value):
                     is_match = False
                 bb = bb[1:]
                 tt = tt[1:]
             if is_match:
                 return True
    return False

def tacticKeyword(v):
    return v == 'Set' or v == 'destruct' or v =='fold' or v == 'unfold' or v == 'assert' or v == 'discriminate' or v =='apply' or v == 'simpl' or v == 'rewrite' or v == 'intros' or v == 'firstorder' or v == 'left' or v == 'right' or v == 'injection' or v == 'firstorder' or v =='pose' or v == 'induction' or v =='remember' or v == 'clear' or v == 'assumption' or v == 'constructor' or v == 'intuition' or v == 'Qed' or v == 'Case' or v == 'SCase' or v == 'SSCase' or v == 'SSSCase' or v == 'SSSSCase' or v == 'eapply' or v == 'instantiate' or v == 'crunch' or v == 'erewrite' or v == 'Inductive' or v == 'subst' or v == 'compute' or v=='reflexivity' or v=='mergeSimplifyLeft' or v=='mergeSimplifyRight' or v=='startMerge' or v=='doMergeStates' or v == 'DMMerge' or v=='Transparent' or v=='Opaque' or v=='solveAllPrediates' or v=='simplifyHyp' or v=='stateImplication' or v=='pcrunch' or v=='simp' or v=='Focus' or v=='inversion' or v=='solvePickData' or v=='unfoldHeap' or v=='removeExistentials' or v=='solveSPickElement' or v=='intro' or v=='solveAllPredicates' or v=='admit'

def doParseCoqExpr(tokens,level,blocks):
    global indent
    t = tokens
    #print spaces(indent)+"Parsing"
    #print spaces(indent)+str(tokens[0])
    p = getPrefixes(infixParses,tokens[0],level)
    #print spaces(indent)+"Prefixes"
    #print spaces(indent)+"level"
    #print spaces(indent)+str(level)
    #print spaces(indent)+str(p)
    pp = []
    #print "Parsing expr"
    #print tokens[0]
    if (len(p)>0):
        #print "Starting"
        tokens = tokens[1:]
        pp = getPrefixes(p,tokens[0],level)
        while (len(pp)>0):
            tokens = tokens[1:]
            p = pp
            pp = getPrefixes(p,tokens[0],level)
        pp = []
        #print "p"
        #print p
        for x in p:
            if len(x[1])==0 or type(x[1][0])!=types.StringType:
                pp.append(x)
        #print pp
        if len(pp)==0:
            tokens = t
    if (len(pp) > 0):
        #print spaces(indent)+"DO prefix"
        tail = []
        xx = []
        for z in pp:
            tail.append(z[1])
            xx.append(z[2])
        terms = []
        for x in xx:
            terms.append(CoqNameExpr(t[0:len(t)-len(tokens)],[x]))
        #terms = CoqApplExpr(t[0:len(t)-len(tokens)-1],CoqNameExpr(t[0:len(t)-len(tokens)],[x[2]]),res)
        #terms = []
        #for x in tail:
            #terms.append(None)
        #print "Prefix 1"
        #print tokens[0]
        #print tail
        while (len(tail[0])>0):
            tttt = tokens
            #print spaces(indent)+"Call 1"
            indent = indent+1
            xx = doParseCoqExpr(tokens,tail[0][0],blocks)
            indent = indent-1
            ttail = tail
            tail = []
            for z in ttail:
                tail.append(z[1:])
            tokens = xx[1]
            tterms = []
            for ttt in terms:
                if (ttt==None):
                    ttt = xx[0]
                else:
                    ttt = CoqApplExpr(t[0:len(t)-len(tokens)],ttt,xx[0])
                tterms.append(ttt)
            terms = tterms
            while len(tail[0])>0 and type(tail[0][0])==types.StringType:
                if len(tokens)==0:
                    raise ParseError("Cannot parse CoqExpr",tokens)
                ttail = tail
                tail = []
                tterms = terms
                terms = []
                for x in range(0,len(ttail)):
                    if tokens[0].value==ttail[x][0]:
                        tail.append(ttail[x][1:])
                        terms.append(tterms[x])
                if len(tail)==0:
                    print spaces(indent)+"Start"
                    print spaces(indent)+str(t[0])
                    print spaces(indent)+str(level)
                    print spaces(indent)+"Finish"
                    print spaces(indent)+str(tokens[0])
                    print spaces(indent)+str(tokens[1])
                    print spaces(indent)+str(tokens[2])
                    print spaces(indent)+str(tokens[3])
                    raise ParseError("Cannot parse CoqExpr",tokens)
                tokens = tokens[1:]
        res = terms[0]
        rlevel = pp[0][0]
    elif len(tokens)>1 and tokens[0].typ=='fix':
        #print spaces(indent)+"DO fix"
        res = parseCoqFixExpr(tokens,blocks)
        tokens = res[1]
        res = res[0]
        rlevel = 1
    elif len(tokens)>1 and tokens[0].typ=='let':
        #print spaces(indent)+"DO let"
        res = parseCoqLetExpr(tokens,blocks)
        tokens = res[1]
        res = res[0]
        rlevel = 1000
    elif len(tokens)>1 and tokens[0].typ=='match':
        #print spaces(indent)+"DO match"
        res = parseCoqMatchExpr(tokens)
        tokens = res[1]
        res = res[0]
        rlevel = 1000
    elif len(tokens)>3 and tokens[0].value=='context' and tokens[1].typ=='leftBracket':
        #print spaces(indent)+"DO context"
        res = parseCoqExpr(tokens[2:],[])
        tokens = res[1]
        res = res[0]
        if tokens[0].typ!='rightBracket':
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse CoqExpr",tokens)
        tokens = tokens[1:]
        res = CoqContextExpr(t[0:len(t)-len(tokens)],res)
        rlevel = 1000
    elif len(tokens)>4 and tokens[0].value=='exists':
        #print spaces(indent)+"DO exists"
        tttt = tokens
        params = []
        tokens = tokens[1:]
        vars = []
        while len(tokens)>1 and (tokens[0].typ=='leftParen' or tokens[0].typ=='ID' or tokens[0].typ=='leftBrace' or tokens[0].typ=='_'):
            cb = False
            if tokens[0].typ=='ID' or tokens[0].typ=='_':
                ttt = None
                n = tokens[0].value
                if len(tokens)>2 and tokens[1].typ=='colon':
                    x = parseCoqExpr(tokens[2:],[])
                    tokens = x[1]
                    t = x[0]
                else:
                    tokens = tokens[1:]
                vars.insert(0,(n,ttt,cb))
            else:
                if tokens[0].typ=='leftBrace':
                    cb = True
                ln = []
                tokens = tokens[1:]
                while len(tokens)>1 and (tokens[0].typ=='ID' or tokens[0].typ=='_'):
                    ln.append(tokens[0].value)
                    tokens = tokens[1:]
                ttt = None
                if tokens[0].typ=='colon':
                    x = parseCoqExpr(tokens[1:],[])
                    ttt = x[0]
                    tokens = x[1]
                for n in ln:
                    vars.insert(0,(n,ttt,cb))
                if len(tokens)==0 or (tokens[0].typ != 'rightParen' and tokens[0].typ != 'rightBrace'):
                    raise ParseError('cannot parse forall',tokens)
                tokens = tokens[1:]
        if len(tokens)<2 or tokens[0].typ!='comma':
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse CoqExpr", tokens)
        #print spaces(indent)+"Parsing expr"
        #print spaces(indent)+str(tokens[0])
        #print spaces(indent)+"call 3"
        indent = indent+1
        x = doParseCoqExpr(tokens[1:],0,blocks)
        indent = indent-1
        tokens = x[1]
        expr = x[0]
        for v in vars:
            expr = CoqExistsExpr(tttt[0:len(tttt)-len(tokens)],v[0],v[1],expr)
        res = expr
        rlevel = 1000
    elif len(tokens)>1 and tokens[0].typ=='fun':
        #print spaces(indent)+"DO fun"
        tttt = tokens
        params = []
        tokens = tokens[1:]
        while tokens[0].typ=='leftParen' or tokens[0].typ=='ID' or tokens[0].typ=='_':
            if tokens[0].typ=='ID' or tokens[0].typ=='_':
                tpe = None
                if (tokens[1]).typ=='colon':
                    x = parseCoqExpr(tokens[2:],[])
                    tokens = x[1]
                    tpe = x[0]
                else:
                    tokens = tokens[1:]
                params.append((tokens[0].value,tpe))
            else:
                if len(tokens)<4 or (tokens[1].typ!='ID' and tokens[1].typ!='_'):
                    raise ParseError("Cannot parse CoqExpr",tokens)
                pos = 1
                n = []
                while (len(tokens)>pos and (tokens[pos].typ=='ID' or tokens[pos].typ=='_')):
                    n.append(tokens[pos].value)
                    pos = pos+1
                if tokens[pos].typ=='colon':
                    x = parseCoqExpr(tokens[pos+1:],[])
                    tokens = x[1]
                    tpe = x[0]
                else:
                    tokens = tokens[pos:]
                    tpe = None
                if (tokens[0].typ!="rightParen"):
                    print tokens[0]
                    print tokens[1]
                    print tokens[2]
                    print tokens[3]
                    raise ParseError("Cannot parse expr",tokens)
                tokens=tokens[1:]
                for nn in n:
                    params.append((n,tpe))
        if len(tokens)<2 or tokens[0].typ!='equalGreater':
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse CoqExpr",tokens)
        x = parseCoqExpr(tokens[1:],blocks)
        tokens = x[1]
        rlevel = 10
        res = CoqFunExpr(tttt[0:len(tttt)-len(tokens)],params,x[0])
    elif len(tokens)>1 and tokens[0].typ=='forall':
        #print spaces(indent)+"DO forall"
        #print "Parsing forall"
        #print tokens[0]
        res = parseCoqForallExpr(tokens,blocks)
        tokens = res[1]
        res = res[0]
        rlevel = 10
    elif tokens[0].typ=='atsign' and (tokens[1].typ=='ID' or tokens[1].typ=='Context'):
        ttt = tokens
        tokens = tokens[1:]
        #print spaces(indent)+"DO ID"
        name = [tokens[0].value]
        tokens = tokens[1:]
        while (tokens[0].typ=='period' and tokens[1].typ=='ID' and tokens[0].line==tokens[1].line and tokens[0].column+1==tokens[1].column):
            name.append(tokens[1].value)
            tokens = tokens[2:] 
        res = CoqAtNameExpr(ttt[0:len(ttt)-len(tokens)],name)
        rlevel = 1000
    elif tokens[0].typ=='dotdot':
        #print spaces(indent)+"DO dotdot"
        res = CoqDotDotExpr(tokens[0:1])
        tokens = tokens[1:]
        rlevel = 1000
    elif tokens[0].typ=='leftBracket':
        #print "Parsing list"
        #print tokens[0]
        tokens = tokens[1:]
        ttq = tokens
        ll = []
        lens = []
        while len(tokens) > 0 and tokens[0].typ != 'rightBracket':
            #print "Member"
            #print tokens[0]
            x = doParseCoqExpr(tokens,0,[[CoqLex.Token('semicolon',';',0,0)]])
            tokens = x[1]
            #print "After"
            #print tokens[0]
            lens.append(len(ttq)-len(tokens))
            if len(tokens)==0 or (tokens[0].typ != 'rightBracket' and tokens[0].typ != 'semicolon'):
                if (len(tokens) > 0):
                    print tokens[0]
                raise ParseError("Illegal list construct", tokens)
            ll.append(x[0])
            if tokens[0].typ=='semicolon':
                tokens = tokens[1:]
        if len(ll)==0:
            res = CoqNameExpr(ttq[0:2],["nil"])
        else:
            s = len(ttq)-len(tokens)
            res = CoqNameExpr(ttq[s::s+1],["nil"])
            i = len(ll)-1
            while (i > -1):
                if i==0:
                    b = 0
                else:
                    b = lens[i-1]+1
                res1 = CoqApplExpr(ttq[b:lens[i]],CoqNameExpr(ttq[b:lens[i]],["Cons"]),ll[i])
                res = CoqApplExpr(ttq[b:s],res1,res)
                i = i - 1
        #print "Done parsing list"
        #print tokens[0]
        rlevel = 1000
        tokens = tokens[1:]
    elif tokens[0].typ=='questionMark' and tokens[1].typ=='NUMBER':
        #print spaces(indent)+"DO questionMark"
        res = CoqQuestionNameExpr(tokens[0:2],tokens[1].value)
        tokens = tokens[2:]
        rlevel = 1000
    elif tokens[0].typ=='questionMark' and tokens[1].typ=='ID':
        #print spaces(indent)+"DO questionMark"
        res = CoqQuestionNameExpr(tokens[0:2],tokens[1].value)
        tokens = tokens[2:]
        rlevel = 1000
    elif tokens[0].typ=='ID' or tokens[0].typ=='Context':
        ttt = tokens
        #print spaces(indent)+"DO ID"
        name = [tokens[0].value]
        tokens = tokens[1:]
        while (len(tokens)>1 and tokens[0].typ=='period' and tokens[1].typ=='ID' and tokens[0].line==tokens[1].line and tokens[0].column+1==tokens[1].column):
            name.append(tokens[1].value)
            tokens = tokens[2:] 
        res = CoqNameExpr(ttt[0:len(ttt)-len(tokens)],name)
        rlevel = 1000
    elif tokens[0].typ=='QUOTATION':
        #print spaces(indent)+"DO QUOTATION"
        res = CoqQuotationExpr(tokens[0:1],tokens[0].value[1:len(tokens[0].value)-1])
        tokens = tokens[1:]
        rlevel = 1000
    elif tokens[0].typ=='NUMBER':
        #print spaces(indent)+"DO NUMBER"
        res = CoqNumberExpr(tokens[0:1],int(tokens[0].value))
        tokens = tokens[1:]
        rlevel = 1000
    elif tokens[0].typ=='_':
        #print spaces(indent)+"DO _"
        res = CoqUnderscoreExpr(tokens[0:1])
        tokens = tokens[1:]
        rlevel = 1000
    elif len(tokens)>1 and tokens[0].typ=='leftBrace' and tokens[1].typ=='bar':
        ttt = tokens = tokens[2:]
        maps = []
        while len(tokens)>1 and tokens[0].typ=='ID' and tokens[1].typ=='colonEqual':
            v = tokens[0].value
            x = doParseCoqExpr(tokens[2:],0,[[CoqLex.Token('semicolon',';',0,0)]])
            tokens = x[1]
            maps.append((v,x[0]))
            print "MAP"
            print v
            print x[0]
            if tokens[0].typ=='semicolon':
                tokens = tokens[1:]
            print tokens[0]
        if tokens[0].typ != 'bar' or tokens[1].typ !='rightBrace':
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse CoqExpr",tokens)
        tokens = tokens[2:]
        print "DONE"
        res = CoqRecordExpr(ttt[0:len(ttt)-len(tokens)],maps)
        print res
        rlevel = 1000
    elif tokens[0].typ=='leftBrace':
        ttt = tokens
        #print "Parsing paren"
        #print tokens[1].typ
        #print spaces(indent)+"call 4"
        indent = indent+1
        x = doParseCoqExpr(tokens[1:],0,[])
        indent = indent-1
        tokens = x[1]
        res = x[0]
        if len(tokens) > 1 and tokens[0].typ=='colon':
            x = doParseCoqExpr(tokens[1:],0,[])
            typ = x[0]
            tokens = x[1]
        else:
            typ = None
        if len(tokens) > 1 and tokens[0].typ=='bar':
            x = doParseCoqExpr(tokens[1:],0,[])
            cond = x[0]
            tokens = x[1]
        else:
            cond = None
        if tokens[0].typ!='rightBrace':
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse CoqExpr",tokens)
        rlevel = 1000
        #print "Finishing paren"
        #print tokens[0]
        #print tokens[1]
        tokens = tokens[1:]
        res = CoqBraceExpr(ttt[0:len(ttt)-len(tokens)],res,typ,cond)
    elif tokens[0].typ=='leftParen':
        #print spaces(indent)+"DO leftParen"
        ttt = tokens
        #print "Parsing paren"
        #print tokens[1].typ
        #print spaces(indent)+"call 4"
        indent = indent+1
        x = doParseCoqExpr(tokens[1:],0,[])
        indent = indent-1
        tokens = x[1]
        res = x[0]
        if tokens[0].typ=='comma':
            terms = [res]
            while tokens[0].typ=='comma':
                #print spaces(indent)+"call 5"
                indent = indent+1
                x = doParseCoqExpr(tokens[1:],0,[])
                indent = indent-1
                tokens = x[1]
                terms.append(x[0])
            if tokens[0].typ!='rightParen':
                print tokens[0]
                print tokens[1]
                print tokens[2]
                print tokens[3]
                raise ParseError("Cannot parse CoqExpr",tokens)
            rlevel = 1000
            res = CoqTupleExpr(ttt[0:len(ttt)-len(tokens)+1],terms)
            #print "Finishing tuple"
        elif tokens[0].typ!='rightParen':
            print tokens[0]
            #print tokens[1]
            #print tokens[2]
            #print tokens[3]
            raise ParseError("Cannot parse CoqExpr",tokens)
        rlevel = 1000
        #print "Finishing paren"
        #print tokens[0]
        #print tokens[1]
        tokens = tokens[1:]
    else:
        print "DO error"
        print tokens[0]
        #print tokens[1]
        #print tokens[2]
        #print tokens[3]
        raise ParseError("Cannot parse CoqExpr",tokens)
    ct = True
    while ct and len(tokens) > 1 and not(matchBlock(tokens,blocks)):
        #print spaces(indent)+"Checking infixes"
        #print spaces(indent)+str(rlevel)
        #print spaces(indent)+str(level)
        #print t
        #print t[0]
        #print tokens[0]
        p = getInfixes(infixParses, tokens[0], rlevel, level)
        #print spaces(indent)+str(p)
        if (len(p)>0):
            tttt = tokens
            pp = getPrefixes(p,tokens[0],level)
            while (len(pp)>0):
                tokens = tokens[1:]
                p = pp
                pp = getPrefixes(p,tokens[0],level)
            pp = []
            for x in p:
                if len(x[1])==0 or type(x[1][0])!=types.StringType:
                    pp.append(x)
            x = pp[0]
            tail = x[1]
            terms = CoqApplExpr(t[0:len(t)-len(tokens)],CoqNameExpr(tttt[0:len(tttt)-len(tokens)],[x[2]]),res)
            while (len(tail)>0):
                #print spaces(indent)+"call 6"
                indent = indent+1
                xx = doParseCoqExpr(tokens,tail[0],blocks)
                indent = indent-1
                tail = tail[1:]
                tokens = xx[1]
                if (terms==None):
                    terms = xx[0]
                else:
                    terms = CoqApplExpr(t[0:len(t)-len(tokens)],terms,xx[0])
                while len(tail)>0 and type(tail[0])==types.StringType:
                    if len(tokens)==0 or tokens[0].value!=tail[0]:
                        print tokens[0]
                        raise ParseError("Cannot parse CoqExpr",tokens)
                    tokens = tokens[1:]
                    tail = tail[1:]
            res = terms
            rlevel = x[0]
        else:
            if rlevel>=100 and level<100:
                if len(tokens)>0 and (tokens[0].typ=='leftParen' or tokens[0].typ=='ID' or tokens[0].typ=='NUMBER' or tokens[0].typ=='forall' or tokens[0].typ=='_' or tokens[0].typ=='questionMark' or tokens[0].typ=='OP' or tokens[0].typ=='match' or tokens[0].typ=='leftBrace' or tokens[0].typ=='leftBracket'):
                    try:
                        #print spaces(indent)+"call 7"
                        indent = indent+1
                        xx = doParseCoqExpr(tokens,100,blocks)
                        indent = indent-1
                        tokens = xx[1]
                        res = CoqApplExpr(t[0:len(t)-len(tokens)],res,xx[0])
                        rlevel = 100
                    except ParseError:
                        ct = False
                else:
                    ct = False
                #except ParseError as e:
                #    print "Trapped parse error"
                #    print e
                #    print e.tokens[0]
                #    print e.tokens[1]
                #    print e.tokens[2]
                #    print e.tokens[3]
                #    print "Done trap"
                #    ct = False
            else:
                ct = False
    #print spaces(indent)+"Returning"
    return (res,tokens,rlevel)

def parseCoqExpr(tokens,blocks):
    #print spaces(indent)+"Call 8"
    x = doParseCoqExpr(tokens,0,blocks)
    return (x[0],x[1])

def parseCoqExprOrStar(tokens,blocks):
    if len(tokens)>0 and tokens[0].value=='*':
        return (CoqStarExpr(tokens),tokens[1:])
    else:
        return parseCoqExpr(tokens,blocks)

# ****************************************************************************

class CoqLtacExpr(CoqParseObject):
    def __init__(self,tokens):
        CoqParseObject.__init__(self,tokens)
        self.subgoals = 0
        self.unfocused = 0
        self.result = ""
        self.old_result = None
        pass
    def getListRepr(self):
        return ["Ltac"]
    @classmethod
    def create(cls,l,tokens):
        return CoqLtacExpr(tokens)
    def __repr__(self):
        return "class CoqLtacExpr"
    def __coqstr__(self):
        return "<CoqLtacExpr>"

# ****************************************************************************

class CoqBadLtacExpr(CoqLtacExpr):
    def __init__(self,tokens):
        CoqLtacExpr.__init__(self,tokens)
    def getListRepr(self):
        return ["BadLtacExpr"]
    @classmethod
    def create(cls,l,tokens):
        return CoqBadLtacExpr(tokens)
    def __repr__(self):
        return "class CoqBadLtacExpr"
    def __coqstr__(self):
        if len(self.tokens)==0:
            return "Bad tactic"
        else:
            return "Unparsed: "+self.tokens[0].value

# ****************************************************************************

class CoqBraceLtacExpr(CoqLtacExpr):
    def __init__(self,tokens,el):
        CoqLtacExpr.__init__(self,tokens)
        self.expr_list = el
    def getListRepr(self):
        x = ["CoqBraceLtacExpr"]
        for e in self.expr_list:
            x.append(e)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqBraceLtacExpr(tokens,l[1:])
    def __repr__(self):
        return "class CoqBraceLtacExpr "+self.__coqstr__()
    def dependencies(self):
        x = []
        for v in self.expr_list:
            x = x+v.dependencies()
        return x
    def __coqstr__(self):
        x = "{ "
        for z in self.expr_list:
            x = x + z.__coqstr__() + ". "
        x = x + "}"
        return x

#def CoqBraceLtacExpr(CoqLtacExpr):
#    def __init__(self,tokens,l):
#        CoqLtacExpr.__init__(self,tokens)
#        self.tactics = l
#    def getListRepr(self):
#        return ["BadLtacExpr"]
#    @classmethod
#    def create(cls,l,tokens):
#        return CoqBadLtacExpr(tokens,l)
#    def __repr__(self):
#        return "class CoqBraceLtacExpr"
#    def __coqstr__(self):
#        l = "{ "
#        for x in self.tactics:
#            l = l + x.__coqstr__()+". "
#        l = l + " }"
#        return l

# ****************************************************************************

def parseCoqLtacExpr(tokens):
    print "parseCoqLtacExpr "+str(tokens[0])
    t = tokens
    try:
        if tokens[0].typ=='leftParen':
            ttt = tokens
            print "paren parse"
            x = parseCoqLtacExpr(tokens[1:])
            print "after paren parse"
            tokens = x[1]
            e = x[0]
            print tokens[0]
            if tokens[0].typ!='rightParen':
                print tokens[0]
                raise ParseError("Cannot parse CoqLtacExpr",tokens)
            tokens = tokens[1:]
            e.tokens = ttt[0:len(ttt)-len(tokens)]
            expr = e
            x = (expr,tokens)
        else:
            #print spaces(indent)+"parseCoqLtacExpr before tac"
            #print spaces(indent)+str(tokens[0])
            x = parseCoqLtacTacExpr(tokens)
            #print spaces(indent)+"parseCoqLtacExpr after tac"
            #print tokens[0]
            #print tokens[1]
            #print tokens[2]
            #print tokens[3]
            tokens = x[1]
            expr = x[0]
        #print spaces(indent)+"ParseCoqLtacExpr check"
        if tokens[0].typ=='barBar':
            x = parseCoqLtacExprOr(expr,tokens,0)
            tokens = x[1]
            expr = x[0]
        if (tokens[0].typ=='semicolon'):
            #print spaces(indent)+"LtacExpr tokens"
            #print tokens[0]
            #print tokens[1]
            #print tokens[2]
            #print tokens[3]
            #print t[0]
            #print t[1]
            #print t[2]
            #print t[3]
            x = parseCoqLtacExprConcat(expr,t,len(t)-len(tokens))
            print "end parseCoqLtacExpr "+str(x[1][0])
            return x
        elif (tokens[0].typ=='leftBracket'):
            x = parseCoqLtacExprSubConcat(expr,t,len(t)-len(tokens))
            tokens = x[1]
            expr = x[0]
            while tokens[0].typ=='semicolon':
                x = parsCoqLtacExprConcat(expr,len(t)-len(tokens))
                tokens = x[1]
                expr = x[0]
            if tokens[0].typ=='barBar':
                print "end2 parseCoqLtacExpr "+str(tokens[0])
                return parseCoqLtacExprOr(expr,tokens,0)
            else:
                print "end3 parseCoqLtacExpr "+str(tokens[0])
                return x
        else:
            print "end4 parseCoqLtacExpr "+str(tokens[0])
            return x
    except ParseError:
        print "Bad tactic parse"
        tokens = t
        print tokens[0]
        l = len(tokens)
        p = 0
        level = 0
        while p < len(tokens) and (tokens[p].typ!='period' or level > 0):
            if tokens[p].typ=='leftParen' or tokens[p].typ=='leftBracket' or tokens[p].typ=='leftBrace':
                level = level + 1
            if tokens[p].typ=='rightParen' or tokens[p].typ=='rightBracket' or tokens[p].typ=='rightBrace':
                level = level - 1
            p = p + 1
        print "p = "+str(p)
        return (CoqBadLtacExpr(tokens[0:p]),tokens[p:])

def parseCoqTacticCommand(tokens):
    tt = tokens
    if len(tokens) > 0 and tokens[0].typ=='leftBrace':
        tokens = tokens[1:]
        l = []
        while len(tokens) > 0 and tokens[0].typ!='rightBrace':
            x = parseCoqTacticCommand(tokens)
            if x[0]==None:
                exit(1)
            tokens = x[1]
            l.append(x[0])
            print "END BRACE LOOP CYCLE "+str(tokens[0])
        tokens = tokens[1:]
        return (CoqBraceLtacExpr(tt[0:len(tt)-len(tokens)],l),tokens)
    else:
        print "IN CYCLE"
        x = parseCoqLtacExpr(tokens)
        print "OUT CYCLE"
        tokens = x[1]
        if len(tokens)==0 or tokens[0].typ != 'period':
            raise ParseError("Bad CoqTacticCommand", tokens)
        x[0].tokens.append(tokens[0])
        tokens = tokens[1:]
        return (x[0],tokens)

class CoqLtacExprConcat(CoqLtacExpr):
    def __init__(self,tokens,el):
        CoqLtacExpr.__init__(self,tokens)
        self.expr_list = el
    def getListRepr(self):
        x = ["LtacConcat"]
        for e in self.expr_list:
            x.append(e)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqLtacExprConcat(tokens,l[1:])
    def __repr__(self):
        return "class CoqLtacExprConcat "+self.__coqstr__()
    def dependencies(self):
        x = []
        for v in self.expr_list:
            x = x+v.dependencies()
        return x
    def __coqstr__(self):
        x = ""
        asem = False
        for z in self.expr_list:
            if asem:
                x = x + "; "
            asem = True
            x = x + z.__coqstr__()
        return x

def parseCoqLtacExprConcat(expr,tokens,pos):
    #print spaces(indent)+"Parsing concat"
    #print spaces(indent)+str(tokens[0])
    #print spaces(indent)+str(tokens[1])
    l = []
    l.append(expr)
    t = tokens
    tokens = tokens[pos:]
    #print spaces(indent)+"parse concat"
    #print spaces(indent)+str(tokens[0])
    while (len(tokens)>0 and tokens[0].typ=='semicolon'):
        print "CYCLE"
        if (tokens[1].typ=='leftBracket'):
            #print spaces(indent)+"Case 1"
            #print spaces(indent)+str(tokens)
            #print "ParseCoqLtacExprSubConcat"
            #print tokens[0]
            #print t[0]
            #print len(tokens)
            #print len(t)
            #print pos
            if len(l)==1:
                e = l[0]
            else:
                e = CoqLtacExprConcat(t[0:len(t)-len(tokens)],l)
            x = parseCoqLtacExprSubConcat(e,t,1+len(t)-len(tokens))
            tokens = x[1]
            expr = x[0]
            #print spaces(indent)+"Case 1 done"
            if tokens[0].typ=='barBar':
                return parseCoqLtacExprOr(expr,tokens,0)
        else:
            print "CONCAT "+str(tokens[1])
            x = parseCoqLtacTacExpr(tokens[1:])
            tokens = x[1]
            print "ExprConcat "+str(tokens[0])
            expr = x[0]
            if tokens[0].typ=='barBar':
                x = parseCoqLtacExprOr(expr,tokens,0)
                tokens = x[1]
                expr = x[0]
            l.append(x[0])
    print "DONE"
    print tokens[0]
    #print spaces(indent)+"Done parsing concat"
    #print tokens[0]
    #print tokens[1]
    return (CoqLtacExprConcat(t[0:len(t)-len(tokens)],l),tokens)

class CoqLtacExprOr(CoqLtacExpr):
    def __init__(self,tokens,el):
        CoqLtacExpr.__init__(self,tokens)
        self.expr_list = el
    def getListRepr(self):
        x = ["LtacOr"]
        for e in self.expr_list:
            x.append(e)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqLtacExprOr(tokens,l[1:])
    def __repr__(self):
        return "class CoqLtacExprOr "+self.__coqstr__()
    def __coqstr__(self):
        x = ""
        asem = False
        for z in self.expr_list:
            if asem:
                x = x + " || "
            asem = True
            x = x + z.__coqstr__()
        return x

def parseCoqLtacExprOr(expr,tokens,pos):
    #print spaces(indent)+"Parsing or"
    #print spaces(indent)+str(tokens[0])
    #print spaces(indent)+str(tokens[1])
    l = []
    l.append(expr)
    t = tokens
    tokens = tokens[pos:]
    #print spaces(indent)+"parse or"
    #print spaces(indent)+str(tokens[0])
    while (len(tokens)>0 and tokens[0].typ=='barBar'):
        x = parseCoqLtacTacExpr(tokens[1:])
        tokens = x[1]
        expr = x[0]
        l.append(x[0])
    #print spaces(indent)+"Done parsing or"
    #print tokens[0]
    #print tokens[1]
    return (CoqLtacExprOr(t[0:len(t)-len(tokens)],l),tokens)

class CoqLtacExprSubConcat(CoqLtacExpr):
    def __init__(self,tokens,ex,el):
        #print spaces(indent)+"Tokens"
        #print spaces(indent)+str(tokens)
        CoqLtacExpr.__init__(self,tokens)
        self.expr = ex
        self.expr_list = el
    def getListRepr(self):
        x = ["LtacSubConcat",self.expr]
        for e in self.expr_list:
            x.append(e)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqLtacExprSubConcat(tokens,l[1],l[2:])
    def __repr__(self):
        return "class CoqLtacExprConcat "+self.__coqstr__()
    def __coqstr__(self):
        x = self.expr.__coqstr__() + "; ["
        asem = False
        for z in self.expr_list:
            if asem:
                x = x + "| "
            asem = True
            if z==None:
                x = x + " "
            else:
                x = x + z.__coqstr__()
        return x+"]"

def parseCoqLtacExprSubConcat(expr,tokens,pos):
    t = tokens
    tokens = tokens[pos:]
    if tokens[0].typ != 'leftBracket':
       raise ParseError("Cannot parse ExprSubConcat",tokens)
    l = []
    while (len(tokens)>1 and (tokens[0].typ=='leftBracket' or tokens[0].typ=='bar')):
        #print spaces(indent)+"Parsing subtactic"
        #print spaces(indent)+str(tokens[1])
        if tokens[1].typ=='bar' or tokens[1].typ=='rightBracket':
            tokens = tokens[1:]
            l.append(None)
        else:
            print "IN CYCLE2"
            x = parseCoqLtacExpr(tokens[1:])
            print "OUT CYCLE2"
            tokens = x[1]
            l.append(x[0])
    if (len(tokens)==0 or tokens[0].typ!='rightBracket'):
        print tokens[0]
        print tokens[1]
        raise ParseError("Cannot parse ExprSubConcat",tokens)
    #print spaces(indent)+"Done parsing subConcat"
    #print spaces(indent)+str(t)
    return (CoqLtacExprSubConcat(t[0:len(t)-len(tokens)+1],expr,l),tokens[1:])

def parseCoqLtacTacExpr(tokens):
    if tokens[0].typ=='leftParen':
        #print spaces(indent)+"Before paren"
        #print spaces(indent)+str(tokens[0])
        print "IN CYCLE3"
        x = parseCoqLtacExpr(tokens[1:])
        print "OUT CYCLE3"
        #print spaces(indent)+"After paren"
        ot = tokens
        tokens = x[1]
        r = x[0]
        if tokens[0].typ!='rightParen':
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise parseError("Cannot parse coqLtacTacExpr",tokens)
        tokens = tokens[1:]
        r.tokens = ot[0:len(r.tokens)+2]
        return (r,tokens)
    elif (len(tokens)>1 and tokens[0].value=='try'):
        return parseCoqLtacTryExpr(tokens)
    elif (len(tokens)>1 and tokens[0].value=='progress'):
        return parseCoqLtacProgressExpr(tokens)
    elif (len(tokens)>1 and tokens[0].value=='repeat'):
        return parseCoqLtacRepeatExpr(tokens)
    elif (len(tokens)>1 and tokens[0].value=='first'):
        return parseCoqLtacFirstExpr(tokens)
    elif (len(tokens)>1 and tokens[0].value=='solve'):
        return parseCoqLtacSolveExpr(tokens)
    elif (len(tokens)>1 and tokens[0].typ=='let'):
        return parseCoqLtacLetExpr(tokens)
    elif (len(tokens)>0 and tokens[0].typ=='ID' and tokens[0].value=='fresh'):
        return parseCoqLtacFreshExpr(tokens)
    elif (len(tokens)>1 and tokens[0].typ=='match' and (tokens[1].typ=='goal' or tokens[1].value=='reverse')):
        return parseCoqLtacMatchGoalExpr(tokens)
    return parseCoqTactic(tokens)
    #except ParseError(e,t):
    #    raise ParseError("Cannot parse CoqLtacTacExpr "+e,t)

class CoqMatchCpattern(CoqParseObject):
    def __init__(self,tokens):
        CoqParseRule.__init__(tokens)
    def getListRepr(self):
        return ["MatchCpattern"]
    @classmethod
    def create(cls,l,tokens):
        return CoqMatchCpattern(tokens)
    def __repr__(self):
        return "class CoqMatchCpattern"
    def __coqstr__(self):
        return "cpattern"

def parseCoqMatchCpattern(tokens):
    return parseCoqMatchWildcard(tokens)

class CoqMatchWildcard(CoqMatchCpattern):
    def __init__(self,tokens,i):
        CoqParseObject.__init__(self,tokens)
        self.id = i
    def getListRepr(self):
        return ["MatchWildcard"]
    @classmethod
    def create(cls,l,tokens):
        return CoqMatchWildcard(tokens)
    def __repr__(self):
        return "class CoqMatchWildcard "+self.id
    def __coqstr__(self):
        return self.id

def parseCoqMatchWildcard(tokens):
    if (len(tokens)>0 and (tokens[0].typ=='_' or tokens[0].typ=='WILDCARD')):
        return (CoqMatchWildcard(tokens[0:1],tokens[0].value),tokens[1:])
    raise ParseError("Cannot parse CoqMatchWildcard",tokens)

class CoqMatchGoalRule(CoqParseObject):
    def __init__(self,tokens,h,p,a):
        CoqParseObject.__init__(self,tokens)
        self.hyps = h
        self.pattern = p
        self.action = a
        pass
    def getListRepr(self):
        x = ["MatchGoalRule"]
        for h in self.hyps:
            x.append(h[0])
            x.append(h[1])
        x.append(p)
        x.append(a)
        return x
    @classmethod
    def create(cls,l,tokens):
        h = []
        for i in range(0,(len(l)-3)/2):
            h.append(l[i*2+1],l[i*2+2])
        return CoqMatchGoalRule(tokens,h,l[len(l)-2],l[len(l)-1])
    def __repr__(self):
        return "class CoqMatchGoalRule"
    def __coqstr__(self):
        s = ""
        if (len(self.hyps)>0):
            s = s+self.hyps[0][0]
            if self.hyps[0][1] != None:
                s = s + ": " + self.hyps[0][1].__coqstr__()
            pos = 1
            while (pos < len(self.hyps)):
                s = s + ", "
                s = s+self.hyps[pos][0]
                if self.hyps[pos][1] != None:
                    s = s + ": " + self.hyps[pos][1].__coqstr__()
                pos = pos + 1
        return s+" |- "+self.pattern.__coqstr__() + " => " + self.action.__coqstr__()

def parseCoqMatchGoalRule(tokens):
    t = tokens
    h = []
    needRbracket = False
    if (tokens[0].typ=='leftBracket'):
        tokens = tokens[1:]
        needRbracket = True
    if (tokens[0].typ=='barDash'):
        pass
    else:
        pa = True
        while (pa):
            print "PA"
            print tokens[0]
            print tokens[1]
            if (len(tokens)>1 and (tokens[0].typ=='ID' or tokens[0].typ=='_') and tokens[1].typ=='colon'):
                x = parseCoqExpr(tokens[2:],[])
                h.append((tokens[0].value,x[0]))
                tokens = x[1]
                if (tokens[0].typ=='barDash' or tokens[0].typ=='equalGreater'):
                    pa = False
                elif (tokens[0].typ!='comma'):
                    print tokens[0]
                    print tokens[1]
                    print tokens[2]
                    print tokens[3]
                    raise ParseError("Cannot parse CoqMatchGoalRule",t)
                else:
                    tokens = tokens[1:]
            elif (len(tokens)>0 and (tokens[0].typ=='ID' or tokens[0].typ=='_')):
                h.append((tokens[0].value,None))
                tokens = tokens[1:]
                if (tokens[0].typ=='barDash' or tokens[0].typ=='equalGreater'):
                    pa = False
                elif (tokens[0].typ!='comma' or tokens[0].typ):
                    print tokens[0]
                    print tokens[1]
                    print tokens[2]
                    print tokens[3]
                    raise ParseError("Cannot parse CoqMatchGoalRule",t)
                else:
                    tokens = tokens[1:]
            else:
                print tokens[0]
                print tokens[1]
                print tokens[2]
                print tokens[3]
                raise ParseError("Cannot parse CoqMatchGoalRule",t)
    print tokens[0]
    if tokens[0].typ=='barDash':
        tokens = tokens[1:]
        x = parseCoqExpr(tokens,[])
        p = x[0]
        tokens = x[1]
    else:
        p = CoqNameExpr(tokens[0:1],h[len(h)-1][0])
        h = h[0:len(h)-1]
    if needRbracket:
        if tokens[0].typ != 'rightBracket':
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse CoqMatchGoalRule",t)
        tokens = tokens[1:]
    if (tokens[0].typ != 'equalGreater'):
        print tokens[0]
        raise ParseError("Cannot parse CoqMatchGoalRule",t)
    tokens = tokens[1:]
    print "IN CYCLE4"
    x = parseCoqLtacExpr(tokens)
    print "OUT CYCLE4"
    a = x[0]
    tokens = x[1]
    return (CoqMatchGoalRule(t[0:len(t)-len(tokens)],h,p,a),tokens)

class CoqLtacFreshExpr(CoqLtacExpr):
    def __init__(self,tokens,n):
        CoqLtacExpr.__init__(self,tokens)
        self.name = n
    def getListRepr(self):
        x = ["MatchFreshExpr"]
        if self.name!=None:
            x.append(self.name)
        return x
    @classmethod
    def create(cls,l,tokens):
        x = None
        if len(l)>1:
            x = l[1]
        return CoqLtacFreshExpr(tokens,x)
    def __repr__(self):
        return "class CoqLtacFreshExpr "+self.name
    def __coqstr__(self):
        if self.name==None:
            return "fresh"
        else:
            return "fresh "+self.name

def parseCoqLtacFreshExpr(tokens):
    t = tokens
    if (tokens[0].typ!='ID' or tokens[0].value!='fresh'):
        raise ParseError("cannot parse CoqLtacFreshExpr",tokens)
    tokens = tokens[1:]
    if tokens[0].typ=='QUOTATION':
        n = tokens[0].value[1:len(tokens)-1]
        tokens = tokens[1:]
    else:
        n = None
    return (CoqLtacFreshExpr(tokens[0:len(t)-len(tokens)],n),tokens)

class CoqLtacLetExpr(CoqLtacExpr):
    def __init__(self,tokens,r,lc,a):
        CoqLtacExpr.__init__(self,tokens)
        self.is_rec = r
        self.let_clauses = lc
        self.atom = a
    def getListRepr(self):
        x = ["LtacLet",self.is_rec]
        if self.name!=None:
            x.append(self.name)
        for l in self.let_clauses:
            x.append(l[0])
            q = ["params"]
            for z in l[1]:
                q.append(z)
            x.append(q)
            x.append(l[2])
        x.append(self.atom)
        return x
    @classmethod
    def create(cls,l,tokens):
        r = l[0]
        lc = []
        for i in range(0,len(l)/3-1):
            n = l[i*3+1]
            p = l[i*3+2][1:]
            v = l[i*3+3]
            lc = (n,p,v)
        a = l[len(l)-1]
        return CoqLtacLetExpr(tokens,r,lc,a)
    def __repr__(self):
        return "class CoqLtacLetExpr"
    def __coqstr__(self):
        r = "let "
        if (self.is_rec):
           r = "let rec "
        pw = False
        for x in self.let_clauses:
            if pw:
                r = r+ "with "
            r = r+x[0]+" "
            for z in x[1]:
                r = r + z+" "
            r = r + ":= "
            r = r + x[2].__coqstr__()
        return r+" in "+self.atom.__coqstr__()

def parseCoqLtacLetExpr(tokens):
    if (tokens[0].typ!='let'):
        raise ParseError("cannot parse CoqLtacLetExpr",tokens)
    lc = []
    tokens = tokens[1:]
    if (tokens[0].typ=='ID' and tokens[0].value=='rec'):
        tokens = tokens[1:]
        r = True
    else:
        r = False
    while (len(tokens) > 2 and tokens[0].typ != 'in'):
        n = tokens[0].value
        if (tokens[0].typ!='ID'):
            raise ParseError("cannot parse CoqLtacLetExpr",tokens)
        pos = 1
        p = []
        while (pos < len(tokens) and tokens[pos].typ=='ID'):
            p.append(tokens[pos].value)
            pos = pos+1
        if (len(tokens)<pos+3 or tokens[pos].typ!='colonEqual'):
            raise ParseError("cannot parse CoqLtacLetExpr",tokens)
        print "IN CYCLE5"
        x = parseCoqLtacExpr(tokens[pos+1:])
        print "OUT CYCLE5"
        tokens = x[1]
        lc.append((n,p,x[0]))
        if (len(tokens)<3 or (tokens[0].typ!='with' and tokens[0].typ!='in')):
            raise ParseError("cannot parse CoqLtacLetExpr",tokens)
        if (tokens[0].typ=='with'):
            tokens = tokens[1:]
    tokens = tokens[1:]
    x = parseCoqLtacExpr(tokens)
    return (CoqLtacLetExpr(tokens[0:len(tokens)-len(x[1])],r,lc,x[0]),x[1])

class CoqLtacFirstExpr(CoqLtacExpr):
    def __init__(self,tokens,el):
        CoqLtacExpr.__init__(self,tokens)
        self.exprs = el
    def getListRepr(self):
        x = "LtacFirst"
        for e in self.exprs:
            x.append(e)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqLtacFirstExpr(tokens,l[1:])
    def __repr__(self):
        return "class CoqLtacFirstExpr"
    def __coqstr__(self):
        x = "first [ "
        abar = False
        for e in self.exprs:
            if abar:
                x = x+ " | "
            abar = True
            x = x + e.__coqstr__()
        return x + " ]"

def parseCoqLtacFirstExpr(tokens):
    t = tokens
    if (len(tokens)<3 or tokens[0].value!='first' or tokens[1].typ!='leftBracket'):
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("cannot parse CoqLtacFirstExpr",tokens)
    x = parseCoqLtacExpr(tokens[2:])
    tokens = x[1]
    l = []
    l.append(x[0])
    while (tokens[0].typ!='rightBracket'):
        x = parseCoqLtacExpr(tokens[1:])
        l.append(x[0])
        tokens = x[1]
        if (len(tokens)<2 or (tokens[0].typ!='bar' and tokens[0].typ!='rightBracket')):
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse CoqLtacFirstExpr",tokens)
    tokens = tokens[1:]
    return (CoqLtacFirstExpr(tokens[0:len(t)-len(tokens)+1],l),tokens)

class CoqLtacSolveExpr(CoqLtacExpr):
    def __init__(self,tokens,el):
        CoqLtacExpr.__init__(self,tokens)
        self.exprs = el
    def getListRepr(self):
        x = "LtacSolve"
        for e in self.exprs:
            x.append(e)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqLtacFirstExpr(tokens,l[1:])
    def __repr__(self):
        return "class CoqLtacSolveExpr"
    def __coqstr__(self):
        x = "solve [ "
        abar = False
        for e in self.exprs:
            if abar:
                x = x+ " | "
            abar = True
            x = x + e.__coqstr__()
        return x + " ]"

def parseCoqLtacSolveExpr(tokens):
    t = tokens
    if (len(tokens)<3 or tokens[0].value!='solve' or tokens[1].typ!='leftBracket'):
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("cannot parse CoqLtacSolveExpr",tokens)
    x = parseCoqLtacExpr(tokens[2:])
    tokens = x[1]
    l = []
    l.append(x[0])
    while (tokens[0].typ!='rightBracket'):
        x = parseCoqLtacExpr(tokens[1:])
        l.append(x[0])
        tokens = x[1]
        if (len(tokens)<2 or (tokens[0].typ!='bar' and tokens[0].typ!='rightBracket')):
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse CoqLtacSolveExpr",tokens)
    tokens = tokens[1:]
    return (CoqLtacSolveExpr(tokens[0:len(t)-len(tokens)+1],l),tokens)

class CoqLtacRepeatExpr(CoqLtacExpr):
    def __init__(self,tokens,e):
        CoqLtacExpr.__init__(self,tokens)
        self.expr = e 
    def getListRepr(self):
        return ["LtacRepeat",e]
    @classmethod
    def create(cls,l,tokens):
        return CoqLtacRepeatExpr(tokens,l[1])
    def __repr__(self):
        return "class CoqLtacRepeatExpr"
    def __coqstr__(self):
        return "repeat "+self.expr.__coqstr__()

def parseCoqLtacRepeatExpr(tokens):
    if (tokens[0].value!='repeat'):
        raise ParseError("cannot parse CoqLtacRepeatExpr",tokens)
    x = parseCoqLtacTacExpr(tokens[1:])
    return (CoqLtacRepeatExpr(tokens[0:len(tokens)-len(x[1])],x[0]),x[1])

class CoqLtacProgressExpr(CoqLtacExpr):
    def __init__(self,tokens,e):
        CoqLtacExpr.__init__(self,tokens)
        self.expr = e 
    def getListRepr(self):
        return ["LtacProgress",e]
    @classmethod
    def create(cls,l,tokens):
        return CoqLtacProgressExpr(tokens,l[1])
    def __repr__(self):
        return "class CoqLtacProgressExpr"
    def __coqstr__(self):
        return "progress "+self.expr.__coqstr__()

def parseCoqLtacProgressExpr(tokens):
    if (tokens[0].value!='progress'):
        raise ParseError("cannot parse CoqLtacProgressExpr",tokens)
    x = parseCoqLtacTacExpr(tokens[1:])
    return (CoqLtacProgressExpr(tokens[0:len(tokens)-len(x[1])],x[0]),x[1])

class CoqLtacTryExpr(CoqLtacExpr):
    def __init__(self,tokens,e):
        CoqLtacExpr.__init__(self,tokens)
        self.expr = e 
    def getListRepr(self):
        return ["LtacTry",e]
    @classmethod
    def create(cls,l,tokens):
        return CoqLtacTryExpr(tokens,l[1])
    def __repr__(self):
        return "class CoqLtacTryExpr"
    def __coqstr__(self):
        return "try "+self.expr.__coqstr__()

def parseCoqLtacTryExpr(tokens):
    if (tokens[0].value!='try'):
        raise ParseError("cannot parse CoqLtacTryExpr",tokens)
    x = parseCoqLtacTacExpr(tokens[1:])
    return (CoqLtacTryExpr(tokens[0:len(tokens)-len(x[1])],x[0]),x[1])

def prules(r):
    if (len(r)==0):
        return ""
    x = r[0].__coqstr__()
    for i in range(1,len(r)):
        x = x + " | " + r[i].__coqstr__()
    return x

class CoqLtacMatchGoalExpr(CoqLtacExpr):
    def __init__(self,tokens,d,r):
        CoqLtacExpr.__init__(self,tokens)
        self.direction = d
        self.rules = r
        pass
    def dependencies(self):
       d = []
       for x in self.rules:
           d = d + x.dependencies()
       return d
    def getListRepr(self):
        x = ["LtacMatchGoal",self.direction]
        for r in self.rules:
            x.append(r)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqLtacMatchGoalExpr(tokens,l[1],l[2:])
    def __repr__(self):
        if (self.direction):
            x = "reverse "
        else:
            x = ""
        return "class CoqMatchGoalExpr"
    def __coqstr__(self):
        if (self.direction):
            x = "reverse "
        else:
            x = ""
        return "match "+x+"goal with\n"+prules(self.rules)+"\nend"

def parseCoqLtacMatchGoalExpr(tokens):
    t = tokens
    if (tokens[1].value=='reverse' and tokens[2].typ=='goal'):
        d =True
        pos = 3
    elif (tokens[1].typ=='goal'):
        d = False
        pos = 2
    tokens = t[pos:]
    if (tokens[0].typ=='with'):
        tokens = tokens[1:]
    else:
        raise ParseError("cannot parse CoqLtacMatchGoalExpr",tokens)
    r = []
    while (len(tokens)>1 and tokens[0].typ=='bar'):
        x = parseCoqMatchGoalRule(tokens[1:])
        r.append(x[0])
        tokens = x[1]
    if (len(tokens)==0 or tokens[0].typ!='end'):
        print tokens[0]
        print tokens[1]
        print tokens[2]
        raise ParseError("CoqLtacMatchGoalExpr",tokens)
    tokens = tokens[1:]
    return (CoqLtacMatchGoalExpr(t[0:len(t)-len(tokens)-1],d,r),tokens)

# ****************************************************************************

class CoqTactic(CoqLtacExpr):
    def __init__(self,tokens):
        CoqLtacExpr.__init__(self,tokens)
        self.result = ""
        self.old_result = None
        #self.currentCoqCycle = -1
        self.unfocused = 0
        self.subgoals =0
    def getListRepr(self):
        return ["Tactic"]
    @classmethod
    def dependencies(self):
        return []
    def create(cls,l,tokens):
        return CoqTactic(tokens)
    def __repr__(self):
        return "class CoqTactic"
    def __coqstr__(self):
        return "<CoqTactic>"
    def getExpressions(self):
        return []
    def updateWithExpressions(self,l):
        return self

def parseCoqTactic(tokens):
    print spaces(indent)+"PARSE COQ TACTIC"
    print spaces(indent)+str(tokens[0])
    if (len(tokens)>3 and tokens[0].typ=='move'):
        return parseCoqMoveTactic(tokens)
    elif (len(tokens)>3 and tokens[0].typ=='pose' and
          tokens[1].typ=='proof'):
        return parseCoqPoseProofTactic(tokens)
    elif (len(tokens)>2 and tokens[0].typ=='pose'):
        return parseCoqPoseTactic(tokens)
    elif (len(tokens)>3 and tokens[0].value=='assert'):
        return parseCoqAssertTactic(tokens)
    elif (len(tokens)>3 and (tokens[0].value=='apply' or tokens[0].value=='eapply')):
        return parseCoqApplyTactic(tokens)
    elif (len(tokens)>3 and tokens[0].value=='destruct'):
        return parseCoqDestructTactic(tokens)
    elif (len(tokens)>3 and tokens[0].value=='remember'):
        return parseCoqRememberTactic(tokens)
    elif (len(tokens)>3 and tokens[0].value=='exists'):
        return parseCoqExistsTactic(tokens)
    elif (len(tokens)>3 and tokens[0].value=='instantiate'):
        return parseCoqInstantiateTactic(tokens)
    elif (len(tokens)>3 and tokens[0].value=='constructor'):
        return parseCoqConstructorTactic(tokens)
    elif (len(tokens)>3 and tokens[0].value=='set'):
        return parseCoqSetTactic(tokens)
    elif (len(tokens)>1 and tokens[0].value=='fail'):
        return parseCoqFailTactic(tokens)
    elif (len(tokens)>1 and tokens[0].value=='Focus'):
        return parseCoqFocusTactic(tokens)
    elif (len(tokens)>1 and tokens[0].value=='clear'):
        return parseCoqClearTactic(tokens)
    elif (len(tokens)>1 and tokens[0].value=='intros'):
        return parseCoqIntrosTactic(tokens)
    elif (len(tokens)>1 and (tokens[0].value=='rewrite' or tokens[0].value=='erewrite')):
        return parseCoqRewriteTactic(tokens)
    elif (len(tokens)>2 and tokens[0].typ=='NUMBER' and tokens[1].typ=='colon'):
        return parseCoqGoalNumTactic(tokens)
    elif (len(tokens)>1 and tokens[0].value=='unfold'):
        return parseCoqUnfoldTactic(tokens)
    elif (len(tokens)>1 and tokens[0].typ=='Ltac'):
        x = parseCoqLtac(tokens)
        res = x[0]
        tokens = [res.tokens[len(res.tokens)-1]]+x[1]
        res.tokens = res.tokens[0:len(res.tokens)-1]
        return (res,tokens)
    elif (len(tokens)>1 and tokens[0].value=='fold'):
        return parseCoqFoldTactic(tokens)
    elif (len(tokens)>1 and tokens[0].value=='simpl'):
        return parseCoqSimplTactic(tokens)
    elif (len(tokens)>1 and tokens[0].value=='injection'):
        return parseCoqInjectionTactic(tokens)
    elif (len(tokens)>1 and tokens[0].value=='Compute'):
        return parseCoqComputeTactic(tokens)
    elif (len(tokens)>1 and tokens[0].value=='Check'):
        return parseCoqComputeTactic(tokens)
    elif (len(tokens)>1 and tokens[0].value=='reflexivity'):
        return parseCoqReflexivityTactic(tokens)
    elif (len(tokens)>1 and tokens[0].typ=='Definition'):
        x = parseCoqDefinition(tokens)
        res = x[0]
        tokens = [res.tokens[len(res.tokens)-1]]+x[1]
        res.tokens = res.tokens[0:len(res.tokens)-1]
        return (res,tokens)
    elif (len(tokens)>1 and tokens[0].typ=='About'):
        x = parseCoqAbout(tokens)
        res = x[0]
        tokens = [res.tokens[len(res.tokens)-1]]+x[1]
        res.tokens = res.tokens[0:len(res.tokens)-1]
        return (res,tokens)
    elif (len(tokens)>1 and tokens[0].typ=='Axiom'):
        x = parseCoqAxiom(tokens)
        res = x[0]
        tokens = [res.tokens[len(res.tokens)-1]]+x[1]
        res.tokens = res.tokens[0:len(res.tokens)-1]
        return (res,tokens)
    elif (len(tokens)>1 and (tokens[0].typ=='Theorem' or tokens[0].typ=='Lemma' or tokens[0].typ=='Example')):
        x = parseCoqTheorem(tokens)
        res = x[0]
        tokens = [res.tokens[len(res.tokens)-1]]+x[1]
        res.tokens = res.tokens[0:len(res.tokens)-1]
        return (res,tokens)
    elif (len(tokens)>1 and tokens[0].typ=='ID' or tokens[0].typ=='Opaque'):
        return parseCoqApplyNotationTactic(tokens)
    else:
        try:
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
        except IndexError:
            pass
        raise ParseError('Cannot parse CoqTactic',tokens)

# ****************************************************************************

class CoqPlaceHolderTactic(CoqTactic):
    def __init__(self,tokens):
        CoqTactic.__init__(self,tokens)
    def __coqstr__(self):
        return "<CoqPlaceHolderTactic>"

# ****************************************************************************

class CoqGoalNumTactic(CoqTactic):
    def __init__(self,tokens,n,t):
        CoqTactic.__init__(self,tokens)
        self.number = n
        self.tactic = t
    def dependencies(self):
        return self.tactic.dependencies()
    def getListRepr(self):
        return ["GoalNumTactic",self.number,self.tactic]
    @classmethod
    def create(cls,l,tokens):
        return CoqGoalNumTactic(tokens,l[1],l[2])
    def __repr__(self):
        return "class CoqGoalNumTactic "+str(self.number)+":"+self.tactic.__coqstr__()
    def __coqstr__(self):
        return str(self.number)+":"+self.tactic.__coqstr__()

def parseCoqGoalNumTactic(tokens):
    tt = tokens
    if (len(tokens)<3 or tokens[0].typ!='NUMBER' or tokens[1].typ != 'colon'):
        raise ParseError(tokens,"Cannot parse GoalNum")
    x = parseCoqLtacExpr(tokens[2:])
    tokens = x[1]
    return (CoqGoalNumTactic(tt[0:len(tt)-len(tokens)],int(tt[0].value),x[0]),tokens)

class CoqAssertTactic(CoqTactic):
    def __init__(self,tokens,i,e,p,t):
        CoqTactic.__init__(self,tokens)
        self.id = i
        self.exp = e
        self.intro_pattern = p
        self.tactic = t
    def dependencies(self):
        d = self.exp.dependencies()
        if (self.tactic!=None):
            d = d+self.tactic.dependencies()
        return d
    def getListRepr(self):
        return ["AssertTactic",self.id,self.exp,self.intro_pattern,self.tactic]
    @classmethod
    def create(cls,l,tokens):
        return CoqAssertTactic(tokens,l[1],l[2],l[3],l[4])
    def __repr__(self):
        return "class CoqAssertTactic "+str(self.id)+" "+self.exp.__coqstr__()
    def __coqstr__(self):
        x = "assert ("
        if (self.id!=None):
            x = x + self.id + " : "
        x = x + self.exp.__coqstr__() + ")"
        if (self.intro_pattern != None):
            x = x + " as " + self.intro_pattern.__coqstr__()
        if (self.tactic != None):
            x = x + " by " + self.tactic.__coqstr__()
        return x

def parseCoqAssertTactic(tokens):
    tt = tokens
    if (len(tokens)<4 or tokens[0].typ!='ID' or tokens[0].value!='assert'):
        raise ParseError(tokens,"Cannot parse Assert")
    id = None
    if tokens[1].typ=='leftParen':
        pos = 2
        has_paren = True
    else:
        has_paren = False
        pos = 1
    if (has_paren and tokens[pos].typ=='ID' and tokens[pos+1].typ=='colon'):
        id = tokens[2].value
        pos = 4
    x = parseCoqExpr(tokens[pos:],[])
    tokens = x[1]
    e = x[0]
    print "HAS PAREN"
    print has_paren
    if has_paren:
        if (len(tokens)<1 or tokens[0].typ != 'rightParen'):
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError(tokens,"Cannot parse Assert")
        tokens = tokens[1:]
    p = None
    print "Done assert"
    print tokens[0]
    if (len(tokens)>1 and tokens[0].typ=='as'):
        p = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        tokens = p[1]
        p = p[0]
    t = None
    if (len(tokens)>1 and tokens[0].typ=='by'):
        print "Parsing by"
        print tokens[0]
        print tokens[1]
        t = parseCoqLtacExpr(tokens[1:])
        tokens = t[1]
        t = t[0]
    return (CoqAssertTactic(tt[0:len(tt)-len(tokens)],id,e,p,t),tokens)

class CoqPoseProofTactic(CoqTactic):
    def __init__(self,tokens,e,h):
        CoqTactic.__init__(self,tokens)
        self.assertion = e
        self.name = h
    def dependencies(self):
        return self.assertion.dependencies()
    def getListRepr(self):
        return ["PoseProof",self.assertion.getListRepr(),self.name]
    @classmethod
    def create(cls,l,tokens):
        return CoqPoseProof(tokens,l[1],l[2])
    def __repr__(self):
        return "class CoqPoseProof "+self.name
    def __coqstr__(self):
        x = "pose proof "+self.assertion.__coqstr__()
        if self.name != None:
            x = x + " as "+self.name.__coqstr__()
        return x

def parseCoqPoseProofTactic(tokens):
    tt = tokens
    if (len(tokens)<4 or tokens[0].typ!='pose' or
        tokens[1].typ != 'proof'):
        raise ParseError(tokens,"Cannot parse pose proof")
    id = None
    pos = 2
    x = parseCoqExpr(tokens[pos:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
    tokens = x[1]
    e = x[0]
    p = None
    if (len(tokens)>1 and tokens[0].typ=='as'):
        p = parseCoqIntroPattern(tokens[1:])
        tokens = p[1]
        p = p[0]
    return (CoqPoseProofTactic(tt[0:len(tt)-len(tokens)],e,p),tokens)

class CoqPoseTactic(CoqTactic):
    def __init__(self,tokens,e,h):
        CoqTactic.__init__(self,tokens)
        self.assertion = e
        self.name = h
    def dependencies(self):
        return self.assertion.dependencies()
    def getListRepr(self):
        return ["Pose",self.assertion.getListRepr(),self.name]
    @classmethod
    def create(cls,l,tokens):
        return CoqPose(tokens,l[1],l[2])
    def __repr__(self):
        return "class CoqPose "+self.name
    def __coqstr__(self):
        x = "pose "+self.assertion.__coqstr__()
        if self.name != None:
            x = x + " as "+self.name.__coqstr__()
        return x

def parseCoqPoseTactic(tokens):
    tt = tokens
    if (len(tokens)<3 or tokens[0].typ!='pose'):
        raise ParseError(tokens,"Cannot parse pose")
    id = None
    pos = 1
    x = parseCoqExpr(tokens[pos:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
    tokens = x[1]
    e = x[0]
    p = None
    if (len(tokens)>1 and tokens[0].typ=='as'):
        p = parseCoqIntroPattern(tokens[1:])
        tokens = p[1]
        p = p[0]
    return (CoqPoseTactic(tt[0:len(tt)-len(tokens)],e,p),tokens)

class CoqSetTactic(CoqTactic):
    def __init__(self,tokens,i,e):
        CoqTactic.__init__(self,tokens)
        self.id = i
        self.exp = e
    def dependencies(self):
        return self.exp.dependencies()
    def getListRepr(self):
        return ["SetTactic",self.id,self.exp]
    @classmethod
    def definedNames(self):
        return []
    def create(cls,l,tokens):
        return CoqSetTactic(tokens,l[1],l[2])
    def __repr__(self):
        return "class CoqSetTactic "+self.id+" "+self.exp.__coqstr__()
    def __coqstr__(self):
        return "set ("+self.id+" := "+ self.exp.__coqstr__()+")"

def parseCoqSetTactic(tokens):
    tt = tokens
    if (len(tokens)<4 or tokens[0].typ!='ID' or tokens[0].value!='set' or
        tokens[1].typ != 'leftParen' or tokens[2].typ!='ID' or
        tokens[3].typ !='colonEqual'):
        raise ParseError(tokens,"Cannot parse Set")
    id = None
    id = tokens[2].value
    x = parseCoqExpr(tokens[4:],[])
    tokens = x[1]
    e = x[0]
    if (len(tokens)<1 or tokens[0].typ != 'rightParen'):
        raise ParseError(tokens,"Cannot parse Set")
    return (CoqSetTactic(tt[0:len(tt)-len(tokens)],id,e),tokens[1:])

class CoqRewriteTactic(CoqTactic):
    def __init__(self,tokens,t):
        CoqTactic.__init__(self,tokens)
        self.terms = t
        #self.inSpec = iSpec
        #self.bySpec = bSpec
        #self.occurencesSpec = oSpec
        #self.wit = wSpec
    def dependencies(self):
        d = []
        for x in self.terms:
            d = d+x[0].dependencies()
        if self.inSpec!=None:
            d = d+self.inSpec.dependencies()
        if self.bySpec!=None:
            d = d+self.bySpec.dependencies()
        if self.wit!=None:
            for x in self.wit:
                z = x[1].dependencies()
                d = d+x[1].dependencies()
        return d
    def getListRepr(self):
        return ["RewriteTactic",self.terms]
    @classmethod
    def create(cls,l,tokens):
        return CoqRewriteTactic(tokens,l[1])
    def __repr__(self):
        return "class CoqRewriteTactic"
    def __coqstr__(self):
        x = "rewrite"
        opm = False
        for rew in self.terms:
            if opm:
               x = x + ", "
            opm = True
            pcomma = False
            for t in rew[0]:
                if pcomma:
                    x = x + ", "
                pcomma = True
                if t[1]:
                    x = x + " <-"
                x = x + " " + t[0].__coqstr__()
            if rew[3]!=None:
                x = x + " with "
                for z in rew[3]:
                    x = x+" ("+z[0]+" := " + z[1].__coqstr__()+")"
            if rew[1]!=None:
                x = x+" in "+rew[1].__coqstr__()
            if rew[2]!=None:
                x = x+" by "+rew[2].__coqstr__()
        return x

def parseCoqRewriteTactic(tokens):
    tt = tokens
    if (len(tokens)<3 or tokens[0].typ!='ID'):
        raise ParseError(tokens,"Cannot parse CoqRewriteTactic")
    neg = False
    tlist = []
    while tokens[0].value=='rewrite' or tokens[0].value=='erewrite' or tokens[0].typ=='comma':
        tokens = tokens[1:]
        if (len(tokens)>1 and tokens[0].typ=='lessDash'):
            tokens = tokens[1:]
            neg = True
        if (len(tokens)>1 and tokens[0].typ=='dashGreater'):
            tokens = tokens[1:]
        x = parseCoqExpr(tokens,[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        #print spaces(indent)+str(tokens[0])
        tokens = x[1]
        #print spaces(indent)+"Done expr"
        #print spaces(indent)+str(tokens[0])
        terms = [(x[0],neg)]
        #while tokens[0].typ=='comma':
            #tokens = tokens[1:]
            #if (len(tokens)>1 and tokens[0].typ=='lessEqual'):
                #tokens = tokens[1:]
                #neg = True
            #if (len(tokens)>1 and tokens[0].typ=='equalGreater'):
                #tokens = tokens[1:]
            #x = parseCoqExpr(tokens,[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
            #tokens = x[1]
            #terms.append((x[0],neg))
        workDone = True
        inClause = None
        byClause = None
        withClause = None
        occurences = None
        while workDone:
            workDone = False
            if tokens[0].typ=='with' and withClause==None:
                tokens = tokens[1:]
                withClause = []
                while len(tokens)>3 and tokens[0].typ=='leftParen' and tokens[1].typ=='ID' and tokens[2].typ=='colonEqual':
                    x = parseCoqExpr(tokens[3:],[])
                    tokens = x[1]
                    withClause.append((tokens[1].value,x[0]))
                    if len(tokens)==0 or tokens[0].typ!='rightParen':
                        raise ParseError("Cannot parse coqRewriteTactic",tokens)
                    tokens = tokens[1:]
            if tokens[0].typ=='in' and inClause==None:
                x = parseCoqExprOrStar(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
                tokens = x[1]
                inClause = x[0]
                workDone = True
            if tokens[0].typ=='by' and byClause==None:
                workDone = True
                x = parseCoqTactic(tokens)
                tokens = x[1]
                byClause = x[0]
        tlist.append((terms,inClause,byClause,occurences,withClause))
    return (CoqRewriteTactic(tt[0:len(tt)-len(tokens)],tlist),tokens)

class CoqUnfoldTactic(CoqTactic):
    def __init__(self,tokens,d,aSpec,iSpec):
        CoqTactic.__init__(self,tokens)
        self.defs = d
        self.atSpec = aSpec
        self.inSpec = iSpec
    def getListRepr(self):
        x = ["UnfoldTactic",["defs"]+self.defs]
        if inSpec != None:
            x.append(inSpec)
        return x
    @classmethod
    def create(cls,l,tokens):
        b = None
        if len(l)>2:
            b = l[2]
        return CoqUnfoldTactic(tokens,l[1][1:],b)
    def __repr__(self):
        return "class CoqUnfoldTactic"
    def __coqstr__(self):
        x = "unfold"
        pcomma = False
        for t in self.defs:
            if pcomma:
                x = x + ", "
            pcomma = True
            x = x + " " + t.__coqstr__()
        if self.atSpec!=None:
            x = x+" in "+str(self.atSpec)
        if self.inSpec!=None:
            x = x+" in "+self.inSpec.__coqstr__()
        return x
    def getExpressions(self):
        return [self.inSpec]
    def updateWithExpressions(self,l):
        return CoqUnfoldTactic(self.tokens,self.defs,self.atSpec,l[0])

def parseCoqUnfoldTactic(tokens):
    tt = tokens
    if (len(tokens)<3 or tokens[0].typ!='ID'):
        raise ParseError(tokens,"Cannot parse CoqUnfoldTactic")
    x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)],[CoqLex.Token('comma',',',0,0)]])
    print "UNFOLD xxxxxx"
    print x
    tokens = x[1]
    terms = [x[0]]
    while tokens[0].typ=='comma':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)],[CoqLex.Token('comma',',',0,0)]])
        terms.append(x[0])
        tokens = x[1]
    inClause = None
    atClause = None
    if tokens[0].typ=='at' and tokens[1].typ=='NUMBER':
        atClause = tokens[1].value
        tokens = tokens[2:]
    if tokens[0].typ=='in':
        x = parseCoqExprOrStar(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        tokens = x[1]
        inClause = x[0]
    return (CoqUnfoldTactic(tt[0:len(tt)-len(tokens)],terms,atClause,inClause),tokens)

class CoqFoldTactic(CoqTactic):
    def __init__(self,tokens,d,iSpec):
        CoqTactic.__init__(self,tokens)
        self.defs = d
        self.inSpec = iSpec
    def getListRepr(self):
        x = ["FoldTactic",["defs"]+self.defs]
        if inSpec != None:
            x.append(inSpec)
        return x
    @classmethod
    def create(cls,l,tokens):
        b = None
        if len(l)>2:
            b = l[2]
        return CoqUnfoldTactic(tokens,l[1][1:],b)
    def __repr__(self):
        return "class CoqFoldTactic"
    def __coqstr__(self):
        x = "fold"
        pcomma = False
        for t in self.defs:
            if pcomma:
                x = x + ", "
            pcomma = True
            x = x + " " + t.__coqstr__()
        if self.inSpec!=None:
            x = x+" in "+self.inSpec.__coqstr__()
        return x
    def getExpressions(self):
        return [self.inSpec]
    def updateWithExpressions(self,l):
        return CoqFoldTactic(self.tokens,self.defs,l[0])

def parseCoqFoldTactic(tokens):
    tt = tokens
    print "PARSING FOLD"
    print tokens[0]
    print tokens[1]
    print tokens[2]
    print tokens[3]
    print tokens[4]
    if (len(tokens)<3 or tokens[0].typ!='ID'):
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("Cannot parse CoqFoldTactic",tokens)
    x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
    tokens = x[1]
    terms = [x[0]]
    print "FIRST TERM"
    print x[0]
    while tokens[0].typ=='comma':
        x = parseCoqExpr(tokens,[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        tokens = x[1]
        terms.append(x[0])
    inClause = None
    if tokens[0].typ=='in':
        x = parseCoqExprOrStar(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        tokens = x[1]
        inClause = x[0]
    print "RETURNING"
    print CoqFoldTactic(tt[0:len(tt)-len(tokens)],terms,inClause)
    return (CoqFoldTactic(tt[0:len(tt)-len(tokens)],terms,inClause),tokens)

class CoqSimplTactic(CoqTactic):
    def __init__(self,tokens,t,o,h):
        CoqTactic.__init__(self,tokens)
        self.term = t
        self.occurences = o
        self.hyp = h
    def getListRepr(self):
        return ["SimplTactic",self.term,self.occurences,self.hyp]
    @classmethod
    def create(cls,l,tokens):
        return CoqSimplTactic(tokens,l[1],l[2],l[3])
    def __repr__(self):
        return "class CoqSimplTactic"
    def __coqstr__(self):
        x = "simpl"
        pcomma = False
        if len(self.hyp) > 0:
            x = x + " in "
        for h in self.hyp:
            if pcomma:
                x = x + ", "
            pcomma = True
            if h=='*':
                x = x+"*"
            elif h!=None:
                x = x+h.__coqstr__()
        return x

def parseCoqSimplTactic(tokens):
    tt = tokens
    if (len(tokens)<2 or tokens[0].typ!='ID' or tokens[0].value!='simpl'):
        raise ParseError(tokens,"Cannot parse CoqSimplTactic")
    tokens = tokens[1:]
    hyp = []
    while tokens[0].typ=='in' or tokens[0].typ=='comma':
        if tokens[1].value=='*':
            tokens = tokens[2:]
            hyp.append('*')
        else:
            x = parseCoqExprOrStar(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)],[CoqLex.Token('comma',',',0,0)]])
            tokens = x[1]
            hyp.append(x[0])
    return (CoqSimplTactic(tt[0:len(tt)-len(tokens)],None,None,hyp),tokens)

class CoqInjectionTactic(CoqTactic):
    def __init__(self,tokens,t,h):
        CoqTactic.__init__(self,tokens)
        self.term = t
        self.hyps = h
    def getListRepr(self):
        return ["InjectionTactic",self.term,self.hyps]
    @classmethod
    def create(cls,l,tokens):
        return CoqInjectionTactic(tokens,l[1],l[2])
    def __repr__(self):
        return "class CoqInjectionTactic"
    def __coqstr__(self):
        x = "injection "+self.term.__coqstr__()
        if self.hyps != None:
            x = x+" as"
            for z in self.hyps:
                x = x+" "+z
        return x

def parseCoqInjectionTactic(tokens):
    print "HERE"
    tt = tokens
    if (len(tokens)<2 or tokens[0].typ!='ID' or tokens[0].value!='injection'):
        raise ParseError(tokens,"Cannot parse CoqSimplTactic")
    print "HEREA1"
    tokens = tokens[1:]
    print "HEREA2"
    print tokens[0]
    r = parseCoqExpr(tokens,[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
    print "HEREA3"
    hyps = None
    tokens = r[1]
    print tokens[0]
    print "HEREAA"
    if tokens[0].typ=='as':
        print "HEREA"
        tokens = tokens[1:]
        hyps = []
        print "HERE2"
        while (tokens[0].typ=='ID' or tokens[0].typ=='_'):
            hyps.append(tokens[0].value)
            tokens = tokens[1:]
    return (CoqInjectionTactic(tt[0:len(tt)-len(tokens)],r[0],hyps),tokens)

class CoqComputeTactic(CoqTactic):
    def __init__(self,tokens,t,o,h):
        CoqTactic.__init__(self,tokens)
        self.term = t
        self.occurences = o
        self.hyp = h
    def getListRepr(self):
        return ["ComputeTactic",self.term,self.occurences,self.hyp]
    @classmethod
    def create(cls,l,tokens):
        return CoqComputeTactic(tokens,l[1],l[2],l[3])
    def __repr__(self):
        return "class CoqComputeTactic"
    def __coqstr__(self):
        x = "compute"
        if self.hyp=='*':
            x = x+" in *"
        elif self.hyp!=None:
            x = x+" in "+self.hyp.__coqstr__()
        return x

def parseCoqComputeTactic(tokens):
    #print spaces(indent)+"PARSING COMPUTE"
    #print spaces(indent)+str(tokens[0])
    #print spaces(indent)+str(tokens[1])
    tt = tokens
    if (len(tokens)<2 or tokens[0].typ!='ID' or tokens[0].value!='compute'):
        raise ParseError("Cannot parse CoqComputeTactic",tokens)
    tokens = tokens[1:]
    hyp = None
    if tokens[0].typ=='in':
        if tokens[1].value=='*':
            tokens = tokens[2:]
            hyp = '*'
        else:
            x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
            tokens = x[1]
            hyp = x[0]
    return (CoqComputeTactic(tt[0:len(tt)-len(tokens)],None,None,hyp),tokens)

class CoqApplyTactic(CoqTactic):
    def __init__(self,tokens,e,r,h,w):
        CoqTactic.__init__(self,tokens)
        self.is_eapply = e
        self.rule = r
        self.hyp = h
        self.wit = w
    def dependencies(self):
        d = self.rule.dependencies()
        for xx in self.wit:
            d = d+xx[1].dependencies()
        return d
    def getListRepr(self):
        return ["ApplyTactic",self.is_eapply,self.rule,self.hyp,self.wit]
    @classmethod
    def create(cls,l,tokens):
        return CoqApplyTactic(tokens,l[1],l[2],l[3],l[4])
    def __repr__(self):
        return "class CoqApplyTactic"
    def __coqstr__(self):
        x = ""
        if self.is_eapply:
            x = "e"
        x = x+"apply "+self.rule.__coqstr__()
        if self.hyp!=None:
            x = x+" in "+self.hyp.__coqstr__()
        for xx in self.wit:
            x = x + " with ("+xx[0]+" := "+xx[1].__coqstr__()+")"
        return x
    def getExpressions(self):
        return [self.rule,self.hyp,self.wit]
    def updateWithExpressions(self,l):
        return CoqApplyTactic(self.is_eapply,l[0],l[1],l[2])

def parseCoqApplyTactic(tokens):
    tt = tokens
    if (len(tokens)<2):
        raise ParseError(tokens,"Cannot parse CoqApplyTactic")
    if tokens[0].value=='eapply':
        is_eapply = True
    elif tokens[0].value=='apply':
        is_eapply = False
    else:
        raise ParseError(tokens,"Cannot parse CoqApplyTactic")
    x = parseCoqExpr(tokens[1:],[[CoqLex.Token('semicolon',';',0,0)],[CoqLex.Token('period','.',0,0)],[CoqLex.Token('barBar','||',0,0)]])
    exp = x[0]
    tokens = x[1]
    hyp = None
    if tokens[0].typ=='in':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        tokens = x[1]
        hyp = x[0]
    w = []
    while len(tokens)>3 and tokens[0].value=="with":
        if tokens[1].typ!='leftParen' or tokens[2].typ!='ID' or tokens[3].typ!='colonEqual':
            raise ParseError(tokens,"Cannot parse CoqApplyTactic")
        tokens = tokens[1:]
        while len(tokens)>3 and tokens[0].typ=='leftParen' and tokens[1].typ=='ID' or tokens[2].typ=='colonEqual':
            i = tokens[1].value
            x = parseCoqExpr(tokens[3:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
            tokens = x[1]
            w.append((i,x[0]))
            if len(tokens)==0 or tokens[0].typ!='rightParen':
                raise ParseError(tokens,"Cannot parse CoqApplyTactic")
            tokens = tokens[1:]
    return (CoqApplyTactic(tt[0:len(tt)-len(tokens)],is_eapply,exp,hyp,w),tokens)

class CoqAtomIntroPattern(CoqTactic):
    def __init__(self,tokens,hq,n):
        CoqTactic.__init__(self,tokens)
        self.name = n
        self.has_question = hq
    def getListRepr(self):
        return ["AtomIntroPattern",self.pattern]
    @classmethod
    def create(cls,l,tokens):
        return CoqAtomIntroPattern(tokens,l[1],l[2])
    def __repr__(self):
        if self.has_question:
            return "class CoqAtomIntroPattern ?"+str(name)
        else:
            return "class CoqAtomIntroPattern "+str(name)
    def __coqstr__(self):
        if self.has_question:
            x = "?"
        else:
            x = ""
        x = x + self.name
        return x

def parseCoqAtomIntroPattern(tokens):
    tt = tokens
    if (len(tokens)<1):
        raise ParseError(tokens,"Cannot parse CoqIntroOrPattern")
    hq = False
    if tokens[0].typ=='questionMark':
        hq = True
        tokens = tokens[1:]
    if (len(tokens)>0 and (tokens[0].typ=='ID' or tokens[0].typ=='_')):
        name = tokens[0].value
        tokens = tokens[1:]
    else:
        raise ParseError(tokens,"Cannot parse CoqIntroOrPattern")
    return (CoqAtomIntroPattern(tt[0:len(tt)-len(tokens)],hq,name),tokens)

class CoqOrIntroPattern(CoqTactic):
    def __init__(self,tokens,hs):
        CoqTactic.__init__(self,tokens)
        self.pattern = hs
    def getListRepr(self):
        return ["OrIntroPattern",self.pattern]
    @classmethod
    def create(cls,l,tokens):
        return CoqOrIntroPattern(tokens,l[1])
    def __repr__(self):
        return "class CoqOrIntroPattern"
    def __coqstr__(self):
        x = "["
        after_first = False
        for z in self.pattern:
            if after_first:
                x = x + " | "
            after_first = True
            after_ifirst = False
            for zz in z:
                if after_ifirst:
                    x = x + " "
                x = x + zz.__coqstr__()
        x = x + "]"
        return x

def parseCoqOrIntroPattern(tokens):
    tt = tokens
    if (len(tokens)<2 or tokens[0].typ!='leftBracket'):
        raise ParseError(tokens,"Cannot parse CoqIntroPattern")
    subterms = []
    subtt = []
    tokens = tokens[1:]
    while len(tokens)>0 and (tokens[0].typ=='_' or tokens[0].typ=='ID' or tokens[0].typ=='leftBracket' or tokens[0].typ=='leftParen'):
        r = parseCoqIntroPattern(tokens)
        tokens = r[1]
        subtt.append(r[0])
        if len(tokens)>0 and tokens[0].typ=='bar':
            subterms.append(subtt)
            subtt = []
            tokens = tokens[1:]
    subterms.append(subtt)
    if len(tokens)==0 or tokens[0].typ != 'rightBracket':
        print tokens[0]
        raise ParseError("Cannot parse CoqIntroPattern",tokens)
    #while (len(tokens)>1 and (tokens[1].typ=='ID' or tokens[1].typ=='_')):
        #i = tokens[1].value
        #tokens = tokens[1:]
        #id.append(i)
    tokens = tokens[1:]
    return (CoqOrIntroPattern(tt[0:len(tt)-len(tokens)],subterms),tokens)

class CoqAndIntroPattern(CoqTactic):
    def __init__(self,tokens,ia,hs):
        CoqTactic.__init__(self,tokens)
        self.pattern = hs
        self.is_ampersand = ia;
    def getListRepr(self):
        return ["AndIntroPattern",is_ampersand,self.pattern]
    @classmethod
    def create(cls,l,tokens):
        return CoqAndIntroPattern(tokens,l[1],l[2])
    def __repr__(self):
        return "class CoqAndIntroPattern"
    def __coqstr__(self):
        x = "("
        after_first = False
        for z in self.pattern:
            if after_first:
                if is_ampersand:
                    x = x + " & "
                else:
                    x = x + ", "
            after_first = True
            x = x + z.__coqstr__()
        x = x + ")"
        return x

def parseCoqAndIntroPattern(tokens):
    tt = tokens
    if (len(tokens)<2 or tokens[0].typ!='leftParent'):
        raise ParseError(tokens,"Cannot parse CoqIntroOrPattern")
    terms = []
    ia = False
    while len(tokens)>0 and (tokens[0].typ=='ID' or tokens[0].typ=='leftBracket' or tokens[0].typ=='leftParen'):
        r = parseCoqIntroPattern(tokens)
        terms.append(r[0])
        tokens = r[1]
        if len(tokens)==0 or (tokens[0].typ != 'comma' and tokens[0].typ != 'ampersand'):
            raise ParseError(tokens,"Cannot parse CoqIntroAndPattern")
        tokens = tokens[1:]
    if len(tokens)==0 or tokens[0].typ != 'rightParen':
        raise ParseError(tokens,"Cannot parse CoqIntroAndPattern")
    tokens = tokens[1:]
    return (CoqAndIntroPattern(tt[0:len(tt)-len(tokens)],ia,terms),tokens)

def parseCoqIntroPattern(tokens):
    if len(tokens)==0:
        raise ParseError(tokens,"Cannot parse CoqIntroPattern")
    if tokens[0].typ=='ID' or tokens[0].typ=='questionMark' or tokens[0].typ=='_':
        return parseCoqAtomIntroPattern(tokens)
    if tokens[0].typ=='leftBracket':
        return parseCoqOrIntroPattern(tokens)
    if tokens[0].typ=='leftParen':
        print tokens[0]
        return parseCoqAndIntroPattern(tokens)
    raise ParseError("Cannot parse CoqIntroPattern",tokens)

class CoqClearTactic(CoqTactic):
    def __init__(self,tokens,hs):
        CoqTactic.__init__(self,tokens)
        self.hyps = hs
    def getListRepr(self):
        return ["ClearTactic",self.hyps]
    @classmethod
    def create(cls,l,tokens):
        return CoqClearTactic(tokens,l[1])
    def __repr__(self):
        return "class CoqClearTactic"
    def __coqstr__(self):
        x = "clear"
	if (self.hyps!=None):
            for z in self.hyps:
                x = x + " " + z
        return x

def parseCoqClearTactic(tokens):
    tt = tokens
    if (len(tokens)<1 or tokens[0].typ!='ID' or tokens[0].value!='clear'):
        raise ParseError(tokens,"Cannot parse CoqClearTactic")
    id = []
    while (len(tokens)>1 and tokens[1].typ=='ID'):
        i = tokens[1].value
        tokens = tokens[1:]
        id.append(i)
    tokens = tokens[1:]
    return (CoqClearTactic(tt[0:len(tt)-len(tokens)],id),tokens)

class CoqIntrosTactic(CoqTactic):
    def __init__(self,tokens,hs):
        CoqTactic.__init__(self,tokens)
        self.intro_patterns = hs
    def getListRepr(self):
        return ["IntrosTactic",self.hyps]
    @classmethod
    def create(cls,l,tokens):
        return CoqIntrosTactic(tokens,l[1])
    def __repr__(self):
        return "class CoqIntrosTactic"
    def __coqstr__(self):
        x = "intros"
	if (self.intro_patterns != None):
            for z in self.intro_patterns:
                x = x + " " + z.__coqstr__()
        return x

def parseCoqIntrosTactic(tokens):
    tt = tokens
    if (len(tokens)<1 or tokens[0].typ!='ID' or tokens[0].value!='intros'):
        raise ParseError(tokens,"Cannot parse CoqClearTactic")
    id = []
    tokens = tokens[1:]
    while len(tokens)>0 and (tokens[0].typ=='ID' or tokens[0].typ=='leftBracket' or tokens[0].typ=='leftParen' or tokens[0].typ=='_'):
        r = parseCoqIntroPattern(tokens)
        tokens = r[1]
        id.append(r[0])
    print "Done intro"
    print tokens[0]
    return (CoqIntrosTactic(tt[0:len(tt)-len(tokens)],id),tokens)

class CoqRememberTactic(CoqTactic):
    def __init__(self,tokens,h,n,e):
        CoqTactic.__init__(self,tokens)
        self.exp= h
        self.name = n
        self.eqn = e
    def dependencies(self):
        return self.exp.dependencies()
    def getListRepr(self):
        x = ["RememberTactic",self.exp]
        if self.name!=None:
           x.append(self.name)
        return x
    @classmethod
    def create(cls,l,tokens):
        if len(l)>2:
            n = l[2]
        else:
            n = None
        return CoqRememberTactic(tokens,l[1],None)
    def __repr__(self):
        return "class CoqRememberTactic"
    def __coqstr__(self):
        x = "remember ("+self.exp.__coqstr__()+")"
        if self.eqn != None:
            x = x + "eqn:"+self.eqn
        return x

def parseCoqRememberTactic(tokens):
    tt = tokens
    if len(tokens)<3 or tokens[0].typ!='ID' or tokens[0].value!='remember' or (tokens[1].typ!='leftParen' and tokens[1].typ!='ID'):
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("Cannot parse CoqRememberTactic",tokens)
    x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
    tokens = x[1]
    exp = x[0]
    name = None
    if len(tokens) > 0 and tokens[0].typ=='as' and tokens[1].typ=='ID':
        name = tokens[1].value
        tokens = tokens[2:]
    e = None
    if tokens[0].value=='eqn' and tokens[1].typ=='colon':
        e = tokens[2].value
        tokens = tokens[3:]
    return (CoqRememberTactic(tt[0:len(tt)-len(tokens)],exp,name,e),tokens)

class CoqExistsTactic(CoqTactic):
    def __init__(self,tokens,h):
        CoqTactic.__init__(self,tokens)
        self.exp= h
    def dependencies(self):
        return self.exp.dependencies()
    def getListRepr(self):
        x = ["ExistsTactic",self.exp]
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqRememberTactic(tokens,l[1])
    def __repr__(self):
        return "class CoqExistsTactic"
    def __coqstr__(self):
        x = "exists "
        after = False
        for e in self.exp:
            if after:
                x = x + ", "
            after = True
            x = x + e.__coqstr__()
        return x

def parseCoqExistsTactic(tokens):
    tt = tokens
    if len(tokens)<3 or tokens[0].typ!='exists' or tokens[0].value!='exists':
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("Cannot parse CoqExistsTactic",tokens)
    exp = []
    while tokens[0].typ=='exists' or tokens[0].typ=='comma':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        tokens = x[1]
        exp.append(x[0])
    return (CoqExistsTactic(tt[0:len(tt)-len(tokens)],exp),tokens)

class CoqDestructTactic(CoqTactic):
    def __init__(self,tokens,h,p,cl):
        CoqTactic.__init__(self,tokens)
        self.exp= h
        self.pat = p
        self.clauses = cl
    def dependencies(self):
        return self.exp.dependencies()
    def getListRepr(self):
        return ["DestructTactic",self.exp,self.pat,self.clauses]
    @classmethod
    def create(cls,l,tokens):
        return CoqDestructTactic(tokens,l[1],l[2],l[3])
    def __repr__(self):
        return "class CoqDestructTactic"
    def __coqstr__(self):
        x = "destruct ("
        after = False
        for e in self.exp:
              if after:
                  x = x + ", "
              after = True
              x = x + e.__coqstr__()
        x = x + ")"
        if self.pat != None:
            x = x + " as " + self.pat.__coqstr__()
        if self.clauses != None:
            x = x + " in " + self.clauses.__coqstr__()
        return x

def parseCoqDestructTactic(tokens):
    tt = tokens
    if (len(tokens)<3 or tokens[0].typ!='ID' or tokens[0].value!='destruct'):
        raise ParseError(tokens,"Cannot parse CoqDestructTactic")
    x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
    tokens = x[1]
    exp = [x[0]]
    while tokens[0].typ=='comma':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        tokens = x[1]
        exp.append(x[0])
    pat = None
    if len(tokens)>0 and tokens[0].typ=='as':
        x = parseCoqIntroPattern(tokens[1:])
        tokens = x[1]
        pat = x[0]
    cl = None
    if len(tokens)>0 and tokens[0].typ=='in':
        x = parseCoqExprOrStar(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        tokens = x[1]
        cl = x[0]
    return (CoqDestructTactic(tt[0:len(tt)-len(tokens)],exp,pat,cl),tokens)

class CoqConstructorTactic(CoqTactic):
    def __init__(self,tokens,n,w):
        CoqTactic.__init__(self,tokens)
        self.number = n
        self.withList= w
    def dependencies(self):
        d = []
        for w in self.withList:
            d = d  + w.dependencies()
        return d
    def getListRepr(self):
        return ["ConstructorTactic",self.number,self.withList]
    @classmethod
    def create(cls,l,tokens):
        return CoqConstructorTactic(tokens,l[1],l[2])
    def __repr__(self):
        return "class CoqConstructorTactic"
    def __coqstr__(self):
        if self.number==None:
            return "constructor"
        x = "constructor " + str(self.number)
        if len(self.withList) > 0:
            x = x + " with"
            af = False
            for w in self.withList:
                if af:
                    x = x + ","
                x = x + w.__coqstr__()
        return x

def parseCoqConstructorTactic(tokens):
    tt = tokens
    if tokens[1].typ=='period' or tokens[1].typ=='semicolon' or tokens[1].typ=='rightParen':
        return (CoqConstructorTactic(tt[0:1],None,[]),tokens[1:])
    if (len(tokens)<3 or tokens[0].typ!='ID' or tokens[0].value!='constructor' or
        tokens[1].typ != 'NUMBER'):
        print tokens[0]
        print tokens[1]
        raise ParseError("Cannot parse CoqConstructorTactic",tokens)
    n = int(tokens[1].value)
    w = []
    if tokens[2].typ=='with':
        tokens = tokens[2:]
        while tokens[0].typ=='with' or tokens[0].typ=='comma':
            x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
            tokens = x[1]
            exp = x[0]
            w.append(exp)
    else:
        tokens = tokens[2:]
    return (CoqConstructorTactic(tt[0:len(tt)-len(tokens)],n,w),tokens)

class CoqInstantiateTactic(CoqTactic):
    def __init__(self,tokens,n,h,ih):
        CoqTactic.__init__(self,tokens)
        self.number = n
        self.exp= h
        self.hyp = ih
    def dependencies(self):
        if self.number==None:
            return []
        d = self.exp.dependencies()
        if self.hyp!=None:
            d = d+self.hyp.dependencies()
        return d
    def getListRepr(self):
        return ["InstantiateTactic",self.number,self.exp,self.hyp]
    @classmethod
    def create(cls,l,tokens):
        return CoqInstantiateTactic(tokens,l[1],l[2],l[3])
    def __repr__(self):
        return "class CoqInstantiateTactic"
    def __coqstr__(self):
        if self.number==None:
            return "instantiate"
        x = "instantiate ("+str(self.number)+ " := "+self.exp.__coqstr__()+")"
        if (self.hyp != None):
            x = x + " in " + self.hyp.__coqstr__()
        return x

def parseCoqInstantiateTactic(tokens):
    tt = tokens
    if tokens[1].typ=='period' or tokens[1].typ=='semicolon':
        return (CoqInstantiateTactic(tt[0:1],None,None,None),tokens[1:])
    if (len(tokens)<3 or tokens[0].typ!='ID' or tokens[0].value!='instantiate'
        or tokens[1].typ!='leftParen' or tokens[2].typ!='NUMBER' or tokens[3].typ!='colonEqual'):
        raise ParseError("Cannot parse CoqInstantiateTactic",tokens)
    n = int(tokens[2].value)
    x = parseCoqExpr(tokens[4:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
    tokens = x[1]
    exp = x[0]
    if tokens[0].typ!='rightParen':
        raise ParseError(tokens,"Cannot parse CoqInstantiateTactic")
    tokens = tokens[1:]
    ih = None
    if len(tokens)>0 and tokens[0].typ=='in':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        ih = x[0]
        tokens = x[1]
    return (CoqInstantiateTactic(tt[0:len(tt)-len(tokens)],n,exp,ih),tokens)

class CoqFailTactic(CoqTactic):
    def __init__(self,tokens,l,q):
        CoqTactic.__init__(self,tokens)
        self.levels = l
        self.quotations = q
    def getListRepr(self):
        return ["FailTactic",self.levels,self.quotation]
    @classmethod
    def create(cls,l,tokens):
        return CoqFailTactic(tokens,l[1],l[2])
    def __repr__(self):
        return "class CoqFailTactic"
    def __coqstr__(self):
        x = "fail "+str(self.levels)
        for q in self.quotations:
            x = x+' "'+q+'"'
        return x

def parseCoqFailTactic(tokens):
    tt = tokens
    if (len(tokens)<2 or tokens[0].typ!='ID' or tokens[0].value!='fail'):
        raise ParseError(tokens,"Cannot parse CoqFailTactic")
    l = 1
    pos = 1
    if (tokens[1].typ=='NUMBER'):
        l = int(tokens[1].value)
        pos = 2
    q = []
    while (pos < len(tokens) and tokens[pos].typ=='QUOTATION'):
        q.append(tokens[pos].value[1:len(tokens[pos].value)-1])
        pos = pos + 1
    return (CoqFailTactic(tt[0:pos],l,q),tokens[pos:])

class CoqFocusTactic(CoqTactic):
    def __init__(self,tokens,l):
        CoqTactic.__init__(self,tokens)
        self.levels = l
    def getListRepr(self):
        return ["FocusTactic",self.levels]
    @classmethod
    def create(cls,l,tokens):
        return CoqFocusTactic(tokens,l[1])
    def __repr__(self):
        return "class CoqFocusTactic"
    def __coqstr__(self):
        x = "Focus "+str(self.levels)
        return x

def parseCoqFocusTactic(tokens):
    tt = tokens
    if (len(tokens)<2 or tokens[0].typ!='ID' or tokens[0].value!='Focus'):
        raise ParseError(tokens,"Cannot parse CoqFailTactic")
    l = 1
    pos = 1
    if (tokens[1].typ=='NUMBER'):
        l = int(tokens[1].value)
        pos = 2
    return (CoqFocusTactic(tt[0:pos],l),tokens[pos:])

class CoqApplyNotationTactic(CoqTactic):
    def __init__(self,tokens,n,p):
        CoqTactic.__init__(self,tokens)
        self.name=n
        self.params=p
    def dependencies(self):
        d = []
        for x in self.params:
            d = d + x.dependencies()
        return d
    def getListRepr(self):
        x = ["ApplyNotationTactic",self.name]
        for p in self.params:
            x.append(p)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqApplyNotationTactic(tokens,l[1],l[2:])
    def __repr__(self):
        return "class CoqApplyNotationTactic "+self.name
    def __coqstr__(self):
        x = self.name
        for p in self.params:
            x = x + " " + p.__coqstr__()
        return x

def parseCoqApplyNotationTactic(tokens):
    print spaces(indent)+"APPLY NOTATION"
    print spaces(indent)+str(tokens[0])
    print spaces(indent)+str(tokens[1])
    tt = tokens
    if (len(tokens)<1):
        raise ParseError(tokens,"Cannot parse CoqApplyNotationTactic")
    id = tokens[0].value
    tokens = tokens[1:]
    p = []
    while (len(tokens)>0 and tokens[0].typ!='period' and tokens[0].typ!='semicolon' and tokens[0].typ!='bar' and tokens[0].typ!='rightParen' and tokens[0].typ!='rightBracket' and tokens[0].typ != 'barBar') and tokens[0].typ != 'end':
        print "Apply notation "+str(tokens[0])
        x = parseCoqExpr(tokens,[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('semicolon',';',0,0)]])
        p.append(x[0])
        tokens = x[1]
        print "APPLY DONE"
        print x
    return (CoqApplyNotationTactic(tt[0:len(tt)-len(tokens)],id,p),tokens)

class CoqReflexivityTactic(CoqTactic):
    def __init__(self,tokens):
        CoqTactic.__init__(self,tokens)
    def getListRepr(self):
        x = ["ReflexivityTactic"]
    @classmethod
    def create(cls,l,tokens):
        return CoqReflexivityTactic(tokens)
    def __repr__(self):
        return "class CoqReflexivityTactic"
    def __coqstr__(self):
        return "reflexivity"

def parseCoqReflexivityTactic(tokens):
    if (len(tokens)<1 or tokens[0].typ!='ID' or tokens[0].value!='reflexivity'):
        raise ParseError(tokens,"Cannot parse CoqClearTactic")
    return (CoqReflexivityTactic(tokens[0:1]),tokens[1:])

class CoqMoveTactic(CoqTactic):
    def __init__(self,tokens,i1,rel,i2):
        CoqTactic.__init__(self,tokens)
        self.id1 = i1
        self.rel = rel
        self.id2 = i2
    def getListRepr(self):
        x = ["MoveTactic",self.id1,self.rel,self.id2]
    @classmethod
    def create(cls,l,tokens):
        return CoqMoveTactic(tokens,l[1],l[2],l[3])
    def __repr__(self):
        return "class CoqMoveTactic "+id1+" "+self.rel+" "+self.id2
    def __coqstr__(self):
        return "move "+self.id1+" "+self.rel+" "+self.id2

def parseCoqMoveTactic(tokens):
    if (len(tokens)>3 and tokens[1].typ=='ID' and
        tokens[2].typ=='after' and tokens[3].typ=='ID'):
        id1 = tokens[1].value
        id2 = tokens[3].value
        return (CoqMoveTactic(tokens[0:4],id1,'after',id2),tokens[4:])
    elif (len(tokens)>3 and tokens[1].typ=='ID' and
        tokens[2].typ=='before' and tokens[3].typ=='ID'):
        id1 = tokens[1].value
        id2 = tokens[3].value
        return (CoqMoveTactic(tokens[0:4],id1,'before',id2),tokens[4:])
    elif (len(tokens)>3 and tokens[1].typ=='ID' and
        tokens[2].typ=='at' and tokens[3].value=='top'):
        id1 = tokens[1].value
        return (CoqMoveTactic(tokens[0:4],id1,'at','top'),tokens[4:])
    elif (len(tokens)>3 and tokens[1].typ=='ID' and
        tokens[2].typ=='at' and tokens[3].typ=='bottom'):
        id1 = tokens[1].value
        return (CoqMoveTactic(tokens[0:4],id1,'at','bottom'),tokens[4:])
    else:
        raise ParseError('bad CoqMoveTactic',tokens)

# ****************************************************************************

class CoqDeclaration(CoqParseObject):
    def __init__(self,tokens):
        CoqParseObject.__init__(self,tokens)
        self.result = ""
        self.old_result = ""
        self.subgoals = 0
        self.needsReplay = 0
        self.currentCoqState = -1
        pass
    def isProof(self):
        return False
    def markNeedsReplay(self):
        self.needsReplay = 4
    def dependencies(self):
        return []
    def getListRepr(self):
        return ["Declaration"]
    @classmethod
    def create(cls,l,tokens):
        return CoqDeclaration(tokens)
    def getProof(self):
        return []
    def header(self):
        return self.__repr__()
    def getCoqPrefix(self,text):
        return self.getSegment(text)[0]
    def getCoqSuffix(self,text):
        return ""
    def definedNames(self):
        return []
    def indent(self):
        return False
    def undent(self):
        return False
    def isBad(self):
        return False

# ****************************************************************************

class CoqBadDeclaration(CoqDeclaration):
    def __init__(self,tokens,proof):
        CoqDeclaration.__init__(self,tokens)
        self.proof = proof
    def getLstRepr(self):
        return ["BadDeclaration"]
    @classmethod
    def create(cls,l,tokens):
        return CoqBadDeclaration(tokens)
    def __repr__(self):
        return "class CoqBadDeclaration"
    def header(self):
        if len(self.tokens)==0:
            return "Bad or unrecognized"
        elif len(self.tokens)==1:
            return "Unparsed: "+self.tokens[0].value
        else:
            return "Unparsed: "+self.tokens[0].value+" "+self.tokens[1].value
    def __coqstr__(self):
        return "<CoqBadDeclaration>"
    def getProof(self):
        return self.proof
    def isBad(self):
        return True
# ****************************************************************************

class CoqPlaceHolderDeclaration(CoqDeclaration):
    def __init__(self,tokens,defn,decl_list,parents,children,file,indent,undent):
        CoqDeclaration.__init__(self,tokens)
        self.result = ""
        self.old_result = None
        self.subgoals = 0
        self.needsReplay = 0
        self.defn = defn
        self.decl_list = decl_list
        self.parents = parents
        self.children = children
        self.file = file
        self.proof = []
        self.indent_val = False
        self.undent_val = False
    def getListRepr(self):
        return self.defn
    def getProof(self):
        return self.proof
    @classmethod
    def create(cls,l,tokens):
        return CoqDeclaration(tokens)
    def header(self):
        return self.defn
    def definedNames(self):
        return self.decl_list
    def __repr__(self):
        return "Place holder "+str(self.decl_list)
    def __coqstr__(self):
        return self.__repr__()
    def indent(self):
        return self.indent_val
    def undent(self):
        return self.undent_val

# ****************************************************************************

class CoqErrorDeclaration(CoqDeclaration):
    def __init__(self,tokens,message, n):
        CoqDeclaration.__init__(self,tokens)
        self.message = m
        self.tokenNum = n
    def header(self):
        return "SYNTAX ERROR--please fix"
    def insertMessage(self, text):
        t = text.split("\n")
        errorToken = self.tokens[self.tokenNum]
        l = t[self.tokenNum].line
        t[self.tokenNum] = l[0:t.column]+" <<< " + self.message + " >>> "+ l[t.column:]
        return "\n".join(t)
    def __repr__(self):
        return "class CoqErrorDeclaration "+str(self.tokenNum)+" error: "+self.message
    def __coqstr__(self):
        return self.__repr__()

# ****************************************************************************

class CoqSetImplicitArguments(CoqDeclaration):
    def __init__(self,tokens):
        CoqDeclaration.__init__(self,tokens)
    def dependencies(self):
        return []
    def getListRepr(self):
        return ["SetImplicitArguments"]
    @classmethod
    def create(cls,l,tokens):
        return CoqSetTactic(tokens)
    def __repr__(self):
        return "class CoqSetImplicitArguments"
    def definedNames(self):
        return []
    def __coqstr__(self):
        return "Set Implicit Arguments"

def parseCoqSetImplicitArguments(tokens):
    tt = tokens
    if (len(tokens)<3 or tokens[0].typ!='ID' or tokens[0].value!='Set' or
        tokens[1].value != "Implicit" or tokens[2].value != "Arguments"):
        raise ParseError(tokens,"Cannot parse Set ImplicitArguments")
    tokens = tokens[4:]
    print "HERE EEE"
    print tokens[0]
    return (CoqSetImplicitArguments(tt[0:len(tt)-len(tokens)]),tokens)

# ****************************************************************************

class CoqGoal(CoqParseObject):
    def __init__(self,tokens,h,g,sg,fsg,og):
        CoqParseObject.__init__(self,tokens)
        self.subgoals = sg
        self.unfocused_subgoals = fsg
        self.hypotheses = h
        self.goal = g
        self.otherGoals = og
    def getListRepr(self):
        hh = []
        for h in self.hypotheses:
            hh.append(["hyp",h[0],h[1],h[2]])
        return ["Goal",self.subgoals,self.focused_subgoals,hh,self.goal,["Goals"]+self.otherGoals]
    @classmethod
    def create(cls,l,tokens):
        hh = []
        for h in l[3]:
            hh.append((h[1],h[2],h[3]))
        return CoqGoal(tokens,hh,l[4],l[1],l[2],l[5][1:])
    def getProof(self):
        return []
    def header(self):
        return "Goal"
    def __repr__(self):
        return "class CoqGoal "+str(self.subgoals)
    def __coqstr__(self):
        if (self.unfocused_subgoals > 0):
            x = str(self.subgoals) + " focused subgoals ("+str(self.unfocused_subgoals) + " unfocused goals)"
        else:
            x = str(self.subgoals) + " subgoals"
        x = x + "\n============================\n"
        for h in self.hypotheses:
            if h[2]==None:
                x = x + h[0] + " : " + h[1].__coqstr__()+"\n"
            else:
                x = x + h[0] + " := " + h[2].__coqstr__() + " : " + h[1].__coqstr__()+"\n"
        return x+self.goal.__coqstr__()

# ****************************************************************************

def parseCoqGoal(tokens):
    t = tokens
    #print "Parsing goal"
    #print tokens[0]
    #print tokens[1]
    #print tokens[2]
    #print tokens[3]
    #print tokens[4]
    #print tokens[5]
    #print tokens[6]
    #print tokens[7]
    #print tokens[8]
    #print tokens[9]
    if len(tokens)<5 or tokens[0].typ!='NUMBER':
        raise ParseError("Cannot parse goal",tokens)
    subgoals = int(tokens[0].value)
    if tokens[1].value!='subgoal' and tokens[1].value!='focused' and tokens[1].value!='subgoals':
        raise ParseError("Cannot parse goal",tokens)
    #print "Parsing goal 2"
    if tokens[1].value=='focused':
        #print "** FOCUSED PARSED **"
        if (tokens[2].value!='subgoal' and tokens[2].value!='subgoals') or tokens[3].typ !='leftParen' or tokens[6].typ!='NUMBER' or tokens[4].value!='unfocused':
            raise ParseError("Cannot parse goal",tokens)
        unfocused = int(tokens[6].value)
        #print "** FOCUSED PARSED B **"
        #print tokens[4].value
        #print tokens[5].value
        #print tokens[6].value
        #print tokens[7].value
        while tokens[7].value=='-':
            tokens = tokens[2:]
            x = int(tokens[6].value)
            unfocused = unfocused + x
        tokens = tokens[8:]
    else:
        #print "** UNFOCUSED PARSED **"
        unfocused = 0
        tokens = tokens[2:]
    hyp = []
    #print "DONE"
    #print tokens[0]
    if len(tokens) > 3 and tokens[0].typ=='comma' and tokens[1].typ=='ID' and tokens[2].typ=='NUMBER':
        tokens = tokens[3:]
    if len(tokens) > 4 and tokens[0].typ=='leftParen' and tokens[1].typ=='ID' and tokens[2].typ=='NUMBER' and tokens[3].typ=='rightParen':
        tokens = tokens[4:]
    while len(tokens)>3 and tokens[0].typ=='ID' and (tokens[1].typ=='colon' or tokens[1].typ=='colonEqual'):
        x = parseCoqExpr(tokens[2:],[[CoqLex.Token('ID','',0,0),CoqLex.Token('colon',':',0,0)],[CoqLex.Token('ID','',0,0),CoqLex.Token('colonEqual',':=',0,0)],[CoqLex.Token('colon',':',0,0)]])
        var = tokens[0].value
        #print spaces(indent)+"PARSING HYPOTHESIS "+var
        #print spaces(indent)+str(x[1][0])
        if tokens[1].typ=='colon':
            typ = x[0]
            val = None
        else:
            val = x[0]
            tokens = x[1]
            #print spaces(indent)+"After val"
            #print spaces(indent)+str(x[1][0])
            if len(tokens)<2 or tokens[0].typ!='colon':
                print tokens[0]
                print tokens[1]
                print tokens[2]
                print tokens[3]
                raise ParseError("Cannot parse goal",tokens)
            tokens = x[1]
            x = parseCoqExpr(tokens[1:],[[CoqLex.Token('ID','',0,0),CoqLex.Token('colon',':',0,0)],[CoqLex.Token('ID','',0,0),CoqLex.Token('colonEqual',':=',0,0)],[CoqLex.Token('colon',':',0,0)]])
            typ = x[0]
        hyp.append((var,typ,val))
        tokens = x[1]
    if len(tokens)<2 or tokens[0].typ!='SEPERATOR':
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("Cannot parse goal",tokens)
    tokens = tokens[1:]
    #print spaces(indent)+str(len(tokens))
    #print spaces(indent)+str(tokens)
    xx = parseCoqExpr(tokens,[[CoqLex.Token('ID','subgoal',0,0)],[CoqLex.Token('leftParen','(',0,0),CoqLex.Token('ID','dependent',0,0)]])
    tokens = xx[1]
    sg = []
    while len(tokens)>3 and tokens[0].value=='subgoal':
        if tokens[1].typ=='NUMBER' and tokens[2].value=='is' and tokens[3].typ=='colon':
            tokens = tokens[4:]
        elif tokens[1].typ=='NUMBER' and tokens[2].value=='(' and tokens[3].value=='ID' and tokens[4].typ=='NUMBER' and tokens[5].value==')':
            tokens = tokens[8:]
        else:
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse goal",tokens)
        try:
            x = parseCoqExpr(tokens,[[CoqLex.Token('ID','subgoal',0,0)]])
        except ParseError:
            #print tokens[0]
            #print tokens[1]
            return CoqGoal(t[0:len(t)-len(tokens)],hyp,xx[0],subgoals,unfocused,sg)
        sg.append(x[0])
        tokens = x[1]
    return CoqGoal(t[0:len(t)-len(tokens)],hyp,xx[0],subgoals,unfocused,sg)

# ****************************************************************************

class CoqLtac(CoqDeclaration):
    def __init__(self,tokens,x):
        CoqParseObject.__init__(self,tokens)
        self.name = x[0]
        self.params = x[1]
        self.separator = x[2]
        self.definition = x[3]
        self.unfocused = 0
        self.subgoals = 0
        self.full = False
    def dependencies(self):
        return []
        # return self.definition.dependencies()
    def definedNames(self):
        return [self.name]
    def getListRepr(self):
        x = ["Ltac",self.name]
        for p in self.params:
            x.append(p)
        x.append(self.separator)
        x.append(self.definition)
        return x
    @classmethod
    def create(cls,l,tokens):
        params = []
        for i in range(0,len(l)-4):
            params.append(l[2+i])
        return CoqDeclaration(tokens,l[1],params,l[len(l)-2],l[len(l)-1])
    def header(self):
        return "Ltac " + self.name
    def __repr__(self):
        return "class CoqLtac "+pname(self.name)
    def __coqstr__(self):
        x = "Ltac " + self.name + " "
        for i in self.params:
           x = x + i + " "
        x = x + self.separator + " " + self.definition.__coqstr__()
        return x

def parseCoqLtac(tokens):
    pos = 2 
    t = tokens
    if (len(tokens)>2 and tokens[1].typ=='ID'):
        name = tokens[1].value
    else:
        raise ParseError('Ltac header bad',tokens)
    params = []
    while (pos<len(tokens) and tokens[pos].typ=='ID'):
        params.append(tokens[pos].value)
        pos = pos+1
    if (pos >= len(tokens) or tokens[pos].typ!='colonEqual'):
        raise ParseError('Ltac header bad',tokens)
    else:
        pos = pos+1
    print "IN CYCLE5"
    x = parseCoqLtacExpr(tokens[pos:])
    print "OUT CYCLE5"
    body = x[0]
    tokens = x[1]
    if (tokens[0].typ != 'period'):
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError('Ltac header bad',tokens)
    tokens = tokens[1:]
    return (CoqLtac(t[0:len(t)-len(tokens)],(name,params,':=',body)),tokens)

# ****************************************************************************

class CoqExpression(CoqParseObject):
    def __init__(self):
        pass

class CoqOpenScope(CoqDeclaration):
    def __init__(self,t,n):
        self.name = n
        CoqParseObject.__init__(self,t)
    def dependencies(self):
        return []
    def definedNames(self):
        return [self.name]
    def getListRepr(self):
        return ["OpenScope",self.name]
    @classmethod
    def create(cls,l,tokens):
        return CoqOpenScope(tokens,l[1])
    def header(self):
        return "OpenScope " + pname(self.name)
    def __repr__(self):
        return "class CoqOpenScope "+pname(self.name)
    def __coqstr__(self):
        return "Open Scope "+pname(self.name)

def parseCoqOpenScope(tokens):
    pos = 2
    name = []
    while (tokens[pos].typ=='ID' and pos < len(tokens)-1):
        if (tokens[pos+1].typ != 'period'):
            raiseParseError('Cannot parse Require',tokens[pos+1:])
        name.append(tokens[pos].value)
        pos = pos + 2
    return (CoqOpenScope(tokens[0:pos],name),tokens[pos:])

class CoqSetPrintingDepth(CoqDeclaration):
    def __init__(self,t,n):
        CoqParseObject.__init__(self,t)
        self.name = n
    def getListRepr(self):
        return ["SetPrintingDepth",self.name]
    @classmethod
    def create(cls,l,tokens):
        return CoqSetPrintingDepth(tokens,l[1])
    def header(self):
        return "Set Printing Depth " + self.name
    def __repr__(self):
        return "class CoqSetPrintingDepth "+self.name
    def __coqstr__(self):
        return "Set Printing Depth "+self.name
    #def definedNames(self):
        #return ["@Depth"]

def parseCoqSetPrintingDepth(tokens):
    if len(tokens)<5 or tokens[3].typ!='NUMBER' or tokens[4].typ != 'period':
        raiseParseError('Cannot parse Set Printing Depth',tokens)
    name = tokens[3].value
    return (CoqSetPrintingDepth(tokens[0:5],name),tokens[5:])

class CoqUnsetImplicitArguments(CoqDeclaration):
    def __init__(self,t):
        CoqParseObject.__init__(self,t)
    def getListRepr(self):
        return ["UnsetImplicitArguments"]
    @classmethod
    def create(cls,l,tokens):
        return CoqUnsetImplicitArguments(tokens,l[1])
    def header(self):
        return "Unset Implicit Arguments"
    def __repr__(self):
        return "class CoqUnsetImplicitArguments"
    def __coqstr__(self):
        return "Unset Implicit Arguments"
    #def definedNames(self):
        #return ["@Depth"]

def parseCoqUnsetImplicitArguments(tokens):
    if len(tokens)<4:
        raiseParseError('Cannot parse Set Implicit Arguments',tokens)
    return (CoqUnsetImplicitArguments(tokens[0:4]),tokens[4:])

class CoqHint(CoqDeclaration):
    def __init__(self,t,n,d,s):
        CoqParseObject.__init__(self,t)
        self.name = n
        self.dir = d
        self.symbols = s
    def dependencies(self):
        return self.symbols
    def getListRepr(self):
        return ["Hint",self.name,self.dir,(["symbols"]+self.symbols)]
    @classmethod
    def create(cls,l,tokens):
        return CoqHint(tokens,l[1],l[2],l[3][1:])
    def header(self):
        x = "Hint " + self.name
        for s in self.symbols:
            x = x + " " + s
        return x
    def __repr__(self):
        return "class CoqHint "+self.name
    def __coqstr__(self):
        x = "Hint "+self.name
        if dir:
            x = x + " <-"
        for s in self.symbols:
            x = x + " " + s
        return s
    #def definedNames(self):
        #return ["@hint_"+self.name]

def parseCoqHint(tokens):
    t = tokens
    if len(tokens)<3 or tokens[1].typ!='ID':
        raiseParseError('Cannot parse Hint',tokens)
    name = tokens[1].value
    if name != 'Extern' and name != 'Immediate' and name != 'Constructors' and name != 'Unfold' and name != 'Transparent' and name != 'Opaque' and name != 'rewrite' and name != 'Resolve':
        raise ParseError('Cannot parse Hint',tokens)
    if tokens[2].typ=='lessDash':
        rev = True
        tokens = tokens[3:]
    elif tokens[2].typ=='dashGreater':
        rev = False
        tokens = tokens[3:]
    else:
        rev = False
        tokens = tokens[2:]
    symbols = []
    while len(tokens)>0 and tokens[0].typ=='ID':
        symbols.append(tokens[0].value)
        tokens = tokens[1:]
    if tokens[0].typ!='period':
        raise ParseError('Cannot parse Hint',tokens)
    tokens = tokens[1:]
    return (CoqHint(t[0:len(t)-len(tokens)],name,rev,symbols),tokens)

class CoqOpaque(CoqDeclaration):
    def __init__(self,t,n):
        CoqParseObject.__init__(self,t)
        self.name = n
    def dependencies(self):
        return [self.name]
    def getListRepr(self):
        return ["Opaque",self.name]
    @classmethod
    def create(cls,l,tokens):
        return CoqOpaque(tokens,l[1])
    def header(self):
        return "Opaque " + self.name
    def __repr__(self):
        return "class CoqOpaque "+self.name
    def __coqstr__(self):
        return "Opaque "+self.name

def parseCoqOpaque(tokens):
    if len(tokens)<3 or tokens[1].typ!='ID' or tokens[2].typ != 'period':
        raiseParseError('Cannot parse Opaque',tokens)
    name = tokens[1].value
    return (CoqOpaque(tokens[0:3],name),tokens[3:])

class CoqExport(CoqDeclaration):
    def __init__(self,t,n):
        CoqParseObject.__init__(self,t)
        self.name = n
    def getListRepr(self):
        x = ["Export"]
        for n in self.name:
            x.append(n)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqExport(tokens,l[1:])
    def header(self):
        return "Export " + pname(self.name)
    def __repr__(self):
        return "class CoqExport "+pname(self.name)
    def __coqstr__(self):
        return "Export "+pname(self.name)

def parseCoqExport(tokens):
    pos = 1
    name = []
    while (len(tokens)>pos and tokens[pos].typ=='ID'):
        #if (tokens[pos+1].typ != 'period'):
            #raise ParseError('Cannot parse Require',tokens[pos+1:])
        n = tokens[pos].value
        while (tokens[pos+1].typ=='period' and tokens[pos+2].typ=='ID'):
            pos = pos+2
            n = n + "." + tokens[pos].value
        print n
        name.append(n)
        pos = pos + 1
    pos = pos+1
    return (CoqExport(tokens[0:pos],name),tokens[pos:])

class CoqRequire(CoqDeclaration):
    def __init__(self,t,e,i,n):
        CoqDeclaration.__init__(self,t)
        self.is_export = e
        self.name = n
    def getListRepr(self):
        x = ["Require",self.is_export]
        for n in self.name:
            x.append(n)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqRequire(tokens,l[1],l[2:])
    def header(self):
        return "Require " + pname(self.name)
    def __repr__(self):
        e = ""
        if (self.is_export):
            e = "Export "
        return "class CoqRequire "+e+pname(self.name)
    def __coqstr__(self):
        e = ""
        if (self.is_export):
            e = "Export "
        return "Require "+e+pname(self.name)

def parseCoqRequire(tokens):
    pos = 1
    is_export = False
    is_import = False
    name = []
    if (tokens[pos].typ=='Export'):
        is_export = True
        pos = pos+1
    if (tokens[pos].typ=='Import'):
        is_import = True
        pos = pos+1
    while (len(tokens)>pos and tokens[pos].typ=='ID'):
        #if (tokens[pos+1].typ != 'period'):
            #raise ParseError('Cannot parse Require',tokens[pos+1:])
        n = tokens[pos].value
        while (len(tokens)>pos+2 and tokens[pos+1].typ=='period' and tokens[pos+2].typ=='ID' and
               tokens[pos+2].value!='Set'):
            pos = pos+2
            n = n + "." + tokens[pos].value
        print n
        name.append(n)
        pos = pos + 1
    pos = pos+1
    return (CoqRequire(tokens[0:pos],is_export,is_import,name),tokens[pos:])

class CoqImport(CoqDeclaration):
    def __init__(self,t,n):
        CoqParseObject.__init__(self,t)
        self.name = n
    def getListRepr(self):
        x = ["Import"]
        for n in self.name:
            x.append(n)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqImport(tokens,l[1:])
    def header(self):
        return "Import " + pname(self.name)
    def __repr__(self):
        return "class CoqImport "+pname(self.name)
    def __coqstr__(self):
        return "Import "+pname(self.name)

def parseCoqImport(tokens):
    pos = 1
    name = []
    while (len(tokens)>pos and tokens[pos].typ=='ID'):
        #if (tokens[pos+1].typ != 'period'):
            #raise ParseError('Cannot parse Require',tokens[pos+1:])
        n = tokens[pos].value
        while (tokens[pos+1].typ=='period' and tokens[pos+2].typ=='ID' and
               tokens[pos+2].value!='Set'):
            pos = pos+2
            n = n + "." + tokens[pos].value
        print n
        name.append(n)
        pos = pos + 1
    pos = pos+1
    return (CoqImport(tokens[0:pos],name),tokens[pos:])

def print_tn_params(l):
    s = ""
    for x in l:
        s = s + x[0] + "(" + x[1] + ") "
    return s

class CoqTacticNotation(CoqDeclaration):
    def __init__(self,n,p,t,tt):
        CoqDeclaration.__init__(self,tt)
        self.name = n
        self.params = p
        self.needsReplay = 0
        self.tactic = t
    def dependencies(self):
        return []
        #d = self.tactic.dependencies()
        #for p in self.params:
            #d = d+p.dependencies()
        #return d
    def getListRepr(self):
        x = ["TacticNotation",self.name]
        for p in self.params:
            x.append(p)
        x.append(self.tactic)
        return x
    @classmethod
    def create(cls,l,tokens):
        return CoqTacticNotation(tokens,l[1],l[2:len(l)-1],l[len(l)-1])
    def header(self):
        return "TacticNotation " + self.name
    def __repr__(self):
        e = ""
        return "class CoqTacticNotation "+self.name
    def __coqstr__(self):
        return "Tactic Notation "+'"'+self.name+'" '+print_tn_params(self.params)+":= " + self.tactic.__coqstr__()
    def definedNames(self):
        return [self.name]

def parseCoqTacticNotation(tokens):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'Tactic' or tokens[1].typ != 'Notation' or tokens[2].typ != 'QUOTATION':
        raise ParseError("Cannot parse Tactic notation",tokens)
    else:
        pos = 3
        p = []
        while len(tokens)>pos+4 and tokens[pos].typ=='ID' and (tokens[pos].value=='ident' or tokens[pos].value=='constr' or tokens[pos].value=='tactic') and tokens[pos+1].typ=='leftParen' and tokens[pos+2].typ=='ID' and tokens[pos+3].typ=='rightParen':
            p.append((tokens[pos].value,tokens[pos+2].value))
            pos = pos + 4
        if (tokens[pos].typ != 'colonEqual'):
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse Tactic notation", tokens)
        pos = pos + 1
        x = parseCoqLtacExpr(tokens[pos:])
        #print spaces(indent)+str(x)
        n = tokens[2].value[1:len(tokens[2].value)-2]
        tokens = x[1]
        if (tokens[0].typ!='period'):
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse Tactic notation", tokens)
        return (CoqTacticNotation(n,p,x[0],tt[0:len(tt)-len(tokens)+1]),tokens[1:])

class CoqAbout(CoqDeclaration):
    def __init__(self,tokens,v):
        CoqDeclaration.__init__(self,tokens)
        self.value = v
        self.unfocused = 0
        self.subgoals = 0
        self.full = False
    def dependencies(self):
        return self.value.dependencies()
    def getListRepr(self):
        return ["About",self.returnType]
    @classmethod
    def create(cls,l,tokens):
        return CoqAbout(tokens,l[1])
    def header(self):
        return "About " + self.value.__coqstr__()
    def __repr__(self):
        return "class CoqAbout "+self.value.__coqstr__()
    def __coqstr__(self):
        return "About "+self.value.__coqstr__()
    def definedNames(self):
        return []

def parseCoqAbout(tokens):
    tt = tokens
    if len(tokens)<2 or tokens[0].typ != 'About':
        raise ParseError("Cannot parse Axiom",tokens)
    return_type = None
    x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
    tokens = x[1]
    return_type = x[0]
    if len(tokens)==0 or tokens[0].typ!='period':
        print tokens[0]
        raise ParseError("Cannot parse Definition",tokens)
    tokens = tokens[1:]
    return (CoqAbout(tt[0:len(tt)-len(tokens)],return_type),tokens)

class CoqAxiom(CoqDeclaration):
    def __init__(self,tokens,n,t):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.returnType = t
        self.unfocused = 0
        self.subgoals = 0
        self.full = False
    def dependencies(self):
        x = []
        if self.returnType!=None:
            x = x+self.returnType.dependencies()
        return x
    def getListRepr(self):
        return ["Axiom",self.name,self.returnType]
    @classmethod
    def create(cls,l,tokens):
        return CoqAxiom(tokens,l[1],l[2])
    def header(self):
        return "Axiom " + self.name
    def __repr__(self):
        return "class CoqAxiom "+self.name
    def __coqstr__(self):
        x = "Axiom "+self.name
        if self.returnType != None:
            x = x + ": "+self.returnType.__coqstr__()
        #print self.body
        return x
    def definedNames(self):
        return [self.name]

def parseCoqAxiom(tokens):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'Axiom' or tokens[1].typ != 'ID':
        raise ParseError("Cannot parse Axiom",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    return_type = None
    if len(tokens)>2 and tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
        tokens = x[1]
        return_type = x[0]
    if len(tokens)==0 or tokens[0].typ!='period':
        print tokens[0]
        raise ParseError("Cannot parse Definition",tokens)
    tokens = tokens[1:]
    return (CoqAxiom(tt[0:len(tt)-len(tokens)],name,return_type),tokens)

class CoqParameter(CoqDeclaration):
    def __init__(self,tokens,n,t):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.returnType = t
    def dependencies(self):
        x = []
        if self.returnType!=None:
            x = x+self.returnType.dependencies()
        return x
    def getListRepr(self):
        return ["Parameter",self.name,self.returnType]
    @classmethod
    def create(cls,l,tokens):
        return CoqFunction(tokens,l[1],l[2])
    def header(self):
        return "Parameter " + self.name
    def __repr__(self):
        return "class CoqParameter "+self.name
    def __coqstr__(self):
        x = "Parameter "+self.name
        if self.returnType != None:
            x = x + ": "+self.returnType.__coqstr__()
        #print self.body
        return x
    def definedNames(self):
        return [self.name]

def parseCoqParameter(tokens):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'Parameter' or tokens[1].typ != 'ID':
        raise ParseError("Cannot parse Function",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    return_type = None
    if len(tokens)>2 and tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
        tokens = x[1]
        return_type = x[0]
    if len(tokens)==0 or tokens[0].typ!='period':
        print tokens[0]
        raise ParseError("Cannot parse Parameter",tokens)
    tokens = tokens[1:]
    return (CoqParameter(tt[0:len(tt)-len(tokens)],name,return_type),tokens)

class CoqFunction(CoqDeclaration):
    def __init__(self,tokens,n,ip,p,t,b):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.implicit_params = ip
        self.params = p
        self.returnType = t
        self.body = b
    def dependencies(self):
        d = []
        x = self.body.dependencies()
        for v in self.params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        for v in self.implicit_params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        if self.returnType!=None:
            x = x+self.returnType.dependencies()
        return d+x
    def getListRepr(self):
        return ["Function",self.name,(["params"]+self.implicit_params),(["params"]+self.params),self.returnType,self.body]
    @classmethod
    def create(cls,l,tokens):
        return CoqFunction(tokens,l[1],l[2][1:],l[3][1:],l[4],l[5])
    def header(self):
        return "Function " + self.name
    def __repr__(self):
        return "class CoqFunction "+self.name
    def __coqstr__(self):
        x = "Function "+self.name
        for i in self.implicit_params:
            if i[1]==None:
                x = x + " {"+i[0]+"}"
            else:
                x = x + " {"+i[0]+":"+i[1].__coqstr__()+"}"
        for i in self.params:
            if i[1]==None:
                x = x + " "+i[0]
            else:
                x = x + " ("+i[0]+":"+i[1].__coqstr__()+")"
        if self.returnType != None:
            x = x + ": "+self.returnType.__coqstr__()
        #print self.body
        return x + " := "+self.body.__coqstr__()
    def definedNames(self):
        return [self.name]

def parseCoqFunction(tokens):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'Function' or tokens[1].typ != 'ID':
        raise ParseError("Cannot parse Function",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    implicit_params = []
    while tokens[0].typ=='leftBrace':
        if len(tokens)<4 or tokens[1].typ!='ID':
            raise ParseError("Cannot parse Function",tokens)
        n = []
        pos = 1
        while (len(tokens)>pos and tokens[pos].typ=='ID'):
            n.append(tokens[pos].value)
            pos = pos+1
        if tokens[pos].typ=='colon':
           x = parseCoqExpr(tokens[pos+1:],[])
           tokens = x[1]
           t = x[0]
        else:
           tokens = tokens[pos:]
           t = None
        if (tokens[0].typ!="rightBrace"):
            raise ParseError("Cannot parse Definition",tokens)
        tokens=tokens[1:]
        for nn in n:
            implicit_params.append((nn,t))
    params = []
    while tokens[0].typ=='leftParen' or tokens[0].typ=='ID':
        if tokens[0].typ=='ID':
            params.append((tokens[0].value,None))
            tokens = tokens[1:]
        else:
            if len(tokens)<4 or tokens[1].typ!='ID':
                raise ParseError("Cannot parse Function",tokens)
            pos = 1
            n = []
            while (len(tokens)>pos and tokens[pos].typ=='ID'):
                n.append(tokens[pos].value)
                pos = pos+1
            if tokens[pos].typ=='colon':
               x = parseCoqExpr(tokens[pos+1:],[])
               tokens = x[1]
               t = x[0]
            else:
               tokens = tokens[pos:]
               t = None
            if (tokens[0].typ!="rightParen"):
                 raise ParseError("Cannot parse Function",tokens)
            tokens=tokens[1:]
            for nn in n:
                implicit_params.append((nn,t))
    return_type = None
    if len(tokens)>2 and tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[])
        tokens = x[1]
        return_type = x[0]
    if (len(tokens)<3 or tokens[0].typ!="colonEqual"):
        raise ParseError("Cannot parse Function",tokens)
    x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
    body = x[0]
    tokens = x[1]
    if len(tokens)==0 or tokens[0].typ!='period':
        print tokens[0]
        raise ParseError("Cannot parse Definition",tokens)
    tokens = tokens[1:]
    return (CoqFunction(tt[0:len(tt)-len(tokens)],name,implicit_params,params,return_type,body),tokens)

class CoqModuleType(CoqDeclaration):
    def __init__(self,tokens,n,b):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.bindings = b
    def dependencies(self):
        return []
    def getListRepr(self):
        return ["ModuleType",self.name,self.bindings]
    @classmethod
    def create(cls,l,tokens):
        return CoqModuleType(tokens,l[1],l[2])
    def header(self):
        return "Module Type " + self.name
    def __repr__(self):
        return "class CoqModuleType "+self.name
    def __coqstr__(self):
        x = "Module Type "+self.name
        for b in self.bindings:
            x = x + " ("
            if b[0]=="Import":
                x = x + "Import"
            elif b[0]=="Export":
                x = x + "Export"
            for i in b[1]:
                x = x + " " + i
            x = x + ":" + b[2].__coqstr__() + ")"
        return x

def parseCoqModuleType(tokens):
    ttt = tokens
    if len(tokens)<4:
        raise ParseError("Cannot parse module type",tokens)
    if tokens[0].typ != 'Module':
        raise ParseError("Cannot parse module type",tokens)
    if tokens[1].value != 'Type':
        raise ParseError("Cannot parse module type",tokens)
    if tokens[2].typ != 'ID':
        raise ParseError("Cannot parse module type",tokens[1:])
    v = tokens[2].value
    tokens = tokens[3:]
    b = []
    while tokens[0].typ=='leftParen':
        x = parseCoqModuleBinding(tokens)
        tokens = x[1]
        b.append(x[0])
    if tokens[0].typ != 'period':
        raise ParseError("Cannot parse module type",tokens)
    tokens = tokens[1:]
    return (CoqModuleType(ttt[0:len(ttt)-len(tokens)],v,b),tokens)

class CoqModule(CoqDeclaration):
    def __init__(self,tokens,n,b,t,tl,v):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.moduleType = t
        self.moduleTypeList = tl
        self.bindings = b
        self.value = v
    def dependencies(self):
        return []
    def getListRepr(self):
        return ["Module",self.name,self.moduleType,self.moduleTypeList,self.bindings,self.value]
    @classmethod
    def create(cls,l,tokens):
        return CoqSection(tokens,l[1],l[2],l[3],l[4],l[5])
    def header(self):
        return "Module " + self.name
    def __repr__(self):
        return "class CoqModule "+self.name
    def __coqstr__(self):
        x = "Module "+self.name
        for b in self.bindings:
            x = x + " ("
            if b[0]=="Import":
                x = x + "Import"
            elif b[0]=="Export":
                x = x + "Export"
            for i in b[1]:
                x = x + " " + i
            x = x + ":" + b[2].__coqstr__() + ")"
        if self.moduleType != None:
            x = x + " : " + self.moduleType.__coqstr__()
        for ttt in self.moduleTypeList:
            x = x + " <: " + ttt.__coqstr__()
        if self.value != None:
            x = x + " := " + self.value.__coqstr__()
        return x
    def indent(self):
        return self.value==None

def parseCoqModuleBinding(tokens):
    if tokens[0].typ != 'leftParen':
        print tokens[0]
        raise ParseError("Cannot parse module binding",tokens)
    if tokens[1].typ=='Import':
        m = 'Import'
        tokens = tokens[2:]
    elif tokens[1].typ=='Export':
        m = 'Export'
        tokens = tokens[2:]
    else:
        m = None
        tokens = tokens[1:]
    v = []
    while tokens[0].typ=='ID':
        v.append(tokens[0].value)
        tokens = tokens[1:]
    if tokens[0].typ != 'colon':
        print tokens[0]
        raise ParseError("Cannot parse module binding",tokens)
    x = parseCoqExpr(tokens[1:],[])
    tokens = x[1]
    if tokens[0].typ != 'rightParen':
        print tokens[0]
        raise ParseError("Cannot parse module binding",tokens)
    return ((m,v,x[0]),tokens[1:])

def parseCoqModule(tokens):
    ttt = tokens
    if len(tokens)<3:
        raise ParseError("Cannot parse module",tokens)
    if tokens[0].typ != 'Module':
        raise ParseError("Cannot parse module",tokens)
    if tokens[1].typ != 'ID':
        raise ParseError("Cannot parse module",tokens[1:])
    name = tokens[1].value
    tokens = tokens[2:]
    b = []
    while tokens[0].typ=='leftParen':
        x = parseCoqModuleBinding(tokens)
        b.append(x[0])
        tokens = x[1]
    mtt = []
    if tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
        mt = x[0]
        tokens = x[1]
    else:
        mt = None
        while tokens[0].typ=='lessColon':
            x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
            mtt.append(x[0])
            tokens = x[1]
    v = None
    if tokens[0].typ=='colonEqual':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
        v = x[0]
        tokens = x[1]
    if tokens[0].typ!='period':
        print tokens[0]
        raise ParseError("Cannot parse module binding",tokens)
    tokens = tokens[1:]
    return (CoqModule(ttt[0:len(ttt)-len(tokens)],name,b,mt,mtt,v),tokens)

class CoqSection(CoqDeclaration):
    def __init__(self,tokens,n):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
    def dependencies(self):
        return []
    def getListRepr(self):
        return ["Section",self.name]
    @classmethod
    def create(cls,l,tokens):
        return CoqSection(tokens,l[1])
    def header(self):
        return "Section " + self.name
    def __repr__(self):
        return "class CoqSection "+self.name
    def __coqstr__(self):
        x = "Section "+self.name
        return x
    def indent(self):
        return True

def parseCoqSection(tokens):
    if len(tokens)<3:
        raise ParseError("Cannot parse section",tokens)
    if tokens[0].typ != 'Section':
        raise ParseError("Cannot parse section",tokens)
    if tokens[1].typ != 'ID':
        raise ParseError("Cannot parse section",tokens[1:])
    if tokens[2].typ != 'period':
        raise ParseError("Cannot parse section",tokens[2:])
    return (CoqSection(tokens[0:3],tokens[1].value),tokens[3:])

class CoqEnd(CoqDeclaration):
    def __init__(self,tokens,n):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
    def dependencies(self):
        return []
    def getListRepr(self):
        return ["End",self.name]
    @classmethod
    def create(cls,l,tokens):
        return CoqSection(tokens,l[1])
    def header(self):
        return "End " + self.name
    def __repr__(self):
        return "class CoqEnd "+self.name
    def __coqstr__(self):
        x = "End "+self.name
        return x
    def undent(self):
        return True

def parseCoqEnd(tokens):
    if len(tokens)<3:
        raise ParseError("Cannot parse section",tokens)
    if tokens[0].typ != 'End':
        raise ParseError("Cannot parse section",tokens)
    if tokens[1].typ != 'ID':
        raise ParseError("Cannot parse section",tokens[1:])
    if tokens[2].typ != 'period':
        raise ParseError("Cannot parse section",tokens[2:])
    return (CoqEnd(tokens[0:3],tokens[1].value),tokens[3:])

class CoqContext(CoqDeclaration):
    def __init__(self,tokens,nl):
        CoqDeclaration.__init__(self,tokens)
        self.paramList = nl
    def dependencies(self):
        return []
    def getListRepr(self):
        return ["Context",self.paramList]
    @classmethod
    def create(cls,l,tokens):
        return CoqContext(tokens,l[1])
    def header(self):
        return "Context " + self.paramList[0][1][0]
    def __repr__(self):
        return "class CoqContext "+self.paramList[0][1][0]
    def __coqstr__(self):
        x = ""
        for p in self.paramList:
            if p[0]:
                x = "Context {"
                for n in p[1]:
                    x = x+n+" "
                x = x + ": "+p[2].__coqstr__()+"}"
            else:
                x = "Context ("
                for n in p[1]:
                    x = x+n+" "
                x = x + ": "+p[2].__coqstr__()+")"
        return x

def parseCoqContext(tokens):
    tt = tokens
    if len(tokens)<3:
        raise ParseError("Cannot parse section",tokens)
    if tokens[0].typ != 'Context':
        raise ParseError("Cannot parse section",tokens)
    nl = []
    tokens = tokens[1:]
    while tokens[0].typ=='leftBrace' or tokens[0].typ=='leftParen':
        is_bracket = False
        if tokens[0].typ=='leftBrace':
            is_bracket = True
        name = []
        tokens = tokens[1:]
        while (tokens[0].typ=='ID'):
            name.append(tokens[0].value)
            tokens = tokens[1:]
        if tokens[0].typ != 'colon':
            print tokens[0]
            raise ParseError("Cannot parse context",tokens)
        (e,tokens) = parseCoqExpr(tokens[1:],[])
        if (tokens[0].typ != 'rightBrace' and tokens[0].typ != 'rightParen'):
            raise ParseError("Cannot parse context",tokens)
        tokens = tokens[1:]
        nl.append((is_bracket,name,e))
    if (tokens[0].typ != 'period'):
        print tokens[0]
        raise ParseError("Cannot parse context",tokens[1:])
    return (CoqContext(tt[0:len(tt)-len(tokens)+1],nl),tokens[1:])

class CoqHypothesis(CoqDeclaration):
    def __init__(self,tokens,n,t):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.typ = t
    def dependencies(self):
        return []
    def getListRepr(self):
        return ["Hypothesis",self.name,t.getListRepr()]
    @classmethod
    def create(cls,l,tokens):
        return CoqContext(tokens,l[1],self.createParseObject(l[3]))
    def header(self):
        return "Hypothesis " + self.name
    def __repr__(self):
        return "class CoqHypothesis "+self.name
    def __coqstr__(self):
        x = "Hypothesis "+self.name+" : "+self.typ.__coqstr__()
        return x

def parseCoqHypothesis(tokens):
    tt = tokens
    #print "parseHypothesis"
    #print tokens[0]
    if len(tokens)<3:
        raise ParseError("Cannot parse Hypothesis",tokens)
    if tokens[0].typ != 'Hypothesis':
        raise ParseError("Cannot parse Hypothesis",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    if tokens[0].typ != 'colon':
        raise ParseError("Cannot parse Hypothesis",tokens)
    #print "HYP"
    #print tokens[0]
    (e,tokens) = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
    if (tokens[0].typ != 'period'):
        print tokens[0]
        raise ParseError("Cannot parse context",tokens[0:])
    return (CoqHypothesis(tt[0:len(tt)-len(tokens)+1],name,e),tokens[1:])

class CoqVariable(CoqDeclaration):
    def __init__(self,tokens,n,t):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.typ = t
    def dependencies(self):
        return []
    def getListRepr(self):
        return ["Variable",self.name,t.getListRepr()]
    @classmethod
    def create(cls,l,tokens):
        return CoqContext(tokens,l[1],self.createParseObject(l[3]))
    def header(self):
        x = "Variable"
        for n in self.name:
            x = x + " " + n
        return x
    def __repr__(self):
        x = "class CoqVariable"
        for n in self.name:
            x = x + " " + n
        return x
    def __coqstr__(self):
        x = "Variable"
        for n in self.name:
            x = x+" "+n
        x = x+" : "+self.typ.__coqstr__()
        return x

def parseCoqVariable(tokens):
    tt = tokens
    #print "parseHypothesis"
    #print tokens[0]
    if len(tokens)<3:
        raise ParseError("Cannot parse Variable",tokens)
    if tokens[0].typ != 'Variable':
        raise ParseError("Cannot parse Variable",tokens)
    tokens = tokens[1:]
    name = []
    has_paren = False
    if tokens[0].typ=='leftParen':
        tokens = tokens[1:]
        has_paren = True
    while tokens[0].typ=='ID':
        name.append(tokens[0].value)
        tokens = tokens[1:]
    if tokens[0].typ != 'colon':
        print tokens[0]
        raise ParseError("Cannot parse Variable",tokens)
    #print "HYP"
    #print tokens[0]
    (e,tokens) = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
    if has_paren:
        if (tokens[0].typ != 'rightParen' or tokens[1].typ != 'period'):
            print tokens[0]
            raise ParseError("Cannot parse Variable",tokens[0:])
        tokens = tokens[2:]
    else:
        if (tokens[0].typ != 'period'):
            print tokens[0]
            raise ParseError("Cannot parse Variable",tokens[0:])
        tokens = tokens[1:]
    return (CoqVariable(tt[0:len(tt)-len(tokens)],name,e),tokens)

class CoqCompute(CoqDeclaration):
    def __init__(self,tokens,e):
        CoqDeclaration.__init__(self,tokens)
        self.exp = e
    def dependencies(self):
        return e.dependencies()
    def create(cls,l,tokens):
        return CoqCompute(tokens,l[1])
    def header(self):
        return "compute " + self.exp.__coqstr__()
    def __repr__(self):
        return "class CoqCompute"
    def __coqstr__(self):
        return "compute " + self.exp.__coqstr__()
    def definedNames(self):
        return []

def parseCoqCompute(tokens):
    tt = tokens
    #print "parseHypothesis"
    #print tokens[0]
    if len(tokens)<3:
        raise ParseError("Cannot parse Compute",tokens)
    if tokens[0].typ != 'Compute' and tokens[0].typ != 'Check':
        raise ParseError("Cannot parse Compute",tokens)
    tokens = tokens[1:]
    has_paren = False
    (e,tokens) = parseCoqExpr(tokens,[[CoqLex.Token('period','.',0,0)]])
    if (tokens[0].typ != 'period'):
        print tokens[0]
        raise ParseError("Cannot parse Compute",tokens[0:])
    tokens = tokens[1:]
    return (CoqCompute(tt[0:len(tt)-len(tokens)],e),tokens)

class CoqDefinition(CoqDeclaration):
    def __init__(self,tokens,n,ip,p,t,b,pr):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.implicit_params = ip
        self.params = p
        self.returnType = t
        self.body = b
        self.proof = pr
        self.unfocused = 0
        self.subgoals = 0
        self.full = False
    def editUpdateTokens(self,line_s, col_s, line_oe, col_oe, line_ne, col_ne):
        CoqParseObject.editUpdateTokens(self, line_s, col_s, line_oe, col_oe, line_ne, col_ne)
        for p in self.proof:
            p.editUpdateTokens(line_s, col_s, line_oe, col_oe, line_ne, col_ne)
    def dependencies(self):
        d = []
        x = self.body.dependencies()
        for v in self.params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        for v in self.implicit_params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        for v in self.params:
            try:
                while (v[0] in d):
                    d.remove(v[0])
            except ValueError:
                pass
        for v in self.implicit_params:
            try:
                while (v[0] in d):
                    d.remove(v[0])
            except ValueError:
                pass
        if self.returnType!=None:
            x = x+self.returnType.dependencies()
        return d+x
    def getListRepr(self):
        return ["Definition",self.name,(["params"]+self.implicit_params),(["params"]+self.params),self.returnType,self.body,self.proof]
    @classmethod
    def create(cls,l,tokens):
        return CoqDefinition(tokens,l[1],l[2][1:],l[3][1:],l[4],l[5],l[6])
    def getCoqSuffix(self,text):
        if len(self.proof) > 0:
            return("Qed.")
        else:
            return ""
    def getSegment(self,text):
        if len(self.proof)==0 or self.full:
            return CoqParseObject.getSegment(self,text)
        l1 = self.tokens[0].line
        c1 = self.tokens[0].column
        f = -1
        g = -1
        for i in range(0,len(self.tokens)):
            if self.tokens[i].typ=='Proof' and f < 0:
               f = i-1
            if self.tokens[i].typ=='period' and g < 0:
               g = i
        if f < 0:
            f = g
        l2 = self.tokens[f].line
        c2 = self.tokens[f].column+len(self.tokens[f].value)
        tl = text[l1-1:l2]
        tl[0] = tl[0][c1:]
        tl[l2-l1] = tl[l2-l1][0:c2]
        return ("\n".join(tl),self.updateTokens(l1,c1,self.tokens))
    def header(self):
        return "Definition " + self.name
    def __repr__(self):
        return "class CoqDefinition "+self.name
    def __coqstr__(self):
        x = "Definition "+self.name
        for i in self.implicit_params:
            if i[1]==None:
                x = x + " {"+i[0]+"}"
            else:
                x = x + " {"+i[0]+":"+i[1].__coqstr__()+"}"
        for i in self.params:
            if i[1]==None:
                x = x + " "+i[0]
            else:
                x = x + " ("+i[0]+":"+i[1].__coqstr__()+")"
        if self.returnType != None:
            x = x + ": "+self.returnType.__coqstr__()
        #print self.body
        if self.body==None:
            x = x + "Proof. "
            for p in self.proof:
                x = x + " " + p.__coqstr__()
            x = x + "Qed"
        else:
            x = x + " := "+self.body.__coqstr__()
        return x
    def definedNames(self):
        return [self.name]

def parseCoqDefinition(tokens):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'Definition' or tokens[1].typ != 'ID':
        raise ParseError("Cannot parse Definition",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    implicit_params = []
    while tokens[0].typ=='leftBrace':
        if len(tokens)<4 or tokens[1].typ!='ID':
            raise ParseError("Cannot parse Definition",tokens)
        n = []
        pos = 1
        while (len(tokens)>pos and tokens[pos].typ=='ID'):
            n.append(tokens[pos].value)
            pos = pos+1
        if tokens[pos].typ=='colon':
           x = parseCoqExpr(tokens[pos+1:],[])
           tokens = x[1]
           t = x[0]
        else:
           tokens = tokens[pos:]
           t = None
        if (tokens[0].typ!="rightBrace"):
            raise ParseError("Cannot parse Definition",tokens)
        tokens=tokens[1:]
        for nn in n:
            implicit_params.append((nn,t))
    params = []
    while tokens[0].typ=='leftParen' or tokens[0].typ=='ID':
        if tokens[0].typ=='ID':
            params.append((tokens[0].value,None))
            tokens = tokens[1:]
        else:
            if len(tokens)<4 or tokens[1].typ!='ID':
                raise ParseError("Cannot parse Definition",tokens)
            pos = 1
            n = []
            while (len(tokens)>pos and tokens[pos].typ=='ID'):
                n.append(tokens[pos].value)
                pos = pos+1
            if tokens[pos].typ=='colon':
               x = parseCoqExpr(tokens[pos+1:],[])
               tokens = x[1]
               t = x[0]
            else:
               tokens = tokens[pos:]
               t = None
            if (len(tokens)==0 or tokens[0].typ!="rightParen"):
                 raise ParseError("Cannot parse Definition",tokens)
            tokens=tokens[1:]
            for nn in n:
                implicit_params.append((nn,t))
    return_type = None
    if len(tokens)>2 and tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
        tokens = x[1]
        return_type = x[0]
    pr = []
    print "HERE xxx"
    if (len(tokens)>3 and tokens[0].typ=="period" and tokens[1].typ=="Admitted" and
        tokens[2].typ=='period'):
        tokens = tokens[3:]
        body = None
        pr = []
    elif (len(tokens)>2 and (tokens[0].typ=="period" or tokens[0].typ=="Proof")):
        if (tokens[0].typ=="Proof"):
            tokens = tokens[1:]
        body = None
        tokens = tokens[1:]
        if tokens[0].typ=="Proof" and tokens[1].typ=="period":
            tokens = tokens[2:]
        while len(tokens)>0 and tokens[0].typ!='Qed' and tokens[0].typ!='Abort':
            x = parseCoqLtacExpr(tokens)
            print x[0]
            pr.append(x[0])
            tokens = x[1]
            if len(tokens)==0 or tokens[0].typ != 'period':
                print tokens[0]
                print tokens[1]
                print tokens[2]
                print tokens[3]
                raise ParseError("Cannot parse Fixpoint",tokens)
            x[0].tokens.append(tokens[0])
            tokens = tokens[1:]
        if len(tokens)<2 or (tokens[0].typ!='Qed' and tokens[0].typ!='Abort') or tokens[1].typ != 'period':
            raise ParseError("Cannot parse Fixpoint",tokens)
        tokens = tokens[2:]
    elif (len(tokens)<3 or tokens[0].typ!="colonEqual"):
        print tokens[0]
        raise ParseError("Cannot parse Definition",tokens)
    else:
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
        body = x[0]
        tokens = x[1]
        print "&&&&&&&"
        print name
        print tokens[0]
        if len(tokens)==0 or tokens[0].typ!='period':
            print tokens[0]
            raise ParseError("Cannot parse Definition",tokens)
        tokens = tokens[1:]
    return (CoqDefinition(tt[0:len(tt)-len(tokens)],name,implicit_params,params,return_type,body,pr),tokens)

class CoqNotation(CoqDeclaration):
    def __init__(self,tokens,q,e,l,a):
        CoqDeclaration.__init__(self,tokens)
        self.quotation = q
        self.expr = e
        self.level = l
        self.name = q
        self.associativity = a
    def dependencies(self):
        return self.expr.dependencies()
    def getListRepr(self):
        return ["Notation",self.quotation,self.expr,self.level,self.associativity]
    @classmethod
    def create(cls,l,tokens):
        return CoqNotation(tokens,l[1],l[2],l[3],l[4])
    def header(self):
        return "Notation \"" + self.quotation + "\""
    def __repr__(self):
        return "Notation \"" + self.quotation + "\""
    def __coqstr__(self):
        x = "Notation \""+self.quotation+"\" ("+self.expr.__coqstr__()+")"
        if self.level!=None:
            x = x + " (at level "+str(x)+")"
        return x
    def definedNames(self):
        tk = CoqLex.tokenize(self.quotation)
        n = []
        for t in tk:
            if t.typ=='SQUOTATION' or t.typ=='QUOTATION':
                n.append(t.value[1:len(t.value)-1])
        return n

def parseCoqNotation(tokens):
    tt = tokens
    if len(tokens)<5 or (tokens[0].value != 'Notation' and tokens[0].value != 'Infix') or (tokens[1].typ != 'QUOTATION' and tokens[1].typ != 'ID') or tokens[2].typ!='colonEqual':
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("Cannot parse Notation",tokens)
    if tokens[1].typ=='QUOTATION':
        quotation = tokens[1].value[1:len(tokens[1].value)-1]
    else:
        quotation = tokens[1].value
    if tokens[3].typ=='leftParen':
        x = parseCoqExpr(tokens[4:],[])
        tokens = x[1]
        expr = x[0]
        if (len(tokens)<2 or tokens[0].typ!="rightParen"):
            raise ParseError("Cannot parse Notation",tokens)
        tokens = tokens[1:]
    elif tokens[3].typ=='ID':
        expr = CoqNameExpr(tokens[3:3],[tokens[3].value])
        tokens = tokens[4:]
    if tokens[0].typ=='leftParen':
        if len(tokens)<5 or tokens[1].typ!="at" or tokens[2].value!='level' or tokens[3].typ!='NUMBER' or (tokens[4].typ!='rightParen' and tokens[4].typ!='comma'):
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse Notation",tokens)
        level = int(tokens[3].value)
        associativity = None
        if tokens[4].typ=='comma':
            if tokens[5].value=='right' or tokens[5].value=='left':
                associativity = tokens[5].value
            else:
                print tokens[0]
                print tokens[1]
                print tokens[2]
                print tokens[3]
                raise ParseError("Cannot parse Notation",tokens)
            if tokens[6].value!='associativity' or tokens[7].typ!='rightParen':
                print tokens[0]
                print tokens[1]
                print tokens[2]
                print tokens[3]
                print tokens[4]
                print tokens[5]
                print tokens[6]
                print tokens[7]
                raise ParseError("Cannot parse Notation",tokens)
            tokens = tokens[8:]
        else:
            tokens = tokens[5:]
    else:
        associativity = None
        level = None
    if tokens[0].typ=='colon' and tokens[1].typ=='ID':
        tokens = tokens[2:]
    if len(tokens)==0 or tokens[0].typ!='period':
        print tokens[0]
        raise ParseError("Cannot parse Notation",tokens)
    tokens = tokens[1:]
    return (CoqNotation(tt[0:len(tt)-len(tokens)],quotation,expr,level,associativity),tokens)

class CoqFixpoint(CoqDeclaration):
    def __init__(self,tokens,n,ip,p,t,b,o,pr):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.implicit_params = ip
        self.params = p
        self.returnType = t
        self.order = o
        self.body = b
        self.proof = pr
    def editUpdateTokens(self,line_s, col_s, line_oe, col_oe, line_ne, col_ne):
        CoqParseObject.editUpdateTokens(self, line_s, col_s, line_oe, col_oe, line_ne, col_ne)
        for p in self.proof:
            p.editUpdateTokens(line_s, col_s, line_oe, col_oe, line_ne, col_ne)
    def dependencies(self):
        d = []
        if self.body == None:
            x = []
        else:
            x = self.body.dependencies()
        for v in self.params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        for v in self.implicit_params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        for v in self.params:
            try:
                while (v[0] in d):
                    d.remove(v[0])
            except ValueError:
                pass
        for v in self.implicit_params:
            try:
                while (v[0] in d):
                    d.remove(v[0])
            except ValueError:
                pass
        try:
            while (self.name in x):
                x.remove(self.name)
        except ValueError:
            pass
        if self.returnType!=None:
            x = x+self.returnType.dependencies()
        return d+x
    def getListRepr(self):
        return ["Fixpoint",self.name,(["params"]+self.implicit_params),(["params"]+self.params),self.returnType,self.order,self.body,self.proof]
    @classmethod
    def create(cls,l,tokens):
        return CoqFixpoint(tokens,l[1],l[2][1:],l[3][1:],l[4],l[5],l[6],l[7])
    def getProof(self):
        return self.proof
    def getCoqSuffix(self,text):
        if len(self.proof) > 0:
            return("Qed.")
        else:
            return ""
    def getSegment(self,text):
        l1 = self.tokens[0].line
        c1 = self.tokens[0].column
        f = -1
        g = -1
        for i in range(0,len(self.tokens)):
            if self.tokens[i].typ=='Proof' and f < 0:
               f = i-1
            if self.tokens[i].typ=='period' and g < 0:
               g = i
        if f < 0:
            f = g
        l2 = self.tokens[f].line
        c2 = self.tokens[f].column+len(self.tokens[f].value)
        tl = text[l1-1:l2]
        tl[0] = tl[0][c1:]
        tl[l2-l1] = tl[l2-l1][0:c2]
        return ("\n".join(tl),self.updateTokens(l1,c1,self.tokens))
    def definedNames(self):
        return [self.name]
    def header(self):
        return "Fixpoint " + self.name
    def __repr__(self):
        return "class CoqFixpoint "+self.name
    def __coqstr__(self):
        x = "Fixpoint "+self.name
        for i in self.implicit_params:
            if i[1]==None:
                x = x + " {"+i[0]+"}"
            else:
                x = x + " {"+i[0]+":"+i[1].__coqstr__()+"}"
        for i in self.params:
            if i[1]==None:
                x = x + " "+i[0]
            else:
                x = x + " ("+i[0]+":"+i[1].__coqstr__()+")"
        if self.order != None:
            x = x + " {struct "+self.order+"}"
        if self.returnType != None:
            x = x + ": "+self.returnType.__coqstr__()
        if self.body==None:
            x = x + "Proof. "
            for p in self.proof:
                x = x + " " + p.__coqstr__()
            x = x + "Qed"
        else:
            x = x + " := "+self.body.__coqstr__()
        return x
    def definedNames(self):
        return [self.name]

def parseCoqFixpoint(tokens):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'Fixpoint' or tokens[1].typ != 'ID':
        raise ParseError("Cannot parse Fixpoint",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    implicit_params = []
    pr = []
    while tokens[0].typ=='leftBrace':
        if len(tokens)<4 or tokens[1].typ!='ID':
            raise ParseError("Cannot parse Fixpoint",tokens)
        n = []
        pos = 1
        while (len(tokens)>pos and tokens[pos].typ=='ID'):
            n.append(tokens[pos].value)
            pos = pos+1
        if tokens[pos].typ=='colon':
           x = parseCoqExpr(tokens[pos+1:],[])
           tokens = x[1]
           t = x[0]
        else:
           tokens = tokens[pos:]
           t = None
        if (tokens[0].typ!="rightBrace"):
            raise ParseError("Cannot parse Fixpoint",tokens)
        tokens=tokens[1:]
        for nn in n:
            implicit_params.append((nn,t))
    params = []
    while tokens[0].typ=='leftParen' or tokens[0].typ=='ID':
        if tokens[0].typ=='ID':
            params.append((tokens[0].value,None))
            tokens = tokens[1:]
        else:
            if len(tokens)<4 or tokens[1].typ!='ID':
                raise ParseError("Cannot parse Fixpoint",tokens)
            pos = 1
            n = []
            while (len(tokens)>pos and tokens[pos].typ=='ID'):
                n.append(tokens[pos].value)
                pos = pos+1
            if tokens[pos].typ=='colon':
               x = parseCoqExpr(tokens[pos+1:],[])
               tokens = x[1]
               t = x[0]
            else:
               tokens = tokens[pos:]
               t = None
            if (tokens[0].typ!="rightParen"):
                 raise ParseError("Cannot parse Fixpoint",tokens)
            tokens=tokens[1:]
            for nn in n:
                implicit_params.append((nn,t))
    order = None
    if len(tokens)>4 and tokens[0].typ=='leftBrace' and tokens[1].value=='struct' and tokens[2].typ=='ID' and tokens[3].typ=='rightBrace':
        order = tokens[2].value
        tokens = tokens[4:]
    return_type = None
    if len(tokens)>2 and tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
        tokens = x[1]
        return_type = x[0]
    if (len(tokens)>2 and tokens[0].typ=="period"):
        body = None
        tokens = tokens[1:]
        if tokens[0].typ=="Proof" and tokens[1].typ=="period":
            tokens = tokens[2:]
        while len(tokens)>0 and tokens[0].typ!='Qed' and tokens[0].typ!='Abort':
            x = parseCoqLtacExpr(tokens)
            print x[0]
            pr.append(x[0])
            tokens = x[1]
            if len(tokens)==0 or tokens[0].typ != 'period':
                print tokens[0]
                print tokens[1]
                print tokens[2]
                print tokens[3]
                raise ParseError("Cannot parse Fixpoint",tokens)
            x[0].tokens.append(tokens[0])
            tokens = tokens[1:]
        if len(tokens)<2 or (tokens[0].typ!='Qed' and tokens[0].typ!='Abort') or tokens[1].typ != 'period':
            raise ParseError("Cannot parse Fixpoint",tokens)
        tokens = tokens[2:]
    elif (len(tokens)<3 or tokens[0].typ!="colonEqual"):
        if (len(tokens)>0):
            print tokens[0]
        raise ParseError("Cannot parse Fixpoint",tokens)
    else:
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
        body = x[0]
        tokens = x[1]
        if len(tokens)==0 or tokens[0].typ!='period':
            raise ParseError("Cannot parse Fixpoint",tokens)
        tokens = tokens[1:]
    return (CoqFixpoint(tt[0:len(tt)-len(tokens)],name,implicit_params,params,return_type,body,order,pr),tokens)

class CoqCoFixpoint(CoqDeclaration):
    def __init__(self,tokens,n,ip,p,t,b,o,pr):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.implicit_params = ip
        self.params = p
        self.returnType = t
        self.order = o
        self.body = b
        self.proof = pr
    def editUpdateTokens(self,line_s, col_s, line_oe, col_oe, line_ne, col_ne):
        CoqParseObject.editUpdateTokens(self, line_s, col_s, line_oe, col_oe, line_ne, col_ne)
        for p in self.proof:
            p.editUpdateTokens(line_s, col_s, line_oe, col_oe, line_ne, col_ne)
    def dependencies(self):
        d = []
        x = self.body.dependencies()
        for v in self.params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        for v in self.implicit_params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        for v in self.params:
            try:
                while (v[0] in d):
                    d.remove(v[0])
            except ValueError:
                pass
        for v in self.implicit_params:
            try:
                while (v[0] in d):
                    d.remove(v[0])
            except ValueError:
                pass
        try:
            while (self.name in x):
                x.remove(self.name)
        except ValueError:
            pass
        if self.returnType!=None:
            x = x+self.returnType.dependencies()
        return d+x
    def getListRepr(self):
        return ["CoFixpoint",self.name,(["params"]+self.implicit_params),(["params"]+self.params),self.returnType,self.order,self.body,self.proof]
    @classmethod
    def create(cls,l,tokens):
        return CoqCoFixpoint(tokens,l[1],l[2][1:],l[3][1:],l[4],l[5],l[6],l[7])
    def getProof(self):
        return self.proof
    def getCoqSuffix(self,text):
        return("Qed.")
    def getSegment(self,text):
        l1 = self.tokens[0].line
        c1 = self.tokens[0].column
        f = -1
        g = -1
        for i in range(0,len(self.tokens)):
            if self.tokens[i].typ=='Proof' and f < 0:
               f = i-1
            if self.tokens[i].typ=='period' and g < 0:
               g = i
        if f < 0:
            f = g
        l2 = self.tokens[f].line
        c2 = self.tokens[f].column+len(self.tokens[f].value)
        tl = text[l1-1:l2]
        tl[0] = tl[0][c1:]
        tl[l2-l1] = tl[l2-l1][0:c2]
        return ("\n".join(tl),self.updateTokens(l1,c1,self.tokens))
    def definedNames(self):
        return [self.name]
    def header(self):
        return "CoFixpoint " + self.name
    def __repr__(self):
        return "class CoqCoFixpoint "+self.name
    def __coqstr__(self):
        x = "CoFixpoint "+self.name
        for i in self.implicit_params:
            if i[1]==None:
                x = x + " {"+i[0]+"}"
            else:
                x = x + " {"+i[0]+":"+i[1].__coqstr__()+"}"
        for i in self.params:
            if i[1]==None:
                x = x + " "+i[0]
            else:
                x = x + " ("+i[0]+":"+i[1].__coqstr__()+")"
        if self.order != None:
            x = x + " {struct "+self.order+"}"
        if self.returnType != None:
            x = x + ": "+self.returnType.__coqstr__()
        if self.body==None:
            x = x + "Proof. "
            for p in self.proof:
                x = x + " " + p.__coqstr__()
            x = x + "Qed"
        else:
            x = x + " := "+self.body.__coqstr__()
        return x
    def definedNames(self):
        return [self.name]

def parseCoqCoFixpoint(tokens):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'CoFixpoint' or tokens[1].typ != 'ID':
        raise ParseError("Cannot parse CoFixpoint",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    implicit_params = []
    pr = []
    while tokens[0].typ=='leftBrace':
        if len(tokens)<4 or tokens[1].typ!='ID':
            raise ParseError("Cannot parse CoFixpoint",tokens)
        n = []
        pos = 1
        while (len(tokens)>pos and tokens[pos].typ=='ID'):
            n.append(tokens[pos].value)
            pos = pos+1
        if tokens[pos].typ=='colon':
           x = parseCoqExpr(tokens[pos+1:],[])
           tokens = x[1]
           t = x[0]
        else:
           tokens = tokens[pos:]
           t = None
        if (tokens[0].typ!="rightBrace"):
            raise ParseError("Cannot parse CoFixpoint",tokens)
        tokens=tokens[1:]
        for nn in n:
            implicit_params.append((nn,t))
    params = []
    while tokens[0].typ=='leftParen' or tokens[0].typ=='ID':
        if tokens[0].typ=='ID':
            params.append((tokens[0].value,None))
            tokens = tokens[1:]
        else:
            if len(tokens)<4 or tokens[1].typ!='ID':
                raise ParseError("Cannot parse CoFixpoint",tokens)
            pos = 1
            n = []
            while (len(tokens)>pos and tokens[pos].typ=='ID'):
                n.append(tokens[pos].value)
                pos = pos+1
            if tokens[pos].typ=='colon':
               x = parseCoqExpr(tokens[pos+1:],[])
               tokens = x[1]
               t = x[0]
            else:
               tokens = tokens[pos:]
               t = None
            if (tokens[0].typ!="rightParen"):
                 raise ParseError("Cannot parse CoFixpoint",tokens)
            tokens=tokens[1:]
            for nn in n:
                implicit_params.append((nn,t))
    order = None
    if len(tokens)>4 and tokens[0].typ=='leftBrace' and tokens[1].value=='struct' and tokens[2].typ=='ID' and tokens[3].typ=='rightBrace':
        order = tokens[2].value
        tokens = tokens[4:]
    return_type = None
    if len(tokens)>2 and tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
        tokens = x[1]
        return_type = x[0]
    if (len(tokens)>2 and tokens[0].typ=="period"):
        body = None
        tokens = tokens[1:]
        if tokens[0].typ=="Proof" and tokens[1].typ=="period":
            tokens = tokens[2:]
        while len(tokens)>0 and tokens[0].typ!='Qed' and tokens[0].typ!='Abort':
            x = parseCoqLtacExpr(tokens)
            print x[0]
            pr.append(x[0])
            tokens = x[1]
            if len(tokens)==0 or tokens[0].typ != 'period':
                print tokens[0]
                print tokens[1]
                print tokens[2]
                print tokens[3]
                raise ParseError("Cannot parse CoFixpoint",tokens)
            x[0].tokens.append(tokens[0])
            tokens = tokens[1:]
        if len(tokens)<2 or (tokens[0].typ!='Qed' and tokens[0].typ!='Abort') or tokens[1].typ != 'period':
            raise ParseError("Cannot parse CoFixpoint",tokens)
        tokens = tokens[2:]
    elif (len(tokens)<3 or tokens[0].typ!="colonEqual"):
        if (len(tokens)>0):
            print tokens[0]
        raise ParseError("Cannot parse CoFixpoint",tokens)
    else:
        x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
        body = x[0]
        tokens = x[1]
        if len(tokens)==0 or tokens[0].typ!='period':
            raise ParseError("Cannot parse CoFixpoint",tokens)
        tokens = tokens[1:]
    return (CoqCoFixpoint(tt[0:len(tt)-len(tokens)],name,implicit_params,params,return_type,body,order,pr),tokens)

class CoqRecord(CoqDeclaration):
    def __init__(self,tokens,n,p,t,c,f):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.params = p
        self.inductive_type = t
        self.constructor = c
        self.fields = f
    def dependencies(self):
        d = []
        x = []
        for f in self.fields:
            if f[1]!=None:
                x = x + f[1].dependencies()
        for v in self.params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        if self.inductive_type!=None:
            x = x+self.inductive_type.dependencies()
        while (self.name in x):
            x.remove(self.name)
        return d+x
    def getListRepr(self):
        x = ["Record",self.name,(["params"]+self.params),self.inductive_type,self.constructor]
        for f in self.fields:
            x = x + ["field",c[0],c[1]]
        return x
    @classmethod
    def create(cls,l,tokens):
        fields = []
        for i in range(5,len(l)):
            fields.append((l[i][1],l[i][2]))
        return CoqInductive(tokens,l[1],l[2][1:],l[3],l[4],fields)
    def header(self):
        return "Record " + self.name
    def __repr__(self):
        return "class CoqRecord "+self.name
    def __coqstr__(self):
        x = "Record "+self.name
        for i in self.params:
            if i[1]==None:
                x = x + " "+i[0]
            else:
                x = x + " ("+i[0]+":"+i[1].__coqstr__()+")"
        if self.inductive_type != None:
            x = x + ": "+self.inductive_type.__coqstr__()
        x = x + " := "
        if self.constructor==None:
            x = x + "{"
        else:
            x = x + self.constructor + " {"
        first = True
        for f in self.fields:
            if first==False:
                x = x + "; "
            first = False
            if f[1]==None:
                x = x + f[0]
            else:
                x = x + f[0] + " : " + f[1].__coqstr__()
        return x
    def definedNames(self):
        return [self.name]

def parseCoqRecord(tokens):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'Record' or tokens[1].typ != 'ID':
        raise ParseError("Cannot parse Record",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    params = []
    while tokens[0].typ=='leftParen' or tokens[0].typ=='ID':
        if tokens[0].typ=='ID':
            params.append((tokens[0].value,None))
            tokens = tokens[1:]
        else:
            if len(tokens)<4 or tokens[1].typ!='ID':
                raise ParseError("Cannot parse Inductive",tokens)
            pos = 1
            n = []
            while (len(tokens)>pos and tokens[pos].typ=='ID'):
                n.append(tokens[pos].value)
                pos = pos+1
            if tokens[pos].typ=='colon':
               x = parseCoqExpr(tokens[pos+1:],[])
               tokens = x[1]
               t = x[0]
            else:
               tokens = tokens[pos:]
               t = None
            if (tokens[0].typ!="rightParen"):
                 raise ParseError("Cannot parse Inductive",tokens)
            tokens=tokens[1:]
            for nn in n:
                implicit_params.append((nn,t))
    if len(tokens)>2 and tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[])
        tokens = x[1]
        return_type = x[0]
    elif len(tokens)>2 and tokens[0].typ=='colonEqual':
        return_type = None
    else:
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("Cannot parse Record",tokens)
    if (len(tokens)<3 or tokens[0].typ!="colonEqual"):
        raise ParseError("Cannot parse Record",tokens)
    constructor = None
    if tokens[1].typ=='ID':
        constructor = tokens[1].value
        tokens = tokens[2:]
    else:
        tokens = tokens[1:]
    if tokens[0].typ != 'leftBrace':
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("Cannot parse Record",tokens)
    tokens = tokens[1:]
    first = True
    fields = []
    while first or tokens[0].typ=='semicolon':
        if tokens[0].typ=='semicolon':
            tokens = tokens[1:]
        elif first==False:
            raise ParseError("Cannot parse Record",tokens)
        if len(tokens)<1 or tokens[0].typ!='ID':
            raise ParseError("Cannot parse Record",tokens)
        n = tokens[0].value
        if tokens[1].typ=='colon':
            x = parseCoqExpr(tokens[2:],[[CoqLex.Token('period','.',0,0)]])
            fields.append((n,x[0]))
            tokens = x[1]
        else:
            print tokens[0]
            print tokens[1]
            print tokens[2]
            print tokens[3]
            raise ParseError("Cannot parse Record",tokens)
        first = False
    if len(tokens) < 2 or tokens[0].typ!='rightBrace' or tokens[1].typ!='period':
        raise ParseError("Cannot parse Record",tokens)
    tokens = tokens[2:]
    return (CoqRecord(tt[0:len(tt)-len(tokens)],name,params,return_type,constructor,fields),tokens)

class CoqInductive(CoqDeclaration):
    def __init__(self,tokens,n,ip,p,t,c):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.implicit_params = ip
        self.params = p
        self.inductive_type = t
        self.cases = c
    def dependencies(self):
        d = []
        x = []
        for c in self.cases:
            if c[2]!=None:
                x = x + c[2].dependencies()
        for v in self.params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        for v in self.implicit_params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        if self.inductive_type!=None:
            x = x+self.inductive_type.dependencies()
        while (self.name in x):
            x.remove(self.name)
        return d+x
    def getListRepr(self):
        x = ["Inductive",self.name,(["params"]+self.implicit_params),(["params"]+self.params),self.inductive_type]
        for c in cases:
            x = x + ["case",c[0],c[1],c[2]]
        return x
    @classmethod
    def create(cls,l,tokens):
        cases = []
        for i in range(4,len(l)):
            cases.append((l[i][1],l[i][2]))
        return CoqInductive(tokens,l[1],l[2][1:],l[3][1:],cases)
    def header(self):
        return "Inductive " + self.name
    def __repr__(self):
        return "class CoqInductive "+self.name
    def __coqstr__(self):
        x = "Inductive "+self.name
        for i in self.implicit_params:
            if i[1]==None:
                x = x + " {"+i[0]+"}"
            else:
                x = x + " {"+i[0]+":"+i[1].__coqstr__()+"}"
        for i in self.params:
            if i[1]==None:
                x = x + " "+i[0]
            else:
                x = x + " ("+i[0]+":"+i[1].__coqstr__()+")"
        if self.inductive_type != None:
            x = x + ": "+self.inductive_type.__coqstr__()
        for c in self.cases:
            x = x + " | " + c[0]
            for p in c[1]:
                if p[1]==None:
                    x = x+" "+p[0]
                else:
                    x = x+" ("+p[0]+":"+p[1].__coqstr__()+")"
            if c[2]!=None:
                x = x + " : " + c[2].__coqstr__()
        return x
    def definedNames(self):
        return [self.name]

def parseCoqInductive(tokens):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'Inductive':
        raise ParseError("Cannot parse Inductive",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    implicit_params = []
    while tokens[0].typ=='leftBrace':
        if len(tokens)<4 or tokens[1].typ!='ID':
            raise ParseError("Cannot parse Inductive",tokens)
        n = []
        pos = 1
        while (len(tokens)>pos and tokens[pos].typ=='ID'):
            n.append(tokens[pos].value)
            pos = pos+1
        if tokens[pos].typ=='colon':
           x = parseCoqExpr(tokens[pos+1:],[])
           tokens = x[1]
           t = x[0]
        else:
           tokens = tokens[pos:]
           t = None
        if (tokens[0].typ!="rightBrace"):
            raise ParseError("Cannot parse Inductive",tokens)
        tokens=tokens[1:]
        for nn in n:
            implicit_params.append((nn,t))
    params = []
    while tokens[0].typ=='leftParen' or tokens[0].typ=='ID':
        if tokens[0].typ=='ID':
            params.append((tokens[0].value,None))
            tokens = tokens[1:]
        else:
            if len(tokens)<4 or tokens[1].typ!='ID':
                raise ParseError("Cannot parse Inductive",tokens)
            pos = 1
            n = []
            while (len(tokens)>pos and tokens[pos].typ=='ID'):
                n.append(tokens[pos].value)
                pos = pos+1
            if tokens[pos].typ=='colon':
               x = parseCoqExpr(tokens[pos+1:],[])
               tokens = x[1]
               t = x[0]
            else:
               tokens = tokens[pos:]
               t = None
            if (tokens[0].typ!="rightParen"):
                 raise ParseError("Cannot parse Inductive",tokens)
            tokens=tokens[1:]
            for nn in n:
                implicit_params.append((nn,t))
    order = None
    if len(tokens)>4 and tokens[0].typ=='leftBrace' and tokens[1].value=='struct' and tokens[2].typ=='ID' and tokens[3].typ=='rightBrace':
        order = tokens[2].value
        tokens = tokens[4:]
    if len(tokens)>2 and tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[])
        tokens = x[1]
        return_type = x[0]
    elif len(tokens)>2 and tokens[0].typ=='colonEqual':
        return_type = None
    else:
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("Cannot parse inductive",tokens)
    if (len(tokens)<3 or tokens[0].typ!="colonEqual"):
        raise ParseError("Cannot parse Inductive",tokens)
    cases = []
    if tokens[1].typ=='bar':
        tokens = tokens[2:]
    else:
        tokens = tokens[1:]
    first = True
    while len(tokens)>0 and (first or tokens[0].typ=='bar'):
        if tokens[0].typ=='bar':
            tokens = tokens[1:]
        elif first==False:
            raise ParseError("Cannot parse Inductive",tokens)
        if len(tokens)<1 or tokens[0].typ!='ID':
            raise ParseError("Cannot parse Inductive",tokens)
        n = tokens[0].value
        tokens = tokens[1:]
        pp = []
        while tokens[0].typ=='ID' or tokens[0].typ=='leftParen':
            if tokens[0].typ=='ID':
                pp.append((tokens[0].value,None))
                tokens = tokens[1:]
            else:
                if len(tokens)<4 or tokens[1].typ!='ID' or tokens[2].typ!='colon':
                    print tokens[0]
                    raise ParseError("Cannot parse Inductive",tokens)
                x = parseCoqExpr(tokens[3:],[[CoqLex.Token('period','.',0,0)],[CoqLex.Token('colon',':',0,0)]])
                pp.append((tokens[1].value,x[0]))
                tokens = x[1]
                if tokens[0].typ!='rightParen':
                    print tokens[0]
                    raise ParseError("Cannot parse Inductive",tokens)
                tokens = tokens[1:]
        if tokens[0].typ=='colon':
            x = parseCoqExpr(tokens[1:],[[CoqLex.Token('period','.',0,0)]])
            cases.append((n,pp,x[0]))
            tokens = x[1]
        else:
            cases.append((n,pp,None))
        first = False
    if len(tokens)==0 or tokens[0].typ!='period':
        if len(tokens)>0:
            print tokens[0]
        else:
            print "End of file"
        raise ParseError("Cannot parse Inductive",tokens)
    tokens = tokens[1:]
    return (CoqInductive(tt[0:len(tt)-len(tokens)],name,implicit_params,params,return_type,cases),tokens)

class CoqCoInductive(CoqDeclaration):
    def __init__(self,tokens,n,ip,p,t,c):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.implicit_params = ip
        self.params = p
        self.inductive_type = t
        self.cases = c
    def dependencies(self):
        d = []
        x = []
        for c in self.cases:
            if c[2]!=None:
                x = x + c[2].dependencies()
        for v in self.params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        for v in self.implicit_params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    x.remove(v[0])
            except ValueError:
                pass
        if self.inductive_type!=None:
            x = x+self.inductive_type.dependencies()
        while (self.name in x):
            x.remove(self.name)
        return d+x
    def getListRepr(self):
        x = ["CoInductive",self.name,(["params"]+self.implicit_params),(["params"]+self.params),self.inductive_type]
        for c in cases:
            x = x + ["case",c[0],c[1],c[2]]
        return x
    @classmethod
    def create(cls,l,tokens):
        cases = []
        for i in range(4,len(l)):
            cases.append((l[i][1],l[i][2],l[i][3]))
        return CoqCoInductive(tokens,l[1],l[2][1:],l[3][1:],cases)
    def header(self):
        return "CoInductive " + self.name
    def __repr__(self):
        return "class CoqCoInductive "+self.name
    def __coqstr__(self):
        x = "CoInductive "+self.name
        for i in self.implicit_params:
            if i[1]==None:
                x = x + " {"+i[0]+"}"
            else:
                x = x + " {"+i[0]+":"+i[1].__coqstr__()+"}"
        for i in self.params:
            if i[1]==None:
                x = x + " "+i[0]
            else:
                x = x + " ("+i[0]+":"+i[1].__coqstr__()+")"
        if self.inductive_type != None:
            x = x + ": "+self.inductive_type.__coqstr__()
        for c in self.cases:
            if c[2]==None:
                x = x + " | " + c[0]
                for i in c[1]:
                   x = x+" "+i
            else:
                x = x + " | " + c[0]
                for i in c[1]:
                   x = x+" "+i
                x = x + " : " + c[2].__coqstr__()
        return x
    def definedNames(self):
        return [self.name]

def parseCoqCoInductive(tokens):
    tt = tokens
    if len(tokens)<4 or tokens[0].typ != 'CoInductive' or tokens[1].typ != 'ID':
        raise ParseError("Cannot parse Inductive",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    implicit_params = []
    while tokens[0].typ=='leftBrace':
        if len(tokens)<4 or tokens[1].typ!='ID':
            raise ParseError("Cannot parse Inductive",tokens)
        n = []
        pos = 1
        while (len(tokens)>pos and tokens[pos].typ=='ID'):
            n.append(tokens[pos].value)
            pos = pos+1
        if tokens[pos].typ=='colon':
           x = parseCoqExpr(tokens[pos+1:],[])
           tokens = x[1]
           t = x[0]
        else:
           tokens = tokens[pos:]
           t = None
        if (tokens[0].typ!="rightBrace"):
            raise ParseError("Cannot parse Inductive",tokens)
        tokens=tokens[1:]
        for nn in n:
            implicit_params.append((nn,t))
    params = []
    while tokens[0].typ=='leftParen' or tokens[0].typ=='ID':
        if tokens[0].typ=='ID':
            params.append((tokens[0].value,None))
        else:
            if len(tokens)<4 or tokens[1].typ!='ID':
                raise ParseError("Cannot parse Inductive",tokens)
            pos = 1
            n = []
            while (len(tokens)>pos and tokens[pos].typ=='ID'):
                n.append(tokens[pos].value)
                pos = pos+1
            if tokens[pos].typ=='colon':
               x = parseCoqExpr(tokens[pos+1:],[])
               tokens = x[1]
               t = x[0]
            else:
               tokens = tokens[pos:]
               t = None
            if (tokens[0].typ!="rightParen"):
                 raise ParseError("Cannot parse Inductive",tokens)
            tokens=tokens[1:]
            for nn in n:
                implicit_params.append((nn,t))
    order = None
    if len(tokens)>4 and tokens[0].typ=='leftBrace' and tokens[1].value=='struct' and tokens[2].typ=='ID' and tokens[3].typ=='rightBrace':
        order = tokens[2].value
        tokens = tokens[4:]
    if len(tokens)>2 and tokens[0].typ=='colon':
        x = parseCoqExpr(tokens[1:],[])
        tokens = x[1]
        return_type = x[0]
    elif len(tokens)>2 and tokens[0].typ=='colonEqual':
        return_type = None
    else:
        print tokens[0]
        print tokens[1]
        print tokens[2]
        print tokens[3]
        raise ParseError("Cannot parse inductive",tokens)
    if (len(tokens)<3 or tokens[0].typ!="colonEqual"):
        raise ParseError("Cannot parse Inductive",tokens)
    cases = []
    if tokens[1].typ=='bar':
        tokens = tokens[2:]
    else:
        tokens = tokens[1:]
    first = True
    while first or tokens[0].typ=='bar':
        if tokens[0].typ=='bar':
            tokens = tokens[1:]
        elif first==False:
            raise ParseError("Cannot parse Inductive",tokens)
        if len(tokens)<1 or tokens[0].typ!='ID':
            raise ParseError("Cannot parse Inductive",tokens)
        n = tokens[0].value
        tokens = tokens[1:]
        pp = []
        while tokens[0].typ=='ID' or tokens[0].value=='_':
            pp.append(tokens[0].value)
            tokens = tokens[1:]
        if tokens[0].typ=='colon':
            x = parseCoqExpr(tokens[2:],[[CoqLex.Token('period','.',0,0)]])
            cases.append((n,pp,x[0]))
            tokens = x[1]
        else:
            tokens = tokens[1:]
            cases.append((n,pp,None))
        first = False
    if len(tokens)==0 or tokens[0].typ!='period':
        print tokens[0]
        raise ParseError("Cannot parse Inductive",tokens)
    tokens = tokens[1:]
    return (CoqCoInductive(tt[0:len(tt)-len(tokens)],name,implicit_params,params,return_type,cases),tokens)

class CoqTheorem(CoqDeclaration):
    def __init__(self,tokens,n,ip,t,p,q):
        CoqDeclaration.__init__(self,tokens)
        self.result = ""
        self.old_result = None
        #self.currentCoqCycle = -1
        self.unfocused = 0
        self.subgoals =0
        self.name = n
        self.implicit_params = ip
        self.theorem = t
        self.proof = p
        self.result = ""
        self.qed = q
        self.full = False
    def isProof(self):
        return len(self.proof)>0
    def markNeedsReplay(self):
        CoqDeclaration.markNeedsReplay()
        for x in self.proof:
            x.needsReplay = 2
    def editUpdateTokens(self,line_s, col_s, line_oe, col_oe, line_ne, col_ne):
        CoqParseObject.editUpdateTokens(self, line_s, col_s, line_oe, col_oe, line_ne, col_ne)
        for p in self.proof:
            p.editUpdateTokens(line_s, col_s, line_oe, col_oe, line_ne, col_ne)
    def dependencies(self):
        x = self.theorem.dependencies()
        d = []
        for v in self.implicit_params:
            if v[1]!=None:
               d = d+v[1].dependencies()
            try:
                while (v[0] in x):
                    while (v[0] in x):
                        x.remove(v[0])
            except ValueError:
                pass
        #for t in self.proof:
            #d = d+t.dependencies()
        #print "Theorem dependencies "+str(self.name)+" "+str(d)+" "+str(x)
        return d+x
    def getListRepr(self):
        return ["Theorem",self.name,(["params"]+self.implicit_params),self.theorem,self.qed]+self.proof
    @classmethod
    def create(cls,l,tokens):
        return CoqTheorem(tokens,l[1],l[2][1:],l[3],l[4],l[5:])
    def getProof(self):
        return self.proof
    def header(self):
        return "Theorem " + self.name
    def __repr__(self):
        return "class CoqTheorem "+self.name
    def getCoqSuffix(self,text):
        return self.qed+"."
    def getSegment(self,text):
        if (self.full):
            return CoqParseObject.getSegment(self,text)
        l1 = self.tokens[0].line
        c1 = self.tokens[0].column
        f = -1
        g = -1
        for i in range(0,len(self.tokens)):
            if self.tokens[i].typ=='Proof' and f < 0:
               f = i-1
            if self.tokens[i].typ=='period' and g < 0:
               g = i
        if f < 0:
            f = g
        l2 = self.tokens[f].line
        c2 = self.tokens[f].column+len(self.tokens[f].value)
        tl = text[l1-1:l2]
        tl[0] = tl[0][c1:]
        tl[l2-l1] = tl[l2-l1][0:c2]
        return ("\n".join(tl),self.updateTokens(l1,c1,self.tokens))
    def definedNames(self):
        return [self.name]

    def __coqstr__(self):
        x = "Theorem "+self.name
        for i in self.implicit_params:
            if i[1]==None:
                x = x + " {"+i[0]+"}"
            else:
                x = x + " {"+i[0]+":"+i[1].__coqstr__()+"}"
        x = x + " : "+self.theorem.__coqstr__() + ". Proof."
        for p in self.proof:
            x = x + " " + p.__coqstr__()
        return x + " Qed."

def parseCoqTheorem(tokens):
    tt = tokens
    if len(tokens)<4 or (tokens[0].typ != 'Theorem' and tokens[0].typ != 'Lemma' and tokens[0].typ != 'Example' and tokens[0].typ != 'Fact') or tokens[1].typ != 'ID':
        raise ParseError("Cannot parse Theorem",tokens)
    name = tokens[1].value
    tokens = tokens[2:]
    implicit_params = []
    while (tokens[0].typ=='leftBrace' or tokens[0].typ=='leftParen') or tokens[0].typ=='ID':
        if tokens[0].typ=='ID':
            implicit_params.append((tokens[0].value,None))
            tokens = tokens[1:]
        else:
            if len(tokens)<4 or tokens[1].typ!='ID':
                raise ParseError("Cannot parse Theorem",tokens)
            n = []
            pos = 1
            while (len(tokens)>pos and tokens[pos].typ=='ID'):
                n.append(tokens[pos].value)
                pos = pos+1
            if tokens[pos].typ=='colon':
               x = parseCoqExpr(tokens[pos+1:],[])
               tokens = x[1]
               t = x[0]
            else:
               tokens = tokens[pos:]
               t = None
            if (tokens[0].typ!="rightBrace" and tokens[0].typ!="rightParen"):
                raise ParseError("Cannot parse Theorem",tokens)
            tokens=tokens[1:]
            for nn in n:
                implicit_params.append((nn,t))
    if (len(tokens)<3 or tokens[0].typ!="colon"):
        print tokens[0]
        raise ParseError("Cannot parse Theorem",tokens)
    print tokens[1]
    x = parseCoqExpr(tokens[1:],[[CoqLex.Token('ID','Proof',0,0)],[CoqLex.Token('period','.',0,0)]])
    theorem = x[0]
    tokens = x[1]
    print "THEOREM BODY"
    print tokens[0]
    #print tokens[1]
    #print tokens[2]
    #print tokens[3]
    #print tokens[4]
    #print tokens[5]
    if len(tokens)>=5 and tokens[0].typ=='period' and tokens[1].value=='Proof' and tokens[2].typ=='period' and tokens[3].value=='Admitted' and tokens[4].typ=='period':
        tokens = tokens[5:]
        proof = []
        return (CoqTheorem(tt[0:len(tt)-len(tokens)],name,implicit_params,theorem,proof,'Admitted'),tokens)
    elif len(tokens)>3 and tokens[0].typ=='period' and tokens[1].typ=='Proof' and tokens[2].typ=='period':
        tokens = tokens[3:]
    elif len(tokens)>3 and tokens[0].typ=='period' and tokens[1].value=='Admitted' and tokens[2].typ=='period':
        tokens = tokens[3:]
        proof = []
        return (CoqTheorem(tt[0:len(tt)-len(tokens)],name,implicit_params,theorem,proof,'Admitted'),tokens)
    elif len(tokens)>1 and tokens[0].typ=='period':
        tokens = tokens[1:]
    else:
        print tokens[0]
        raise ParseError("Cannot parse Theorem",tokens)
    proof = []
    print "START TACTIC PARSE"
    while len(tokens)>0 and tokens[0].typ!='Qed' and tokens[0].typ != 'Defined' and tokens[0].typ != 'Abort' and tokens[0].value != 'Admitted':
        print "CYCLE TACTIC PARSE"
        print tokens[0]
        x = parseCoqTacticCommand(tokens)
        print x[0]
        if x[0]==None:
            exit()
        proof.append(x[0])
        tokens = x[1]
    d = tokens[0].typ
    if len(tokens)<2 or (tokens[0].typ!='Abort' and tokens[0].typ!='Qed' and tokens[0].typ!='Defined') or tokens[1].typ != 'period':
        raise ParseError("Cannot parse Theorem",tokens)
    return (CoqTheorem(tt[0:len(tt)-len(tokens)+2],name,implicit_params,theorem,proof,d),tokens[2:])

class CoqImplicitArguments(CoqDeclaration):
    def __init__(self,tokens,n,p):
        CoqDeclaration.__init__(self,tokens)
        self.name = n
        self.implicit_params = p
    def dependencies(self):
        return [[self.name]]
    def getListRepr(self):
        return ["ImplicitArguments",self.name]+self.implicit_params
    @classmethod
    def create(cls,l,tokens):
        return CoqImplicitArguments(tokens,l[1],l[2:])
    def header(self):
        return "ImplicitArguments " + self.name
    def __repr__(self):
        return "class CoqImplicitArguments "+self.name
    def definedNames(self):
        return [("@ia_"+self.name)]
    def __coqstr__(self):
        x = "Implicit Arguments "+self.name+" ["
        pcomma = False
        for i in self.implicit_params:
            if pcomma:
                x = x + ","
            pcomma = True
            x = x+i
        return x + "]"

def parseCoqImplicitArguments(tokens):
    tt = tokens
    if len(tokens)<5 or tokens[0].value != 'Implicit' or tokens[1].value != 'Arguments' or tokens[2].typ!='ID' or tokens[3].typ!='leftBracket':
        raise ParseError("Cannot parse Implicit Arguments",tokens)
    name = tokens[2].value
    params = []
    tokens = tokens[4:]
    cont = True
    while cont:
        if len(tokens)<2 or tokens[0].typ!='ID':
            raise ParseError("Cannot parse implicit Arguments",tokens)
        params.append(tokens[0].value)
        if tokens[1].typ=='rightBracket':
            cont = False
        elif tokens[1].typ!='ID':
            raise ParseError("Cannot parse implicit Arguments",tokens)
        tokens = tokens[1:]
    tokens = tokens[1:]
    if len(tokens)<1 or tokens[0].typ != 'period':
        raise ParseError("Cannot parse Implicit Arguments",tokens)
    return (CoqImplicitArguments(tt[0:len(tt)-len(tokens)+1],name,params),tokens[1:])

def parseCoqDeclaration(tokens):
    try:
        if (len(tokens)>0 and tokens[0].typ=='Require'):
            return parseCoqRequire(tokens)
        elif (len(tokens)>0 and tokens[0].typ=='Import'):
            return parseCoqImport(tokens)
        elif (len(tokens)>0 and tokens[0].typ=='Export'):
            return parseCoqExport(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Section'):
            return parseCoqSection(tokens)
        elif (len(tokens)>2 and tokens[0].typ=='Module' and tokens[1].value=='Type'):
            return parseCoqModuleType(tokens)
        elif (len(tokens)>2 and tokens[0].typ=='Module'):
            return parseCoqModule(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='End'):
            return parseCoqEnd(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Context'):
            return parseCoqContext(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Hypothesis'):
            return parseCoqHypothesis(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Variable'):
            return parseCoqVariable(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Compute'):
            return parseCoqCompute(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Check'):
            return parseCoqCompute(tokens)
        elif (len(tokens)>1 and tokens[0].value=='Opaque'):
            return parseCoqOpaque(tokens)
        elif (len(tokens)>1 and tokens[0].value=='Hint'):
            return parseCoqHint(tokens)
        elif (len(tokens)>3 and tokens[0].value=='Set' and tokens[1].value=='Implicit' and tokens[2].value=='Arguments'):
            return parseCoqSetImplicitArguments(tokens)
        elif (len(tokens)>3 and tokens[0].value=='Set' and tokens[1].value=='Printing' and tokens[2].value=='Depth'):
            return parseCoqSetPrintingDepth(tokens)
        elif (len(tokens)>3 and tokens[0].value=='Unset' and tokens[1].value=='Implicit' and tokens[2].value=='Arguments'):
            return parseCoqUnsetImplicitArguments(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Open' and tokens[1].typ=='Scope'):
            return parseCoqOpenScope(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Ltac'):
            return parseCoqLtac(tokens)
        elif (len(tokens)>3 and tokens[0].typ=='Tactic' and tokens[1].typ=='Notation'):
            return parseCoqTacticNotation(tokens)
        elif (len(tokens)>1 and tokens[0].value=='Notation'):
            return parseCoqNotation(tokens)
        elif (len(tokens)>1 and tokens[0].value=='Infix'):
            return parseCoqNotation(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Fixpoint'):
            return parseCoqFixpoint(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='CoFixpoint'):
            return parseCoqCoFixpoint(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Definition'):
            return parseCoqDefinition(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Function'):
            return parseCoqFunction(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Axiom'):
            return parseCoqAxiom(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='About'):
            return parseCoqAbout(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Parameter'):
            return parseCoqParameter(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Inductive'):
            return parseCoqInductive(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='CoInductive'):
            return parseCoqCoInductive(tokens)
        elif (len(tokens)>1 and tokens[0].typ=='Record'):
            return parseCoqRecord(tokens)
        elif (len(tokens)>1 and (tokens[0].typ=='Theorem' or tokens[0].typ=='Lemma' or tokens[0].typ=='Example' or tokens[0].typ=='Fact')):
            print "Parsing theorem"
            return parseCoqTheorem(tokens)
        elif (len(tokens)>2 and tokens[0].value=='Implicit' and tokens[1].value=='Arguments'):
            return parseCoqImplicitArguments(tokens)
        else:
            if len(tokens)>0:
                print tokens[0]
                if len(tokens)>1:
                    print tokens[1]
                    #print tokens[2]
                    #print tokens[3]
            raise ParseError('Cannot parse declaration',tokens)
    except ParseError:
        print "Bad decl parse"
        l = len(tokens)
        p = 0
        level = 0
        proof = []
        if tokens[0].value=='Theorem' or tokens[0].value=='Example':
            seen_qed = 0;
            tactic_start = 0
            seen_proof = 0
            while p < len(tokens) and (tokens[p].typ!='period' or level > 0 or seen_qed==0):
                if tokens[p].typ=='leftParen' or tokens[p].typ=='leftBracket' or tokens[p].typ=='leftBrace':
                    level = level + 1
                if tokens[p].typ=='rightParen' or tokens[p].typ=='rightBracket' or tokens[p].typ=='rightBrace':
                    level = level - 1
                if level==0 and (tokens[p].value=='Qed' or tokens[p].value=='Admitted' or tokens[p].value=='Abort' or tokens[p].value=='Defined'):
                    seen_qed = 1
                if level==0 and tokens[p].value=='Proof':
                    seen_proof = 1
                    tactic_start = p+2
                if level==0 and tokens[p].typ=='period' and seen_proof and seen_qed==0 and p > tactic_start:
                    proof.append(CoqBadLtacExpr(tokens[tactic_start:p]))
                    tactic_start = p+1
                p = p + 1
        else:
            while p < len(tokens) and (tokens[p].typ!='period' or level > 0):
                if tokens[p].typ=='leftParen' or tokens[p].typ=='leftBracket' or tokens[p].typ=='leftBrace':
                    level = level + 1
                if tokens[p].typ=='rightParen' or tokens[p].typ=='rightBracket' or tokens[p].typ=='rightBrace':
                    level = level - 1
                p = p + 1
        if p < len(tokens):
            p = p + 1
        return (CoqBadDeclaration(tokens[0:p],proof),tokens[p:])


def parseCoqProgram(tokens):
    p = []
    while (len(tokens)>0):
        print "DECL PARSING "+str(tokens[0])
        x = parseCoqDeclaration(tokens)
        print x[0]
        p.append(x[0])
        tokens = x[1]
    return p

def topParseCoqTactic(tokens):
    r = []
    while len(tokens)>0:
        try:
            x = parseCoqLtacExpr(tokens)
            tokens = x[1]
            if len(tokens)==0 or tokens[0].typ != 'period':
                print tokens[0]
                print tokens[1]
                print tokens[2]
                print tokens[3]
                raise ParseError("Cannot parse Tactic",tokens)
            x[0].tokens.append(tokens[0])
            tokens = tokens[1:]
            #if (len(tokens)>0):
                #raise ParseError("Junk at the end of tactic",tokens)
            r.append(x[0])
        except IndexError:
            tokens = []
    return r

def createParseObject(l):
    if len(l)==0:
        return l
    if l[0]=='Parse':
        return CoqParseObject.create(l)
    elif l[0]=='Number':
        return CoqNumberExpr.create(l)
    elif l[0]=='Name':
        return CoqNameExpr.create(l)
    elif l[0]=='StarExpr':
        return CoqStarExpr.create(l)
    elif l[0]=='Quotation':
        return CoqQuotationExpr.create(l)
    elif l[0]=='AtName':
        return CoqAtNameExpr.create(l)
    elif l[0]=='DotDot':
        return CoqDotDotExpr.create(l)
    elif l[0]=='Underscore':
        return CoqUnderscoreExpr.create(l)
    elif l[0]=='ContextExpr':
        return CoqContextExpr.create(l)
    elif l[0]=='BraceExpr':
        return CoqBraceExpr.create(l)
    elif l[0]=='Hypothesis':
        return CoqHypothesis.create(l)
    elif l[0]=='Variable':
        return CoqVariable.create(l)
    elif l[0]=='Compute':
        return CoqCompute.create(l)
    elif l[0]=='Appl':
        return CoqApplExpr.create(l)
    elif l[0]=='Fun':
        return CoqFunExpr.create(l)
    elif l[0]=='Tuple':
        return CoqTupleExpr.create(l)
    elif l[0]=='Exists':
        return CoqExistsExpr.create(l)
    elif l[0]=='Forall':
        return CoqForallExpr.create(l)
    elif l[0]=='Match':
        return CoqMatchExpr.create(l)
    elif l[0]=='Ltac':
        return CoqLtacExpr.create(l)
    elif l[0]=='LtacConcat':
        return CoqLtacExprConcat.create(l)
    elif l[0]=='LtacOr':
        return CoqLtacExprOr.create(l)
    elif l[0]=='LtacSubConcat':
        return CoqLtacExprSubConcat.create(l)
    elif l[0]=='MatchCpattern':
	return CoqMatchCpattern.create(l)
    elif l[0]=='MatchWildcard':
        return CoqMatchWildcard.create(l)
    elif l[0]=='MatchGoalRule':
        return CoqMatchGoalRule.create(l)
    elif l[0]=='MatchFreshExpr':
        return CoqLtacFreshExpr.create(l)
    elif l[0]=='LtacLet':
        return CoqLtacLetExpr.create(l)
    elif l[0]=='LtacFirst':
        return CoqLtacFirstExpr.create(l)
    elif l[0]=='LtacSolve':
        return CoqLtacSolveExpr.create(l)
    elif l[0]=='LtacTry':
        return CoqLtacTryExpr.create(l)
    elif l[0]=='LtacProgress':
        return CoqLtacProgressExpr.create(l)
    elif l[0]=='LtacRepeat':
        return CoqLtacRepeatExpr.create(l)
    elif l[0]=='LtacMatchGoal':
        return CoqLtacMatchGoalExpr.create(l)
    elif l[0]=='Tactic':
        return CoqTactic.create(l)
    elif l[0]=='AssertTactic':
        return CoqAssertTactic.create(l)
    elif l[0]=='GoalNumTactic':
        return CoqGoalNumTactic.create(l)
    elif l[0]=='SetTactic':
        return CoqSetTactic.create(l)
    elif l[0]=='RewriteTactic':
        return CoqRewriteTactic.create(l)
    elif l[0]=='SimplTactic':
        return CoqSimplTactic.create(l)
    elif l[0]=='InjectionTactic':
        return CoqInjectionTactic.create(l)
    elif l[0]=='ComputeTactic':
        return CoqComputeTactic.create(l)
    elif l[0]=='ApplyTactic':
        return CoqApplyTactic.create(l)
    elif l[0]=='ClearTactic':
        return CoqClearTactic.create(l)
    elif l[0]=='IntrosTactic':
        return CoqIntrosTactic.create(l)
    elif l[0]=='RememberTactic':
        return CoqRememberTactic.create(l)
    elif l[0]=='DestructTactic':
        return CoqDestructTactic.create(l)
    elif l[0]=='InstantiateTactic':
        return CoqInstantiateTactic.create(l)
    elif l[0]=='FailTactic':
        return CoqFailTactic.create(l)
    elif l[0]=='FocusTactic':
        return CoqFocusTactic.create(l)
    elif l[0]=='FoldTactic':
        return CoqFoldTactic.create(l)
    elif l[0]=='UnfoldTactic':
        return CoqUnfoldTactic.create(l)
    elif l[0]=='ReflexivityTactic':
        return CoqReflexivityTactic.create(l)
    elif l[0]=='MoveTactic':
        return CoqMoveTactic.create(l)
    elif l[0]=='Declaration':
        return CoqDeclaration.create(l)
    elif l[0]=='Ltac':
        return CoqLtac.create(l)
    elif l[0]=='OpenScope':
        return CoqOpenScope.create(l)
    elif l[0]=='SetPrintingDepth':
        return CoqSetPrintingDepth.create(l)
    elif l[0]=='SetImplicitArguments':
        return CoqSetImplicitArguments.create(l)
    elif l[0]=='SetImplicitArguments':
        return CoqSetImplicitArguments.create(l)
    elif l[0]=='UnsetImplicitArguments':
        return CoqUnsetImplicitArguments.create(l)
    elif l[0]=='Opaque':
        return CoqOpaque.create(l)
    elif l[0]=='Hint':
        return CoqHint.create(l)
    elif l[0]=='TacticNotation':
        return CoqTacticNotation.create(l)
    elif l[0]=='Require':
        return CoqRequire.create(l)
    elif l[0]=='Import':
        return CoqImport.create(l)
    elif l[0]=='Export':
        return CoqExport.create(l)
    elif l[0]=='Definition':
        return CoqDefinition.create(l)
    elif l[0]=='Section':
        return CoqSection.create(l)
    elif l[0]=='ModuleType':
        return CoqModuleType.create(l)
    elif l[0]=='Module':
        return CoqModule.create(l)
    elif l[0]=='Context':
        return CoqContext.create(l)
    elif l[0]=='Function':
        return CoqFunction.create(l)
    elif l[0]=='Notation':
        return CoqNotation.create(l)
    elif l[0]=='CoFixpoint':
        return CoqCoFixpoint.create(l)
    elif l[0]=='Fix':
        return CoqFixExpr.create(l)
    elif l[0]=='Inductive':
        return CoqInductive.create(l)
    elif l[0]=='CoInductive':
        return CoqCoInductive.create(l)
    elif l[0]=='Record':
        return CoqRecord.create(l)
    elif l[0]=='Theorem':
        return CoqTheorem.create(l) 
    elif l[0]=='ImplicitArguments':
        return CoqImplicitArguments.create(l)
    else:
        return None

def returnDiffs(term1,term2,parent1,parent2,stack):
    if term1==term2:
        return []
    elif type(term1)==types.IntType or type(term1)==types.StringType or type(term1)==types.NoneType or type(term1)==types.BooleanType or type(term2)==types.IntType or type(term2)==types.StringType or type(term2)==types.NoneType or type(term2)==types.BooleanType:
        t1s = parent1.tokens[0]
        t1e = parent1.tokens[len(parent1.tokens)-1]
        t2s = parent2.tokens[0]
        t2e = parent2.tokens[len(parent2.tokens)-1]
        #print spaces(indent)+"Diff case 1"
        #print spaces(indent)+str(parent1)
        #print spaces(indent)+str(parent2)
        return [(((t1s.line,t1s.column),(t1e.line,t1e.column)),((t2s.line,t2s.column),(t2e.line,t2e.column)))]
    elif type(term1)==types.ListType and type(term2)==types.ListType:
        #print "List process"
        #print term1
        #print term2
        #print parent1
        #print parent2
        #print parent1.tokens
        #print parent1.tokens[0].line
        #print parent1.tokens[0].column
        #print parent1.tokens[len(parent1.tokens)-1].line
        #print parent1.tokens[len(parent1.tokens)-1].column
        #print parent2.tokens[0].line
        #print parent2.tokens[0].column
        #print parent2.tokens[len(parent2.tokens)-1].line
        #print parent2.tokens[len(parent2.tokens)-1].column
        #try:
            #if len(term1)>1 and term1[1].name=='sepStar':
                #print "^^^^^ star1"
                #print parent1
        #except AttributeError as q:
            #pass
        #try:
            #if len(term2)>1 and term2[1].name=='sepStar':
                #print "^^^^^ star2"
                #print parent2
        #except AttributeError as q:
            #pass
        diffs = []
        first = True
        haveStr = False
        #if len(term1)!=len(term2):
            #print "====================== Difference ================="
        while len(term1)>0 and len(term2)>0:
            if type(term1[0])==types.InstanceType and type(term2[0])==types.InstanceType:
                t1 = term1[0].getListRepr()
                t2 = term2[0].getListRepr()
                st1 = [(parent1,parent2)]+stack
                diffs = diffs + returnDiffs(t1,t2,term1[0],term2[0],st1)
                term1 = term1[1:]
                term2 = term2[1:]
            elif type(term1[0])==types.ListType and type(term2[0])==types.ListType:
                if len(term1[0])==len(term2[0]):
                    term1 = term1[0]+term1[1:]
                    term2 = term2[0]+term2[1:]
                else:
                    t1s = parent1.tokens[0]
                    t1e = parent1.tokens[len(parent1.tokens)-1]
                    t2s = parent2.tokens[0]
                    t2e = parent2.tokens[len(parent2.tokens)-1]
                    #print "Diff case 2"
                    #print parent1
                    #print parent2
                    return [(((t1s.line,t1s.column),(t1e.line,t1e.column)),((t2s.line,t2s.column),(t2e.line,t2e.column)))]
            elif term1[0]!=term2[0]:
                if first==False and type(term1[0])==types.StringType and type(term2[0])==types.StringType and haveStr==False:
                    t1 = None
                    i = 0
                    while i < len(parent1.tokens) and t1==None:
                        if parent1.tokens[i].value==term1[0]:
                            t1 = parent1.tokens[i]
                        i = i+1
                    t2 = None
                    i = 0
                    while i < len(parent2.tokens) and t2==None:
                        if parent2.tokens[i].value==term2[0]:
                            t2 = parent2.tokens[i]
                        i = i+1
                    if t1==None or t2==None:
                        t1s = parent1.tokens[0]
                        t1e = parent1.tokens[len(parent1.tokens)-1]
                        t2s = parent2.tokens[0]
                        t2e = parent2.tokens[len(parent2.tokens)-1]
                        #print "Diff case 3"
                        #print parent1
                        #print parent2
                        return [(((t1s.line,t1s.column),(t1e.line,t1e.column)),((t2s.line,t2s.column),(t2e.line,t2e.column)))]
                    else:
                        haveStr = True
                        #print "***************** Name diff ********"
                        #print term1[0]
                        #print term2[0]
                        diffs.append((((t1.line,t1.column),(t1.line,t1.column+len(t1.value))),((t2.line,t2.column),(t2.line,t2.column+len(t2.value)))))
                        term1 = term1[1:]
                        term2 = term2[1:]
                else:
                    t1s = parent1.tokens[0]
                    t1e = parent1.tokens[len(parent1.tokens)-1]
                    t2s = parent2.tokens[0]
                    t2e = parent2.tokens[len(parent2.tokens)-1]
                    #print "Diff case 4"
                    #print parent1
                    #print parent2
                    #for s in stack:
                        #print "&&&&&&&&&&&&&&&&&&&&&&"
                        #print s[0].tokens[0]
                        #print s[1].tokens[0]
                        #print s[0].tokens[len(s[0].tokens)-1]
                        #print s[1].tokens[len(s[1].tokens)-1]
                        #print "**********************"
                        #print s[0].__coqstr__()
                        #print "######################"
                        #print s[1].__coqstr__()
                        #print "**********************"
                    return [(((t1s.line,t1s.column),(t1e.line,t1e.column)),((t2s.line,t2s.column),(t2e.line,t2e.column)))]
            else:
                term1 = term1[1:]
                term2 = term2[1:]
            first = False
        if len(term1)>0 or len(term2)>0:
            t1s = parent1.tokens[0]
            t1e = parent1.tokens[len(parent1.tokens)-1]
            t2s = parent2.tokens[0]
            t2e = parent2.tokens[len(parent2.tokens)-1]
            return [(((t1s.line,t1s.column),(t1e.line,t1e.column)),((t2s.line,t2s.column),(t2e.line,t2e.column)))]
        return diffs
    elif type(term1)==types.ListType or type(term2)==types.ListType:
        t1s = parent1.tokens[0]
        t1e = parent1.tokens[len(parent1.tokens)-1]
        t2s = parent2.tokens[0]
        t2e = parent2.tokens[len(parent2.tokens)-1]
        #print "Diff case 5"
        #print parent1
        #print parent2
        return [(((t1s.line,t1s.column),(t1e.line,t1e.column)),((t2s.line,t2s.column),(t2e.line,t2e.column)))]
    t1 = term1.getListRepr()
    t2 = term2.getListRepr()
    st1 = [(parent1,parent2)]+stack
    return returnDiffs(t1,t2,term1,term2,st1)

def updateDiffs(term1,term2,diffs):
    line1 = term1.tokens[0].line
    col1 = term1.tokens[0].column
    line2 = term2.tokens[0].line
    col2 = term2.tokens[0].column
    d = []
    for x in diffs:
        l1a = x[0][0][0]-line1+1
        c1a = x[0][0][1]
        if l1a==1:
            c1a = c1a-col1
        l1b = x[0][1][0]-line1+1
        c1b = x[0][1][1]
        if l1b==1:
            c1b = c1b-col1
        l2a = x[1][0][0]-line2+1
        c2a = x[1][0][1]
        if l2a==1:
            c2a = c2a-col2
        l2b = x[1][1][0]-line2+1
        c2b = x[1][1][1]
        if l2b==1:
            c2b = c2b-col2
        d.append((((l1a,c1a),(l1b,c1b)),((l2a,c2a),(l2b,c2b))))
    return d

def diffs(term1,term2):
    return updateDiffs(term1,term2,returnDiffs(term1.getListRepr(),term2.getListRepr(),term1,term2,[]))

#f = open('SatSolverMain.v')
#statements = f.read()

CoqLex.initLex()

#program = []

#for token in CoqLex.tokenize(statements):
    #print token
    #program.append(token)

#parseCoqProgram(program)

