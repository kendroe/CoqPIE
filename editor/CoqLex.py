#
# PIE - Python based IDe for Coq
#
# CoqLex.py
#
# This file contains code for the Coq Lexer
#
# (C) 2015, 2016 Kenneth Roe
# All rights reserved
#
import collections
import re

Token = collections.namedtuple('Token', ['typ', 'value', 'line', 'column'])

keywords = {'Require', 'Export' ,'Opaque', 'CoFixpoint', 'match', 'with', 'end',
            'if', 'then', 'else', 'Fixpoint', 'Implicit', 'Arguments', 'fun',
            'Definition', 'forall', 'exists', 'fix', 'Function',
            'Theorem', 'Proof', 'Qed', 'Defined', 'Open', 'Scope', 'Ltac',
            'move', 'after', 'goal', 'try', 'before', 'About',
            'after', 'at', 'bottom', 'Tactic', 'Notation',
            'let', 'in', 'as', 'by', 'Inductive', 'CoInductive', 'return',
            'WHILE', 'DO', 'LOOP', 'IF', 'THEN', 'ELSE', 'FI', 'Abort',
            'if', 'then', 'else', 'Import', 'Section', 'Context',
            'pose', 'proof', 'End', 'Parameter', 'Axiom', 'Lemma',
            'Hypothesis', 'Variable', 'Record', 'Module', 'Example', 'Admitted',
            'Compute', 'Check', 'Fact' }

# ('COMMENT', r'(\(\*(\(\*[A-Za-z0-9_\.\ \t,\/\#\*\:\[\]\n\~\{\}\<\>\-\(\)\=]*\*\))|[A-Za-z0-9_\.\ \t,\/\#\*\:\[\]\n\~\{\}\<\>\-\(\)\=])*\*\)'),

token_specification = [
    ('COMMENT', r'\(\*((?!\*\))(\S|\n|\ ))*\*\)'),
    ('SEPERATOR', r'\=\=\=\=\=\=\=*'),
    ('lessDashGreater', r'\<\-\>'),
    ('SQUOTATION', r'\'((?!\")(\S|\n|\ ))*\''),
    ('QUOTATION', r'\"((?!\")(\S|\n|\ ))*\"'),
    ('NUMBER',  r'\d+'),         # Integer
    ('dashGreater',   r'\->'),
    ('lessDash',  r'<\-'),
    ('_',    r'_'),
    ('equalGreater',    r'=>'),
    ('cell',      r'\|\-\>'),
    ('lessColon',   r'\<\:'),
    ('barDash',   r'\|\-'),
    ('barBar',   r'\|\|'),
    ('colonColonEqual',  r'::='),          # Assignment operator
    ('colonEqual',  r':='),          # Assignment operator
    ('OP',      r'\-\-\>\>|\:\:\=|\-\-\-\>|\*\*\*\*|\*\*\*|\+\+\+\+|\-\-\-|\+\+\+|\+\+|\~\~|\-\-\>|\-\-|\=\=\=\=|\=\=\=|\<\<\=|\<\<\<\<|\*\\\/\*|\!\!|\!|\*\*|\/\/\\\\|\\\\\/\/|\\\/|\/\\|\+|\*|\/|\-|<>|<\=|>\=|<|>|\~|\:\:|\&\&|\%|\#|\!|\!\!|\^|\\\\'),
    ('ampersand',r'\&'),
    ('atsign',r'\@'),
    ('questionMark',r'\?'),
    ('leftBracket',r'\['),
    ('rightBracket',r'\]'),
    ('leftBrace',  r'\{'),
    ('rightBrace',  r'\}'),
    ('leftParen',  r'\('),
    ('rightParen',  r'\)'),
    ('dotdot',  r'\.\.'),         # Unexpanded subterm 
    ('period',  r'\.'),           # End of declaration
    ('colon',   r':'),
    ('comma',   r','),
    ('equal',   r'='),
    ('doubleQuote',  r'"'),
    ('bar',     r'\|'),
    ('semicolon',     r';'),           # Statement terminator
    ('WILDCARD',      r'\?[A-Za-z_][A-Za-z0-9_\']*'),   # Identifiers
    ('ID',      r'[A-Za-z_][A-Za-z0-9_\']*'),   # Identifiers
    ('NEWLINE', r'\n'),          # Line endings
    ('SKIP',    r'[ \t]')       # Skip over spaces and tabs
]

get_token = None

def initLex():
    global get_token
    global token_specification
    global keywords
    tok_regex = '|'.join('(?P<%s>%s)' % pair for pair in token_specification)
    print "*** REGEX ***"
    print tok_regex
    get_token = re.compile(tok_regex).match

def tokenize(s):
    global keywords
    global get_token
    line = 1
    pos = line_start = 0
    mo = get_token(s)
    while mo is not None:
        #print "*** Token ***"
        #print mo
        #print mo.lastgroup
        typ = mo.lastgroup
        #print mo.group(typ)
        for i in range(mo.start(),mo.end()):
            if s[i]=='\n':
                line_start = i+1
                line += 1
        val = mo.group(typ)
        if typ == 'ID' and val in keywords:
             typ = val
        if typ != 'SKIP' and typ != 'NEWLINE' and typ != 'COMMENT':
            yield Token(typ, val, line, mo.start()-line_start)
        pos = mo.end()
        mo = get_token(s, pos)
    if pos != len(s):
        print line
        print pos
        raise RuntimeError("Unexpected character %r on line %d"%(s[pos], line))

#statements = '''
#    IF quantity THEN
#        total := total + price * quantity;
#        tax := price * 0.05;
#    ENDIF;
#'''

#f = open('../Coq4/SfLib.v')
#statements = f.read()

#initLex()

#for token in tokenize(statements):
#    print(token)

