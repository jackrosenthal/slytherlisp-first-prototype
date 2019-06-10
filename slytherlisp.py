import sys
import re
from functools import reduce
import operator
import readline
import traceback

int_re = re.compile(r'^\d+$')
float_re = re.compile(r'^\d+\.\d*$')
token_re = re.compile(r'''
    ^\s*(\(|\)
    |\d+\.?\d*
    |"(?:\\"|[^"])*"
    |[^0-9"()\s][^"()\s]*)(.*)$''', re.DOTALL | re.VERBOSE)
white_re = re.compile(r'^\s*$')


class Symbol(str):
    def __repr__(self):
        return 'Symbol("{}")'.format(str(self))


class NilType:
    def __repr__(self):
        return 'NIL'

    def __bool__(self):
        return False

    def __eq__(self, other):
        return isinstance(other, NilType) or other is None


NIL = NilType()


class SE(list):
    def __repr__(self):
        return '(' + ' '.join(repr(s) for s in self) + ')'


def tokenize(s):
    while not white_re.match(s):
        m = token_re.match(s)
        if not m:
            raise SyntaxError(
                "Couldn't match {!r} to any known tokens!".format(s))
        yield m.group(1)
        s = m.group(2)


def parse(tokens):
    for t in tokens:
        if t != '(':
            raise SyntaxError(
                "Wasn't expecting {} at the outside of an SE!".format(t))
        yield parse_se(tokens)


def parse_se(tokens):
    r = SE()
    for t in tokens:
        if t == ')':
            return r
        if t == '(':
            r.append(parse_se(tokens))
        elif t.startswith('"'):
            r.append(parse_strlit(t))
        elif int_re.match(t):
            r.append(int(t))
        elif float_re.match(t):
            r.append(float(t))
        elif t.lower() == 'nil':
            r.append(NIL)
        else:
            r.append(Symbol(t))
    raise SyntaxError("SE did not end?")


strlit_tokens = [
    (re.compile(a.replace('\\', '\\\\')), b)
    for a, b in (
        (r'\0', lambda m:'\0'),
        (r'\a', lambda m:'\a'),
        (r'\b', lambda m:'\b'),
        (r'\f', lambda m:'\f'),
        (r'\n', lambda m:'\n'),
        (r'\r', lambda m:'\r'),
        (r'\t', lambda m:'\t'),
        (r'\v', lambda m:'\v'),
        (r'\e', lambda m:'\033'),
        (r'\"', lambda m:'"'),
        (r'\x([0-9a-fA-F]{2})', lambda m:chr(int(m.group(1), base=16))),
        (r'\0([0-7]{2})', lambda m:chr(int(m.group(1), base=8))),
    )
]


def strlit_tokenize(s):
    drop = 0
    for tpl in zip(*(s[n:] + '\0' * n for n in range(min(4, len(s))))):
        if drop:
            drop -= 1
            continue
        partial = ''.join(tpl)
        for p, ld in strlit_tokens:
            m = p.match(partial)
            if m:
                yield ld(m)
                drop = len(m.group(0)) - 1
                continue
        yield tpl[0]


def parse_strlit(t):
    return ''.join(strlit_tokenize(t[1:-1]))


class Cons:
    def __init__(self, car, cdr):
        self.car = car
        self.cdr = cdr

    def __iter__(self):
        yield self.car
        if self.cdr != NIL:
            yield from self.cdr

    def __repr__(self):
        return '(cons {!r} {!r})'.format(self.car, self.cdr)


def make_cons_list(l):
    if not l:
        return NIL
    return Cons(l[0], make_cons_list(l[1:]))


builtin_functions = {
    '+': lambda *args: sum(args),
    '*': lambda *args: reduce(operator.mul, args),
    '-': lambda *args: sum((-a for a in args[1:]), args[0]),
    '/': lambda *args: reduce(operator.truediv, args),
    'expt': lambda a, b: a ** b,
    'cons': Cons,
    'list': lambda *l: make_cons_list(l),
    'car': lambda c: c.car,
    'cdr': lambda c: c.cdr,
    'cadr': lambda c: c.cdr.car,
    'cddr': lambda c: c.cdr.cdr,
    'map': lambda f, *l: make_cons_list(list(map(f, *l))),
    'print': print,
    'if': lambda cond, then, otherwise: then if cond else otherwise,
    'mod': operator.mod,
}


class LexicalVarStorage:
    def __init__(self, environ):
        self.environ = environ
        self.vars = {}

    def fork(self):
        f = {}
        f.update(self.environ)
        f.update(self.vars)
        return f

    def __setitem__(self, k, v):
        if k in self.environ.keys():
            self.environ[k] = v
        else:
            self.vars[k] = v

    def __getitem__(self, k):
        if k in self.vars.keys():
            return self.vars[k]
        if k in self.environ.keys():
            return self.environ[k]
        return builtin_functions[k]


class LispFunction:
    def __init__(self, arglist, *statements, environ=None):
        self.statements = statements
        self.environ = environ or {}

        for i, a in enumerate(arglist):
            if a == '&rest':
                self.argnames, self.rest = arglist[:i], arglist[i + 1]
                break
        else:
            self.argnames, self.rest = arglist, None

    def __call__(self, *args):
        stg = LexicalVarStorage(self.environ)
        for name, val in zip(self.argnames, args):
            stg.vars[name] = val
        if self.rest:
            stg.vars[self.rest] = make_cons_list(args[len(self.argnames):])
        r = NIL
        for st in self.statements:
            r = lisp_eval(st, stg)
        return r


def lisp_eval(expr, stg):
    if expr == []:
        return NIL
    if isinstance(expr, Symbol):
        return stg[expr]
    if not isinstance(expr, list):
        return expr
    fn = expr[0]
    if not isinstance(fn, Symbol):
        raise ValueError("SEs must start with a symbol to be evaluated")
    if fn.lower() == 'defun':
        f = LispFunction(expr[2], *expr[3:], environ=stg.fork())
        stg[expr[1]] = f
        return f
    if fn.lower() == 'setq':
        r = lisp_eval(expr[2], stg)
        stg[expr[1]] = r
        return r
    if fn.lower() == 'lambda':
        f = LispFunction(expr[1], *expr[2:], environ=stg.fork())
        return f
    args = [lisp_eval(a, stg) for a in expr]
    return args[0](*args[1:])


class Interpreter:
    def __init__(self):
        self.stg = LexicalVarStorage({})

    def eval(self, expr):
        return lisp_eval(expr, self.stg)

    def exec(self, code):
        r = NIL
        for se in parse(tokenize(code)):
            r = self.eval(se)
        return r

    def interact(self):
        while True:
            try:
                print(repr(self.exec(input("> "))))
            except KeyboardInterrupt:
                print()
                continue
            except EOFError:
                return
            except Exception as e:
                traceback.print_exc()


if __name__ == '__main__':
    interp = Interpreter()
    if len(sys.argv) < 2:
        interp.interact()
    else:
        with open(sys.argv[1]) as f:
            interp.exec(f.read())
