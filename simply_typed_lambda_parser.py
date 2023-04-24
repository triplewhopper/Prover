from typing import List, Deque, Iterable, Callable, Union, Set, TypeVar, Dict, Literal, Optional, Type, overload
from collections import deque, ChainMap
import simply_typed_lambda_calculi as stlc

__author__ = 'triplewhopper'
# abstract_header: Set[str] = {'λ', }
# binary_operator: Set[str] = {'+', '-', '*', '/', '\\/', '/\\'}
# unary_operator: Set[str] = {'-', '~'}
# precedence: Dict[str, int] = {
#     '\\/': 4, '/\\': 3, '->': 0, '+': 5, '*': 6
# }
reserved_words: Set[str] = {
    'case', 'of', 'λ', '⊥', '∀', '∃', 'exists', 'forall', 'False', 'lambda', 'inl', 'inr', 'fst', 'snd'
}


class TryParsingParenthesizedFailed(RuntimeError):
    ...


U = TypeVar('U')


class CleverDeque(Deque[U]):
    """
    a deque that supports undo popleft.
    """

    def __init__(self, *args, **kwargs):
        super(CleverDeque, self).__init__(*args, **kwargs)
        self.consumed: List[U] = []

    def popleft(self) -> U:
        v = super(CleverDeque, self).popleft()
        self.consumed.append(v)
        return v

    def undo_popleft(self):
        if self.consumed:
            self.appendleft(self.consumed[-1])
            del self.consumed[-1]


class Context:
    """
    This class manages the variable context while parsing,
    and it supports searching for a variable **by name**.


    If there are `at least` two variables with the **same** name,

    Case 1. Both are **bound variables**:
        The one bound to inside lambda will be returned.
    Case 2. A bound var and a free var:
        The bound one will be returned.
    Case 3. Both are **free variables**:
        The one appeared most recently, in other words, the right-most one, will be returned.
        This also applies to those passed in as arguments in __init__.
    """

    def __init__(self, free_vars: Iterable[stlc.TypedVariable] = tuple(), typenames: Iterable[str] = tuple(),
                 **kwargs: str):
        self.bound_var: List[stlc.TypedVariable] = []
        self.free_var: List[stlc.TypedVariable] = list(free_vars)
        self.individual_types: Set[str] = set(typenames)
        for k, v in kwargs.items():
            self.free_var.append(stlc.TypedVariable(parseType(CleverDeque(tokenizer(v)), self), k))
        # self.infix: Dict[str, stlc.TypedVariable] = {}
        # self.precedence

    # def add_free_variable(self, name):
    @staticmethod
    def _find(seq: List['stlc.TypedVariable'], name: str) -> Optional['stlc.TypedVariable']:
        """
        :param seq: the list in which to search.
        :param name: the variable name
        :return: the ``TypedVariable`` object closest to the end of list. ``None`` if not found.
        """
        for i in reversed(range(len(seq))):
            if name == seq[i].name:
                return seq[i]

    def getVarByName(self, name: str) -> Optional['stlc.TypedVariable']:
        """
        **firstly** search in bound variables, **secondly** search in free variables.

        return ``None`` when not found.
        """
        if (v := Context._find(self.bound_var, name)) is None:
            v1 = Context._find(self.free_var, name)
            return v1
        else:
            try:
                v.get_type()
            except TypeError as e:
                raise e
            return v

    # def add_infix(self, op_name: str, name: str, type: str):
    #     assert isinstance(op_name, str)
    #     assert isinstance(name, str)
    #     tokens = deque(tokenizer(type))
    #     t = parseType(tokens, Context())
    #     v = stlc.TypedVariable(t, name)
    #     try:
    #         if self.infix[op_name] != v:
    #             raise RuntimeError(f'infix {repr(op_name)}(aka {self.infix[op_name]}) has already existed.')
    #     except KeyError:
    #         self.infix[op_name] = v


# class BinaryOp:
#     def __init__(self, op: str, priority: int, associativity: Optional[Literal['left', 'right']]):
#         self.op = op
#         self.priority = priority
#         self.associativity = associativity


# def try_to_match_operator(q: Deque[str]):
#     try:
#         double = q[0] + q[1]
#     except IndexError as e:
#         ...
# if q[0] in {'(', ')', 'λ', '.', '+', '*'}:


def tokenizer(s: str) -> Iterable[str]:
    assert isinstance(s, str)
    q: Deque[str] = deque(s)
    # print(f'q={q}')
    state: List[int] = [0]
    identifier: List[str] = []
    integer_constant: List[str] = []
    while q:
        head = q[0]
        if state[-1] == 0:
            assert not identifier
            assert not integer_constant
            q.popleft()
            if head in {'(', ')', 'λ', '.', ':', ',', '~', '⊥', '∀', '∃', '<', '>', '+', '*', '|'}:
                yield head
            elif head == '\\':
                y = head
                try:
                    if q[0] == '/':
                        y = '\\/'
                        q.popleft()
                except IndexError:
                    ...
                yield y
            elif head == '/':
                y = head
                try:
                    if q[0] == '\\':
                        y = '/\\'
                        q.popleft()
                except IndexError:
                    ...
                yield y
            elif head == '-':
                y = head
                try:
                    if q[0] == '>':
                        y = '->'
                        q.popleft()
                except IndexError:
                    ...
                yield y
            elif head == '=':
                y = head
                try:
                    if q[0] == '>':
                        y = '=>'
                        q.popleft()
                except IndexError:
                    ...
                yield y
            elif head.isalpha() or head == '_':
                identifier.append(head)
                state.append(1)
            elif head.isspace():
                ...
            elif head.isdigit():
                integer_constant.append(head)
                state.append(2)
            else:
                raise RuntimeError(f'head={repr(head)}@state {state[-1]}')
        elif state[-1] == 1:
            if head.isalnum() or head == '_':
                identifier.append(head)
                q.popleft()
            elif head.isspace() or not head.isalnum():
                yield ''.join(identifier)
                identifier.clear()
                state.append(0)
            else:
                raise RuntimeError(f'head={head}, identifier={identifier} @state {state[-1]}')

        elif state[-1] == 2:
            if head.isdigit():
                integer_constant.append(head)
                q.popleft()
            else:
                yield ''.join(integer_constant)
                integer_constant.clear()
                state.append(0)

    if identifier:
        assert state[-1] == 1
        assert not integer_constant
        yield ''.join(identifier)
    if integer_constant:
        assert state[-1] == 2
        assert not identifier
        yield ''.join(integer_constant)


r"""
**S** → **Term** | **Term** ``':'`` **Type**
**Term** → **Apply** 
**Apply** → **Apply** **NonApp** | **NonApp**
**NonApp** → **FuncDef** | ``'('`` **Term** ``')'`` | **Pair** | **Variable** | **Constant**
             | **Inl** | **Inr** | **First** | **Second** | **CaseOf**
**Inl** → ``'inl'`` ``'('`` **Term** ``')'`` 
**Inr** → ``'inr'`` ``'('`` **Term** ``')'`` 
**First** → ``'fst'`` ``'('`` **Term** ``')'`` 
**Second** → ``'snd'`` ``'('`` **Term** ``')'``
**CaseOf** → ``'case'`` **Term** ``'of'`` **Term** ``'=>'`` **Term** ``'|'`` **Term** ``'=>'`` **Term**
**Pair** → ``'('`` **Term** ``','`` **Term** ``')'``
**FuncDef** → ``'λ'`` **Variable** ``':'`` Type ``'.'`` **Term**
**Variable** → ``identifier``
**Constant** → ``digits``

**Type** → **ImplType**
**ImplType** → **ImplType** ``'->'`` **SumType** | **SumType**
**SumType** → **SumType** ``'\/'`` **ProductType** | **ProductType**
**ProductType** → **ProductType** ``'/\'`` **PredicateApply**
**PredicateApply** → **PredicateApply** **NotType** | **NotType**
**NotType** → ``'~'`` **NotType** | **SingleType**
**SingleType** → **IndividualType** | ``'('`` **Type** ``')'`` | **QuantifiedType** | 
**IndividualType** → ``identifier``
**QuantifiedType** → 
    **Quantifier** **Variable** ``':'`` **IndividualType** ``'.'`` **QuantifiedType**
    |**Quantifier** **Variable** ``':'`` **ImplType** ``'.'`` **QuantifiedType** 
    | **Type**
**Quantifier** → ``'∀'`` | ``'∃'``
"""


def parseS(q: CleverDeque[str], env: 'Context') -> 'stlc.ITypedLambda':
    """
    **S** → **Term** | **Term** ``':'`` **Type**
    """
    v = parseTerm(q, env)
    if not q:
        assert q[0] == ':', f'expected type specification sign \':\', got {repr(q[0])}'
        q.popleft()
        t = parseType(q, env)
        v.type_check(t)
    return v


def parseTerm(q: CleverDeque[str], env: Context) -> 'stlc.ITypedLambda':
    """
    **Term** → **Apply**
    """
    return parseApply(q, env)


def parseApply(q: CleverDeque[str], env: Context) -> Union['stlc.TypedApply',
                                                           'stlc.TypedVariable']:
    """
    **Apply** → **Apply** **NonApp** | **NonApp**
    """
    m = parseNonApp(q, env)
    # while q and q[0] != ')' and q[0] != ',' and q[0] != ':' and q[0] not in stlc.BinaryTypeTerm.op_table:
    while q and q[0] in {'λ', '(', 'inl', 'inr', 'fst', 'snd', 'case'} or q[0].isidentifier() or q[0].isdigit():
        if q[0] == 'of':
            break
        # print(f'm={m}')
        n = parseNonApp(q, env)
        m = stlc.TypedApply(m, n)
    return m


def parseNonApp(q: CleverDeque[str], env: Context) -> Union['stlc.TypedFuncDef', 'stlc.ITypedLambda']:
    """
    **NonApp** → **FuncDef** | ``'('`` **Term** ``')'`` | **Pair** | **CaseOf**
    | **Inl** | **Inr** |**First** | **Second** | **Variable** | **Constant**
    """
    if q[0] == 'λ':
        v = parseFuncDef(q, env)
        return v
    elif q[0] == '(':
        try:
            v = parseParenthesized(parseTerm, q, env)
        except TryParsingParenthesizedFailed as e:
            assert isinstance(e.args[0], stlc.ITypedLambda)
            v = parsePair(q, env, e.args[0])
        return v
    elif q[0] == 'case':
        return parseCaseOf(q, env)
    elif q[0] == 'inl':
        raise NotImplementedError
        return parseInl(q, env)
    elif q[0] == 'inr':
        raise NotImplementedError
        return parseInr(q, env)
        # return parseInr(q, env)
    elif q[0] == 'fst':
        return parseFirst(q, env)
        # return parseFirst(q, env)
    elif q[0] == 'snd':
        return parseSecond(q, env)
        # return parseSecond(q, env)
    elif q[0].isidentifier():
        return parseVariable(q, env)
    elif q[0].isdigit():
        return parseConstant(q, env)
    else:
        raise RuntimeError(f'unexpected token {repr(q[0])}')


T = TypeVar('T', bound='Union[stlc.ITypedLambda, stlc.IType]')


def parseParenthesized(kont: Callable[[CleverDeque[str], Context], T],
                       q: CleverDeque[str],
                       env: Context) -> T:
    assert q, 'unexpected EOF.'
    assert q[0] == '(', r"expected left parenthesis '(', got {}.".format(repr(q[0]))
    q.popleft()

    res = kont(q, env)
    assert res is not None
    assert q, 'unexpected EOF.'
    if q[0] != ')':
        if q[0] == ',':
            raise TryParsingParenthesizedFailed(res)
        else:
            raise AssertionError(r"expected right parenthesis ')', got {}.".format(repr(q[0])))
    else:
        q.popleft()
        return res


def parse_labeled_4in1(q: CleverDeque[str], env: Context) -> 'stlc.ITypedLambda':
    """
    **Inl** → ``'inl'`` ``'('`` **Term** ``')'``

    **Inr** → ``'inr'`` ``'('`` **Term** ``')'``

    **First** → ``'fst'`` ``'('`` **Term** ``')'``

    **Second** → ``'snd'`` ``'('`` **Term** ``')'``

    """
    try:
        assert q[1] == '(', r"missed '('."
    except IndexError:
        raise RuntimeError('unexpected EOF.')
    q.popleft()
    q.popleft()
    term = parseTerm(q, env)

    assert q, 'unexpected EOF.'
    assert q[0] == ')', r"missed '('."
    q.popleft()
    return term


def parseInl(q: CleverDeque[str], env: Context) -> 'Callable[[stlc.Or], stlc.TypedInl]':
    """**Inl** → ``'inl'`` ``'('`` **Term** ``')'`` """
    assert q[0] == 'inl', r"Expected 'inl', got {} instead.".format(repr(q[0]))
    term = parse_labeled_4in1(q, env)

    def closure(union_t: 'stlc.Or'):
        assert isinstance(union_t, stlc.Or)
        return stlc.TypedInl(union_t, term)

    return closure


def parseInr(q: CleverDeque[str], env: Context) -> 'Callable[[stlc.Or], stlc.TypedInr]':
    """**Inr** → ``'inr'`` ``'('`` **Term** ``')'`` """
    assert q[0] == 'inr', r"Expected 'inr', got {} instead.".format(repr(q[0]))
    term = parse_labeled_4in1(q, env)

    def closure(union_t: 'stlc.Or'):
        assert isinstance(union_t, stlc.Or)
        return stlc.TypedInr(union_t, term)

    return closure


def parseFirst(q: CleverDeque[str], env: Context) -> 'stlc.TypedFirst':
    """**First** → ``'fst'`` ``'('`` **Term** ``')'`` """
    assert q[0] == 'fst', r"Expected 'fst', got {} instead.".format(repr(q[0]))
    term = parse_labeled_4in1(q, env)
    return stlc.TypedFirst(term)


def parseSecond(q: CleverDeque[str], env: Context) -> 'stlc.TypedSecond':
    """**Second** → ``'snd'`` ``'('`` **Term** ``')'``"""
    assert q[0] == 'snd', r"Expected 'snd', got {} instead.".format(repr(q[0]))
    term = parse_labeled_4in1(q, env)
    return stlc.TypedSecond(term)


def parseCaseOf(q: CleverDeque[str], env: Context) -> 'stlc.TypedCaseOf':
    """
    **CaseOf** → ``'case'`` **Term** ``'of'`` **Term** ``'=>'`` **Term** ``'|'`` **Term** ``'=>'`` **Term**
    """
    assert q[0] == 'case'
    q.popleft()

    t = parseTerm(q, env)

    case_ex_t = t.get_type()
    assert isinstance(case_ex_t, stlc.Or)
    assert q[0] == 'of'
    q.popleft()

    # case1 = parseTerm(q, env)
    if q[0] == 'inl':
        case1 = parseInl(q, env)(case_ex_t)
    elif q[0] == 'inr':
        case1 = parseInr(q, env)(case_ex_t)
    else:
        raise RuntimeError

    assert q[0] == '=>'
    q.popleft()

    e1 = parseTerm(q, env)

    assert q[1] == '|'
    q.popleft()

    # case2 = parseTerm(q, env)
    assert q[0] == 'inl' or q[0] == 'inr'
    if q[0] == 'inl':
        case2 = parseInl(q, env)(case_ex_t)
    elif q[0] == 'inr':
        case2 = parseInr(q, env)(case_ex_t)
    else:
        raise RuntimeError

    assert q[0] == '=>'
    q.popleft()

    e2 = parseTerm(q, env)
    assert e1.get_type() == e2.get_type()
    return stlc.TypedCaseOf(t, case1, e1, case2, e2)


def parsePair(q: CleverDeque[str], env: Context, v0: 'stlc.ITypedLambda') -> 'stlc.TypedPair':
    """**Pair** → ``'('`` **Term** ``','`` **Term** ``')'``"""
    assert q, 'unexpected EOF when parsing Pair.'
    assert q[0] == ',', f'missing comma after {v0} when parsing Pair.'
    assert isinstance(v0, stlc.ITypedLambda)
    q.popleft()
    v = parseTerm(q, env)
    res = stlc.TypedPair(v0, v)
    assert q, 'unexpected EOF when parsing Pair.'
    assert q[0] == ')', r"expected right parenthesis ')', got {}.".format(repr(q[0]))
    q.popleft()
    return res


def parseFuncDef(q: CleverDeque[str], env: Context) -> 'stlc.TypedFuncDef':
    """**FuncDef** → ``'λ'`` **Variable** ``':'`` Type ``'.'`` **Term**"""
    try:
        assert q[0] == 'λ'  # or q[0] == '\\'
        assert q[1].isidentifier()
        assert q[2] == ':'
        var_name = q[1]
    except IndexError:
        raise RuntimeError('unexpected EOF.')
    q.popleft()
    q.popleft()
    q.popleft()
    var = stlc.TypedVariable(name=var_name)
    env.bound_var.append(var)
    var_t = parseType(q, env)
    var.set_type(var_t)

    try:
        assert q[0] == '.'
        q.popleft()
    except IndexError:
        raise RuntimeError('unexpected EOF.')

    body = parseTerm(q, env)
    assert var is env.bound_var[-1]
    del env.bound_var[-1]
    return stlc.TypedFuncDef(var, body)


def parseVariable(q: CleverDeque[str], env: Context) -> 'stlc.TypedVariable':
    """ **Variable** → ``identifier`` """
    assert q[0].isidentifier() and q[0] != 'λ', f'invalid variable name {repr(q[0])}.'
    assert q[0] not in reserved_words, f'{repr(q[0])} is a reserved word.'
    name = q.popleft()
    if (v := env.getVarByName(name)) is None:
        s = input(f'please specify the type of free variable {repr(name)}:')
        var_t = parseType(CleverDeque(tokenizer(s)), env)
        print(f'bind free variable {repr(name)} with type {var_t}.')
        v1 = stlc.TypedVariable(var_t, name)
        env.free_var.append(v1)
        return v1
    else:
        return v


def parseConstant(q: CleverDeque[str], env: Context) -> 'stlc.TypedConstant':
    """**Constant** → ``digits``"""
    assert q, 'unexpected EOF while parsing constant.'
    v = q[0]
    q.popleft()
    if 'int' in env.individual_types:
        const_t = stlc.IndividualType('int')
        s = input(f'inferred constant {v} has type {const_t}.\n'
                  'Please press Enter to confirm & continue, or specify another type below:\n')
        while 1:
            if s:
                const_t = parseType(CleverDeque(tokenizer(s)), env)
                s = input(f'specified {v} with type {const_t}. Press Enter to confirm, or specify a new type:')
            else:
                return stlc.TypedConstant(const_t, int(v))

    else:
        s = input(f'Please specify a type for constant {v}:\n')
        while 1:
            const_t = parseType(CleverDeque(tokenizer(s)), env)
            s = input(f'specified {v} with type {const_t}. Press Enter to confirm, or specify a new type:')
            if not s:
                return stlc.TypedConstant(const_t, int(v))


# Type -> FuncType
# FuncType -> FuncType '->' SumType | SumType
# SumType -> SumType '\/' ProductType | ProductType
# ProductType -> ProductType '/\' SingleType
# SingleType -> id | '(' Type ')' | ForallType | ExistsType


def parseType(q: CleverDeque[str], env: Context) -> stlc.IType:
    """**Type** → **ImplType**"""
    return parseBinaryOp(q, env)


def parseBinaryOp(q: CleverDeque[str], env: Context, current_precedence: int = 1) -> stlc.IType:
    r"""
    **ImplType** → **ImplType** ``'->'`` **SumType** | **SumType**

    **SumType** → **SumType** ``'\/'`` **ProductType** | **ProductType**

    **ProductType** → **ProductType** ``'/\'`` **PredicateApply**
    """
    table: Dict[int, stlc.Associativity] = stlc.BinaryTypeTerm.asso_table
    op_table: Dict[str, Type[stlc.BinaryTypeTerm]] = stlc.BinaryTypeTerm.op_table
    if current_precedence > max(table.keys()):
        v0 = parsePredicateApply(q, env)
        return v0
    else:
        v0 = parseBinaryOp(q, env, current_precedence + 1)
    if stlc.BinaryTypeTerm.asso_table[current_precedence] == stlc.Associativity.LEFT:
        while 1:
            if not q or q[0] == ')' or q[0] == '.':
                break
            assert q[0] in op_table.keys(), ''
            if op_table[(op := q[0])].precedence == current_precedence:
                q.popleft()
                v1 = parseBinaryOp(q, env, current_precedence + 1)
                v0 = op_table[op](v0, v1)
            else:
                break
        return v0
    else:
        stack: List[stlc.IType] = [v0]
        op_stack: List[str] = []
        while 1:
            if not q or q[0] == ')' or q[0] == '.':
                break
            assert q[0] in op_table.keys()
            if op_table[(op := q[0])].precedence == current_precedence:
                q.popleft()
                v1 = parseBinaryOp(q, env, current_precedence + 1)
                stack.append(v1)
                op_stack.append(op)
            else:
                break
        while len(stack) >= 2:
            x, y = stack[-2], stack[-1]
            stack.pop()
            stack.pop()
            stack.append(op_table[op_stack.pop()](x, y))
        return stack[0]


def parsePredicateApply(q: CleverDeque[str], env: Context) -> stlc.IType:
    """**PredicateApply** → **PredicateApply** **NotType** | **NotType**"""
    m = parseNotType(q, env)
    if q and q[0] not in {')', ',', '.', ':'} and q[0] not in stlc.BinaryTypeTerm.op_table:
        while q and q[0] not in {')', ',', '.', ':'} and q[0] not in stlc.BinaryTypeTerm.op_table:
            # print(f'm={m}')
            n = parseNotType(q, env)
            assert isinstance(m, stlc.ITypedLambda)
            assert isinstance(n, stlc.ITypedLambda)
            m = stlc.PredicateApply(m, n)
    return m


def parseNotType(q: CleverDeque[str], env: Context) -> stlc.IType:
    """**NotType** → ``'~'`` **NotType** | **SingleType**"""
    if q[0] == '~':
        q.popleft()
        v = parseNotType(q, env)
        return stlc.Not(v)
    else:
        return parseSingleType(q, env)


def parseSingleType(q: CleverDeque[str], env: Context) -> Union[stlc.TypedVariable, stlc.IType]:
    """
    **SingleType** → **IndividualType**| **TypedVariable** | ``'('`` **Type** ``')'`` | **QuantifiedType**

    **IndividualType** → ``identifier``
    """
    v: Optional[stlc.IType] = None
    if q[0] == '(':
        v = parseParenthesized(parseType, q, env)
    elif q[0] == '∀' or q[0] == '∃':
        v = parseQuantifiedType(q, env, q[0])
    elif q[0] == '⊥':
        v = stlc.Falsum()
        q.popleft()
    elif q[0].isidentifier():
        assert q[0] != 'λ', 'invalid typename λ'
        if (v0 := env.getVarByName(q[0])) is not None:
            q.popleft()
            return v0
        else:
            if q[0] in env.individual_types:
                v = stlc.IndividualType(q[0])
                q.popleft()
            else:
                raise RuntimeError(
                    f'{repr(q[0])} unspecified yet. '
                    f'Check the arguments you passed to Context object before calling parse function.')

    assert v is not None
    return v


# ∀x.∃y. x in Nat /\ y in Nat -> x + 1 = y     λx.λy.λz
# ∀x:Nat.∃y:Nat. x + 1 = y
# ∀x:Nat.
def parseQuantifiedType(q: CleverDeque[str], env: Context, quantifier: str):
    """
    **QuantifiedType** →
        **Quantifier** **Variable** ``':'`` **IndividualType** ``'.'`` **QuantifiedType**

        |**Quantifier** **Variable** ``':'`` **ImplType** ``'.'`` **QuantifiedType**

        | **Type**

    **Quantifier** → ``'∀'`` | ``'∃'``
    """
    try:
        assert q[0] == quantifier
        assert q[1].isidentifier()
        assert q[2] == ':'
        var_name = q[1]
    except IndexError:
        raise RuntimeError('unexpected EOF.')
    q.popleft()
    q.popleft()
    q.popleft()
    var = stlc.TypedVariable(name=var_name)
    env.bound_var.append(var)
    var_t = parseType(q, env)
    var.set_type(var_t)

    assert isinstance(var_t, stlc.IndividualType)
    try:
        assert q[0] == '.'
        q.popleft()
    except IndexError:
        raise RuntimeError('unexpected EOF.')
    if q and q[0] == '∀' or q[0] == '∃':
        body = parseQuantifiedType(q, env, q[0])
        assert body is not None
    else:
        body = parseType(q, env)
        assert body is not None
    assert var is env.bound_var[-1]
    del env.bound_var[-1]
    if quantifier == '∀':
        return stlc.ForAllType(var, body)
    elif quantifier == '∃':
        return stlc.ExistsType(var, body)
    assert 0


def parse_type(s: str, typenames: List[str], **kwargs: str):
    r"""
    Parses a logical formula ``s``.

    .. note::
    The prover supports **only** the automatic proving of *propositional logic*, as of Jul. 23, 2022.

    Formulae in *first-order-logic* (aka *FOL*) are probably parsed correctly
    but the *automatic proving* remains incomplete.

    :type s:
        str

    :param s:
        A formula in propositional logic.

    :param typenames:
        A list of proposition symbols (usually written in uppercase) in the formula.
        The parser will report an error if unspecified letters encountered,
        or ask for specification in an interactive environment.
        For example, for ``s='A/\B'``, typenames should be ``['A', 'B']``.
    :type typenames: List[str]

    :param kwargs:
        This is originally designed for function symbols appearing in first-order-logic.
        For example, the binary relation *less than*(``lt``) for natural numbers can be written as
        ``lt='nat->nat->Prop'``,
        where ``nat`` is the type of natural numbers, and ``Prop`` the type of proposition.
        At present, it is just for parsing, and for theorem proving in propositional logic, it is redundant.
    :return:
        An IType object, which has a ``deduce`` method to call.
    """
    stlc.TypedVariable.counter = 0
    return parseType(CleverDeque(tokenizer(s)), Context(typenames=typenames, **kwargs))


def parse_formula(s: str, typenames: List[str], **kwargs: str):
    stlc.TypedVariable.counter = 0
    return parseS(CleverDeque(tokenizer(s)), Context(typenames=typenames, **kwargs))


if __name__ == '__main__':
    e = ['x', '(x)', 'x y', '(x y z)', 'x (y z)', '(x y) (z)', 'x0 x1 x2 x3 (x4 (x5 x6) ((x6 x7 x8) x9) x10)']
    formula1 = '(λx.z) (λw.w w w)λw. w w w'
    formula2 = 'λx.λy.y x x x y x'
    formula3 = 'λx:A->B.λy:A.x y:(A->B)->A->B'
    formula4 = '(λf:int->int. λy:int. f(f y)) (λz:int. + z 1) : int->int'.replace('+', 'add')
    formula5 = 'λx:~A.λy:A. x y:~A->A->⊥'
    formula6 = r'(∀x:nat.x<x+1)' \
               r'->((∀x:nat.∀y:nat.∀z:nat.(x<y/\y<z -> x<z)) -> ∀x:nat. x < (x+1)+1)'
    formula6_2 = r'(∀x:nat.P(x, add(x, 1)))->' \
                 r'((∀x:nat.∀y:nat.∀z:nat.(P(x, y)/\P(y, z) -> P(x, z))) -> ∀x:nat. P(x, add(x, 2))'
    formula7 = r'λp:(∀x:nat.P(x, x+1)). (λq:(∀x:nat.∀y:nat.∀z:nat.(P(x, y)/\P(y, z) -> P(x, z)) .λx:nat. q x (x+1))'
    formula8 = r'λp: (∀x:nat. x<x+1). ' \
               r'(' \
               r'λq: (∀x:nat. ∀y:nat. ∀z:nat. (x<y/\y<z -> x<z)). ' \
               r'λx:nat. ' \
               r'q x (x+1) (x+1)+1 (p x , p x+1)' \
               r'): ' + formula6
    formula9 = r'λx:nat.λy:nat.λz:nat.λp:P(x, y)/\P(y, z). P(x, z)'
    formula10 = r'λx:A.λy:B.x:A->B->A'
    formula11 = r'(A\/B)->(B\/A)'
    formula12 = r'λx:A\/B.case x of inl m => inr m | inr n => inl n:(A\/B)->(B\/A)'
    formula15 = r'(A\/(B\/C))->((A\/B)\/C)'
    de_morgan1 = r'(~(A\/B)->(~A/\~B))/\((~A/\~B)->~(A\/B))'
    de_morgan2 = r'(A\/B)->~(~A/\~B)'
    de_morgan3 = r'(A/\B)->~(~A\/~B)'
    de_morgan4 = r'(~P\/~Q)->~(P/\Q)'
    formula18 = r'∀x:R. impl (gt x 0) (gt (mul x x) 0) '
    formula19 = r'∀x:G.∀y:G. eq x y -> eq y x'
    formula20 = r'((∀x:G.eq x x)->' \
                r'(∀x:G.∀y:G.eq x y->eq y x)->' \
                r'(∀x:G.∀y:G.∀z:G.eq x y/\eq y z->eq x z)->' \
                r'(∃e:G.∀x:G.eq e (mul x e)/\eq e (mul e x))->' \
                r'(∃e:G.∀x:G.∃y:G.eq e (mul x y)/\ eq e (mul y x)))->' \
                r'(∀x:G.∀y:G.∀z:G.eq (mul x (mul y z)) (mul (mul x y) z))->' \
                r'((∃e:G.∀x:G.eq e (mul x e)/\eq e (mul e x)->∀x:G. eq e (mul x x))->' \
                r' (∀x:G.∀y:G.eq (mul x y) (mul y x)))'
    formula21 = r'(∀x:nat.lt x (S x))' \
                r'->((∀x:nat.∀y:nat.∀z:nat. lt x y /\ lt y z -> lt x z) -> ∀x:nat. lt x (S (S x)))'
    formula22 = r'A->~~A'
    formula23 = r'A->(A->B)->B'
    formula24 = r'A/\B->A'
    formula25 = r'A/\B->B'
    formula26 = r'~~(A\/~A)'
    peirce_law = r'((P->Q)->P)->P'
    formula27 = r'(A->B->C)->((A->B)->(A->C))'
    formula28 = r'A->(A\/B)'
    formula29 = r'(A\/B)->(A->C)->(B->C)->C'
    formula30x = r'~~~P\/~~P'
    formula31 = r'(A->~A)->~(~A->A)'
    formula32 = r'~(A->B)->~A'
    formula33 = r'(⊥->P)->((P->Q)->(X\/(Q->P)))->(X->(P\/~Q))->Q->P'
    formula34 = r'((P->~P)/\(~~Q->~Q))->~(P\/Q)'
    formula35 = r'~(P\/~Q)->~(Q->P)'
    law_of_distribution_1 = r'(A/\(B\/C))->((A/\B)\/(A/\C))'
    law_of_distribution_2 = r'(A\/(B/\C))->((A\/B)/\(A\/C))'
    # (A\/~A->False)->False => \x.(A\/~A->False).False

    # s = '(λf.f f)(λf.λx.f(f x))'

    # for e in e:
    #     q = deque(tokenizer(e))
    #     print(f'tokens={list(q)}')
    #     print(t := parseTerm(q, []))
    # context = Context([stlc.TypedVariable(parseType(deque(tokenizer('int->int->int')), Context()), 'add')])
    # print(t.get_type())
    # def new_fv(typekwargs):
    #     return stlc.TypedVariable(parseType(CleverDeque(tokenizer(type)), Context()), name)

    # print(parse_type(r'(⊥->P)->P\/~Q->Q->P', typenames=['X', 'P', 'Q']).deduce(env=[], hypothesis={}, visit={}))
    # print(parse_type(de_morgan1, typenames=['A', 'B']))
    # print(parseS(deque(tokenizer(formula8)), Context()))

    # print(parse_type(formula21, lt='nat->nat->Prop', S='nat->nat', typenames=['nat', 'Prop']))
    # stlc.__my_debug__ = True
    print(t := parse_type(formula15, typenames=['A', 'B', 'C']))
    # print(parse_type(formula20, eq='G->G->Prop', mul='G->G->G', typenames=['G', 'Prop']))
    # print(parse_type(formula22, eq='G->G->Prop', mul='G->G->G', typenames=['A', 'B', 'C', 'P', 'Q', 'G', 'Prop']))
    # print(t.de_bruijn_index([]))
    f = t.deduce([], {}, {})
    print(f, ':', f.get_type())
    assert f.get_type() == t
    # print(t.beta_reduce_impl())
    # print(t.beta_reduce_impl().beta_reduce_impl())
