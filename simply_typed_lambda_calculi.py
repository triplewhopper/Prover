from typing import Optional, Union, TypeVar, Dict, List, ChainMap, FrozenSet, Generic, Tuple, Type, Set
from abc import ABC, abstractmethod
import sys
import lambda_interface as lc_interface
from collections import OrderedDict, deque
import enum

assert sys.version_info >= (3, 8)
T = TypeVar('T')
T1 = TypeVar('T1')
T2 = TypeVar('T2')
__my_debug__ = False
__author__ = 'triplewhopper'
# class Context(Mapping[KT, VT]):
#     def __init__(self, vars: List[KT]):
#         self.vars = vars
#         self.roster: Dict[T, List[int]] = {}
#         for i, v in enumerate(self.vars):
#             self.roster.setdefault(v).append(i)
#
#     def __setitem__(self, key: T, value: 'IType'):
#         assert isinstance(key, str)
#         assert isinstance(value, IType)
#     def __getitem__(self, item: T):
#
#     def __delitem__(self, key: T):
#         ...
TypeContext = Dict['Variable', List['IType']]


# class TypeContext(Dict['Variable', 'IType']):
#     def __init__(self, *args, **kwargs):
#         super(TypeContext, self).__init__(*args, **kwargs)
class Context:
    table: Dict[str, Dict[int, Optional['Context']]] = dict()
    assert sys.version_info >= (3, 8)

    def __init__(self, var: 'TypedVariable', father: Optional['Context'] = None):
        self.var = var
        self.father = father
        if father is None:
            self.depth = 0
        else:
            self.depth = father.depth + 1
        try:
            a = Context.table[var.name]
            last_key = next(reversed(a.keys()))
        except KeyError:
            Context.table[var.name] = {self.depth: self}
            return
        assert a
        assert last_key < self.depth
        assert self.depth not in a
        a[self.depth] = self

    def check(self, var: 'TypedVariable'):
        ...

    @classmethod
    def add_free_variable(cls, var: 'TypedVariable'):
        try:
            t = cls.table[var.name]
        except KeyError:
            ...


def compatible(u: FrozenSet['TypedVariable'], v: FrozenSet['TypedVariable']) -> bool:
    for x in u:
        for y in v:
            if x.name == y.name:
                if x.get_type() != y.get_type():
                    return False
    return True


class IType(ABC):
    @abstractmethod
    def latex_form(self) -> str:
        ...

    @abstractmethod
    def deduce(self, env: List['ITypedLambda'],
               hypothesis: Dict['IType', 'ITypedLambda'], visit: Dict['IType', int]) -> 'ITypedLambda':
        ...

    def _repr_latex_(self) -> str:
        if self.free_variables:
            fv = r'\{' + ', '.join(map(lambda x: x.latex_form() + ': ' + x.get_type(), self.free_variables)) + r'\}'
        else:
            fv = ''
        return '$' + fv + r'\vdash ' + self.latex_form() + '$'

    @abstractmethod
    def __eq__(self, other: 'IType') -> bool:
        ...

    @property
    @abstractmethod
    def free_variables(self) -> FrozenSet['TypedVariable']:
        ...

    @property
    @abstractmethod
    def has_substitution(self) -> bool:
        ...

    def get_type(self):
        return self

    @abstractmethod
    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        ...


class DeductionFailed(RuntimeError):
    ...


class IndividualType(IType, str):
    empty_set = frozenset()

    def __init__(self, *args, **kwargs):
        if isinstance(self, Falsum):
            assert str.__eq__(self, '⊥')
        else:
            assert self.isidentifier()

    @property
    def free_variables(self):
        return IndividualType.empty_set

    @property
    def has_substitution(self) -> bool:
        return False

    def __eq__(self, other: 'IType') -> bool:
        if isinstance(other, IndividualType):
            return str.__eq__(self, other)
        return False

    def __hash__(self):
        return str.__hash__(self)

    def latex_form(self) -> str:
        return self

    def deduce(self, env: List['ITypedLambda'], hypothesis: Dict['IType', 'ITypedLambda'],
               visit: Dict['IType', int]) -> 'ITypedLambda':
        if self in hypothesis:
            return hypothesis[self]
        # visit = visit.new_child()
        # visit.setdefault(self, 0)

        new: Dict[IType, ITypedLambda] = {}
        new_apply: Dict[IType, ITypedLambda] = {}
        new_fst_snd: Dict[IType, ITypedLambda] = {}
        if __my_debug__:
            print(f'Individual.deduce(self={self}, hypothesis={hypothesis}, env={env}, visit={visit})')
        while 1:
            if self in hypothesis:
                return hypothesis[self]
            new.clear()
            new_apply.clear()
            new_fst_snd.clear()
            while 1:
                for x_t, x in hypothesis.items():
                    for y_t, y in hypothesis.items():
                        if isinstance(x_t, Impl) \
                                and x_t.t0 == y_t and x_t.t1 not in hypothesis \
                                and x_t.t1 not in new and x_t.t1 not in new_apply:
                            v = TypedApply(x, y)
                            assert v.get_type() == x_t.t1
                            new_apply[x_t.t1] = v
                        elif isinstance(y_t, Impl) \
                                and y_t.t0 == x_t and y_t.t1 not in hypothesis \
                                and y_t.t1 not in new and y_t.t1 not in new_apply:
                            v = TypedApply(y, x)
                            assert v.get_type() == y_t.t1
                            new_apply[y_t.t1] = v
                if new_apply:
                    new.update(new_apply)
                    new_apply.clear()
                else:
                    break

            while 1:
                for x_t, x in hypothesis.items():
                    if isinstance(x_t, And):
                        if x_t.t0 not in hypothesis and x_t.t0 not in new and x_t.t0 not in new_fst_snd:
                            new[x_t.t0] = TypedFirst(x)
                        if x_t.t1 not in hypothesis and x_t.t1 not in new and x_t.t0 not in new_fst_snd:
                            new[x_t.t1] = TypedSecond(x)
                if new_fst_snd:
                    new.update(new_fst_snd)
                    new_fst_snd.clear()
                else:
                    break

            if new and visit:
                visit.clear()

            wait_to_deduce: Dict[Impl, ITypedLambda] = {}

            for x_t, x in hypothesis.items():
                if isinstance(x_t, Impl):
                    if x_t.t1 not in hypothesis and x_t.t1 not in new and x_t.t0 != self and x_t.t0 not in visit:  # and x_t.t1 == self:
                        wait_to_deduce.setdefault(x_t, x)
                        visit[x_t.t0] = 1
            if __my_debug__:
                print(f'wait_to_deduce={wait_to_deduce}')
                print(f'new={new}')
            if new:
                hypothesis.update(new)
                visit.clear()
                if self in new:
                    return new[self]

            assert self not in wait_to_deduce

            for x_t, x in wait_to_deduce.items():
                try:
                    e = x_t.t0.deduce(env, hypothesis, visit)
                except DeductionFailed:
                    continue
                new[x_t.t1] = v = TypedApply(x, e)

            if new:
                hypothesis.update(new)
                visit.clear()
            else:
                wait_to_destruct: Dict[Or, ITypedLambda] = {}
                for x_t, x in hypothesis.items():
                    if isinstance(x_t, Or) and (x_t.t0 not in hypothesis and x_t.t1 not in hypothesis):
                        wait_to_destruct.setdefault(x_t, x)
                if __my_debug__:
                    print(f'wait_to_destruct={wait_to_destruct}')
                for x_t, x in wait_to_destruct.items():
                    visit[self] = 1
                    try:
                        e0, e1 = x_t.destruct(self, env, hypothesis, visit)
                        case_of = TypedCaseOf(x,
                                              TypedInl(x_t, e0.var), e0.body,
                                              TypedInr(x_t, e1.var), e1.body)

                        new[self] = case_of
                        visit.clear()
                        break
                    except DeductionFailed:
                        ...
                    finally:
                        if self in visit:
                            del visit[self]
                if new:
                    hypothesis.update(new)
                    continue
                raise DeductionFailed

        # end_pos = len(env)
        # while (head_pos := visit[self]) < len(env):
        #     h = env[head_pos]
        #     h_t = h.get_type()
        #     visit[self] += 1
        #     if self in hypothesis:
        #         del env[end_pos:]
        #         # if visit[self] > end_pos:
        #         #     visit[self] = end_pos
        #         return hypothesis[self]
        #     print(
        #         f'Individual.deduce bfs(head_pos={head_pos}, end_pos={end_pos})(self={self}, h={h}, h_t={h_t}, env={env}, visit={visit})')
        #     if isinstance(h_t, IndividualType):
        #         assert h_t != self
        #         assert h_t in hypothesis
        #         func_t = Impl(h_t, self)
        #         if func_t in hypothesis:
        #             hypothesis[self] = v = TypedApply(hypothesis[func_t], hypothesis[h_t])
        #             del env[end_pos:]
        #             return v
        #         else:
        #             try:
        #                 e = func_t.deduce(env, hypothesis, visit)
        #             except DeductionFailed:
        #                 continue
        #             hypothesis[func_t] = e
        #             hypothesis[self] = v = TypedApply(e, hypothesis[h_t])
        #             del env[end_pos:]
        #             return v
        #
        #     elif isinstance(h_t, And):
        #         if h_t.t0 not in hypothesis:
        #             hypothesis[h_t.t0] = v = TypedFirst(h)
        #             env.append(v)
        #         if h_t.t1 not in hypothesis:
        #             hypothesis[h_t.t1] = v = TypedSecond(h)
        #             env.append(v)
        #     elif isinstance(h_t, Or):
        #         assert 0
        #     elif isinstance(h_t, Impl):
        #         if h_t.t1 not in hypothesis:
        #             # visit_self0 = visit[self]
        #             try:
        #                 e = h_t.t0.deduce(env, hypothesis, visit)
        #             except DeductionFailed:
        #                 # visit[self] = visit_self0
        #                 continue
        #             hypothesis[h_t.t1] = v = TypedApply(h, e)
        #             env.append(v)
        #
        # del env[end_pos:]
        # # if visit[self] > end_pos:
        # #     visit[self] = end_pos
        # raise DeductionFailed

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        return self


class Associativity(enum.Enum):
    RIGHT = 'RIGHT'
    LEFT = 'LEFT'


class BinaryTypeTerm(IType):
    """
    operators with same precedence must have same associativity
    """
    precedence: Optional[int] = None
    associativity = Associativity.LEFT
    asso_table = {1: Associativity.RIGHT, 2: Associativity.LEFT, 3: Associativity.LEFT}
    middle: str
    middle_latex: str
    op_table: Dict[str, 'Type[BinaryTypeTerm]']

    def __init__(self, t0: IType, t1: IType):
        self.t0 = t0
        self.t1 = t1
        self.hash_v = hash((self.__class__, self.t0, self.t1))
        self.string: Optional[str] = None
        self._has_substituion = self.t0.has_substitution or self.t1.has_substitution
        self._free_variables: FrozenSet['TypedVariable'] = self.t0.free_variables | self.t1.free_variables

    @property
    def free_variables(self) -> FrozenSet['TypedVariable']:
        return self._free_variables

    @property
    def has_substitution(self) -> bool:
        return self._has_substituion

    def __eq__(self, other: 'IType') -> bool:
        assert isinstance(other, IType)
        if isinstance(other, BinaryTypeTerm):
            return self.__class__.middle == other.__class__.middle and self.t0 == other.t0 and self.t1 == other.t1
        return False

    def __hash__(self):
        return self.hash_v

    def __str__(self):
        if self.string is None:
            self.string = self._print_format().format(self.t0, self.t1)
        return self.string

    __repr__ = __str__

    def _print_format(self):
        s0, s1 = '{}', '{}'
        t0, t1 = self.t0, self.t1

        if isinstance(t0, BinaryTypeTerm) and t0.precedence <= self.precedence:
            s0 = '({})'
        elif isinstance(t0, (ForAllType, ExistsType)):
            s0 = '({})'
        if isinstance(t1, BinaryTypeTerm) and (
                t1.precedence < self.precedence or (t1.precedence == self.precedence and self.middle != '->')):
            s1 = '({})'
        elif isinstance(t1, (ForAllType, ExistsType)):
            s1 = '({})'
        return r'{} {} {}'.format(s0, self.middle, s1)

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        t0 = self.t0.de_bruijn_index(bound_vars)
        t1 = self.t1.de_bruijn_index(bound_vars)
        res = self._print_format().format(t0, t1)
        return res

    def latex_form(self) -> str:
        s0 = self.t0.latex_form()
        s1 = self.t1.latex_form()
        if isinstance(self.t0, BinaryTypeTerm) and self.t0.__class__.precedence <= self.__class__.precedence:
            s0 = f'\\left({s0}\\right)'
        if isinstance(self.t1, BinaryTypeTerm) and self.t1.__class__.precedence <= self.__class__.precedence:
            s1 = f'\\left({s1}\\right)'
        return r'{} {} {}'.format(s0, self.__class__.middle_latex, s1)


class And(BinaryTypeTerm):
    precedence = 3
    middle = "/\\"
    middle_latex = r"\land"

    def deduce(self, env: List['ITypedLambda'], hypothesis: Dict['IType', 'ITypedLambda'],
               visit: Dict['IType', int]) -> 'ITypedLambda':
        if self in hypothesis:
            return hypothesis[self]
        if __my_debug__:
            print(f'And.deduce(self={self}, hypothesis={hypothesis}, env={env}, visit={visit})')
        hypothesis[self] = v = TypedPair(self.t0.deduce(env, hypothesis, visit), self.t1.deduce(env, hypothesis, visit))
        visit.clear()
        return v


class Or(BinaryTypeTerm):
    precedence = 2
    middle = r"\/"
    middle_latex = r"\lor"

    def destruct(self,
                 goal: IType,
                 env: List['ITypedLambda'],
                 hypothesis: Dict['IType', 'ITypedLambda'],
                 visit: Dict['IType', int]) \
            -> 'Tuple[TypedFuncDef, TypedFuncDef]':
        if __my_debug__:
            print(f'Or.destruct(self={self}, goal={goal}, hypothesis={hypothesis}, env={env}, visit={visit})')
        try:
            if __my_debug__:
                print(f'{goal}を証明するための場合分け1: {self.t0}')
            e0 = Impl(self.t0, goal).deduce(env, hypothesis, visit)
        except DeductionFailed as e:
            if __my_debug__:
                print(f'{goal}を証明するための場合分け1: {self.t0}は失敗')
            raise e
        if __my_debug__:
            print(f'{goal}を証明するための場合分け1: {self.t0}は成功, e0: {e0.get_type()} = {e0}')
        try:
            if __my_debug__:
                print(f'{goal}を証明するための場合分け2: {self.t1}')
            e1 = Impl(self.t1, goal).deduce(env, hypothesis, visit)
        except DeductionFailed as e:
            if __my_debug__:
                print(f'{goal}を証明するための場合分け2: {self.t1}は失敗')
            raise e
        if __my_debug__:
            print(f'{goal}を証明するための場合分け2: {self.t1}は成功, e1: {e1.get_type()} = {e1}')
        assert isinstance(e0, TypedFuncDef)
        assert isinstance(e1, TypedFuncDef)

        # del env[end_pos:]
        # if visit[self] > end_pos:
        #     visit[self] = end_pos
        return e0, e1

    def deduce(self, env: List['ITypedLambda'], hypothesis: Dict['IType', 'ITypedLambda'],
               visit: Dict['IType', int]) -> 'ITypedLambda':
        if self in hypothesis:
            return hypothesis[self]
        try:
            if __my_debug__:
                print(f'Or.deduce<{self.t0}>(self={self}, hypothesis={hypothesis}, env={env}, visit={visit})')
            inl = TypedInl(self, self.t0.deduce((env0 := env.copy()), hypothesis, visit))
            hypothesis[self] = inl
            visit.clear()
            return inl
        except DeductionFailed:
            assert env == env0
            ...
        assert env == env0
        try:
            if __my_debug__:
                print(f'Or.deduce<{self.t1}>(self={self}, hypothesis={hypothesis}, env={env}, visit={visit})')
            inr = TypedInr(self, self.t1.deduce((env1 := env.copy()), hypothesis, visit))
            hypothesis[self] = inr
            visit.clear()
            return inr
        except DeductionFailed as e:
            assert env == env1, f'env ={env}\nenv1={env1}'

        wait_to_destruct: Dict[Or, ITypedLambda] = {}
        for x_t, x in hypothesis.items():
            if isinstance(x_t, Or) and (x_t.t0 not in hypothesis and x_t.t1 not in hypothesis):
                wait_to_destruct.setdefault(x_t, x)
        if __my_debug__:
            print(f'in Or.deduce(self={self}), wait_to_destruct={wait_to_destruct}')
        for x_t, x in wait_to_destruct.items():
            visit[self] = 1
            try:
                e0, e1 = x_t.destruct(self, env, hypothesis, visit)
                case_of = TypedCaseOf(x,
                                      TypedInl(x_t, e0.var), e0.body,
                                      TypedInr(x_t, e1.var), e1.body)

                hypothesis[self] = case_of
                visit.clear()
                return case_of
            except DeductionFailed:
                ...
            finally:
                if self in visit:
                    del visit[self]
        raise DeductionFailed
        # if self not in visit:
        #     visit[self] = 0
        # end_pos = len(env)
        # while (head_pos := visit[self]) < len(env):
        #     h = env[head_pos]
        #     h_t = h.get_type()
        #     visit[self] += 1
        #     if self in hypothesis:
        #         del env[end_pos:]
        #         if visit[self] > end_pos:
        #             visit[self] = end_pos
        #         return hypothesis[self]
        #     elif h_t == self.t0:
        #         assert h_t in hypothesis
        #         del env[end_pos:]
        #         if visit[self] > end_pos:
        #             visit[self] = end_pos
        #         hypothesis[self] = v = TypedInl(self, h)
        #         return v
        #     elif h_t == self.t1:
        #         del env[end_pos:]
        #         if visit[self] > end_pos:
        #             visit[self] = end_pos
        #         assert h_t in hypothesis
        #         hypothesis[self] = v = TypedInr(self, h)
        #         return v
        #     elif isinstance(h_t, Or):
        #         print('jjj')
        #         try:
        #             e0 = Impl(h_t.t0, self).deduce(env, hypothesis, visit)
        #         except DeductionFailed:
        #             continue
        #         try:
        #             e1 = Impl(h_t.t1, self).deduce(env, hypothesis, visit)
        #         except DeductionFailed:
        #             continue
        #         assert isinstance(e0, TypedFuncDef)
        #         assert isinstance(e1, TypedFuncDef)
        #         del env[end_pos:]
        #         if visit[self] > end_pos:
        #             visit[self] = end_pos
        #         hypothesis[self] = v = TypedCaseOf(h, TypedInl(h_t, e0.var), e0.body, TypedInr(h_t, e1.var), e1.body)
        #         return v
        #     elif isinstance(h_t, And):
        #         if h_t.t0 not in hypothesis:
        #             hypothesis[h_t.t0] = v = TypedFirst(h)
        #             env.append(v)
        #         if h_t.t1 not in hypothesis:
        #             hypothesis[h_t.t1] = v = TypedSecond(h)
        #             env.append(v)
        #     elif isinstance(h_t, Impl):
        #         if h_t.t1 not in hypothesis:
        #             try:
        #                 e = h_t.t0.deduce(env, hypothesis, visit)
        #             except DeductionFailed:
        #                 continue
        #             hypothesis[h_t.t1] = v = TypedApply(h, e)
        #             env.append(v)
        #     elif isinstance(h_t, IndividualType):
        #         env.append(TypedInl(self, self.t0.deduce(env,hypothesis, visit)))
        #         env.append(TypedInr(self, self.t1.deduce(env,hypothesis, visit)))
        #
        # del env[end_pos:]
        # if visit[self] > end_pos:
        #     visit[self] = end_pos
        # raise DeductionFailed

    # def deduce(self, env: List['typed_lambda.Var']) -> 'typed_lambda.LambdaTerm':
    #     return typed_lambda.Union(self.t0.deduce(env), self.t1.deduce(env))


class Impl(BinaryTypeTerm):
    precedence = 1
    associativity = Associativity.RIGHT
    middle = "->"
    middle_latex = r"\rightarrow"

    def deduce(self, env: List['ITypedLambda'], hypothesis: Dict['IType', 'ITypedLambda'],
               visit: Dict['IType', int]) -> 'Union[ITypedLambda, TypedFuncDef]':
        if __my_debug__:
            print(f'Impl.deduce(self={self}, hypothesis={hypothesis}, visit={visit}, env={env})')
        assert len(env) < 30
        if self in hypothesis:
            return hypothesis[self]

        if isinstance(self.t0, (IndividualType, Impl, ForAllType)):
            var = TypedVariable(self.t0)
            env.append(var)
            if self.t0 not in hypothesis:
                if __my_debug__:
                    print(f'in Impl.deduce(self={self}), added {self.t0} to hypotheses.')
                hypothesis[self.t0] = var
                assert len(hypothesis) >= 1
                visit.clear()

            try:
                b = self.t1.deduce(env, hypothesis, visit)
                # be careful of exceptions!
                if __my_debug__:
                    print(f'in Impl.deduce(self={self}), after deducing funtion body, hypothesis={hypothesis}')
                hypothesis[self] = f = TypedFuncDef(var, b)
                visit.clear()
            finally:
                assert env[-1] is var
                del env[-1]
                # for k in visit:
                #     assert visit[k] <= len(env)
                tmp = [k for k, v in hypothesis.items() if var in v.free_variables]
                for k in tmp:
                    del hypothesis[k]
            return f

        elif isinstance(self.t0, And):
            var = TypedVariable(self.t0)
            fst = TypedFirst(var)
            snd = TypedSecond(var)
            env.append(fst)
            env.append(snd)
            hypothesis.setdefault(self.t0.t0, fst)
            hypothesis.setdefault(self.t0.t1, snd)
            try:
                b = self.t1.deduce(env, hypothesis, visit)
                hypothesis[self] = f = TypedFuncDef(var, b)
                visit.clear()
            finally:
                assert fst is env[-2]
                assert snd is env[-1]
                del env[-2:]
                tmp = [k for k, v in hypothesis.items() if var in v.free_variables]
                # for k in visit:
                #     assert visit[k] <= len(env)
                for k in tmp:
                    del hypothesis[k]
            return f

        elif isinstance(self.t0, Or):
            e0, e1 = self.t0.destruct(self.t1, env, hypothesis, visit)
            var = TypedVariable(self.t0)
            case_of = TypedCaseOf(var,
                                  TypedInl(self.t0, e0.var), e0.body,
                                  TypedInr(self.t0, e1.var), e1.body)
            hypothesis[self] = f = TypedFuncDef(var, case_of)
            visit.clear()
            return f
        elif isinstance(self.t0, ForAllType):
            raise NotImplementedError
        elif isinstance(self.t0, ExistsType):
            raise NotImplementedError
        elif isinstance(self.t0, PredicateApply):
            raise NotImplementedError
        else:
            raise NotImplementedError

    # def is_possible_return_type(self, t: 'IType'):
    #     if t == self.t1:
    #         return True
    #     if not isinstance(self.t1, (Impl, ForAllType, ExistsType)):
    #         return False
    #     else:
    #         return self.t1.is_possible_return_type(t)


BinaryTypeTerm.op_table = {cls.middle: cls for cls in BinaryTypeTerm.__subclasses__()}


# class RuntimeInfix(BinaryTypeTerm):
#     BinaryTypeTerm.op_table.update({})

class Not(Impl):
    precedence = 4

    def __init__(self, t0: IType):
        super(Not, self).__init__(t0, Falsum())
        self.hash_v = hash((self.__class__, self.t0))

    def __eq__(self, other: 'IType'):
        assert isinstance(other, IType)
        if isinstance(other, Impl):
            return self.t0 == other.t0 and self.t1 == other.t1
        return False

    def __hash__(self):
        return self.hash_v

    def __str__(self):
        s0 = str(self.t0)

        if not isinstance(self.t0, (IndividualType, Not, Falsum)):
            s0 = f'({s0})'
        return r'~{}'.format(s0)

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        t0 = self.t0.de_bruijn_index(bound_vars)
        if not isinstance(self.t0, (IndividualType, Not, Falsum)):
            t0 = f'({t0})'
        return r'~{}'.format(t0)

    def deduce(self, env: List['ITypedLambda'], hypothesis: Dict['IType', 'ITypedLambda'],
               visit: Dict['IType', int]) -> 'ITypedLambda':
        return Impl.deduce(self, env, hypothesis, visit)

    def latex_form(self) -> str:
        s = self.t0.latex_form()
        if not isinstance(self.t0, (IndividualType, Not, Falsum)):
            s = r'\left( {} \right)'.format(s)
        return r'\neg {}'.format(s)


class Falsum(IndividualType, IType):
    def __new__(cls, *args, **kwargs):
        return str.__new__(cls, '⊥')

    def __eq__(self, other: 'IType'):
        return isinstance(other, Falsum)

    def __hash__(self):
        return str.__hash__(self)

    def latex_form(self) -> str:
        return r'\bot'

    # def deduce(self, env: List['ITypedLambda']) -> 'ITypedLambda':
    #     print(f'env={env}')
    #     raise NotImplementedError


class ITypedLambda(lc_interface.ILambdaTerm):

    @property
    @abstractmethod
    def free_variables(self) -> 'FrozenSet[TypedVariable]':
        ...

    @abstractmethod
    def __eq__(self, other: 'ITypedLambda') -> bool:
        """alpha equivalence"""
        ...

    SelfITyped = TypeVar('SelfITyped', bound='ITypedLambda')

    @abstractmethod
    def beta_reduce_impl(self, lazy_substitute: bool) -> 'ITypedLambda':
        """leftmost and out-most"""
        raise NotImplementedError

    @abstractmethod
    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        ...

    @abstractmethod
    def get_type(self) -> IType:
        """
        This method gets the ``IType`` bound to certain term.

        :exception TypeError: when type is yet incomplete.
        """
        ...

    def _repr_latex_(self) -> str:
        if self.free_variables:
            fv = r'\{' + ', '.join(map(lambda x: x.latex_form(), self.free_variables)) + r'\}'
        else:
            fv = ''
        res = '\n$' + fv + r'\vdash ' + self.latex_form() + r'\\ : ' + self.get_type().latex_form() + '$\n'
        # return res
        return res.replace(r'\left(', '(').replace(r'\right)', ')').replace(r'\left[', '[').replace(r'\right]', ']')

    @abstractmethod
    def latex_form(self) -> str:
        ...

    def substitute(self: SelfITyped, x: 'TypedVariable', p: 'ITypedLambda') -> 'Union[SelfITyped, TypedSubstitute]':
        """
        Replace variable `x` appearing freely in ``self`` with term `p`.
        """
        assert isinstance(x, TypedVariable)
        if x in self.free_variables:
            return TypedSubstitute(self, x, p)
        return self

    @abstractmethod
    def type_infer(self, t: 'IType'):
        ...

    @abstractmethod
    def type_check(self, t: 'IType'):
        ...

    assert sys.version_info >= (3, 7)

    def where(self: SelfITyped, **kwargs: 'Tuple[IType, ITypedLambda]') -> 'Union[SelfITyped,ITypedLambda]':
        """require >=Python 3.7, for dict to preserve keyword order."""
        if kwargs:
            res = self
            for k, v in ((TypedVariable(_v[0], _k), _v[1]) for _k, _v in kwargs.items()):
                if k in self.free_variables:
                    res = TypedSubstitute(res, k, v)
                else:
                    raise KeyError(f'{k.name} is not a free variable. Check your spelling. ')
            return res
        return self


class TypedVariable(ITypedLambda):
    counter = 0

    def __init__(self, var_t: Optional['IType'] = None, name: Optional[str] = None):
        assert name is None or isinstance(name, str)
        if name is None:
            self.__name = TypedVariable.new_name()
        else:
            self.__name = name
        self.__type = var_t
        self.hash_v = (self.__name, self.__type).__hash__()
        self.__free_variables = frozenset((self,))

    @property
    def free_variables(self) -> 'FrozenSet[TypedVariable]':
        return self.__free_variables

    @property
    def has_substitution(self) -> bool:
        return False

    @property
    def name(self):
        return self.__name

    def __eq__(self, other: ITypedLambda):
        """alpha equivalence"""
        assert isinstance(other, ITypedLambda)
        if isinstance(other, TypedVariable):
            if other.__name == self.__name and other.__type == self.__type:
                return True
        return False

    def __hash__(self):
        return self.hash_v

    def __repr__(self):
        return f'<var {repr(self.__name)}:{self.__type}/>'

    def __str__(self):
        res = self.__name
        if res.startswith('%'):
            return res.replace('%', 't_')
        return res

    def beta_reduce_impl(self, lazy_substitute: bool):
        return self

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        for i in reversed(range(len(bound_vars))):
            if bound_vars[i] == self:
                return len(bound_vars) - i
        return self.__str__()

    def get_type(self) -> IType:
        if self.__type is None:
            raise TypeError(f'variable {self.name} used with incomplete type')
        return self.__type

    def latex_form(self) -> str:
        res = self.__name
        if '_' in res:
            res = res.replace('_', r'\_')
        if res.startswith('%'):
            return res.replace('%', 't_{') + '}'
        assert self.__type is not None
        return res

    @classmethod
    def new_name(cls):
        res = f'%{cls.counter}'
        cls.counter += 1
        return res

    def set_type(self, var_t: 'IType'):
        assert isinstance(var_t, IType)
        assert self.__type is None
        self.__type = var_t


class TypedFuncDef(ITypedLambda):
    def __init__(self, variable: TypedVariable, body: ITypedLambda):
        assert isinstance(variable, TypedVariable)
        assert isinstance(body, (ITypedLambda, IType))
        self.var = variable
        self.body = body
        self._type = Impl(self.var.get_type(), self.body.get_type())
        self._free_variables: Optional[FrozenSet[TypedVariable]] = None
        self._hash_v: Optional[int] = None
        self._has_substitution = body.has_substitution
        # self._has_substitution = False
        # self._de_bruijn_index: Optional[str] = None

    @property
    def free_variables(self) -> FrozenSet[TypedVariable]:
        if self._free_variables is None:
            self._free_variables = self.body.free_variables.difference([self.var])
        return self._free_variables

    @property
    def has_substitution(self) -> bool:
        return self._has_substitution

    def __eq__(self, other: ITypedLambda):
        assert isinstance(other, ITypedLambda)
        if isinstance(other, TypedFuncDef):
            return self.__hash__() == other.__hash__() and \
                   self.get_type() == other.get_type() and \
                   self.body.de_bruijn_index([self.var]) == other.body.de_bruijn_index([other.var])
        else:
            return False

    def __hash__(self):
        if self._hash_v is None:
            self._hash_v = hash(self.de_bruijn_index([]))
        return self._hash_v

    def __repr__(self):
        return f'(λ{repr(self.var)}.{repr(self.body)})'

    def __str__(self):
        return f'λ{self.var}:{self.var.get_type()}.{self.body}'

    # @lru_cache(maxsize=2)
    def beta_reduce_impl(self, lazy_substitute: bool) -> 'TypedFuncDef':
        m = self.body.beta_reduce_impl(lazy_substitute)
        if not lazy_substitute:
            assert not m.has_substitution
        if m is self.body:
            return self
        return self.__class__(self.var, m)

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        # if not self.free_variables and self._de_bruijn_index is not None:
        #     return self._de_bruijn_index
        bound_vars.append(self.var)
        res = 'λ{}: {}'.format(self.var.get_type(), self.body.de_bruijn_index(bound_vars))
        del bound_vars[-1]
        return res

    def get_type(self) -> IType:
        if self._type is None:
            raise TypeError('Incomplete type FuncDef.')
        return self._type

    def latex_form(self) -> str:
        return r'\lambda {}:{}.{}'.format(self.var.latex_form(),
                                          self.var.get_type().latex_form(),
                                          self.body.latex_form())


class ForAllType(TypedFuncDef, IType):

    def deduce(self, env: List['ITypedLambda'], hypothesis: Dict['IType', 'ITypedLambda'],
               visit: Dict['IType', int]) -> 'ITypedLambda':
        hypothesis.setdefault()

    def __eq__(self, other: IType):
        assert isinstance(other, IType)
        if isinstance(other, ForAllType):
            return TypedFuncDef.__eq__(self, other)
        return False

    __hash__ = TypedFuncDef.__hash__

    def __str__(self):
        return f'∀{self.var}:{self.var.get_type()}.{self.body}'

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        bound_vars.append(self.var)
        res = '∀{}: {}'.format(self.var.get_type(), self.body.de_bruijn_index(bound_vars))
        del bound_vars[-1]
        return res

    def latex_form(self) -> str:
        return r'\forall {}:{}.{}'.format(self.var.latex_form(),
                                          self.var.get_type().latex_form(),
                                          self.body.latex_form())


class ExistsType(TypedFuncDef, IType):

    def deduce(self, env: List['ITypedLambda'], hypothesis: Dict['IType', 'ITypedLambda'],
               visit: Dict['IType', int]) -> 'ITypedLambda':
        raise NotImplementedError

    def __eq__(self, other: 'IType'):
        assert isinstance(other, IType)
        if isinstance(other, ExistsType):
            return TypedFuncDef.__eq__(self, other)
        return False

    __hash__ = TypedFuncDef.__hash__

    def __str__(self):
        return f'∃{self.var}:{self.var.get_type()}.{self.body}'

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        bound_vars.append(self.var)
        res = '∃{}: {}'.format(self.var.get_type(), self.body.de_bruijn_index(bound_vars))
        del bound_vars[-1]
        return res

    def latex_form(self) -> str:
        return r'\exists {}:{}.{}'.format(self.var.latex_form(), self.var.get_type().latex_form(),
                                          self.body.latex_form())


class TypedApply(ITypedLambda):

    def __init__(self, m: 'ITypedLambda', n: 'ITypedLambda'):
        assert isinstance(m, ITypedLambda)
        assert isinstance(n, ITypedLambda)
        m_t = m.get_type()
        assert isinstance(m_t, Impl), f'{m} expected to have type like *->*, got {m_t}.'
        assert m_t.t0 == n.get_type(), f'unmatched argument type of {m}:{m_t} to {n}:(type {n.get_type()}).'

        self.m = m
        self.n = n
        self._type = m_t.t1
        self._free_variables: Optional[FrozenSet[TypedVariable]] = None
        self._has_substitution = m.has_substitution or n.has_substitution
        self._hash_v: Optional[int] = None

    @property
    def free_variables(self) -> FrozenSet[TypedVariable]:
        if self._free_variables is None:
            assert compatible(self.m.free_variables, self.n.free_variables)
            self._free_variables = self.m.free_variables | self.n.free_variables
        return self._free_variables

    @property
    def has_substitution(self) -> bool:
        return self._has_substitution

    def __eq__(self, other: ITypedLambda):
        assert isinstance(other, ITypedLambda)
        if isinstance(other, TypedApply):
            return self.de_bruijn_index([]) == other.de_bruijn_index([])
        else:
            return False

    def __hash__(self):
        if self._hash_v is None:
            self._hash_v = hash(self.de_bruijn_index([]))
        return self._hash_v

    def __repr__(self):
        return f'({repr(self.m)} {repr(self.n)})'

    def __str__(self):
        m = str(self.m)
        n = str(self.n)
        return self._print_format().format(m, n)

    def _print_format(self):
        m = '{}'
        n = '{}'
        if isinstance(self.m, (TypedFuncDef, TypedSubstitute)):
            m = '({})'
        if isinstance(self.n, (TypedApply, TypedFuncDef)):
            n = '({})'
        return f'{m} {n}'

    def beta_reduce_impl(self, lazy_substitute: bool) -> 'Union[TypedApply, TypedSubstitute]':
        if lazy_substitute:
            m, n = self.m, self.n
            if m.has_substitution or n.has_substitution:
                if m.has_substitution:
                    m = m.beta_reduce_impl(lazy_substitute)
                    assert self is not m
                if n.has_substitution:
                    n = n.beta_reduce_impl(lazy_substitute)
                    assert self is not n
                return TypedApply(m, n)
            else:
                if isinstance(m, TypedFuncDef):
                    return m.body.substitute(m.var, n)
                m = m.beta_reduce_impl(lazy_substitute)
                if m is self.m:
                    n = n.beta_reduce_impl(lazy_substitute)
                    if n is self.n:
                        return self
                    else:
                        return TypedApply(m, n)
                else:
                    return TypedApply(m, n)
        else:
            tmp = self.beta_reduce_impl(lazy_substitute=True)
            while tmp.has_substitution:
                tmp = tmp.beta_reduce_impl(lazy_substitute=True)
            return tmp

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        m = self.m.de_bruijn_index(bound_vars)
        n = self.n.de_bruijn_index(bound_vars)
        return self._print_format().format(m, n)

    def get_type(self) -> IType:
        return self._type

    def latex_form(self) -> str:
        m = self.m.latex_form()
        n = self.n.latex_form()
        if isinstance(self.m, (TypedFuncDef, TypedSubstitute)):
            m = f'\\left({m}\\right)'
        if isinstance(self.n, (TypedApply, TypedFuncDef)):
            n = f'\\left({n}\\right)'
        return f'{m}\\ {n}'


class PredicateApply(TypedApply, IType):

    def deduce(self, env: List['ITypedLambda'], hypothesis: Dict['IType', 'ITypedLambda'],
               visit: Dict['IType', int]) -> 'ITypedLambda':
        raise NotImplementedError

    def __eq__(self, other: IType):
        assert isinstance(other, IType)
        assert isinstance(other, IType)
        if isinstance(other, PredicateApply):
            return TypedApply.__eq__(self, other)
        return False

    def __hash__(self):
        return TypedApply.__hash__(self)

    def latex_form(self) -> str:
        return TypedApply.latex_form(self)


class TypedSubstitute(ITypedLambda):

    def __init__(self, term: ITypedLambda, var: TypedVariable, to: ITypedLambda):
        assert isinstance(term, ITypedLambda)
        assert isinstance(var, TypedVariable)
        assert isinstance(to, ITypedLambda)
        assert not isinstance(to, TypedSubstitute)
        assert var.get_type() == to.get_type()
        self.term = term
        self.var = var
        self.to = to
        self.__hash_v: Optional[int] = None
        self.__type = term.get_type()

    @property
    def has_substitution(self) -> bool:
        return True

    @property
    def free_variables(self) -> 'FrozenSet[TypedVariable]':
        n, x = self.to, self.var
        if isinstance(self.term, (TypedApply, TypedPair, TypedFirst, TypedSecond, TypedInl, TypedInr)):
            if x in self.term.free_variables:
                return n.free_variables | self.term.free_variables.difference([x])
            else:
                return self.term.free_variables
        elif isinstance(self.term, TypedFuncDef):
            if self.term.var == x:
                return self.term.free_variables
            else:
                y, m = self.term.var, self.term.body
                # [N/x] (λy.M) = λy.[N/x]M (x!=y&&yがNに自由に出現しない場合)
                return n.free_variables | m.free_variables.difference([x, y])
        elif isinstance(self.term, TypedCaseOf):
            raise NotImplementedError
        elif isinstance(self.term, TypedVariable):
            if self.term == x:
                return n.free_variables
            else:
                return self.term.free_variables
        else:
            assert isinstance(self.term, TypedSubstitute)
            return n.free_variables | self.term.free_variables.difference([x])

    def __eq__(self, other: 'ITypedLambda'):
        assert isinstance(other, ITypedLambda)
        if isinstance(other, TypedSubstitute):
            return self.__hash__() == other.__hash__() and \
                   self.de_bruijn_index([]) == other.de_bruijn_index([])
        return False

    def __hash__(self):
        if self.__hash_v is None:
            self.__hash_v = hash(self.de_bruijn_index([]))
        return self.__hash_v

    def __str__(self):
        to = self.to.__str__()
        var = self.var.__str__()
        term = self.term.__str__()
        return self._print_format().format(to, var, term)

    def _print_format(self) -> str:
        if isinstance(self.term, (TypedApply, TypedFuncDef)):
            return '[{}/{}]({})'
        elif isinstance(self.term, (TypedVariable, TypedConstant)):
            return '([{}/{}]{})'
        return '[{}/{}]{}'

    def beta_reduce_impl(self, lazy_substitute: bool) -> 'ITypedLambda':
        if lazy_substitute:
            n, x = self.to, self.var
            if self.term.has_substitution:
                return TypedSubstitute(self.term.beta_reduce_impl(lazy_substitute), self.var, self.to)
            if isinstance(self.term, TypedApply):
                m1, m2 = self.term.m, self.term.n
                return TypedApply(m1.substitute(x, n), m2.substitute(x, n))
            elif isinstance(self.term, TypedFuncDef):
                if self.term.var == x:
                    return self.term
                else:
                    y, m = self.term.var, self.term.body
                    if y in n.free_variables:
                        z = TypedVariable(y.get_type())
                        return TypedFuncDef(z, m.substitute(y, z).substitute(x, n))
                    else:
                        return TypedFuncDef(y, m.substitute(x, n))
            elif isinstance(self.term, TypedVariable):
                assert self.term.get_type() == x.get_type()
                if self.term == x:
                    return n
                else:
                    return self.term
            else:
                assert isinstance(self.term, TypedSubstitute)
                return self.term.beta_reduce_impl(lazy_substitute).substitute(self.var, self.to)
        else:
            tmp = self.beta_reduce_impl(lazy_substitute=True)
            while tmp.has_substitution:
                tmp = tmp.beta_reduce_impl(lazy_substitute=True)
            return tmp

    def de_bruijn_index(self, bound_vars: List['TypedVariable']):
        to = self.to.de_bruijn_index(bound_vars)
        var = '1'
        bound_vars.append(self.var)
        term = self.term.de_bruijn_index(bound_vars)
        del bound_vars[-1]
        return self._print_format().format(to, var, term)

    def get_type(self) -> IType:
        return self.__type

    def latex_form(self) -> str:
        to = self.to.latex_form()
        var = self.var.latex_form()
        term = self.term.latex_form()
        if isinstance(self.term, (TypedApply, TypedFuncDef)):
            return r'\left[ {} / {} \right] \left( {} \right)'.format(to, var, term)
        elif isinstance(self.term, (TypedVariable, TypedConstant)):
            return r'\left( \left[ {} / {} \right ] {} \right)'.format(to, var, term)
        return r'\left[ {} / {} \right] {}'.format(to, var, term)


class TypedPair(ITypedLambda):

    def __init__(self, first: ITypedLambda, second: ITypedLambda):
        assert isinstance(first, ITypedLambda)
        assert isinstance(second, ITypedLambda)
        self.first = first
        self.second = second
        self.__type = And(first.get_type(), second.get_type())
        self.__free_variables: Optional[FrozenSet[TypedVariable]] = None
        self.__has_substitution = self.first.has_substitution or self.second.has_substitution

    @property
    def free_variables(self) -> FrozenSet[TypedVariable]:
        if self.__free_variables is None:
            assert compatible(self.first.free_variables, self.second.free_variables)
            self.__free_variables = self.first.free_variables | self.second.free_variables
        return self.__free_variables

    @property
    def has_substitution(self) -> bool:
        return self.__has_substitution

    def __eq__(self, other: 'ITypedLambda') -> bool:
        assert isinstance(other, ITypedLambda)
        if isinstance(other, TypedPair):
            return self.__hash__() == other.__hash__() and self.first == other.first and self.second == other.second
        else:
            return False

    def __str__(self):
        return TypedPair._print_format().format(self.first, self.second)

    __repr__ = __str__

    @staticmethod
    def _print_format():
        m = '{}'
        n = '{}'
        return f'({m}, {n})'

    def beta_reduce_impl(self, lazy_substitute: bool) -> 'TypedPair':
        if lazy_substitute:
            m = self.first
            n = self.second
            if m.has_substitution or n.has_substitution:
                if m.has_substitution:
                    m = m.beta_reduce_impl(lazy_substitute)
                    assert self is not m
                if n.has_substitution:
                    n = n.beta_reduce_impl(lazy_substitute)
                    assert self is not n
                return TypedPair(m, n)
            else:
                m = m.beta_reduce_impl(lazy_substitute)
                if m is self.first:
                    n = n.beta_reduce_impl(lazy_substitute)
                    if n is self.second:
                        return self
                    else:
                        return TypedPair(m, n)
                else:
                    return TypedPair(m, n)
        else:
            tmp = self.beta_reduce_impl(lazy_substitute=True)
            while tmp.has_substitution:
                tmp = tmp.beta_reduce_impl(lazy_substitute=True)
            return tmp

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        m = self.first.de_bruijn_index(bound_vars)
        n = self.second.de_bruijn_index(bound_vars)
        return self._print_format().format(m, n)

    def get_type(self) -> And:
        return self.__type

    def latex_form(self) -> str:
        return r'\left( {}, {} \right)'.format(self.first.latex_form(), self.second.latex_form())


class TypedFirst(ITypedLambda):
    def __init__(self, p: ITypedLambda):
        assert isinstance(p, ITypedLambda)
        t = p.get_type()
        assert isinstance(t, And)
        if isinstance(p, TypedPair):
            self.obj: Optional[ITypedLambda] = p.first
        else:
            self.obj: Optional[ITypedLambda] = None
        self.p = p
        self.__type = t.t0
        # self.__hash_v = hash((0, self.p))

    @property
    def free_variables(self) -> 'FrozenSet[TypedVariable]':
        return self.p.free_variables

    @property
    def has_substitution(self) -> bool:
        return self.p.has_substitution

    def __eq__(self, other: ITypedLambda):
        assert isinstance(other, ITypedLambda)
        raise NotImplementedError
        if self.__type == other.get_type():
            if isinstance(other, TypedFirst):
                if self.obj is None and other.obj is None:
                    return
        return False
        return self.obj == other

    def __str__(self):
        return TypedFirst._print_format().format(self.p)

    def __repr__(self):
        return f'<fst p:{self.p.get_type()}={self.p}/>'

    @staticmethod
    def _print_format():
        return 'fst({})'

    def beta_reduce_impl(self, lazy_substitute: bool) -> 'ITypedLambda':
        raise NotImplementedError
        if lazy_substitute:
            if self.p.has_substitution:
                return TypedFirst(self.p.beta_reduce_impl(lazy_substitute))

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        p = self.p.de_bruijn_index(bound_vars)
        return self._print_format().format(p)

    def get_type(self) -> IType:
        return self.__type

    def latex_form(self) -> str:
        return r'\mathrm{{fst}} \left( {} \right) '.format(self.p.latex_form())


class TypedSecond(ITypedLambda):
    def __init__(self, p: ITypedLambda):
        assert isinstance(p, ITypedLambda)
        t = p.get_type()
        assert isinstance(t, And)
        if isinstance(p, TypedPair):
            self.obj: Optional[ITypedLambda] = p.second
        else:
            self.obj: Optional[ITypedLambda] = None
        self.p = p
        self.__type = t.t1

    @property
    def free_variables(self) -> 'FrozenSet[TypedVariable]':
        return self.p.free_variables

    @property
    def has_substitution(self) -> bool:
        return self.p.has_substitution

    def __eq__(self, other: ITypedLambda):
        raise NotImplementedError
        return self.obj == other

    def __str__(self):
        return TypedSecond._print_format().format(self.p)

    def __repr__(self):
        return f'<snd p:{self.p.get_type()}={self.p}/>'

    @staticmethod
    def _print_format():
        return 'snd({})'

    def beta_reduce_impl(self, lazy_substitute: bool) -> 'ITypedLambda':
        raise NotImplementedError
        if lazy_substitute:
            if self.p.has_substitution:
                return TypedSecond(self.p.beta_reduce_impl(lazy_substitute))

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        p = self.p.de_bruijn_index(bound_vars)
        return self._print_format().format(p)

    def get_type(self) -> IType:
        return self.__type

    def latex_form(self) -> str:
        return r'\mathrm{{snd}} \left( {} \right) '.format(self.p.latex_form())


class TypedCaseOf(ITypedLambda):

    def __init__(self, e: ITypedLambda,
                 inl: Union['TypedInl', 'TypedInr'], e_l: ITypedLambda,
                 inr: Union['TypedInl', 'TypedInr'], e_r: ITypedLambda):
        assert isinstance(e, ITypedLambda)
        assert isinstance(e.get_type(), Or)
        assert isinstance(inl, (TypedInl, TypedInr))
        assert isinstance(inr, (TypedInl, TypedInr))
        assert isinstance(inl.obj, TypedVariable)
        assert isinstance(inr.obj, TypedVariable)
        assert isinstance(e_l, ITypedLambda)
        assert isinstance(e_r, ITypedLambda)
        self.e = e
        self.inl = inl
        self.inr = inr
        self.e_l = e_l
        self.e_r = e_r
        t1, t2 = e_l.get_type(), e_r.get_type()
        assert t1 == t2
        self.__free_variables: Optional[FrozenSet[TypedVariable]] = None
        self.__has_substitution = e_l.has_substitution or e_r.has_substitution
        self.__hash_v: Optional[int] = None

    @property
    def free_variables(self) -> 'FrozenSet[TypedVariable]':
        if self.__free_variables is None:
            assert compatible(self.e_l.free_variables, self.e_r.free_variables)
            self.__free_variables = (
                    self.e.free_variables | self.e_l.free_variables | self.e_r.free_variables).difference(
                self.inl.free_variables, self.inr.free_variables)
        return self.__free_variables

    @property
    def has_substitution(self) -> bool:
        return self.__has_substitution

    def __eq__(self, other: 'ITypedLambda') -> bool:
        assert isinstance(other, ITypedLambda)
        if isinstance(other, TypedCaseOf):
            return self.__hash__() == other.__hash__() and self.inl == other.inl and self.inr == other.inr
        else:
            return False

    def __str__(self):
        return 'case {} of {} => {} | {} => {}'.format(
            self.e,
            str(self.inl), self.inl.obj.get_type(), self.e_l,
            str(self.inr), self.inr.obj.get_type(), self.e_r)

    def __repr__(self):
        return str(self)

    def __hash__(self):
        if self.__hash_v is None:
            self.__hash_v = hash(self.de_bruijn_index([]))
        return self.__hash_v

    def beta_reduce_impl(self, lazy_substitute: bool) -> 'ITypedLambda':
        raise NotImplementedError

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        m = self.m.de_bruijn_index(bound_vars)
        n = self.n.de_bruijn_index(bound_vars)
        return self._print_format().format(m, n)

    def get_type(self) -> IType:
        return self.e_l.get_type()

    def latex_form(self) -> str:
        return r'\mathrm{{case}}\ {}\ \mathrm{{of}}\ {} \Rightarrow {} \mid {} \Rightarrow {} '.format(
            self.e.latex_form(), self.inl.latex_form(), self.e_l.latex_form(), self.inr.latex_form(),
            self.e_r.latex_form())


class TypedInl(ITypedLambda):

    def __init__(self, union_t: Or, obj: ITypedLambda):
        self.obj = obj
        self.__type = union_t
        assert obj.get_type() == union_t.t0

    @property
    def free_variables(self) -> 'FrozenSet[TypedVariable]':
        return self.obj.free_variables

    def __eq__(self, other: 'ITypedLambda') -> bool:
        assert isinstance(other, ITypedLambda)
        if isinstance(other, TypedInl):
            return self.__type == other.get_type() and self.obj == other.obj
        return False

    def __str__(self):
        return 'inl({})'.format(self.obj)

    def __repr__(self):
        return str(self)

    def get_type(self) -> Or:
        return self.__type

    def latex_form(self) -> str:
        return r'\mathrm{{inl}}\left( {} \right)'.format(self.obj.latex_form())


class TypedInr(ITypedLambda):
    def __init__(self, union_t: Or, obj: ITypedLambda):
        self.obj = obj
        self.__type = union_t
        assert obj.get_type() == union_t.t1

    @property
    def free_variables(self) -> 'FrozenSet[TypedVariable]':
        return self.obj.free_variables

    def __eq__(self, other: 'ITypedLambda') -> bool:
        assert isinstance(other, ITypedLambda)
        if isinstance(other, TypedInr):
            return self.__type == other.get_type() and self.obj == other.obj
        return False

    def __str__(self):
        return 'inr({})'.format(self.obj)

    def __repr__(self):
        return str(self)

    def get_type(self) -> IType:
        return self.__type

    def latex_form(self) -> str:
        return r'\mathrm{{inr}}\left( {} \right)'.format(self.obj.latex_form())


class TypedConstant(ITypedLambda, Generic[T]):
    __slots__ = 'value', 'value_t', '__hash_v'
    empty_set: 'FrozenSet[TypedVariable]' = frozenset()

    def __init__(self, value_t: IType, value: T):
        # assert value_t.latex_form() == 'int'
        self.value = value
        self.value_t = value_t
        self.__hash_v = hash((self.value_t, self.value))

    @property
    def free_variables(self) -> 'FrozenSet[TypedVariable]':
        return TypedConstant.empty_set

    @property
    def has_substitution(self) -> bool:
        return False

    def __eq__(self, other: ITypedLambda):
        assert isinstance(other, ITypedLambda)
        if isinstance(other, TypedConstant):
            if self.value_t == other.value_t and self.value == other.value:
                return True
        return False

    def __hash__(self):
        return self.__hash_v

    def __repr__(self):
        return '<{}: {}/>'.format(self.value, self.value_t)

    def __str__(self):
        return '{}^{{{}}}'.format(self.value, self.value_t)

    def beta_reduce_impl(self, lazy_substitute: bool) -> 'ITypedLambda':
        return self

    def de_bruijn_index(self, bound_vars: List['TypedVariable']) -> str:
        return f'const {str(self)}'

    def get_type(self) -> IType:
        return self.value_t

    def latex_form(self) -> str:
        return str(self)


if __name__ == '__main__':
    print(TypedVariable.__mro__)
    print({lc_interface.parse('λx.x'): Impl('A', 'B')})
