from typing import List, FrozenSet, TypeVar
from abc import ABC, abstractmethod
import sys

VarT = TypeVar('VarT')

__author__ = 'triplewhopper'
class ILambdaTerm:
    @property
    @abstractmethod
    def free_variables(self) -> FrozenSet[VarT]:
        ...

    @property
    @abstractmethod
    def has_substitution(self) -> bool:
        ...

    def _repr_latex_(self) -> str:
        if self.free_variables:
            fv = r'\{' + ', '.join(map(lambda x: x.latex_form(), self.free_variables)) + r'\}'
        else:
            fv = ''
        return '$' + fv + r'\vdash ' + self.latex_form() + '$'

    def beta_reduce(self, lazy_substitute: bool = False, max_step=1) -> 'ILambdaTerm':
        assert isinstance(lazy_substitute, bool)
        assert isinstance(max_step, int)
        assert max_step >= 1
        res = self
        for _ in range(max_step):
            lookahead = res.beta_reduce_impl(lazy_substitute)
            if lookahead is res:
                if _ <= 1:
                    print('1 step.')
                else:
                    print(f'{_} steps.')
                break
            else:
                res = lookahead
        return res

    @abstractmethod
    def beta_reduce_impl(self, lazy_substitute: bool) -> 'ILambdaTerm':
        """leftmost and out-most"""
        ...

    @abstractmethod
    def de_bruijn_index(self, bound_vars: List[VarT]) -> str:
        ...

    @abstractmethod
    def latex_form(self) -> str:
        ...

    assert sys.version_info >= (3, 7)

    def where(self, **kwargs):
        """require >=Python 3.7, for dict to preserve keyword order."""
        ...
