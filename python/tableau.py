from __future__ import annotations

from abc import abstractmethod
from dataclasses import dataclass, field
from enum import Enum
from functools import reduce
from itertools import chain, count, filterfalse, islice, product
from typing import Any, Callable, Container, Dict, FrozenSet, \
                   Iterable, Iterator, List, Optional, Tuple, Union, cast
import re

from pml import *

Signature = Dict[Symbol, int]


PatternLike = Union[Pattern, Assertion, Membership]

def free_evars(ps: Iterable[PatternLike]) -> FrozenSet[EVar]:
    ret : FrozenSet[EVar] = frozenset()
    for assertion in ps:
        ret = ret.union(assertion.free_evars())
    return ret

def restrict(ps: Iterable[PatternLike], vars : Iterable[EVar]) -> Iterable[PatternLike]:
    vars_set = set(vars)
    def free_evars_is_subset(p: PatternLike) -> bool:
        return p.free_evars() <= vars_set
    return filter(free_evars_is_subset, ps)

def restrict_a(ps: Iterable[Assertion], vars : Iterable[EVar]) -> Iterable[Assertion]:
    return cast(Iterable[Assertion], restrict(ps, vars))
def restrict_m(ps: Iterable[Membership], vars : Iterable[EVar]) -> Iterable[Membership]:
    return cast(Iterable[Membership], restrict(ps, vars))
def restrict_u(ps: Iterable[ForallAssertion], vars : Iterable[EVar]) -> Iterable[ForallAssertion]:
    return cast(Iterable[ForallAssertion], restrict(ps, vars))

DefList = List[Pattern]
def definition_list(p: Pattern, def_list: DefList) -> DefList:
    if def_list is None: def_list = []

    if isinstance(p, (SVar, EVar, Symbol, Bottom, Top)):
        return def_list
    elif isinstance(p, Not) and (isinstance(p.subpattern, (SVar, EVar, Symbol))):
        return def_list
    elif isinstance(p, (And, Or)):
        def_list = definition_list(p.left,  def_list)
        def_list = definition_list(p.right, def_list)
        return def_list
    elif isinstance(p, (App, DApp)):
        for arg in p.arguments:
            def_list = definition_list(arg,  def_list)
        return def_list
    elif isinstance(p, Mu):
        if p not in def_list:
            def_list = def_list + [p]
            def_list = definition_list(p.subpattern.substitute(p.bound, SVar(def_list.index(p)).to_positive_normal_form()), def_list)
        return def_list
    elif isinstance(p, Nu):
        return definition_list(p.negate(), def_list)
    else:
        raise RuntimeError("Unsupported pattern: " + str(p))

class Assertion:
    @abstractmethod
    def negate(self) -> 'Assertion':
        raise NotImplementedError

    @abstractmethod
    def free_evars(self) -> FrozenSet[EVar]:
        raise NotImplementedError

    @abstractmethod
    def substitute(self, x: Var, v: Pattern) -> Assertion:
        raise NotImplementedError

    def substitute_multi(self, xs: Iterable[EVar] , vs: Iterable[Pattern]) -> Assertion:
        # TODO: We do not do simultanious substitutions
        ret = self
        for (x, v) in zip(xs, vs):
            ret = ret.substitute(x, v)
        return ret

    @abstractmethod
    def to_latex(self) -> str:
        raise NotImplementedError

    @abstractmethod
    def to_utf(self) -> str:
        raise NotImplementedError

@dataclass(frozen=True)
class Matches(Assertion):
    variable: EVar
    pattern:  Pattern

    def negate(self) -> Matches:
        return Matches(self.variable, self.pattern.negate())

    def free_evars(self) -> FrozenSet[EVar]:
        return self.pattern.free_evars().union([self.variable])

    def substitute(self, x: Var, v: Pattern) -> Matches:
        assert isinstance(self.variable.substitute(x, v), EVar)
        return Matches(cast(EVar, self.variable.substitute(x, v)), self.pattern.substitute(x, v))

    def to_latex(self) -> str:
        return self.variable.to_latex() + ' \\vDash ' + self.pattern.to_latex()

    def to_utf(self) -> str:
        return self.variable.to_utf() + ' |= ' + self.pattern.to_utf()

@dataclass(frozen=True)
class AllOf(Assertion):
    assertions: FrozenSet[Assertion]

    def negate(self) -> AnyOf:
        return AnyOf(frozenset([a.negate() for a in self.assertions]))

    def free_evars(self) -> FrozenSet[EVar]:
        ret : FrozenSet[EVar] = frozenset()
        for assertion in self.assertions:
            ret = ret.union(assertion.free_evars())
        return ret

    def substitute(self, x: Var, v: Pattern) -> AllOf:
        return AllOf(frozenset([a.substitute(x, v) for a in self.assertions]))

    def to_latex(self) -> str:
        return ' \\bigwedge '.join(map(lambda a: a.to_latex(), self.assertions))

    def to_utf(self) -> str:
        return ' and '.join(map(lambda a: a.to_utf(), self.assertions))

@dataclass(frozen=True)
class AnyOf(Assertion):
    assertions: FrozenSet[Assertion]

    def negate(self) -> AllOf:
        return AllOf(frozenset([a.negate() for a in self.assertions]))

    def free_evars(self) -> FrozenSet[EVar]:
        ret : FrozenSet[EVar] = frozenset()
        for assertion in self.assertions:
            ret = ret.union(assertion.free_evars())
        return ret

    def substitute(self, x: Var, v: Pattern) -> AnyOf:
        return AnyOf(frozenset([a.substitute(x, v) for a in self.assertions]))

    def to_latex(self) -> str:
        return ' \\bigvee '.join(map(lambda a: a.to_latex(), self.assertions))

    def to_utf(self) -> str:
        return ' or '.join(map(lambda a: a.to_utf(), self.assertions))

@dataclass(frozen=True)
class ExistsAssertion(Assertion):
    bound: frozenset[EVar]
    subassertion: Assertion

    def negate(self) -> 'ForallAssertion':
        return ForallAssertion(self.bound, self.subassertion.negate())

    def free_evars(self) -> FrozenSet[EVar]:
        return self.subassertion.free_evars() - self.bound

    def substitute(self, x: Var, v: Pattern) -> ExistsAssertion:
        if x in self.bound: return self
        else:               return ExistsAssertion(self.bound, self.subassertion.substitute(x, v))

    def to_latex(self) -> str:
        return '\\exists ' + ','.join(map(lambda p: p.to_latex(), self.bound)) + \
                    ' \\ldotp ' + self.subassertion.to_latex()

    def to_utf(self) -> str:
        return '∃ ' + ','.join(map(lambda p: p.to_utf(), self.bound)) + \
                    ' . (' + self.subassertion.to_utf() + ')'

@dataclass(frozen=True)
class ForallAssertion(Assertion):
    bound: frozenset[EVar]
    subassertion: Assertion

    def negate(self) -> ExistsAssertion:
        return ExistsAssertion(self.bound, self.subassertion.negate())

    def free_evars(self) -> FrozenSet[EVar]:
        return self.subassertion.free_evars() - self.bound

    def substitute(self, x: Var, v: Pattern) -> ForallAssertion:
        if x in self.bound: return self
        else:               return ForallAssertion(self.bound, self.subassertion.substitute(x, v))

    def to_latex(self) -> str:
        return '\\forall ' + ','.join(map(lambda p: p.to_latex(), self.bound)) + \
                    ' \\ldotp ' + self.subassertion.to_latex()

    def to_utf(self) -> str:
        return '∀ ' + ','.join(map(lambda p: p.to_utf(), self.bound)) + \
                    ' . ' + self.subassertion.to_utf()


def is_existential(alpha: Assertion) -> bool:
    if not isinstance(alpha, Matches): return False
    return isinstance(alpha.pattern, (App, Exists))

@dataclass(frozen=False, unsafe_hash=True)
class Membership:
    """ Represents the membership of a tuple of constants in a symbols interpretation.

        This is NOT a frozen class to allow for postponing the resolution step as far as
        possible.
    """

    symbol:   Symbol
    elements: Tuple[EVar,...]
    class Status(Enum):
        Undecided   = 0
        Holds       = 1
        DoesNotHold = 2
    status: Status = field(compare=False)

    owning_sequent: Optional['Sequent']

    def free_evars(self) -> FrozenSet[EVar]:
        return frozenset(self.elements)

Sequent = Union['BasicSequent', 'UnsatSequent', 'ChooseExistentialSequent']
class Sat:
    pass


class BasicSequent:
    gamma          : List[Assertion]
    basics         : List[Membership]
    universals     : List[ForallAssertion]

    children       : List[Sequent] = []
    pg_children     : Dict[Assertion, List['GameNode']] = {}

    def __init__(self, gamma:List[Assertion], basics:List[Membership], universals:List[ForallAssertion]) -> None:
        self.gamma      = gamma
        self.basics     = basics
        self.universals = universals

    def get_children(self) -> List['Sequent']:
        return self.children

    def extend_memberships(self, signature : Signature, vars : List[EVar]) -> None:
        C = free_evars(self.gamma).union(vars)
        for (symbol, arity) in signature.items():
            # TODO: only consider tuples that include something from vars
            for tuple in product(C, repeat = arity + 1):
                self.basics += [ Membership( symbol = symbol
                                           , elements = tuple
                                           , status = Membership.Status.Undecided
                                           , owning_sequent = self
                                           ) ]

    def build_children(self, K : List[EVar]) -> Tuple[Optional[Membership], List[Sequent]]:
        """ Returns a membership that needs to be resolved on in order to continue,
            and the list on incomplete nodes.
        """
        non_existential = list(filterfalse(is_existential, self.gamma))
        if non_existential:
            alpha, *_ = self.gamma
            return self.apply_nonexistential_rule()
        return self.apply_choose_existentials()

    def apply_nonexistential_rule(self) -> Tuple[Optional[Membership], List[Sequent]]:
        assertion, *rest = self.gamma
        child : Sequent
        if isinstance(assertion, Matches):
            p = assertion.pattern
            if isinstance(p, (Bottom)):
                child = UnsatSequent()
                self.children = [ ]
                for g in self.gamma:
                    self.pg_children[g] = [UnsatGameNode()]
                return (None, self.children)
            elif isinstance(p, (Top)):
                child = BasicSequent(gamma = rest, basics = self.basics, universals = self.universals)
                self.children = [child]
                self.pg_children[assertion] = [BasicGameNode(assertion, self)]
                for assertion in rest:
                    self.pg_children[assertion] = [BasicGameNode(assertion, child)]
                return (None, self.children)
            assert False
        return (None, [])

    def apply_choose_existentials(self) -> Tuple[Optional[Membership], List[Sequent]]:
        for existential in self.gamma:
            child = ChooseExistentialSequent(existential, self)
            self.children += [ child ]
            for assertion in self.gamma:
                if assertion == existential: continue
                self.pg_children[assertion] = [ChooseExistentialGameNode(assertion, child)]
            return (None, self.children)
        return (None, self.children)

    def free_evars(self) -> FrozenSet[EVar]:
        ret : FrozenSet[EVar] = frozenset()
        # No need to check other assertions since basics should contain all memberships
        for membership in self.basics:
            ret = ret.union(membership.free_evars())
        return ret

@dataclass(frozen=True)
class UnsatSequent:
    def build_children(self, K : List[EVar]) -> Tuple[Optional[Membership], List[Sequent]]:
        return (None, [])

    def get_children(self) -> List['Sequent']:
        return [self]

@dataclass(frozen=False)
class ChooseExistentialSequent:
    alpha    : Assertion
    parent   : BasicSequent
    children : List[BasicSequent] = []

    def build_children(self, K : List[EVar]) -> Tuple[Optional[Membership], List[Sequent]]:
        assert isinstance(self.alpha, Matches)
        assert isinstance(self.alpha.pattern, (App, Exists))

        for inst in self.instantiations(K):
            self.children += [BasicSequent( gamma       = list(restrict_a(self.parent.gamma, inst.free_evars()))
                                          , basics      = list(restrict_m(self.parent.basics, inst.free_evars()))
                                          , universals  = list(restrict_u(self.parent.universals, inst.free_evars()))
                                          )]
        return (None, cast(List[Sequent], self.children))

    def instantiations(self, K : List[EVar]) -> List[Assertion]:
        assert isinstance(self.alpha, Matches)
        assert isinstance(self.alpha.pattern, (App, Exists))

        if isinstance(self.alpha.pattern, App):
            instantiations(len(self.alpha.pattern.arguments), self.alpha.free_evars(), self.parent.free_evars(), K)

    def get_children(self) -> List['Sequent']:
        assert False

@dataclass(frozen=True)
class BasicGameNode:
    assertion:  Assertion
    sequent:    BasicSequent

    def priority(self, def_list: DefList) -> int: 
        if isinstance(self.assertion, Matches):
            p = self.assertion.pattern
            if isinstance(p, Top):
                return 0 # Tops only child is Top, so this can be any even value`
            if isinstance(p, (Bottom, EVar)) \
               or (isinstance(p, Not) and isinstance(p.subpattern, EVar)):
                return 0 # Cannot repeat infinitly on any trace, so value doesn't matter.
            if isinstance(p, (And, Or, SVar)) \
               or (isinstance(p, Not) and isinstance(p.subpattern, SVar)):
                return 2 * len(def_list) + 2 # Not relevant; some other node will have lower or equal priority
            if isinstance(p, Nu):
                return 2 * def_list.index(p.negate())
            if isinstance(p, Mu):
                return 2 * def_list.index(p) + 1
            if isinstance(p,  App) and is_atomic_application(p) or \
               isinstance(p, DApp) and is_atomic_application(p.negate()):
                # These are equivalent to Top()
                return 0
            if isinstance(p, (Exists, App)):
                return 2 * len(def_list) + 1
            if     isinstance(p, (Forall, DApp)):
                return 2 * len(def_list) + 2
            raise RuntimeError("Unimplemented: " + str(p))
        if isinstance(self.assertion, ExistsAssertion):
            return 2 * len(def_list) + 1
        if isinstance(self.assertion, ForallAssertion):
            return 2 * len(def_list) + 2
        if isinstance(self.assertion, (AllOf, AnyOf)):
            return 2 * len(def_list) + 2 # Not relevant; some other node will have lower or equal priority
        else:
            raise RuntimeError("Unimplemented: " + str(self.assertion))

    def player(self) -> int:
        """ If a node has player N, then that player can make a move """
        if isinstance(self.assertion, Matches):
            if isinstance(self.assertion.pattern, (Top, Bottom, Mu, Nu, SVar, EVar)) or \
               (isinstance(self.assertion.pattern, Not) and isinstance(self.assertion.pattern.subpattern, SVar)) or \
               (isinstance(self.assertion.pattern, Not) and isinstance(self.assertion.pattern.subpattern, EVar)):
                # There is no choice to be made here, so it does not matter whose turn it is.
                return 0
            if isinstance(self.assertion.pattern, (And, Forall, DApp)):
                return 1
            if isinstance(self.assertion.pattern, (Or,  Exists, App)):
                return 0
            raise RuntimeError("Unimplemented: " + str(self.assertion.pattern))
        if isinstance(self.assertion, (AllOf, ForallAssertion)):
            return 1
        if isinstance(self.assertion, (AnyOf, ExistsAssertion)):
            return 0
        raise RuntimeError("Unimplemented: " + str(self))

    def label(self) -> str:
        return self.assertion.to_utf()

    def get_pg_children(self) -> List[GameNode]:
        """ Returns a list of (source, list of destination) pairs.
            Each source node appears exactly once.
        """
        return self.sequent.pg_children[self.assertion] 

@dataclass
class ResolveGameNode:
    assertion:  Assertion
    membership: Membership
    sequent:    Sequent

    def priority(self, def_list: DefList) -> int:
        return 2 * len(def_list) + 2 # Not relevant; some other node will have lower or equal priority

    def player(self) -> int:
        return 0

    def label(self) -> str:
        return "Resolve on:" + str(self.membership)

    def get_pg_children(self) -> List[GameNode]:
        """ Returns a list of (source, list of destination) pairs.
            Each source node appears exactly once.
        """
        assert False

@dataclass(frozen=True)
class ChooseExistentialGameNode:
    assertion:  Assertion
    sequent:    ChooseExistentialSequent

    def priority(self, def_list: DefList) -> int:
        return 2 * len(def_list) + 2 # Not relevant; some other node will have lower or equal priority

    def player(self) -> int:
        return 1

    def label(self) -> str:
        return self.assertion.to_utf()

    def get_pg_children(self) -> List[GameNode]:
        """ Returns a list of (source, list of destination) pairs.
            Each source node appears exactly once.
        """
        assert False


@dataclass(frozen=True)
class UnsatGameNode:
    def priority(self, def_list: DefList) -> int:
        return 1

    def player(self) -> int:
        return 0 # Not relevant. No choice

    def label(self) -> str:
        return "Unsat"

    def get_pg_children(self) -> List[GameNode]:
        """ Returns a list of (source, list of destination) pairs.
            Each source node appears exactly once.
        """
        return [UnsatGameNode()]


GameNode = Union[ BasicGameNode, ResolveGameNode, UnsatGameNode, ChooseExistentialGameNode ]

class Tableau:
    root : BasicSequent
    def_list : DefList

    def __init__(self, pattern: Pattern, sig: Signature, K: List[EVar]):
        self.root = BasicSequent( gamma        = [Matches(K[0], pattern)]
                                , basics       = []
                                , universals   = []
                                )
        self.root.extend_memberships(sig, [K[0]])
        self.def_list = definition_list(pattern, def_list = [])
        next_nodes : List[Sequent] = [self.root]
        while next_nodes:
            first, *rest = next_nodes
            (resolve_on, new_nodes) = first.build_children(K)
            next_nodes = new_nodes + rest
            if resolve_on:
                next_nodes = self.resolve(resolve_on, next_nodes)
        return

    def resolve(self, membership: Membership, next_nodes : List[Sequent]) -> List[Sequent]:
        assert False

    def serialize_game(self) -> SerializedParityGame:
        ret = []
        serialized_nodes : Dict[GameNode, int] = {}

        def ident(node: GameNode) -> int:
            if node not in serialized_nodes:
                serialized_nodes[node] = len(serialized_nodes)
            return serialized_nodes[node]

        def pgsolver_priority(node: GameNode) -> int:
            # PGSolver the *highest* infinitely recurring priority determines the winner.
            # While in our paper, we define the lowest priority infinitly recurring sequent
            # to be the deciding priority, PGSolver considers the highest priority infinitly recurring sequent.

            # Must be greater than max possible priority and an even number.
            max_priority = 2 * len(self.def_list) + 2
            return max_priority - node.priority(self.def_list)

        node_queue      : List[GameNode]      = [BasicGameNode(self.root.gamma[0], self.root)]
        processed_nodes : FrozenSet[GameNode] = frozenset()
        while node_queue:
            node, *node_queue = node_queue
            if node in processed_nodes:
                continue
            processed_nodes = processed_nodes.union([node])
            dests = node.get_pg_children()
            ret += [(ident(node),
                     pgsolver_priority(node),
                     node.player(),
                     sorted(list(map(ident, node.get_pg_children()))),
                     node.label()
                    )]
            node_queue += dests
        print('ret', ret)
        return ret

    """
    def add( self
           , assertion: Assertion
           , C: FrozenSet[EVar]
           , K: List[EVar]
           , def_list: DefList
           ) -> None:
        next : Assertion

        if isinstance(assertion, Matches):
            p = assertion.pattern
            if   isinstance(p, (Bottom)):
                self.satisfiable = False
                return
            elif isinstance(p, (Top)):
                self.internal_edges += [(assertion, assertion)]
            elif isinstance(p, EVar):
                if assertion.variable != p:
                    next = Matches(assertion.variable, Bottom())
                    self.internal_edges += [(assertion, next)]
                    self.add(next, C, K, def_list)
                    return
                else:
                    self.internal_edges += [(assertion, assertion)]
                    return
            elif isinstance(p, Not) and isinstance(p.subpattern, EVar): # x \in Not(y)
                if assertion.variable == p.subpattern: # if x \in Not(x)
                    next = Matches(assertion.variable, Bottom())
                    self.internal_edges += [(assertion, next)]
                    self.add(next, C, K, def_list)
                    return
                else: # x \in Not(y)
                    self.internal_edges += [(assertion, assertion)]
                    return

            elif isinstance(p, App):
                if (is_atomic_application(p)):
                    membership = Membership( p.symbol
                                           , tuple([assertion.variable, *cast(Iterable[EVar], p.arguments)])
                                           , Membership.Status.Holds
                                           )
                    if membership in self.memberships:
                        self.internal_edges += [(assertion, assertion)]
                        return
                    else:
                        next = Matches(assertion.variable, Bottom())
                        self.internal_edges += [(assertion,next), (assertion.negate(), next)]
                        self.add(next, C, K , def_list)
                        return

                bound_vars = list(take(len(p.arguments), diff(K, C)))
                next = ExistsAssertion(frozenset(bound_vars)
                                      , AllOf(frozenset( [ Matches( assertion.variable, App(p.symbol, *bound_vars)) ]
                                                       + [ Matches(bound, arg) for (bound, arg) in zip(bound_vars, p.arguments) ]
                                      )      )         )
                self.internal_edges += [(assertion, next)]
                self.add(next, C, K, def_list)
                return
            elif isinstance(p, DApp):
                if (is_atomic_application(p.negate())):
                    membership = Membership( p.symbol
                                           , tuple([assertion.variable, *cast(Iterable[EVar], p.negate().arguments)])
                                           , Membership.Status.DoesNotHold
                                           )
                    if membership in self.memberships:
                        self.internal_edges += [(assertion, assertion)]
                        return
                    else:
                        next = Matches(assertion.variable, Bottom())
                        self.internal_edges += [(assertion,next), (assertion.negate(), next)]
                        self.add(next, C, K , def_list)
                        return

                bound_vars = list(take(len(p.arguments), diff(K, C)))
                next  = ForallAssertion( frozenset(bound_vars)
                                       , AnyOf(frozenset( [ Matches( assertion.variable, App(p.symbol, *bound_vars).negate()) ]
                                                        + [ Matches(bound, arg) for (bound, arg) in zip(bound_vars, p.arguments) ]
                                       )      )         )
                self.internal_edges += [(assertion, next)]
                self.add(next , C, K , def_list)
                return
            elif isinstance(p, And):
                next = AllOf(frozenset([ Matches(assertion.variable, p.left), Matches(assertion.variable, p.right) ]))
                self.internal_edges += [(assertion, next)]
                self.add(next , C, K , def_list)
                return
            elif isinstance(p, Or):
                next = AnyOf(frozenset([ Matches(assertion.variable, p.left), Matches(assertion.variable, p.right)]))
                self.internal_edges += [(assertion, next)]
                self.add(next , C, K , def_list)
                return
            elif isinstance(p, (Nu, Mu)):
                next = Matches(assertion.variable, unfold(p, def_list))
                if (assertion, next) in self.internal_edges:
                    return
                self.internal_edges += [(assertion, next)]
                self.add(next, C, K, def_list)
                return
            elif isinstance(p, SVar) and isinstance(p.name, int): # Only consider bound `SVar`s.
                next = Matches(assertion.variable, def_list[p.name])
                self.internal_edges += [(assertion, next)]
                self.add(next, C, K, def_list)
                return
            elif isinstance(p, Not) and isinstance(p.subpattern, SVar) and isinstance(p.subpattern.name, int): # Only consider bound `SVar`s.
                next = Matches(assertion.variable, def_list[p.subpattern.name].negate())
                self.internal_edges += [(assertion, next)]
                self.add(next, C, K, def_list)
                return
            else:
                raise RuntimeError("Unimplemented: " + str(assertion))
        elif isinstance(assertion, AllOf):
            for a in assertion.assertions:
                node.internal_edges += [(assertion, a)]
                self.add(a, C, K, def_list)
            return
        elif isinstance(assertion, AnyOf):
            ret = []
            for a in assertion.assertions:
                ret += add_to_closure(a, partial_closure, partial_edges + [(assertion, a)], C, K, def_list)
            ret
            return
        elif isinstance(assertion, ExistsAssertion):
            self.existentials += [assertion]
            return
        elif isinstance(assertion, ForallAssertion):
            self.universals += [assertion]
            bound = list(assertion.bound)
            for instantiation in product(C, repeat = len(assertion.bound)):
                new_closures = []
                for (closure, edges) in curr_closures:
                    next = assertion.subassertion.substitute_multi(bound, instantiation)
                    new_closures += add_to_closure( next
                                                  , closure
                                                  , edges + [(assertion, next)]
                                                  , C, K, def_list)
                curr_closures = new_closures
            return curr_closures
        else:
            raise RuntimeError("Unimplemented: " + str(assertion))

    """

# ----

Closure = FrozenSet[Union[Matches, ForallAssertion, ExistsAssertion]]

@dataclass(frozen=True)
class PGNode():
    assertion: Assertion
    closure: Closure

@dataclass(frozen=True)
class Unsat():
    pass

PGNodeGeneralized = Union[PGNode, Unsat]
ParityGame = Dict[PGNodeGeneralized, FrozenSet[PGNodeGeneralized]]
SerializedParityGameEntry = Tuple[int, int, int, List[int], str]
SerializedParityGame = List[SerializedParityGameEntry]

def instantiations( length: int
                  , curr_assertion: FrozenSet[EVar]
                  ,  curr_closures: FrozenSet[EVar]
                  ,      available: List[EVar]
                  ) -> Iterable[Tuple[EVar,...]]:
    available = diff(available, curr_closures)
    curr      = sorted(list(curr_assertion))
    return list(instantiations_lists(length, curr, available))

def instantiations_lists(length: int, curr: List[EVar], avail: List[EVar]) -> Iterable[Tuple[EVar,...]]:
    if length == 0:
        yield ()
        return
    if length == 1:
        for item in curr:
            yield (item,)
        yield (avail[0],)
        return

    for curr_item in curr:
        for tuple in instantiations_lists(length - 1, curr, avail):
            yield (curr_item, *tuple)
    for tuple in instantiations_lists(length - 1, curr + [avail[0]], avail[1:]):
        yield (avail[0], *tuple)
    return

run = 0
def run_pgsolver(game: SerializedParityGame) -> bool:
    def entry_to_string(entry : SerializedParityGameEntry) -> str:
        source, priority, player, dests, label = entry
        assert len(dests) > 0
        return " ".join([str(source), str(priority), str(player), ",".join(map(str, dests)), '"' + label.replace('"', "'") + '"' ])
    input = "; \n".join(map(entry_to_string, game)) + ';'
    from subprocess import check_output, CalledProcessError, PIPE
    try:
        output = check_output(['pgsolver', '-local',  'stratimprloc2', '0'], input=input, text=True, stderr=PIPE)
    except CalledProcessError as e:
        print('PGSolver failed')
        print(input)
        print(e.stderr)
        raise

    match = re.search(r'Winner of initial node is player (\d)\n', output)
    if match is None:
        raise RuntimeError("PGGame not well formed?\n" + output)

    global run
    run += 1
    with open('/tmp/in.'  + str(run) + '.pg', 'w') as pg_file:
        pg_file.write(input)
    with open('/tmp/out.' + str(run) + '.pg', 'w') as pg_file:
        pg_file.write(check_output(['pgsolver', '-global',  'recursive', '-pg'], input=input, text=True))

    return match.group(1) == '0'

def is_atomic_application(app : App) -> bool:
    return all(map(lambda arg: isinstance(arg, EVar), app.arguments))

"""
def complete_closures_for_signature( closures: List[Tuple[Closure, PartialEdges]]
                                   , C: FrozenSet[EVar]
                                   , K: List[EVar]
                                   , signature: Signature
                                   , def_list : DefList
                                   ) -> List[Tuple[Closure, PartialEdges]]:
    # TODO: This should be replaced by some form of resulution
    for (symbol, arity) in signature.items():
        for tuple in product(C, repeat = arity + 1):
            new_closures = []
            for (partial_closure, partial_edges) in closures:
                first, *rest = tuple
                new_edges : PartialEdges = []
                x = add_to_closure(Matches(first, App(symbol, *rest)),          partial_closure, partial_edges, C, K, def_list)
                y = add_to_closure(Matches(first, App(symbol, *rest).negate()), partial_closure, partial_edges, C, K, def_list)
                new_closures += x
                new_closures += y
            closures = new_closures
    return closures
"""

"""
def instantiate_universals( closures: List[Tuple[Closure, PartialEdges]]
                          , C: FrozenSet[EVar]
                          , K: List[EVar]
                          , def_list: DefList
                          ) -> List[Tuple[Closure, PartialEdges]]:
    ret = []
    for (closure, partial_edges) in closures:
        curr_closures = [(closure, partial_edges)]
        for universal in closure:
            if not isinstance(universal, ForallAssertion):
                continue
            curr_closures = add_to_closures(universal, curr_closures, C, K, def_list)
        ret += curr_closures
    return ret
"""

def is_sat(pattern: Pattern, K: List[EVar], sig: Signature) -> bool:
    print('---- is_sat')
    pattern = pattern.to_positive_normal_form()
    tableau = Tableau(pattern, sig, K)
    print('tableau', tableau)
    serialized = tableau.serialize_game()
    if run_pgsolver(serialized):
        return True
    return False

