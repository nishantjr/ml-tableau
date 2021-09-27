from __future__ import annotations

from abc import abstractmethod
from dataclasses import dataclass
from itertools import chain, count, islice, product
from typing import Any, Container, Dict, FrozenSet, Iterable, Iterator, List, Tuple, TypeVar, Union, cast
from subprocess import check_output
import re

from pml import *

Signature = Dict[Symbol, int]

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
    elif isinstance(p, (Mu, Nu)):
        if p not in def_list:
            def_list = def_list + [p]
            def_list = definition_list(p.subpattern.substitute(p.bound, SVar(def_list.index(p))), def_list)
        return def_list
    else:
        raise RuntimeError("Unsupported pattern: " + str(p))

class Assertion:
    @abstractmethod
    def negate(self) -> 'Assertion':
        raise NotImplementedError

    @abstractmethod
    def free_evars(self) -> FrozenSet[EVar]:
        raise NotImplementedError

@dataclass(frozen=True)
class Matches(Assertion):
    variable: EVar
    pattern:  Pattern

    def negate(self) -> Matches:
        return Matches(self.variable, self.pattern.negate())

    def free_evars(self) -> FrozenSet[EVar]:
        return self.pattern.free_evars().union([self.variable])

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

Closure = FrozenSet[Assertion]
def free_evars(cl: Closure) -> FrozenSet[EVar]:
    ret : FrozenSet[EVar] = frozenset()
    for assertion in cl:
        ret = ret.union(assertion.free_evars())
    return ret

@dataclass(frozen=True)
class PGNode():
    assertion: Assertion
    closure: Closure

@dataclass(frozen=True)
class Root():
    assertion: Assertion

@dataclass(frozen=True)
class Unsat():
    pass

PGNodeGeneralized = Union[PGNode, Root, Unsat]

ParityGame = Dict[PGNodeGeneralized, FrozenSet[PGNodeGeneralized]]
SerializedParityGameEntry = Tuple[int, int, int, List[int], str]
SerializedParityGame = List[SerializedParityGameEntry]

Tableau = Dict[Closure, FrozenSet[Closure]]

def serialize_parity_game(root: PGNodeGeneralized, edges: ParityGame, def_list: DefList) -> SerializedParityGame:
    ret = []
    keys = list(edges.keys())

    def ident(node: PGNodeGeneralized) -> int:
        if isinstance(node, Root):
            return 0
        if isinstance(node, Unsat):
            return 2
        return 3 + keys.index(node)

    def priority(node: PGNodeGeneralized, def_list: DefList) -> int:
        # If the lowest-priority infinitly recurring node has even priority, player 0  wins (pattern is sat).
        # Otherwise player 1 wins (pattern is unsat).
        if isinstance(node, Root):
            return 0 # Cannot repeat infinitly on any trace, so value doesn't matter.
        if isinstance(node, Unsat):
            return 1
        if isinstance(node.assertion, Matches):
            if isinstance(node.assertion.pattern, (Top, Bottom)):
                return 0 # Cannot repeat infinitly on any trace, so value doesn't matter.
            if isinstance(node.assertion.pattern, Nu):
                return 2 * def_list.index(node.assertion.pattern)
            if isinstance(node.assertion.pattern, Mu):
                return 2 * def_list.index(node.assertion.pattern) + 1
            if isinstance(node.assertion.pattern, (Exists)):
                return 2 * len(def_list) + 1
            if     isinstance(node.assertion.pattern, App) \
               and not is_atomic_application(node.assertion.pattern):
                return 2 * len(def_list) + 1
            return 2 * len(def_list) + 2
        else:
            return 2 * len(def_list)

    def player(node: PGNodeGeneralized) -> int:
        # If a node has player N, then that player can make a move
        if isinstance(node, (Root, Unsat)):
            # There is no choice to be made here, so it does not matter whose turn it is.
            return 0 
        if isinstance(node.assertion, Matches):
            if isinstance(node.assertion.pattern, (Top, Bottom, Mu, Nu, SVar, EVar)) or \
               (isinstance(node.assertion.pattern, Not) and isinstance(node.assertion.pattern.subpattern, EVar)):
                # There is no choice to be made here, so it does not matter whose turn it is.
                return 0 
            if isinstance(node.assertion.pattern, (And, Forall, DApp)):
                return 1
            if isinstance(node.assertion.pattern, (Or,  Exists, App)):
                return 0
            raise RuntimeError("Unimplemented: " + str(node.assertion.pattern))
        if isinstance(node.assertion, AllOf):
            return 1
        if isinstance(node.assertion, AnyOf):
            return 0
        raise RuntimeError("Unimplemented: " + str(node))

    def label(node: PGNodeGeneralized) -> str:
        if isinstance(node, Unsat):
            return "Unsat"
        elif isinstance(node, Root):
            return str(node.assertion)
        else:
            return str(node.assertion)

    for source, destinations in edges.items():
        ret += [(ident(source),
                 priority(source, def_list),
                 player(source),
                 sorted(list(map(ident, destinations))),
                 label(source)
                )]
    return ret

def run_pgsolver(game: SerializedParityGame) -> bool:
    def entry_to_string(entry : SerializedParityGameEntry) -> str:
        source, priority, player, dests, label = entry
        assert len(dests) > 0
        return " ".join([str(source), str(priority), str(player), ",".join(map(str, dests)), '"' + label.replace('"', "'") + '"' ])
    input = "; \n".join(map(entry_to_string, game)) + ';'
    output = check_output(['pgsolver', '-local',  'stratimprloc2', '0'], input=input, text=True)
    match = re.search(r'Winner of initial node is player (\d)\n', output)
    if match is None:
        raise RuntimeError("PGGame not well formed?\n" + output)

    # Dot output only works for global strategies for some reason
    check_output(['pgsolver', '-global',  'recursive', '-d', '/tmp/out.dot'], input=input, text=True)

    return match.group(1) == '0'

PartialEdges = List[Tuple[Assertion, Assertion]]

def is_atomic_application(app : App) -> bool:
    return all(map(lambda arg: isinstance(arg, EVar), app.arguments))

def add_app_dapp_to_closure(pairs : List[Tuple[Matches, Matches]] , partial_closure: Closure, partial_edges: PartialEdges, K: List[EVar]) -> List[Tuple[Closure, PartialEdges]]:
    curr_closures = [(partial_closure, partial_edges)]
    for (app, dapp) in pairs:
        assert isinstance(app.pattern, App)
        assert isinstance(dapp.pattern, DApp)
        assert app.pattern.symbol == dapp.pattern.symbol

        if is_atomic_application(app.pattern):
            new_closures = []
            for (curr_closure, curr_edges) in curr_closures:
                if Matches(app.variable, app.pattern.negate()) == dapp:
                    return add_to_closure( Matches(app.variable, Bottom())
                                         , curr_closure
                                         , curr_edges +
                                           [(dapp, Matches(app.variable, Bottom()))
                                           ,( app, Matches(app.variable, Bottom())) 
                                           ]
                                         , K
                                         )

                any_of : List[Assertion] = []
                for ci, phii in zip(app.pattern.arguments, dapp.pattern.arguments):
                    assert isinstance(ci, EVar)
                    any_of += [Matches(ci, phii)]
                new_closures += add_to_closure( AnyOf(frozenset(any_of))
                                              , curr_closure
                                              , curr_edges + [ (dapp, AnyOf(frozenset(any_of))) ]
                                              , K)
            curr_closures = new_closures
    return curr_closures

def add_to_closure(assertion: Assertion, partial_closure: Closure, partial_edges: PartialEdges, K: List[EVar]) -> List[Tuple[Closure, PartialEdges]]:
    if isinstance(assertion, Matches):
        p = assertion.pattern
        if   isinstance(p, (Bottom)):
            return []
        elif isinstance(p, (Top)):
            return [( partial_closure.union([assertion])
                    , partial_edges + [(assertion, assertion)]
                    )]
        elif isinstance(p, EVar):
            if assertion.variable != p:
                return add_to_closure( Matches(assertion.variable, Bottom())
                                     , partial_closure.union([assertion])
                                     , partial_edges + [(assertion, Matches(assertion.variable, Bottom()))]
                                     , K)
            return [(partial_closure, partial_edges)]
        elif isinstance(p, Not):
            assert isinstance(p.subpattern, EVar)
            if Matches(assertion.variable, p.negate()) in partial_closure:
                return add_to_closure( Matches(assertion.variable, Bottom())
                                     , partial_closure.union([assertion])
                                     , partial_edges + [(assertion, Matches(assertion.variable, Bottom()))]
                                     , K)
            return [(partial_closure, partial_edges)]
        elif isinstance(p, DApp):
            partial_closure = partial_closure.union([assertion])
            if (is_atomic_application(p.negate())):
                partial_edges = partial_edges + [(assertion, assertion)]
            apps = [a for a in partial_closure if    isinstance(a, Matches)
                                                and isinstance(a.pattern, App)
                                                and a.pattern.symbol == p.symbol]
            return add_app_dapp_to_closure( list(product(apps, [assertion]))
                                          , partial_closure
                                          , partial_edges
                                          , K
                                          )
        elif isinstance(p, App):
            partial_closure = partial_closure.union([assertion])
            if (is_atomic_application(p)):
                partial_edges = partial_edges + [(assertion, assertion)]
            dapps = [a for a in partial_closure if   isinstance(a, Matches)
                                                and isinstance(a.pattern, DApp)
                                                and a.pattern.symbol == p.symbol]
            return add_app_dapp_to_closure( list(product([assertion], dapps))
                                          , partial_closure
                                          , partial_edges
                                          , K
                                          )
        elif isinstance(p, And):
            ret = []
            partial_closure = partial_closure.union([assertion])
            for (closure, edges) in add_to_closure( Matches(assertion.variable, p.left)
                                         , partial_closure
                                         , partial_edges + [(assertion, Matches(assertion.variable, p.left))]
                                         , K
                                         ):
                ret += add_to_closure( Matches(assertion.variable, p.right)
                                     , closure
                                     , edges + [(assertion, Matches(assertion.variable, p.right))]
                                     , K)
            return ret
        elif isinstance(p, Or):
            ret = []
            partial_closure = partial_closure.union([assertion])
            for next in [p.left, p.right]:
                ret += add_to_closure( Matches(assertion.variable, next)
                                     , partial_closure
                                     , partial_edges + [(assertion, Matches(assertion.variable, next))]
                                     , K
                                     )
            return ret

        else:
            raise RuntimeError("Unimplemented: ")
    elif isinstance(assertion, AllOf):
        curr_closures = [(partial_closure, partial_edges)]
        for a in assertion.assertions:
            new_closures = []
            for (closure, edges) in curr_closures:
                new_closures += add_to_closure( a
                                              , closure
                                              , edges + [(assertion, a)]
                                              , K)
            curr_closures = new_closures
        return curr_closures
    elif isinstance(assertion, AnyOf):
        ret = []
        for a in assertion.assertions:
            ret += add_to_closure(a, partial_closure, partial_edges + [(assertion, a)], K)
        return ret
    else:
        raise RuntimeError("Unimplemented: ")

def complete_closures_for_signature( closures: List[Tuple[Closure, PartialEdges]]
                                   , C: FrozenSet[EVar]
                                   , K: List[EVar]
                                   , signature: Signature
                                   , parity_game : ParityGame) -> List[Closure]:
    # TODO: This should be replaced by some form of resulution
    for (symbol, arity) in signature.items():
        for tuple in product(C, repeat = arity + 1):
            new_closures = []
            for (partial_closure, partial_edges) in closures:
                first, *rest = tuple
                new_edges : PartialEdges = []
                x = add_to_closure(Matches(first, App(symbol, *rest)),          partial_closure, partial_edges, K)
                y = add_to_closure(Matches(first, App(symbol, *rest).negate()), partial_closure, partial_edges, K)
                new_closures += x
                new_closures += y
            closures = new_closures

    ret : List[Closure] = []
    sources : List[PGNode] = []
    dests : List[PGNode] = []
    for (closure, partial_edges) in closures:
        for (source, dest) in partial_edges:
            source_node = PGNode(source, closure)
            sources += [source_node]
            parity_game[source_node] = parity_game.get(source_node, frozenset()).union([PGNode(dest, closure)])
            dests += [PGNode(dest, closure)]
        ret += [closure]
    for node in diff(dests, sources):
        parity_game[node] = frozenset({Unsat()})
    return ret

T = TypeVar('T')
def diff(l1: List[T] , l2_set: Container[T]) -> List[T]:
    # Preserves order
    return [item for item in l1 if item not in l2_set]

def take(n: int, l: List[EVar]) -> List[EVar]:
  return list(islice(l, n))

def build_tableau( curr_node: Closure
                 , partial_tableau: Tableau
                 , partial_game : ParityGame
                 , K: List[EVar]
                 , signature: Signature) -> None:
    if curr_node in partial_tableau.keys(): return
    next_nodes : List[Closure] = []
    for assertion in curr_node:
        if not isinstance(assertion, Matches):
            continue
        p = assertion.pattern
        if not isinstance(p, App):
            continue
        if all(map(lambda arg: isinstance(arg, EVar), p.arguments)):
            continue

        failed_instantiations : List[Assertion] = []
        potential_variables = list(assertion.free_evars()) + take(len(p.arguments), diff(K, free_evars(curr_node)))

        source_node = PGNode(assertion, curr_node)
        for instantiation in product(potential_variables, repeat = len(p.arguments)):
            new_assertion = AllOf(frozenset( failed_instantiations
                                           + [ Matches(assertion.variable,  App(p.symbol, *instantiation)) ]
                                           + [ Matches(inst, arg) for (inst, arg) in zip(instantiation, p.arguments) ]
                                           ))
            new_tableau_node = frozenset(instantiation) <= free_evars(frozenset({assertion}))
            if new_tableau_node:
                new_closure = curr_node
                copied_assertions : Closure = frozenset()
            else:
                new_closure = frozenset({ a for a in curr_node if p.free_evars() <= free_evars(frozenset({assertion})) })
                copied_assertions = new_closure

            new_closures = complete_closures_for_signature( add_to_closure(new_assertion, new_closure, [], K)
                                                          , free_evars(new_closure).union(frozenset(instantiation))
                                                          , K
                                                          , signature
                                                          , partial_game
                                                          )
            for new_closure in new_closures:
                dest_node = PGNode(new_assertion, new_closure)
                partial_game[source_node] = partial_game.get(source_node, frozenset()).union([dest_node])
                if new_tableau_node:
                    for copied in copied_assertions:
                        copied_node = PGNode(copied, curr_node)
                        partial_game[copied_node] = partial_game.get(source_node, frozenset()).union([PGNode(copied, new_closure)])

            next_nodes += new_closures
            # TODO: add game edges
            failed_instantiations += [new_assertion.negate()]
        if not source_node in partial_game.keys():
            partial_game[source_node] = frozenset([Unsat()])

    partial_tableau[curr_node] = frozenset(next_nodes)

    for node in next_nodes:
        build_tableau(node, partial_tableau, partial_game, K, signature)

def build_closures(a: Matches, K: List[EVar], signature: Signature, partial_game: ParityGame) -> List[Closure]:
    closures = add_to_closure(a, frozenset(), [], K)
    C = a.free_evars().union([a.variable])
    return complete_closures_for_signature(closures, C, K, signature, partial_game)

def build_tableaux(assertion : Matches, K: List[EVar], signature: Signature) -> ParityGame:
    def_list : DefList = definition_list(assertion.pattern, def_list = [])
    game : ParityGame = {}
    tableau : Tableau = {}
    closures = build_closures(assertion, K, signature, game)
    if closures:
        game[Root(assertion)] = frozenset([PGNode(assertion, closure) for closure in closures])
    else:
        game[Root(assertion)] = frozenset([Unsat()])
    for closure in closures:
        build_tableau(closure, tableau, game, K, signature)
    return game

def is_sat(p: Pattern, K: List[EVar], signature: Signature) -> bool:
    p = p.to_positive_normal_form()
    game = build_tableaux(Matches(K[0], p), K, signature)
    game[Unsat()] = frozenset({Unsat()})
    serialized = serialize_parity_game(Root(Matches(K[0], p)), game, definition_list(p, []))
    return run_pgsolver(serialized)

