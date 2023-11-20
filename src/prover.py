#!/usr/bin/env python3

from __future__ import annotations
from abc import ABC, abstractmethod
import itertools
import random

from logic import *
from util import *
from proofrules import *
from parser import parse, fmla_parse
from verifier import verify

class Tactic(ABC):

    @abstractmethod
    def apply(self, seq: Sequent) -> set[Proof]:
        return set([seq])

class InstantiateForallTactic(Tactic):

    """
    A general tactic for proving sequents with a quantified
    formula in the context. The constructor takes a set of
    objects to instantiate the quantified variable with, and
    for each object `e`, `apply` returns a proof with one application
    of `@L` where the quantified variable is replaced with `e`
    in the context of the premise.
    """
    
    def __init__(self, grounds: set[Formula|Agent|Resource|Key]):
        self.grounds = grounds

    def apply(self, seq: Sequent) -> set[Proof]:
        pfs = set([])
        # seq is p1, ..., pn |- delta
        for p in seq.gamma:
            if not isinstance(p.p, Forall):
                continue
            # p is Proposition(@x . q)
            x = p.p.x
            q = p.p.p
            for e in self.grounds:
                # A new assumption to add to the context of the premise
                # by substituting e for x.
                new_assume = Proposition(apply_formula(q, {x: e}))
                # If this assumption is already in the context, don't bother
                # generating a proof
                if new_assume not in seq.gamma:
                    # The context for the premise of the proof that will be added
                    # contains the new assumption, and removes the @x . p judgement
                    # to avoid repeating the same step in the future.
                    new_gamma = [r for r in seq.gamma if r != p] + [new_assume]
                    # Before adding the proof, need to check whether delta is a
                    # truth (proposition) judgement or affirmation.
                    # This determines whether to use the "normal" @L rule, or the
                    # version that matches affirmation judgements.
                    which_rule = forallLeftRule if isinstance(seq.delta, Proposition) else forallLeftAffRule
                    # Add the proof to the return set.
                    pfs |= set([Proof([Sequent(new_gamma, seq.delta)], seq, which_rule)])
        return pfs

class SignTactic(Tactic):

    """
    A tactic for incorporating a signed credential into
    assumptions as a `says` formula. The `says` formula
    obtained by applying the `Sign` rule to `cred` with
    the public key of `agent` is incorporated into the
    context of an application of `Cut`. So if this tactic
    were constructed as:
    
    SignTactic(parse('sign(open(#b, <r>), [k])'), Agent('#a'))
    
    And applied to the following sequent:
    
    iskey(#a, [k]), sign(open(#b, <r>), [k]) |- P

    Then it would yield the following proof.

                        T.0  T.1
    cut -------------------------------------------------
        iskey(#a, [k]), sign(open(#b, <r>), [k]) |- P

    The premise `T.0` will be a closed proof of
    `#a says open(#b, <r>)` if and only if:
        - The `cred` argument is in the context of the
          sequent that the tactic is applied to.
        - The sequent that the tactic is applied to
          has an `iskey` predicate that associates the
          `agent` argument with the key appearing in
          the `cred` argument, i.e. `iskey(#a, [k])` in
          this example.
    The premise `T.1` of the resulting proof will be a
    sequent (i.e., an open/unclosed premise) with a set
    of assumptions identical to those in the sequent that
    the tactic is applied to, but will also include
    `#a says open(#b, <r>)`. I.e.:

    #a says open(#b, <r>), iskey(#a, [k]), sign(open(#b, <r>), [k]) |- P

    If the two conditions listed above are not true of
    the sequent that the tactic is applied to, then
    `apply` returns the empty set.

    The proofs returned by this tactic can be closed by
    combining with other tactics using `ThenTactic`, or
    by applying other tactics to `pf.premises[1].conclusion`,
    (assuming `pf` is the returned proof), which will contain
    the unfinished sequent with the new `says` in its
    assumption, and chaining the two proofs together with
    `chain`.
    """
    
    def __init__(self, cred: Formula, agent: Agent):
        self._cred = cred
        self._ag = agent
        # _says is the formula that we want to introduce in the cut
        self._says = App(Operator.SAYS, 2, [agent, cred.args[0]])
        # _iskey associates agent to the key in cred
        self._iskey = App(Operator.ISKEY, 2, [agent, cred.args[1]])
        # cred and _iskey need to be present in the sequent to
        # apply this tactic
        self._reqs = [
            Proposition(cred),
            Proposition(self._iskey)
        ]

    def apply(self, seq: Sequent) -> set[Proof]:
        # make sure all of the required assumptions are present
        if not all(p in seq.gamma for p in self._reqs):
            return set([])
        # if the `says` formula is already in the sequent's
        # assumptions, then there is no need to introduce it
        # again
        if Proposition(self._says) in seq.gamma:
            return set([])
        # cutgoal is the formula that we want to prove in the
        # left premise of the `cut` application
        cutgoal = Sequent(seq.gamma, Proposition(self._says))
        # `Sign` requires proving `_iskey` and `_cred`
        # We already checked that these are in the context,
        # so if we've gotten this far then we know that both
        # are proved with one application of the identity rule
        pf_iskey = get_one_proof(Sequent(seq.gamma, Proposition(self._iskey)), RuleTactic(identityRule))
        pf_cred = get_one_proof(Sequent(seq.gamma, Proposition(self._cred)), RuleTactic(identityRule))
        # The left premise of the cut is proved by combining these proofs
        # using the `Sign` rule
        pf_cutgoal = Proof([pf_iskey, pf_cred], cutgoal, signRule)
        # The right premise of the cut will copy the assumptions
        # in the current sequent, and add _says
        new_gamma = (
            seq.gamma + 
            [Proposition(self._says)]
        )
        newgoal = Sequent(new_gamma, seq.delta)
        # We need to look at the delta (proof goal) of the given sequent
        # to determine whether to use the version of `cut` for truth
        # or affirmation judgements
        whichRule = cutRule if isinstance(seq.delta, Proposition) else affCutRule
        # Now put everything together and return the proof
        return set([Proof([pf_cutgoal, newgoal], seq, whichRule)])

class RuleTactic(Tactic):

    """
    A general tactic for applying the rules in `proofrules` to make
    single-step progress on a proof. This does not attempt to apply
    the quantifier rules, and will raise `ValueError` if the constructor
    is given such a rule.
    """
    
    def __init__(self, rule: Rule):
        match rule:
            case Rule(_, _, '@L')|Rule(_,_,'@R'):
                raise ValueError(f'RuleTactic cannot be applied to @L or @R')
        self._rule = rule

    def apply(self, seq: Sequent) -> set[Proof]:
        pfs = set([])
        # Attempt to unify the given sequent with the conclusion of the rule.
        rhos = list(matchs_sequent(self._rule.conclusion, seq, {}))
        # There may be more than one substitution that unifies the
        # sequent with the rule, i.e., more than one opportunity to
        # apply the rule to this sequent. This tactic will generate
        # proofs for all of them.
        for rho in rhos:
            # We want to remove any assumptions from the sequent that
            # were used to match the rule. This is a general heuristic
            # to avoid infinite applications of the same step when
            # the tactic is combined with repetitive tactics.
            rule_gamma = apply_sequent(self._rule.conclusion, rho).gamma
            red_gamma = [p for p in seq.gamma if p not in rule_gamma]
            # The premises of each proof are obtained by applying
            # the substitution rho to each rule premise, and adding
            # the assumptions from the goal sequent that were not
            # used to match with the rule.
            prems = [
                Sequent(
                    list(set(apply_sequent(prem, rho).gamma + red_gamma)), 
                    apply_sequent(prem, rho).delta
                ) 
                for prem in self._rule.premises
            ]
            # Add the proof to the return set, and carry on
            pfs |= set([Proof(prems, seq, self._rule)])
        return pfs

class ThenTactic(Tactic):

    """
    A combinator tactic to apply a sequence of tactics,
    chaining the proofs obtained by later tactics to any
    unclosed branches of proofs generated by earlier tactics.

    This can be used in two modes, depending on the value 
    of `pass_on` given to the constructor. If `pass_on` is 
    `True`, then if the first tactic in the sequence fails
    to produce any proofs, then the next tactic is applied
    to the original sequent. If `pass_on` is `False`, then
    when the first tactic produces no proofs, no further
    tactics are applied.

    Most applications of this tactic will want to use it with
    `pass_on` set to `True`, so this is the default value.
    """
    
    def __init__(self, ts: list[Tactic], pass_on=True):
        self._ts = ts
        self._pass = pass_on

    def apply(self, seq: Sequent) -> set[Proof]:
        pfs = set([])
        # This tactic calls itself recursively, and
        # will terminate when the sequence of tactics
        # to apply is empty.
        if len(self._ts) > 0:
            # The first tactic in the sequence is applied directly,
            # and the remaining are dealt with recursively.
            t1, t2 = self._ts[0], ThenTactic(self._ts[1:], pass_on=self._pass)
            t1_pfs = t1.apply(seq)
            # If the first tactic didn't yield any proofs, then
            # return an empty set if `pass_on` is `False`.
            # Otherwise, just proceed to the next tactic
            # with the original sequent.
            if len(t1_pfs) == 0:
                return t2.apply(seq) if self._pass else set([])
            else:
                for pf1 in t1_pfs:
                    # For each proof returned by the first tactic,
                    # find the set of remaining unclosed branches
                    # (i.e. "obligations") by calling verify.
                    obs = [ob for ob in verify(pf1) if ob != seq]
                    # If all of the branches are closed, then
                    # simply return this proof.
                    # No future tactics will be able to make further
                    # progress on it.
                    if len(obs) == 0:
                        return set([pf1])
                    # Generate proofs for the remaining obligations
                    # by applying the rest of the tactic sequence
                    # to them
                    t2_pfs = [(ob, t2.apply(ob)) for ob in obs]
                    # Now we have a *set* of proofs for each unclosed
                    # branch. We don't know a priori which of them
                    # will be able to close, so we return proofs that
                    # try every combination of proof for all premises.
                    combs = list(
                        itertools.product(
                            *[pf if len(pf) > 0 else [ob] for ob, pf in t2_pfs]
                        )
                    )
                    # The list of combinations can be empty if there were
                    # no proofs for one of the obligations.
                    if len(combs) > 0:
                        for comb in combs:
                            # If this isn't the case, then chain each combination
                            # of obligation proofs onto the current proof,
                            # and add it to the return set.
                            chains = {ob: comb[i] for i, ob in enumerate(obs)}
                            pfs |= set([chain(pf1, chains)])
                    else:
                        # If this happens, then just add the current proof.
                        pfs |= set([pf1])
        return pfs

class OrElseTactic(Tactic):

    """
    Apply a sequence of tactics until progress is made.
    Specifically, continue applying tactics in the
    given sequence while they fail to produce any proofs.
    When a tactic does produce proofs, return them and
    stop applying further tactics.
    """
    
    def __init__(self, ts: list[Tactic]):
        self._ts = ts

    def apply(self, seq: Sequent) -> set[Proof]:
        # This works in a similar way to ThenTactic,
        # making recursive calls to itself
        # for as long as tactics attempted so far do not
        # produce any proofs.
        if len(self._ts) > 0:
            t_pfs = self._ts[0].apply(seq)
            if len(t_pfs) == 0:
                return OrElseTactic(self._ts[1:]).apply(seq)
            else:
                return t_pfs
        return set([])

class CertTactic(Tactic):

    """

    """

    def __init__(self, agent: Agent, pk: Key, CA: Agent, kca: Key):
        self._ag = agent
        self._pk = pk
        self._CA = CA
        self._kca = kca
        # _iskey is the formula that we want to introduce in the cut
        self._iskey = App(Operator.ISKEY, 2, [agent, pk])
        # _isCA confirms the given CA agent is a CA
        self._isCA = parse("ca(#ca)")
        # _CAsays is the formula that CA confirms iskey(agent, pk)
        self._CAsays = App(Operator.SAYS, 2, [CA, self._iskey])
        # isCA and CAsays need to be present in the sequent to apply this tactic
        self._reqs = [
            Proposition(self._CAsays),
            Proposition(self._isCA)
        ]

    def apply(self, seq: Sequent) -> set[Proof]:
        # print(stringify(seq))
        # make sure all of the required assumptions are present
        if not all(p in seq.gamma for p in self._reqs):
            # if not (self._CAsays in seq.gamma):
            #     # print("not CA says")
            # elif not (self._isCA in seq.gamma):
                # print("not isCA")
            # print("not all reqs are met")
            return set([])
        # if the `iskey` formula is already in the sequent's
        # assumptions, then there is no need to introduce it
        # again
        if Proposition(self._iskey) in seq.gamma:
            # print("already there")
            return set([])
        # cutgoal is the formula that we want to prove in the
        # left premise of the `cut` application
        cutgoal = Sequent(seq.gamma, Proposition(self._iskey))
        # `Cert` requires proving `_isCA` and `_CAsays`
        # We already checked that these are in the context,
        # so if we've gotten this far then we know that both
        # are proved with one application of the identity rule
        pf_isCA = get_one_proof(Sequent(seq.gamma, Proposition(self._isCA)), RuleTactic(identityRule))
        pf_CAsays = get_one_proof(Sequent(seq.gamma, Proposition(self._CAsays)), RuleTactic(identityRule))
        # The left premise of the cut is proved by combining these proofs
        # using the `Sign` rule
        pf_cutgoal = Proof([pf_isCA, pf_CAsays], cutgoal, certRule)
        # The right premise of the cut will copy the assumptions
        # in the current sequent, and add _iskey
        new_gamma = (
            seq.gamma + 
            [Proposition(self._iskey)]
        )
        newgoal = Sequent(new_gamma, seq.delta)
        # We need to look at the delta (proof goal) of the given sequent
        # to determine whether to use the version of `cut` for truth
        # or affirmation judgements
        whichRule = cutRule if isinstance(seq.delta, Proposition) else affCutRule
        # Now put everything together and return the proof
        return set([Proof([pf_cutgoal, newgoal], seq, whichRule)])


def chain(pf: Proof, chains: dict[Sequent, Proof]) -> Proof:
    """
    Chain proofs for unclosed branches of a proof into
    the original proof. An unclosed branch in a proof
    will manifest as a `Sequent` object in a premise,
    rather than a `Proof` object. The `chains` argument
    maps these sequents to proofs, which are substituted
    into the given proof `pf`.
    
    Args:
        pf (Proof): A proof, potentially containing unclosed
            branches.
        chains (dict[Sequent, Proof]): Mapping of unfinished
            branches to their proofs.
    
    Returns:
        Proof: The proof described in the summary.
    """
    # If the mapping contains a proof for the original
    # conclusion, then return it.
    if pf.conclusion in chains:
        return chains[pf.conclusion]
    new_prems = []
    # Look for unfinished branches among the premises.
    for prem in pf.premises:
        if isinstance(prem, Proof):
            # If a premise already has a proof, it may still
            # contain unfinished branches. Recurse on it.
            new_prems.append(chain(prem, chains))    
        elif prem in chains:
            # Otherwise, if the premise is a sequent mapped to
            # a proof by the given `chains`, then use the mapping
            new_prems.append(chains[prem] if chains[prem] is not None else prem)
        else:
            # Otherwise, it is a sequent that the mapping does
            # not have a proof for. Leave it unchanged.
            new_prems.append(prem)
    return Proof(new_prems, pf.conclusion, pf.rule)

def get_one_proof(seq: Sequent, t: Tactic) -> Optional[Proof]:
    """
    Convenience function to look for a closed proof
    in the set returned by a tactic.
    
    Args:
        seq (Sequent): A sequent to apply the tactic to.
        t (Tactic): Tactic to apply.
    
    Returns:
        Optional[Proof]: If the tactic yields a closed proof,
            i.e., one for which `verify` returns an empty set
            of obligations, then that proof is returned.
            Otherwise, `None`.
    """
    for pf in t.apply(seq):
        if len(verify(pf)) == 0:
            return pf
    return None

def prove(seq: Sequent) -> Optional[Proof]:
    """
    Produce a proof for a given sequent, if the
    student's tactic is able to find one. You
    should implement this function by developing
    one or more tactics for the authorization
    policies specified in the lab, and applying them
    to `seq`.
    
    Args:
        seq (Sequent): Sequent to prove.
    
    Returns:
        Optional[Proof]: A closed proof of `seq`, if
            one exists. Otherwise `None`.
    """
    # P -> Q, P |- Q
    if seq.delta == parse("(#root says open(#pdoan, <pdoan.txt>)) true"):
        t = ThenTactic(
            [
                # Get #ca says iskey(root, pkr)
                SignTactic(parse('sign(iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                # Get iskey(root, pkr)
                CertTactic(Agent('#root'), Key('[2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get root says open(#pdoan, <pdoan.txt>)
                SignTactic(parse('sign((open(#pdoan, <pdoan.txt>)), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])'), Agent('#root')),
                # Close the proof
                RuleTactic(identityRule)
            ]
        )
        return get_one_proof(seq, t)

    elif seq.delta == parse("(#root says open(#pdoan, <shared.txt>)) true"):

        t = ThenTactic(
            [
                # Get #ca says iskey(root, pkr)
                SignTactic(parse('sign(iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                # Get iskey(root, pkr)
                CertTactic(Agent('#root'), Key('[2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get #ca says iskey(mfred, pkm)
                SignTactic(parse('sign((iskey(#mfredrik, [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                # Get iskey(mfred, pkm)
                CertTactic(Agent('#mfredrik'), Key('[d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get #root aff open(#pdoan, <shared.txt>) in delta
                RuleTactic(saysRightRule),
                # Get #root says the delegation rule
                SignTactic(parse("sign(((@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                # Get the delegation rule
                # (@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>)))
                RuleTactic(saysLeftRule),
                # Use pdoan as x in the for all clause
                InstantiateForallTactic([Agent("#pdoan")]),
                # Split the mfred says open() -> open() clause
                RuleTactic(impLeftAffRule),
                # Get #mfred says open(<pdoan>, <shared.txt>) in gamma
                SignTactic(parse("sign((open(#pdoan, <shared.txt>)), [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])"), Agent("#mfredrik")),
                # Remove the aff in #root aff open(#pdoan, <shared.txt>)
                RuleTactic(affRule),
                # Close the branches
                RuleTactic(identityRule),
                # Get #mfred says open(<pdoan>, <shared.txt>) in gamma again because the first time does not seem to work
                SignTactic(parse("sign((open(#pdoan, <shared.txt>)), [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])"), Agent("#mfredrik")),
                RuleTactic(identityRule),
            ]
        )
        # print()
        # print("get_one_proof=", stringify(get_one_proof(seq, t)))
        return get_one_proof(seq, t)

    elif seq.delta == parse("(#root says open(#pdoan, <secret.txt>)) true"):
        print("seq =")
        print(stringify(seq))

        t = ThenTactic(
            [
                # Get the key certifications in gamma
                # Get iskey(root, pkr)
                SignTactic(parse('sign(iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                CertTactic(Agent('#root'), Key('[2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get iskey(mfred, pkm)
                SignTactic(parse('sign((iskey(#mfredrik, [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                CertTactic(Agent('#mfredrik'), Key('[d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get iskey(duena, pkd)
                SignTactic(parse('sign((iskey(#dsduena, [db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                CertTactic(Agent('#dsduena'), Key('[db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get iskey(justin, pkj)
                SignTactic(parse('sign((iskey(#justinyo, [d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                CertTactic(Agent('#justinyo'), Key('[d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get iskey(dhamank, pkdh)
                SignTactic(parse('sign((iskey(#mdhamank, [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                CertTactic(Agent('#mdhamank'), Key('[71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                
                # Change the right hand side to aff
                RuleTactic(saysRightRule),

                # Get the delegation formula by #root in gamma
                SignTactic(parse("sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                RuleTactic(saysLeftRule),

                # Get open(#mfred, <secret.txt>) in gamma
                SignTactic(parse("sign((open(#mfredrik, <secret.txt>)), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                RuleTactic(saysLeftRule),

                # Get open(#dsduena, <secret.txt>) in gamma
                InstantiateForallTactic(set([Agent("#mfredrik")])),
                InstantiateForallTactic(set([Resource("<secret.txt>")])),
                RuleTactic(impLeftAffRule),
                InstantiateForallTactic(set([Agent("#dsduena")])),
                SignTactic(parse("sign((open(#dsduena, <secret.txt>)), [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])"), Agent("#mfredrik")),
                RuleTactic(impLeftAffRule),
                # RuleTactic(saysLeftRule),

                # Get open(#justinyo, <secret.txt>) in gamma
                # Get the delegation formula by #root in gamma
                SignTactic(parse("sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                RuleTactic(saysLeftRule),
                InstantiateForallTactic(set([Agent("#dsduena")])),
                InstantiateForallTactic(set([Resource("<secret.txt>")])),
                RuleTactic(impLeftAffRule),
                InstantiateForallTactic(set([Agent("#justinyo")])),
                SignTactic(parse("sign((open(#justinyo, <secret.txt>)), [db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f])"), Agent("#dsduena")),
                RuleTactic(impLeftAffRule),
                # RuleTactic(saysLeftRule),

                # Get open(#mdhamank, <secret.txt>) in gamma
                # Get the delegation formula by #root in gamma
                SignTactic(parse("sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                RuleTactic(saysLeftRule),
                InstantiateForallTactic(set([Agent("#justinyo")])),
                InstantiateForallTactic(set([Resource("<secret.txt>")])),
                RuleTactic(impLeftAffRule),
                InstantiateForallTactic(set([Agent("#mdhamank")])),
                SignTactic(parse("sign((open(#mdhamank, <secret.txt>)), [d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af])"), Agent("#justinyo")),
                RuleTactic(impLeftAffRule),
                # RuleTactic(saysLeftRule),

                # Get open(#pdoan, <secret.txt>) in gamma
                # Get the delegation formula by #root in gamma
                SignTactic(parse("sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                RuleTactic(saysLeftRule),
                InstantiateForallTactic(set([Agent("#mdhamank")])),
                InstantiateForallTactic(set([Resource("<secret.txt>")])),
                RuleTactic(impLeftAffRule),
                InstantiateForallTactic(set([Agent("#pdoan")])),
                SignTactic(parse("sign((open(#pdoan, <secret.txt>)), [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f])"), Agent("#mdhamank")),
                RuleTactic(impLeftAffRule),
                # RuleTactic(saysLeftRule),

                RuleTactic(affRule),
                
                # Close the branches
                RuleTactic(identityRule)
            ]
        )

        return get_one_proof(seq, t)

if __name__ == '__main__':

    # seq = parse("""ca(#ca), iskey(#ca, [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    # sign((iskey(#mdhamank, [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    # sign((iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    # sign((iskey(#justinyo, [d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    # sign((iskey(#dsduena, [db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    # sign((iskey(#mfredrik, [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    # sign((open(#siruih, <secret.txt>)), [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f]),
    # sign((open(#mfredrik, <secret.txt>)), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]),
    # sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]),
    # sign((open(#mdhamank, <secret.txt>)), [d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af]),
    # sign((open(#pdoan, <secret.txt>)), [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f]),
    # sign((open(#pdoan, <pdoan.txt>)), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]),
    # sign((open(#mfredrik, <shared.txt>)), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]),
    # sign((open(#justinyo, <secret.txt>)), [db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f]),
    # sign(((@A . (((#mfredrik says open(A, <shared.txt>)) -> open(A, <shared.txt>))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]),
    # sign((open(#dsduena, <secret.txt>)), [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]),
    # sign((open(#pdoan, <shared.txt>)), [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]) |- (#root says open(#pdoan, <secret.txt>))""")

    seq = parse("""ca(#ca), iskey(#ca, [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    sign((iskey(#mdhamank, [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    sign((iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    sign((iskey(#justinyo, [d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    sign((iskey(#dsduena, [db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    sign((iskey(#mfredrik, [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]),
    sign((open(#mfredrik, <secret.txt>)), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]),
    sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]),
    sign((open(#mdhamank, <secret.txt>)), [d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af]),
    sign((open(#pdoan, <secret.txt>)), [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f]),
    sign((open(#justinyo, <secret.txt>)), [db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f]),
    sign((open(#dsduena, <secret.txt>)), [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]) |- (#root says open(#pdoan, <secret.txt>))""")

    t = ThenTactic(
            [
                # Get the key certifications in gamma
                # Get iskey(root, pkr)
                SignTactic(parse('sign(iskey(#root, [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                CertTactic(Agent('#root'), Key('[2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get iskey(mfred, pkm)
                SignTactic(parse('sign((iskey(#mfredrik, [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                CertTactic(Agent('#mfredrik'), Key('[d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get iskey(duena, pkd)
                SignTactic(parse('sign((iskey(#dsduena, [db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                CertTactic(Agent('#dsduena'), Key('[db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get iskey(justin, pkj)
                SignTactic(parse('sign((iskey(#justinyo, [d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                CertTactic(Agent('#justinyo'), Key('[d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                # Get iskey(dhamank, pkdh)
                SignTactic(parse('sign((iskey(#mdhamank, [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f])), [43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f])'), Agent('#ca')),
                CertTactic(Agent('#mdhamank'), Key('[71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f]'), Agent('#ca'), Key('[43:c9:43:e6:28:37:ec:23:1a:bc:83:c6:eb:87:e8:6f]')),
                
                # Change the right hand side to aff
                RuleTactic(saysRightRule),

                # Get the delegation formula by #root in gamma
                SignTactic(parse("sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                RuleTactic(saysLeftRule),

                # Get open(#mfred, <secret.txt>) in gamma
                SignTactic(parse("sign((open(#mfredrik, <secret.txt>)), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                RuleTactic(saysLeftRule),

                # Get open(#dsduena, <secret.txt>) in gamma
                InstantiateForallTactic(set([Agent("#mfredrik")])),
                InstantiateForallTactic(set([Resource("<secret.txt>")])),
                RuleTactic(impLeftAffRule),
                InstantiateForallTactic(set([Agent("#dsduena")])),
                SignTactic(parse("sign((open(#dsduena, <secret.txt>)), [d3:c6:2a:1b:63:20:f9:75:fd:1b:ec:fc:ad:19:f1:47])"), Agent("#mfredrik")),
                RuleTactic(impLeftAffRule),
                # RuleTactic(saysLeftRule),

                # Get open(#justinyo, <secret.txt>) in gamma
                # Get the delegation formula by #root in gamma
                SignTactic(parse("sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                RuleTactic(saysLeftRule),
                InstantiateForallTactic(set([Agent("#dsduena")])),
                InstantiateForallTactic(set([Resource("<secret.txt>")])),
                RuleTactic(impLeftAffRule),
                InstantiateForallTactic(set([Agent("#justinyo")])),
                SignTactic(parse("sign((open(#justinyo, <secret.txt>)), [db:b2:b9:b7:01:83:9c:3e:7d:ac:c4:87:00:cd:79:2f])"), Agent("#dsduena")),
                RuleTactic(impLeftAffRule),
                # RuleTactic(saysLeftRule),

                # Get open(#mdhamank, <secret.txt>) in gamma
                # Get the delegation formula by #root in gamma
                SignTactic(parse("sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                RuleTactic(saysLeftRule),
                InstantiateForallTactic(set([Agent("#justinyo")])),
                InstantiateForallTactic(set([Resource("<secret.txt>")])),
                RuleTactic(impLeftAffRule),
                InstantiateForallTactic(set([Agent("#mdhamank")])),
                SignTactic(parse("sign((open(#mdhamank, <secret.txt>)), [d2:15:e7:01:be:ef:fa:e6:08:ca:6c:bd:90:f4:1b:af])"), Agent("#justinyo")),
                RuleTactic(impLeftAffRule),
                # RuleTactic(saysLeftRule),

                # Get open(#pdoan, <secret.txt>) in gamma
                # Get the delegation formula by #root in gamma
                SignTactic(parse("sign(((@A . ((@R . ((open(A, R) -> (@B . (((A says open(B, R)) -> open(B, R)))))))))), [2b:8f:e8:9b:8b:76:37:a7:3b:7e:85:49:9d:87:7b:3b])"), Agent("#root")),
                RuleTactic(saysLeftRule),
                InstantiateForallTactic(set([Agent("#mdhamank")])),
                InstantiateForallTactic(set([Resource("<secret.txt>")])),
                RuleTactic(impLeftAffRule),
                InstantiateForallTactic(set([Agent("#pdoan")])),
                SignTactic(parse("sign((open(#pdoan, <secret.txt>)), [71:14:55:85:b1:59:ae:76:b2:56:4b:36:09:01:f5:3f])"), Agent("#mdhamank")),
                RuleTactic(impLeftAffRule),
                # RuleTactic(saysLeftRule),

                RuleTactic(affRule),
                
                # Close the branches
                RuleTactic(identityRule)
            ]
        )
        
    for pf in t.apply(seq):
        # print()
        # print("pf =", pf)
        print(stringify(pf, pf_width=50))
    pass
