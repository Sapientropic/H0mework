/-
  Proposition 74: finite cost bounds for stateful generative queries.

  Proposition 73 introduced the combined query object:

      State -> Row -> State -> Prop

  This file supplies the matching finite/materialized complexity skeleton.  A
  finite stateful query evaluates to a finite set of `(row, nextState)` pairs
  for a given input state.  Its structural work bound scans the finite
  `Row × State` transition domain in the `bind` case, so the cost is explicit
  rather than hidden in "field interference".

  Boundary: primitive transitions are still supplied as finite relations, and
  this is worst-case structural accounting.  It does not price source reopen,
  model candidate generation, cache fill/replacement, or the cost of producing
  the finite state/row domains.
-/

import H0mework.Realization.Reflexive.GenerativeAlgebra

/-! ## Finite executable stateful generative algebra -/

/-- A finite executable counterpart of `StatefulGenAlg`, with Boolean guards.
-/
inductive FiniteStatefulGenAlg (State Row Prim : Type*) where
  | empty
  | ret : Row -> FiniteStatefulGenAlg State Row Prim
  | primitive : Prim -> FiniteStatefulGenAlg State Row Prim
  | union : FiniteStatefulGenAlg State Row Prim ->
      FiniteStatefulGenAlg State Row Prim -> FiniteStatefulGenAlg State Row Prim
  | inter : FiniteStatefulGenAlg State Row Prim ->
      FiniteStatefulGenAlg State Row Prim -> FiniteStatefulGenAlg State Row Prim
  | diff : FiniteStatefulGenAlg State Row Prim ->
      FiniteStatefulGenAlg State Row Prim -> FiniteStatefulGenAlg State Row Prim
  | guard : (State -> Row -> State -> Bool) ->
      FiniteStatefulGenAlg State Row Prim -> FiniteStatefulGenAlg State Row Prim
  | bind : FiniteStatefulGenAlg State Row Prim ->
      (Row -> FiniteStatefulGenAlg State Row Prim) ->
        FiniteStatefulGenAlg State Row Prim

namespace FiniteStatefulGenAlg

/-- Pair domain of possible produced rows and next states. -/
def pairDomain {State Row : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row) :
    Finset (Row × State) :=
  rowDomain.product stateDomain

/-- Evaluate a finite stateful query from one current state. -/
def evalFinset {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State)) :
    FiniteStatefulGenAlg State Row Prim -> State -> Finset (Row × State)
  | empty, _x => ∅
  | ret value, x => {(value, x)}
  | primitive p, x => env p x
  | union p q, x =>
      evalFinset stateDomain rowDomain env p x ∪
        evalFinset stateDomain rowDomain env q x
  | inter p q, x =>
      evalFinset stateDomain rowDomain env p x ∩
        evalFinset stateDomain rowDomain env q x
  | diff p q, x =>
      evalFinset stateDomain rowDomain env p x \
        evalFinset stateDomain rowDomain env q x
  | guard predicate q, x =>
      (evalFinset stateDomain rowDomain env q x).filter
        (fun pair => predicate x pair.1 pair.2 = true)
  | bind q k, x =>
      (evalFinset stateDomain rowDomain env q x).biUnion
        (fun pair => evalFinset stateDomain rowDomain env (k pair.1) pair.2)

/-- Instrumented evaluator with a structural operation counter. -/
def evalWithCost {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State)) :
    FiniteStatefulGenAlg State Row Prim -> State -> Finset (Row × State) × Nat
  | empty, _x => (∅, 0)
  | ret value, x => ({(value, x)}, 0)
  | primitive p, x => (env p x, 0)
  | union p q, x =>
      let ep := evalWithCost stateDomain rowDomain env p x
      let eq := evalWithCost stateDomain rowDomain env q x
      (ep.1 ∪ eq.1, ep.2 + eq.2 + ep.1.card + eq.1.card)
  | inter p q, x =>
      let ep := evalWithCost stateDomain rowDomain env p x
      let eq := evalWithCost stateDomain rowDomain env q x
      (ep.1 ∩ eq.1, ep.2 + eq.2 + ep.1.card + eq.1.card)
  | diff p q, x =>
      let ep := evalWithCost stateDomain rowDomain env p x
      let eq := evalWithCost stateDomain rowDomain env q x
      (ep.1 \ eq.1, ep.2 + eq.2 + ep.1.card + eq.1.card)
  | guard predicate q, x =>
      let eq := evalWithCost stateDomain rowDomain env q x
      (eq.1.filter (fun pair => predicate x pair.1 pair.2 = true),
        eq.2 + eq.1.card)
  | bind q k, x =>
      let eq := evalWithCost stateDomain rowDomain env q x
      let branch := fun pair =>
        evalWithCost stateDomain rowDomain env (k pair.1) pair.2
      (eq.1.biUnion (fun pair => (branch pair).1),
        eq.2 + eq.1.card +
          eq.1.sum (fun pair => (branch pair).2 + (branch pair).1.card))

/-- Structural worst-case work bound for a stateful query.  In the `bind` case
the continuation is budgeted over every possible `(row, nextState)` pair in the
finite transition domain. -/
def workBound {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row) :
    FiniteStatefulGenAlg State Row Prim -> Nat
  | empty => 0
  | ret _ => 0
  | primitive _ => 0
  | union p q => workBound stateDomain rowDomain p +
      workBound stateDomain rowDomain q +
      (pairDomain stateDomain rowDomain).card +
      (pairDomain stateDomain rowDomain).card
  | inter p q => workBound stateDomain rowDomain p +
      workBound stateDomain rowDomain q +
      (pairDomain stateDomain rowDomain).card +
      (pairDomain stateDomain rowDomain).card
  | diff p q => workBound stateDomain rowDomain p +
      workBound stateDomain rowDomain q +
      (pairDomain stateDomain rowDomain).card +
      (pairDomain stateDomain rowDomain).card
  | guard _ q => workBound stateDomain rowDomain q +
      (pairDomain stateDomain rowDomain).card
  | bind q k => workBound stateDomain rowDomain q +
      (pairDomain stateDomain rowDomain).card +
      (pairDomain stateDomain rowDomain).sum
        (fun pair => workBound stateDomain rowDomain (k pair.1) +
          (pairDomain stateDomain rowDomain).card)

/-! ## Result soundness and finite-domain containment -/

/-- THEOREM 1: the instrumented evaluator returns the denotational finite
result. -/
theorem evalWithCost_result_eq {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State)) :
    forall q x,
      (evalWithCost stateDomain rowDomain env q x).1 =
        evalFinset stateDomain rowDomain env q x := by
  intro q
  induction q with
  | empty =>
      intro x
      rfl
  | ret value =>
      intro x
      rfl
  | primitive p =>
      intro x
      rfl
  | union p q ihp ihq =>
      intro x
      simp [evalWithCost, evalFinset, ihp x, ihq x]
  | inter p q ihp ihq =>
      intro x
      simp [evalWithCost, evalFinset, ihp x, ihq x]
  | diff p q ihp ihq =>
      intro x
      simp [evalWithCost, evalFinset, ihp x, ihq x]
  | guard predicate q ih =>
      intro x
      simp [evalWithCost, evalFinset, ih x]
  | bind q k ihq ihk =>
      intro x
      simp [evalWithCost, evalFinset, ihq x, ihk]

/-- If primitive transitions, returned rows, and current states are inside the
finite domains, every stateful query result stays inside the finite pair
domain. -/
theorem evalFinset_subset_pairDomain {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv : forall p x, env p x ⊆ pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain) :
    forall q x,
      evalFinset stateDomain rowDomain env q x ⊆
        pairDomain stateDomain rowDomain := by
  intro q
  induction q with
  | empty =>
      intro x pair hpair
      simp [evalFinset] at hpair
  | ret value =>
      intro x pair hpair
      have hpairEq : pair = (value, x) := by
        simpa [evalFinset] using hpair
      subst pair
      simp [pairDomain, hRow value, hCurrent x]
  | primitive p =>
      intro x pair hpair
      exact hEnv p x hpair
  | union p q ihp ihq =>
      intro x pair hpair
      simp [evalFinset] at hpair
      rcases hpair with hpair | hpair
      · exact ihp x hpair
      · exact ihq x hpair
  | inter p q ihp _ihq =>
      intro x pair hpair
      simp [evalFinset] at hpair
      exact ihp x hpair.1
  | diff p q ihp _ihq =>
      intro x pair hpair
      simp [evalFinset] at hpair
      exact ihp x hpair.1
  | guard predicate q ih =>
      intro x pair hpair
      simp [evalFinset] at hpair
      exact ih x hpair.1
  | bind q k ihq ihk =>
      intro x pair hpair
      simp [evalFinset] at hpair
      rcases hpair with ⟨midRow, midState, _hmid, hbranch⟩
      exact ihk midRow midState hbranch

/-- Instrumented results stay inside the finite pair domain. -/
theorem evalWithCost_result_subset_pairDomain {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv : forall p x, env p x ⊆ pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (q : FiniteStatefulGenAlg State Row Prim) (x : State) :
    (evalWithCost stateDomain rowDomain env q x).1 ⊆
      pairDomain stateDomain rowDomain := by
  intro pair hpair
  have hEval :
      pair ∈ evalFinset stateDomain rowDomain env q x := by
    simpa [evalWithCost_result_eq stateDomain rowDomain env q x] using hpair
  exact evalFinset_subset_pairDomain stateDomain rowDomain env hEnv hRow
    hCurrent q x hEval

/-- Instrumented result cardinality is bounded by the finite transition-domain
size. -/
theorem evalWithCost_result_card_le_pairDomain {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv : forall p x, env p x ⊆ pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (q : FiniteStatefulGenAlg State Row Prim) (x : State) :
    (evalWithCost stateDomain rowDomain env q x).1.card ≤
      (pairDomain stateDomain rowDomain).card := by
  exact Finset.card_le_card
    (evalWithCost_result_subset_pairDomain stateDomain rowDomain env hEnv
      hRow hCurrent q x)

/-! ## Structural cost bound -/

/-- THEOREM 2: the instrumented cost is bounded by the structural work bound. -/
theorem evalWithCost_cost_le_workBound {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv : forall p x, env p x ⊆ pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain) :
    forall q x,
      (evalWithCost stateDomain rowDomain env q x).2 ≤
        workBound stateDomain rowDomain q := by
  intro query
  induction query with
  | empty =>
      intro x
      simp [evalWithCost, workBound]
  | ret value =>
      intro x
      simp [evalWithCost, workBound]
  | primitive p =>
      intro x
      simp [evalWithCost, workBound]
  | union p q ihp ihq =>
      intro x
      rcases hp : evalWithCost stateDomain rowDomain env p x with ⟨sp, cp⟩
      rcases hq : evalWithCost stateDomain rowDomain env q x with ⟨sq, cq⟩
      have ihp' : cp ≤ workBound stateDomain rowDomain p := by
        simpa [hp] using ihp x
      have ihq' : cq ≤ workBound stateDomain rowDomain q := by
        simpa [hq] using ihq x
      have hsp : sp.card ≤ (pairDomain stateDomain rowDomain).card := by
        have hsub : sp ⊆ pairDomain stateDomain rowDomain := by
          simpa [hp] using evalWithCost_result_subset_pairDomain
            stateDomain rowDomain env hEnv hRow hCurrent p x
        exact Finset.card_le_card hsub
      have hsq : sq.card ≤ (pairDomain stateDomain rowDomain).card := by
        have hsub : sq ⊆ pairDomain stateDomain rowDomain := by
          simpa [hq] using evalWithCost_result_subset_pairDomain
            stateDomain rowDomain env hEnv hRow hCurrent q x
        exact Finset.card_le_card hsub
      simp [evalWithCost, workBound, hp, hq]
      omega
  | inter p q ihp ihq =>
      intro x
      rcases hp : evalWithCost stateDomain rowDomain env p x with ⟨sp, cp⟩
      rcases hq : evalWithCost stateDomain rowDomain env q x with ⟨sq, cq⟩
      have ihp' : cp ≤ workBound stateDomain rowDomain p := by
        simpa [hp] using ihp x
      have ihq' : cq ≤ workBound stateDomain rowDomain q := by
        simpa [hq] using ihq x
      have hsp : sp.card ≤ (pairDomain stateDomain rowDomain).card := by
        have hsub : sp ⊆ pairDomain stateDomain rowDomain := by
          simpa [hp] using evalWithCost_result_subset_pairDomain
            stateDomain rowDomain env hEnv hRow hCurrent p x
        exact Finset.card_le_card hsub
      have hsq : sq.card ≤ (pairDomain stateDomain rowDomain).card := by
        have hsub : sq ⊆ pairDomain stateDomain rowDomain := by
          simpa [hq] using evalWithCost_result_subset_pairDomain
            stateDomain rowDomain env hEnv hRow hCurrent q x
        exact Finset.card_le_card hsub
      simp [evalWithCost, workBound, hp, hq]
      omega
  | diff p q ihp ihq =>
      intro x
      rcases hp : evalWithCost stateDomain rowDomain env p x with ⟨sp, cp⟩
      rcases hq : evalWithCost stateDomain rowDomain env q x with ⟨sq, cq⟩
      have ihp' : cp ≤ workBound stateDomain rowDomain p := by
        simpa [hp] using ihp x
      have ihq' : cq ≤ workBound stateDomain rowDomain q := by
        simpa [hq] using ihq x
      have hsp : sp.card ≤ (pairDomain stateDomain rowDomain).card := by
        have hsub : sp ⊆ pairDomain stateDomain rowDomain := by
          simpa [hp] using evalWithCost_result_subset_pairDomain
            stateDomain rowDomain env hEnv hRow hCurrent p x
        exact Finset.card_le_card hsub
      have hsq : sq.card ≤ (pairDomain stateDomain rowDomain).card := by
        have hsub : sq ⊆ pairDomain stateDomain rowDomain := by
          simpa [hq] using evalWithCost_result_subset_pairDomain
            stateDomain rowDomain env hEnv hRow hCurrent q x
        exact Finset.card_le_card hsub
      simp [evalWithCost, workBound, hp, hq]
      omega
  | guard predicate q ih =>
      intro x
      rcases hq : evalWithCost stateDomain rowDomain env q x with ⟨sq, cq⟩
      have ihq' : cq ≤ workBound stateDomain rowDomain q := by
        simpa [hq] using ih x
      have hsq : sq.card ≤ (pairDomain stateDomain rowDomain).card := by
        have hsub : sq ⊆ pairDomain stateDomain rowDomain := by
          simpa [hq] using evalWithCost_result_subset_pairDomain
            stateDomain rowDomain env hEnv hRow hCurrent q x
        exact Finset.card_le_card hsub
      simp [evalWithCost, workBound, hq]
      omega
  | bind q k ihq ihk =>
      intro x
      rcases hq : evalWithCost stateDomain rowDomain env q x with ⟨sq, cq⟩
      have ihq' : cq ≤ workBound stateDomain rowDomain q := by
        simpa [hq] using ihq x
      have hsqSub : sq ⊆ pairDomain stateDomain rowDomain := by
        simpa [hq] using evalWithCost_result_subset_pairDomain
          stateDomain rowDomain env hEnv hRow hCurrent q x
      have hsqCard : sq.card ≤ (pairDomain stateDomain rowDomain).card :=
        Finset.card_le_card hsqSub
      have hpoint :
          ∀ pair ∈ sq,
            (evalWithCost stateDomain rowDomain env (k pair.1) pair.2).2 +
              (evalWithCost stateDomain rowDomain env (k pair.1) pair.2).1.card ≤
            workBound stateDomain rowDomain (k pair.1) +
              (pairDomain stateDomain rowDomain).card := by
        intro pair _hpair
        have hcost := ihk pair.1 pair.2
        have hcard := evalWithCost_result_card_le_pairDomain
          stateDomain rowDomain env hEnv hRow hCurrent (k pair.1) pair.2
        omega
      have hsumPoint :
          sq.sum (fun pair =>
            (evalWithCost stateDomain rowDomain env (k pair.1) pair.2).2 +
              (evalWithCost stateDomain rowDomain env (k pair.1) pair.2).1.card) ≤
          sq.sum (fun pair =>
            workBound stateDomain rowDomain (k pair.1) +
              (pairDomain stateDomain rowDomain).card) := by
        exact Finset.sum_le_sum hpoint
      have hsumSubset :
          sq.sum (fun pair =>
            workBound stateDomain rowDomain (k pair.1) +
              (pairDomain stateDomain rowDomain).card) ≤
          (pairDomain stateDomain rowDomain).sum (fun pair =>
            workBound stateDomain rowDomain (k pair.1) +
              (pairDomain stateDomain rowDomain).card) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsqSub (by
          intro pair _hDomain _hNotMem
          exact Nat.zero_le
            (workBound stateDomain rowDomain (k pair.1) +
              (pairDomain stateDomain rowDomain).card))
      simp [evalWithCost, workBound, hq]
      omega

/-!
  Summary:
  - Finite stateful-generative queries have an executable evaluator producing
    `(row, nextState)` pairs.
  - Results stay inside the finite transition domain when primitives, returned
    rows, and current states are domain-covered.
  - The executable cost is bounded by a structural worst-case bound whose
    `bind` case scans all possible intermediate `(row, state)` pairs.

  Remaining boundary:
  - This is worst-case finite-domain accounting.  It does not amortize repeated
    queries and does not price materialization, source reopen, external model
    generation, or cache policy.
-/
