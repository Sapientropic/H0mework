/-
  Proposition 31: finite cost algebra for Kleisli generative queries.

  Proposition 30 proves denotational completeness for the multi-step
  generative/Kleisli atom-field query language.  This file gives the matching
  finite-domain cost skeleton:

    * executable queries return a finite result set plus an operation count;
    * `bind q k` evaluates `q`, then evaluates each continuation seeded by a
      materialized source row;
    * the structural work bound sums every possible continuation over the
      finite domain, so it is a worst-case bound independent of which rows a
      particular run happens to produce.

  Boundary: primitive predicate/relation calls are still treated as unit cells,
  and this does not bound the cost of producing the finite domain or source
  reopening candidates.
-/

import H0mework.Realization.QueryPlans.P30

/-! ## Executable finite-domain Kleisli queries -/

/-- Executable finite-domain version of the Kleisli generative query algebra. -/
inductive FiniteKleisliFieldAlg (Row Base : Type*) where
  | empty
  | top
  | base : Base -> FiniteKleisliFieldAlg Row Base
  | union : FiniteKleisliFieldAlg Row Base -> FiniteKleisliFieldAlg Row Base ->
      FiniteKleisliFieldAlg Row Base
  | inter : FiniteKleisliFieldAlg Row Base -> FiniteKleisliFieldAlg Row Base ->
      FiniteKleisliFieldAlg Row Base
  | diff : FiniteKleisliFieldAlg Row Base -> FiniteKleisliFieldAlg Row Base ->
      FiniteKleisliFieldAlg Row Base
  | select : (Row -> Bool) -> FiniteKleisliFieldAlg Row Base ->
      FiniteKleisliFieldAlg Row Base
  | bind : FiniteKleisliFieldAlg Row Base ->
      (Row -> FiniteKleisliFieldAlg Row Base) -> FiniteKleisliFieldAlg Row Base

namespace FiniteKleisliFieldAlg

/-- Finite-set denotation. -/
def evalFinset {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row) :
    FiniteKleisliFieldAlg Row Base -> Finset Row
  | empty => ∅
  | top => domain
  | base b => env b
  | union p q => evalFinset domain env p ∪ evalFinset domain env q
  | inter p q => evalFinset domain env p ∩ evalFinset domain env q
  | diff p q => evalFinset domain env p \ evalFinset domain env q
  | select predicate q =>
      (evalFinset domain env q).filter (fun row => predicate row = true)
  | bind q k =>
      (evalFinset domain env q).biUnion
        (fun source => evalFinset domain env (k source))

/-- Instrumented evaluator.  The bind cost charges for the source rows produced
    by `q`, the continuation cost for each such row, and one linear merge scan
    per continuation result. -/
def evalWithCost {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row) :
    FiniteKleisliFieldAlg Row Base -> Finset Row × Nat
  | empty => (∅, 0)
  | top => (domain, 0)
  | base b => (env b, 0)
  | union p q =>
      let ep := evalWithCost domain env p
      let eq := evalWithCost domain env q
      (ep.1 ∪ eq.1, ep.2 + eq.2 + ep.1.card + eq.1.card)
  | inter p q =>
      let ep := evalWithCost domain env p
      let eq := evalWithCost domain env q
      (ep.1 ∩ eq.1, ep.2 + eq.2 + ep.1.card + eq.1.card)
  | diff p q =>
      let ep := evalWithCost domain env p
      let eq := evalWithCost domain env q
      (ep.1 \ eq.1, ep.2 + eq.2 + ep.1.card + eq.1.card)
  | select predicate q =>
      let eq := evalWithCost domain env q
      (eq.1.filter (fun row => predicate row = true), eq.2 + eq.1.card)
  | bind q k =>
      let eq := evalWithCost domain env q
      let branch := fun source => evalWithCost domain env (k source)
      (eq.1.biUnion (fun source => (branch source).1),
        eq.2 + eq.1.card +
          eq.1.sum (fun source => (branch source).2 + (branch source).1.card))

/-- Structural worst-case work bound over a finite materialized domain.  For a
    bind, the continuation is bounded for every possible domain row, not only
    the rows produced by a particular run. -/
def workBound {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) : FiniteKleisliFieldAlg Row Base -> Nat
  | empty => 0
  | top => 0
  | base _ => 0
  | union p q => workBound domain p + workBound domain q +
      domain.card + domain.card
  | inter p q => workBound domain p + workBound domain q +
      domain.card + domain.card
  | diff p q => workBound domain p + workBound domain q +
      domain.card + domain.card
  | select _ q => workBound domain q + domain.card
  | bind q k => workBound domain q + domain.card +
      domain.sum (fun source => workBound domain (k source) + domain.card)

/-- THEOREM 1: the instrumented evaluator returns the denotational result. -/
theorem evalWithCost_result_eq {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row) :
    forall q : FiniteKleisliFieldAlg Row Base,
      (evalWithCost domain env q).1 = evalFinset domain env q := by
  intro q
  induction q with
  | empty =>
      rfl
  | top =>
      rfl
  | base b =>
      rfl
  | union p q ihp ihq =>
      simp [evalWithCost, evalFinset, ihp, ihq]
  | inter p q ihp ihq =>
      simp [evalWithCost, evalFinset, ihp, ihq]
  | diff p q ihp ihq =>
      simp [evalWithCost, evalFinset, ihp, ihq]
  | select predicate q ih =>
      simp [evalWithCost, evalFinset, ih]
  | bind q k ihq ihk =>
      simp [evalWithCost, evalFinset, ihq, ihk]

/-- If primitive base relations are subsets of the materialized domain, every
    Kleisli query result remains inside that domain. -/
theorem evalFinset_subset_domain {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (hEnv : forall b, env b ⊆ domain) :
    forall q : FiniteKleisliFieldAlg Row Base, evalFinset domain env q ⊆ domain := by
  intro q
  induction q with
  | empty =>
      intro x hx
      simp [evalFinset] at hx
  | top =>
      intro x hx
      simpa [evalFinset] using hx
  | base b =>
      intro x hx
      exact hEnv b hx
  | union p q ihp ihq =>
      intro x hx
      simp [evalFinset] at hx
      rcases hx with hx | hx
      · exact ihp hx
      · exact ihq hx
  | inter p q ihp _ihq =>
      intro x hx
      simp [evalFinset] at hx
      exact ihp hx.1
  | diff p q ihp _ihq =>
      intro x hx
      simp [evalFinset] at hx
      exact ihp hx.1
  | select predicate q ih =>
      intro x hx
      simp [evalFinset] at hx
      exact ih hx.1
  | bind q k ihq ihk =>
      intro x hx
      simp [evalFinset] at hx
      rcases hx with ⟨source, _hsource, hxBranch⟩
      exact ihk source hxBranch

/-- Instrumented results also stay inside the finite domain. -/
theorem evalWithCost_result_subset_domain {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteKleisliFieldAlg Row Base) :
    (evalWithCost domain env q).1 ⊆ domain := by
  intro x hx
  have hxEval : x ∈ evalFinset domain env q := by
    simpa [evalWithCost_result_eq domain env q] using hx
  exact evalFinset_subset_domain domain env hEnv q hxEval

/-- Result cardinality is bounded by the finite domain size. -/
theorem evalWithCost_result_card_le_domain {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteKleisliFieldAlg Row Base) :
    (evalWithCost domain env q).1.card ≤ domain.card := by
  exact Finset.card_le_card (evalWithCost_result_subset_domain domain env hEnv q)

/-- THEOREM 2: the instrumented cost is bounded by the structural work bound. -/
theorem evalWithCost_cost_le_workBound {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (hEnv : forall b, env b ⊆ domain) :
    forall q : FiniteKleisliFieldAlg Row Base,
      (evalWithCost domain env q).2 ≤ workBound domain q := by
  intro query
  induction query with
  | empty =>
      simp [evalWithCost, workBound]
  | top =>
      simp [evalWithCost, workBound]
  | base b =>
      simp [evalWithCost, workBound]
  | union p q ihp ihq =>
      rcases hp : evalWithCost domain env p with ⟨sp, cp⟩
      rcases hq : evalWithCost domain env q with ⟨sq, cq⟩
      have ihp' : cp ≤ workBound domain p := by simpa [hp] using ihp
      have ihq' : cq ≤ workBound domain q := by simpa [hq] using ihq
      have hsp : sp.card ≤ domain.card := by
        have hsub : sp ⊆ domain := by
          simpa [hp] using evalWithCost_result_subset_domain domain env hEnv p
        exact Finset.card_le_card hsub
      have hsq : sq.card ≤ domain.card := by
        have hsub : sq ⊆ domain := by
          simpa [hq] using evalWithCost_result_subset_domain domain env hEnv q
        exact Finset.card_le_card hsub
      simp [evalWithCost, workBound, hp, hq]
      omega
  | inter p q ihp ihq =>
      rcases hp : evalWithCost domain env p with ⟨sp, cp⟩
      rcases hq : evalWithCost domain env q with ⟨sq, cq⟩
      have ihp' : cp ≤ workBound domain p := by simpa [hp] using ihp
      have ihq' : cq ≤ workBound domain q := by simpa [hq] using ihq
      have hsp : sp.card ≤ domain.card := by
        have hsub : sp ⊆ domain := by
          simpa [hp] using evalWithCost_result_subset_domain domain env hEnv p
        exact Finset.card_le_card hsub
      have hsq : sq.card ≤ domain.card := by
        have hsub : sq ⊆ domain := by
          simpa [hq] using evalWithCost_result_subset_domain domain env hEnv q
        exact Finset.card_le_card hsub
      simp [evalWithCost, workBound, hp, hq]
      omega
  | diff p q ihp ihq =>
      rcases hp : evalWithCost domain env p with ⟨sp, cp⟩
      rcases hq : evalWithCost domain env q with ⟨sq, cq⟩
      have ihp' : cp ≤ workBound domain p := by simpa [hp] using ihp
      have ihq' : cq ≤ workBound domain q := by simpa [hq] using ihq
      have hsp : sp.card ≤ domain.card := by
        have hsub : sp ⊆ domain := by
          simpa [hp] using evalWithCost_result_subset_domain domain env hEnv p
        exact Finset.card_le_card hsub
      have hsq : sq.card ≤ domain.card := by
        have hsub : sq ⊆ domain := by
          simpa [hq] using evalWithCost_result_subset_domain domain env hEnv q
        exact Finset.card_le_card hsub
      simp [evalWithCost, workBound, hp, hq]
      omega
  | select predicate q ih =>
      rcases hq : evalWithCost domain env q with ⟨sq, cq⟩
      have ihq' : cq ≤ workBound domain q := by simpa [hq] using ih
      have hsq : sq.card ≤ domain.card := by
        have hsub : sq ⊆ domain := by
          simpa [hq] using evalWithCost_result_subset_domain domain env hEnv q
        exact Finset.card_le_card hsub
      simp [evalWithCost, workBound, hq]
      omega
  | bind q k ihq ihk =>
      rcases hq : evalWithCost domain env q with ⟨sq, cq⟩
      have ihq' : cq ≤ workBound domain q := by simpa [hq] using ihq
      have hsqSub : sq ⊆ domain := by
        simpa [hq] using evalWithCost_result_subset_domain domain env hEnv q
      have hsqCard : sq.card ≤ domain.card := Finset.card_le_card hsqSub
      have hpoint :
          ∀ source ∈ sq,
            (evalWithCost domain env (k source)).2 +
              (evalWithCost domain env (k source)).1.card ≤
            workBound domain (k source) + domain.card := by
        intro source _hsource
        have hcost := ihk source
        have hcard := evalWithCost_result_card_le_domain domain env hEnv (k source)
        omega
      have hsumPoint :
          sq.sum (fun source =>
            (evalWithCost domain env (k source)).2 +
              (evalWithCost domain env (k source)).1.card) ≤
          sq.sum (fun source => workBound domain (k source) + domain.card) := by
        exact Finset.sum_le_sum hpoint
      have hsumSubset :
          sq.sum (fun source => workBound domain (k source) + domain.card) ≤
          domain.sum (fun source => workBound domain (k source) + domain.card) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsqSub (by
          intro source _hDomain _hNotMem
          exact Nat.zero_le (workBound domain (k source) + domain.card))
      simp [evalWithCost, workBound, hq]
      omega

/-!
  Summary:
  - Finite Kleisli/generative queries have an executable evaluator.
  - Results stay inside the materialized domain when primitive relations do.
  - The cost is bounded by a structural worst-case `workBound`.
  - `bind` contributes one scan over produced source rows plus, in the bound,
    every possible domain-row continuation.

  Remaining boundary:
  - This is worst-case finite-domain accounting.  It does not provide an
    amortized cache theorem, nor does it price source reopen or model proposal
    generation.
-/
