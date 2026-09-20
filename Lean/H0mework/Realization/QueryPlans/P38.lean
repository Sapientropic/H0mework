/-
  Proposition 38: runtime generator coverage for generative queries.

  Proposition 30 proves Kleisli algebra/calculus completeness relative to a
  declared vocabulary of primitive predicates and generator relations.  This
  file turns that boundary into a first-class certificate:

    if every runtime generator is covered by a declared relation, then every
    runtime generative query plan compiles into the Kleisli query algebra and
    into the matching range-restricted calculus, preserving denotation.

  This is not a claim that model proposals or source reopen are automatically
  correct.  It is the exact bridge from runtime mechanism-faithfulness
  certificates to the already-proved query completeness theorem.
-/

import H0mework.Realization.QueryPlans.P30

/-! ## Runtime generator plans -/

/-- Runtime generative plans: the same safe Boolean/set fragment as
`KleisliFieldAlg`, plus an explicit `generate` node for a runtime generator.
`bind` remains the general query-as-generation operation. -/
inductive RuntimeGenerativePlan (Row Base RuntimeGen : Type*) where
  | empty
  | top
  | base : Base -> RuntimeGenerativePlan Row Base RuntimeGen
  | union :
      RuntimeGenerativePlan Row Base RuntimeGen ->
      RuntimeGenerativePlan Row Base RuntimeGen ->
      RuntimeGenerativePlan Row Base RuntimeGen
  | inter :
      RuntimeGenerativePlan Row Base RuntimeGen ->
      RuntimeGenerativePlan Row Base RuntimeGen ->
      RuntimeGenerativePlan Row Base RuntimeGen
  | diff :
      RuntimeGenerativePlan Row Base RuntimeGen ->
      RuntimeGenerativePlan Row Base RuntimeGen ->
      RuntimeGenerativePlan Row Base RuntimeGen
  | select :
      (Row -> Prop) ->
      RuntimeGenerativePlan Row Base RuntimeGen ->
      RuntimeGenerativePlan Row Base RuntimeGen
  | generate :
      RuntimeGen ->
      RuntimeGenerativePlan Row Base RuntimeGen ->
      RuntimeGenerativePlan Row Base RuntimeGen
  | bind :
      RuntimeGenerativePlan Row Base RuntimeGen ->
      (Row -> RuntimeGenerativePlan Row Base RuntimeGen) ->
      RuntimeGenerativePlan Row Base RuntimeGen

namespace RuntimeGenerativePlan

/-- Denotation of runtime generative plans. -/
def eval {Row Base RuntimeGen : Type*}
    (env : Base -> Row -> Prop)
    (runtimeRel : RuntimeGen -> Row -> Row -> Prop) :
    RuntimeGenerativePlan Row Base RuntimeGen -> Row -> Prop
  | empty, _row => False
  | top, _row => True
  | base b, row => env b row
  | union p q, row => eval env runtimeRel p row \/ eval env runtimeRel q row
  | inter p q, row => eval env runtimeRel p row /\ eval env runtimeRel q row
  | diff p q, row => eval env runtimeRel p row /\ ¬ eval env runtimeRel q row
  | select predicate q, row => predicate row /\ eval env runtimeRel q row
  | generate generator q, row =>
      exists source, eval env runtimeRel q source /\
        runtimeRel generator source row
  | bind q k, row =>
      exists source, eval env runtimeRel q source /\
        eval env runtimeRel (k source) row

end RuntimeGenerativePlan

/-! ## Coverage certificate -/

/-- A runtime generator coverage certificate.  It says every runtime generator
is represented by a declared relation in the Kleisli vocabulary. -/
structure RuntimeGeneratorCoverage (RuntimeGen Gen Row : Type*) where
  toDeclared : RuntimeGen -> Gen
  runtimeRel : RuntimeGen -> Row -> Row -> Prop
  declaredRel : Gen -> Row -> Row -> Prop
  covers :
    forall generator source target,
      declaredRel (toDeclared generator) source target <->
        runtimeRel generator source target

/-! ## Compilation to the proved Kleisli query algebra -/

/-- Compile a covered runtime plan into `KleisliFieldAlg`. -/
def runtimePlanToKleisli {Row Base RuntimeGen Gen : Type*}
    (coverage : RuntimeGeneratorCoverage RuntimeGen Gen Row) :
    RuntimeGenerativePlan Row Base RuntimeGen -> KleisliFieldAlg Row Base
  | RuntimeGenerativePlan.empty => KleisliFieldAlg.empty
  | RuntimeGenerativePlan.top => KleisliFieldAlg.top
  | RuntimeGenerativePlan.base b => KleisliFieldAlg.base b
  | RuntimeGenerativePlan.union p q =>
      KleisliFieldAlg.union (runtimePlanToKleisli coverage p)
        (runtimePlanToKleisli coverage q)
  | RuntimeGenerativePlan.inter p q =>
      KleisliFieldAlg.inter (runtimePlanToKleisli coverage p)
        (runtimePlanToKleisli coverage q)
  | RuntimeGenerativePlan.diff p q =>
      KleisliFieldAlg.diff (runtimePlanToKleisli coverage p)
        (runtimePlanToKleisli coverage q)
  | RuntimeGenerativePlan.select predicate q =>
      KleisliFieldAlg.select predicate (runtimePlanToKleisli coverage q)
  | RuntimeGenerativePlan.generate generator q =>
      KleisliFieldAlg.namedImage coverage.declaredRel
        (coverage.toDeclared generator) (runtimePlanToKleisli coverage q)
  | RuntimeGenerativePlan.bind q k =>
      KleisliFieldAlg.bind (runtimePlanToKleisli coverage q)
        (fun source => runtimePlanToKleisli coverage (k source))

/-- THEOREM 1: covered runtime plans compile denotation-preservingly into the
Kleisli/generative query algebra. -/
theorem runtimePlanToKleisli_sound {Row Base RuntimeGen Gen : Type*}
    (coverage : RuntimeGeneratorCoverage RuntimeGen Gen Row)
    (env : Base -> Row -> Prop) :
    forall q row,
      KleisliFieldAlg.eval env (runtimePlanToKleisli coverage q) row <->
        RuntimeGenerativePlan.eval env coverage.runtimeRel q row := by
  intro q
  induction q with
  | empty =>
      intro row
      rfl
  | top =>
      intro row
      rfl
  | base b =>
      intro row
      rfl
  | union p q ihp ihq =>
      intro row
      simp [runtimePlanToKleisli, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.eval, ihp row, ihq row]
  | inter p q ihp ihq =>
      intro row
      simp [runtimePlanToKleisli, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.eval, ihp row, ihq row]
  | diff p q ihp ihq =>
      intro row
      simp [runtimePlanToKleisli, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.eval, ihp row, ihq row]
  | select predicate q ih =>
      intro row
      simp [runtimePlanToKleisli, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.eval, ih row]
  | generate generator q ih =>
      intro row
      simp [runtimePlanToKleisli, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.namedImage, KleisliFieldAlg.image,
        KleisliFieldAlg.eval, ih, coverage.covers generator]
  | bind q k ihq ihk =>
      intro row
      simp [runtimePlanToKleisli, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.eval, ihq, ihk]

/-- THEOREM 2: covered runtime plans are expressible by Kleisli algebra queries. -/
theorem runtimeGenerativePlan_expressible_by_kleisli_of_generatorCoverage
    {Row Base RuntimeGen Gen : Type*}
    (coverage : RuntimeGeneratorCoverage RuntimeGen Gen Row)
    (env : Base -> Row -> Prop)
    (q : RuntimeGenerativePlan Row Base RuntimeGen) :
    exists alg, forall row,
      KleisliFieldAlg.eval env alg row <->
        RuntimeGenerativePlan.eval env coverage.runtimeRel q row := by
  exact ⟨runtimePlanToKleisli coverage q,
    runtimePlanToKleisli_sound coverage env q⟩

/-- THEOREM 3: covered runtime plans are expressible by the matching
range-restricted calculus. -/
theorem runtimeGenerativePlan_expressible_by_calc_of_generatorCoverage
    {Row Base RuntimeGen Gen : Type*}
    (coverage : RuntimeGeneratorCoverage RuntimeGen Gen Row)
    (env : Base -> Row -> Prop)
    (q : RuntimeGenerativePlan Row Base RuntimeGen) :
    exists formula, forall row,
      KleisliFieldCalc.eval env formula row <->
        RuntimeGenerativePlan.eval env coverage.runtimeRel q row := by
  let alg := runtimePlanToKleisli coverage q
  refine ⟨kleisliAlgToCalc alg, ?_⟩
  intro row
  exact (kleisliAlgToCalc_sound env alg row).trans
    (runtimePlanToKleisli_sound coverage env q row)

/-!
  Boundary:
  - Completeness is relative to the coverage certificate.  If a runtime
    generator has no declared relation, this theorem deliberately does not
    apply.
  - The theorem is denotational.  It does not price source reopen, candidate
    generation, or model calls; Proposition 39 turns those into explicit
    external budgets.
-/
