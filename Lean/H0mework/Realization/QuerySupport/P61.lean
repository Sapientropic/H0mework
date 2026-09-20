/-
  Proposition 61: three-way completeness for covered generative queries.

  Proposition 30 proves the Kleisli/generative atom-field algebra and the
  range-restricted calculus mutually preserve denotation.  Proposition 38
  proves that a runtime generative plan compiles into that algebra/calculus
  when every runtime generator is covered by a declared relation.

  This file closes the loop in the other direction: every Kleisli algebra query
  and every range-restricted calculus formula is also expressible as a runtime
  generative plan.  Thus the covered runtime syntax, the Kleisli algebra, and
  the calculus are mutually expressive over the same primitive atom-field
  vocabulary.

  Boundary: this is still relative completeness.  Runtime `generate` nodes
  require a `RuntimeGeneratorCoverage` certificate before they can be compiled
  to the declared Kleisli vocabulary.  The theorem does not say every external
  model proposal or source reopen operation has such a certificate.
-/

import H0mework.Realization.QueryPlans.P38

/-! ## Compiling Kleisli algebra back to runtime syntax -/

/-- Embed a Kleisli/generative algebra query into runtime-plan syntax.

The embedding does not use runtime `generate`; it uses only the common Boolean,
selection, and `bind` fragment.  This gives the missing reverse direction from
the proved algebra/calculus language back to the executable runtime-shaped
syntax.
-/
def kleisliAlgToRuntimePlan {Row Base RuntimeGen : Type*} :
    KleisliFieldAlg Row Base -> RuntimeGenerativePlan Row Base RuntimeGen
  | KleisliFieldAlg.empty => RuntimeGenerativePlan.empty
  | KleisliFieldAlg.top => RuntimeGenerativePlan.top
  | KleisliFieldAlg.base b => RuntimeGenerativePlan.base b
  | KleisliFieldAlg.union p q =>
      RuntimeGenerativePlan.union (kleisliAlgToRuntimePlan p)
        (kleisliAlgToRuntimePlan q)
  | KleisliFieldAlg.inter p q =>
      RuntimeGenerativePlan.inter (kleisliAlgToRuntimePlan p)
        (kleisliAlgToRuntimePlan q)
  | KleisliFieldAlg.diff p q =>
      RuntimeGenerativePlan.diff (kleisliAlgToRuntimePlan p)
        (kleisliAlgToRuntimePlan q)
  | KleisliFieldAlg.select predicate q =>
      RuntimeGenerativePlan.select predicate (kleisliAlgToRuntimePlan q)
  | KleisliFieldAlg.bind q k =>
      RuntimeGenerativePlan.bind (kleisliAlgToRuntimePlan q)
        (fun source => kleisliAlgToRuntimePlan (k source))

/-- THEOREM 1: embedding Kleisli algebra into runtime-plan syntax preserves
denotation for any runtime generator relation. -/
theorem kleisliAlgToRuntimePlan_sound {Row Base RuntimeGen : Type*}
    (env : Base -> Row -> Prop)
    (runtimeRel : RuntimeGen -> Row -> Row -> Prop) :
    forall q row,
      RuntimeGenerativePlan.eval env runtimeRel
          (kleisliAlgToRuntimePlan q) row <->
        KleisliFieldAlg.eval env q row := by
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
      simp [kleisliAlgToRuntimePlan, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.eval, ihp row, ihq row]
  | inter p q ihp ihq =>
      intro row
      simp [kleisliAlgToRuntimePlan, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.eval, ihp row, ihq row]
  | diff p q ihp ihq =>
      intro row
      simp [kleisliAlgToRuntimePlan, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.eval, ihp row, ihq row]
  | select predicate q ih =>
      intro row
      simp [kleisliAlgToRuntimePlan, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.eval, ih row]
  | bind q k ihq ihk =>
      intro row
      simp [kleisliAlgToRuntimePlan, RuntimeGenerativePlan.eval,
        KleisliFieldAlg.eval, ihq, ihk]

/-- THEOREM 2: every Kleisli/generative algebra query is expressible as a
runtime generative plan. -/
theorem kleisliAlg_expressible_by_runtimePlan {Row Base RuntimeGen : Type*}
    (env : Base -> Row -> Prop)
    (runtimeRel : RuntimeGen -> Row -> Row -> Prop)
    (q : KleisliFieldAlg Row Base) :
    exists p : RuntimeGenerativePlan Row Base RuntimeGen,
      forall row,
        RuntimeGenerativePlan.eval env runtimeRel p row <->
          KleisliFieldAlg.eval env q row := by
  exact ⟨kleisliAlgToRuntimePlan q,
    kleisliAlgToRuntimePlan_sound env runtimeRel q⟩

/-! ## Compiling range-restricted calculus back to runtime syntax -/

/-- Compile a range-restricted calculus formula to runtime syntax via the
already-proved calculus-to-Kleisli translation. -/
def kleisliCalcToRuntimePlan {Row Base RuntimeGen : Type*}
    (f : KleisliFieldCalc Row Base) : RuntimeGenerativePlan Row Base RuntimeGen :=
  kleisliAlgToRuntimePlan (kleisliCalcToAlg f)

/-- THEOREM 3: compiling range-restricted calculus to runtime syntax preserves
denotation. -/
theorem kleisliCalcToRuntimePlan_sound {Row Base RuntimeGen : Type*}
    (env : Base -> Row -> Prop)
    (runtimeRel : RuntimeGen -> Row -> Row -> Prop)
    (f : KleisliFieldCalc Row Base) (row : Row) :
    RuntimeGenerativePlan.eval env runtimeRel
        (kleisliCalcToRuntimePlan f) row <->
      KleisliFieldCalc.eval env f row := by
  exact
    (kleisliAlgToRuntimePlan_sound env runtimeRel (kleisliCalcToAlg f) row).trans
      (kleisliCalcToAlg_sound env f row)

/-- THEOREM 4: every range-restricted calculus formula is expressible as a
runtime generative plan. -/
theorem kleisliCalc_expressible_by_runtimePlan {Row Base RuntimeGen : Type*}
    (env : Base -> Row -> Prop)
    (runtimeRel : RuntimeGen -> Row -> Row -> Prop)
    (f : KleisliFieldCalc Row Base) :
    exists p : RuntimeGenerativePlan Row Base RuntimeGen,
      forall row,
        RuntimeGenerativePlan.eval env runtimeRel p row <->
          KleisliFieldCalc.eval env f row := by
  exact ⟨kleisliCalcToRuntimePlan f,
    kleisliCalcToRuntimePlan_sound env runtimeRel f⟩

/-! ## Closed three-way completeness -/

/-- A compact certificate that a runtime query, a Kleisli algebra query, and a
range-restricted calculus formula all denote the same predicate. -/
structure GenerativeQueryEquivalence
    {Row Base RuntimeGen : Type*}
    (env : Base -> Row -> Prop)
    (runtimeRel : RuntimeGen -> Row -> Row -> Prop) where
  runtimePlan : RuntimeGenerativePlan Row Base RuntimeGen
  kleisliAlg : KleisliFieldAlg Row Base
  calcFormula : KleisliFieldCalc Row Base
  kleisli_iff_runtime :
    forall row,
      KleisliFieldAlg.eval env kleisliAlg row <->
        RuntimeGenerativePlan.eval env runtimeRel runtimePlan row
  calc_iff_runtime :
    forall row,
      KleisliFieldCalc.eval env calcFormula row <->
        RuntimeGenerativePlan.eval env runtimeRel runtimePlan row
  runtime_iff_kleisli :
    forall row,
      RuntimeGenerativePlan.eval env runtimeRel runtimePlan row <->
        KleisliFieldAlg.eval env kleisliAlg row
  runtime_iff_calc :
    forall row,
      RuntimeGenerativePlan.eval env runtimeRel runtimePlan row <->
        KleisliFieldCalc.eval env calcFormula row

/-- THEOREM 5: a covered runtime plan has a three-way runtime/Kleisli/calculus
equivalence certificate. -/
def coveredRuntimePlanGenerativeQueryEquivalence
    {Row Base RuntimeGen Gen : Type*}
    (coverage : RuntimeGeneratorCoverage RuntimeGen Gen Row)
    (env : Base -> Row -> Prop)
    (q : RuntimeGenerativePlan Row Base RuntimeGen) :
    GenerativeQueryEquivalence env coverage.runtimeRel where
  runtimePlan := q
  kleisliAlg := runtimePlanToKleisli coverage q
  calcFormula := kleisliAlgToCalc (runtimePlanToKleisli coverage q)
  kleisli_iff_runtime :=
    runtimePlanToKleisli_sound coverage env q
  calc_iff_runtime := by
    intro row
    exact (kleisliAlgToCalc_sound env (runtimePlanToKleisli coverage q) row).trans
      (runtimePlanToKleisli_sound coverage env q row)
  runtime_iff_kleisli := by
    intro row
    exact (runtimePlanToKleisli_sound coverage env q row).symm
  runtime_iff_calc := by
    intro row
    exact ((kleisliAlgToCalc_sound env
      (runtimePlanToKleisli coverage q) row).trans
      (runtimePlanToKleisli_sound coverage env q row)).symm

/-- THEOREM 6: the covered runtime syntax, the Kleisli/generative algebra, and
the range-restricted calculus are mutually expressive over the same denotation.

This is the Codd-style completeness statement for the current atom-field
generative fragment: runtime plans compile into algebra/calculus when generator
coverage is supplied, and algebra/calculus compile back into runtime syntax
through the shared Boolean/selection/bind core.
-/
theorem covered_runtime_kleisli_calc_mutual_completeness
    {Row Base RuntimeGen Gen : Type*}
    (coverage : RuntimeGeneratorCoverage RuntimeGen Gen Row)
    (env : Base -> Row -> Prop) :
    (forall q : RuntimeGenerativePlan Row Base RuntimeGen,
      exists alg : KleisliFieldAlg Row Base,
        forall row,
          KleisliFieldAlg.eval env alg row <->
            RuntimeGenerativePlan.eval env coverage.runtimeRel q row) /\
    (forall alg : KleisliFieldAlg Row Base,
      exists q : RuntimeGenerativePlan Row Base RuntimeGen,
        forall row,
          RuntimeGenerativePlan.eval env coverage.runtimeRel q row <->
            KleisliFieldAlg.eval env alg row) /\
    (forall q : RuntimeGenerativePlan Row Base RuntimeGen,
      exists formula : KleisliFieldCalc Row Base,
        forall row,
          KleisliFieldCalc.eval env formula row <->
            RuntimeGenerativePlan.eval env coverage.runtimeRel q row) /\
    (forall formula : KleisliFieldCalc Row Base,
      exists q : RuntimeGenerativePlan Row Base RuntimeGen,
        forall row,
          RuntimeGenerativePlan.eval env coverage.runtimeRel q row <->
            KleisliFieldCalc.eval env formula row) := by
  constructor
  · intro q
    exact runtimeGenerativePlan_expressible_by_kleisli_of_generatorCoverage
      coverage env q
  constructor
  · intro alg
    exact kleisliAlg_expressible_by_runtimePlan env coverage.runtimeRel alg
  constructor
  · intro q
    exact runtimeGenerativePlan_expressible_by_calc_of_generatorCoverage
      coverage env q
  · intro formula
    exact kleisliCalc_expressible_by_runtimePlan env coverage.runtimeRel formula

/-- THEOREM 7: compiling a covered runtime query to Kleisli and then embedding
that algebra query back into runtime syntax preserves the original runtime
denotation. -/
theorem runtime_kleisli_runtime_roundtrip_sound
    {Row Base RuntimeGen Gen : Type*}
    (coverage : RuntimeGeneratorCoverage RuntimeGen Gen Row)
    (env : Base -> Row -> Prop)
    (q : RuntimeGenerativePlan Row Base RuntimeGen) (row : Row) :
    RuntimeGenerativePlan.eval env coverage.runtimeRel
        (kleisliAlgToRuntimePlan (runtimePlanToKleisli coverage q)) row <->
      RuntimeGenerativePlan.eval env coverage.runtimeRel q row := by
  exact
    (kleisliAlgToRuntimePlan_sound env coverage.runtimeRel
      (runtimePlanToKleisli coverage q) row).trans
      (runtimePlanToKleisli_sound coverage env q row)

/-- THEOREM 8: compiling a covered runtime query through calculus and then back
to runtime syntax preserves the original runtime denotation. -/
theorem runtime_calc_runtime_roundtrip_sound
    {Row Base RuntimeGen Gen : Type*}
    (coverage : RuntimeGeneratorCoverage RuntimeGen Gen Row)
    (env : Base -> Row -> Prop)
    (q : RuntimeGenerativePlan Row Base RuntimeGen) (row : Row) :
    RuntimeGenerativePlan.eval env coverage.runtimeRel
        (kleisliCalcToRuntimePlan
          (kleisliAlgToCalc (runtimePlanToKleisli coverage q))) row <->
      RuntimeGenerativePlan.eval env coverage.runtimeRel q row := by
  exact
    (kleisliCalcToRuntimePlan_sound env coverage.runtimeRel
      (kleisliAlgToCalc (runtimePlanToKleisli coverage q)) row).trans
      ((kleisliAlgToCalc_sound env
        (runtimePlanToKleisli coverage q) row).trans
        (runtimePlanToKleisli_sound coverage env q row))

/-!
  Summary:
  - Runtime generative plans, Kleisli/generative atom-field algebra, and
    range-restricted calculus are now mutually expressive, relative to runtime
    generator coverage.
  - The reverse direction matters: the proved algebra/calculus languages are
    not merely analysis targets for runtime queries; they can be represented
    again in runtime-shaped syntax.
  - This strengthens the query-completeness story from one-way compilation
    slices to a closed three-language fragment.

  Remaining boundary:
  - This is not full relational completeness for source schemas, joins,
    aggregation, recursion, or unrestricted quantification.
  - It is not a mechanism-faithfulness theorem for uncovered external
    generators.  The coverage certificate is still the honest gate.
  - It is not an amortized complexity theorem; finite/materialized cost remains
    the job of Propositions 31/39/47/49/50.
-/
