/-
  Proposition 132: lifting the named Bool/Prop bridge to whole finite plans.

  P129 supplies the mechanism-faithfulness bridge for one primitive generator
  transition:

      finiteRuntimeRelProp domain runtimeRel g source target
        <-> coverage.runtimeRel g source target

  This file lifts that pointwise bridge through the full runtime generative
  syntax.  The result is the missing denotational seam for named finite
  materialized plans: the executable finite result set is exactly the named
  Prop-valued runtime-plan denotation after compiling the finite plan into the
  domain-restricted runtime syntax.

  This does not add new query power.  It closes a proof plumbing gap: once the
  runtime supplies the P129 transition bridge, it applies to the whole query
  tree, not merely to individual generator edges.
-/

import H0mework.Realization.Query.P129

/-! ## Runtime-plan relation congruence -/

namespace RuntimeGenerativePlan

variable {Row Base RuntimeGen : Type*}

/-- THEOREM 1: runtime-plan denotation is congruent in the primitive generator
relation.  If two runtime relations agree pointwise, every runtime plan has the
same denotation under both. -/
theorem eval_rel_congr
    (env : Base -> Row -> Prop)
    (rel₁ rel₂ : RuntimeGen -> Row -> Row -> Prop)
    (hrel : forall generator source target,
      rel₁ generator source target <-> rel₂ generator source target) :
    forall q row,
      RuntimeGenerativePlan.eval env rel₁ q row <->
        RuntimeGenerativePlan.eval env rel₂ q row := by
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
      simp [RuntimeGenerativePlan.eval, ihp row, ihq row]
  | inter p q ihp ihq =>
      intro row
      simp [RuntimeGenerativePlan.eval, ihp row, ihq row]
  | diff p q ihp ihq =>
      intro row
      simp [RuntimeGenerativePlan.eval, ihp row, ihq row]
  | select predicate q ih =>
      intro row
      simp [RuntimeGenerativePlan.eval, ih row]
  | generate generator q ih =>
      intro row
      constructor
      · rintro ⟨source, hq, hgen⟩
        exact ⟨source, (ih source).mp hq,
          (hrel generator source row).mp hgen⟩
      · rintro ⟨source, hq, hgen⟩
        exact ⟨source, (ih source).mpr hq,
          (hrel generator source row).mpr hgen⟩
  | bind q k ihq ihk =>
      intro row
      constructor
      · rintro ⟨source, hq, hk⟩
        exact ⟨source, (ihq source).mp hq, (ihk source row).mp hk⟩
      · rintro ⟨source, hq, hk⟩
        exact ⟨source, (ihq source).mpr hq, (ihk source row).mpr hk⟩

end RuntimeGenerativePlan

/-! ## Named finite plan denotation bridge -/

namespace NamedFiniteRuntimeRelationBridge

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}

/-- THEOREM 2: the pointwise named Bool/Prop bridge lifts to any compiled
finite runtime plan. -/
theorem runtimePlan_eval_iff_named
    (B : NamedFiniteRuntimeRelationBridge coverage domain runtimeRel)
    (q : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
    (row : Row) :
    RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        (finiteRuntimeRelProp domain runtimeRel)
        (finiteRuntimePlanToRuntimePlan domain q) row <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain q) row := by
  exact RuntimeGenerativePlan.eval_rel_congr
    (finiteRuntimeEnvProp env)
    (finiteRuntimeRelProp domain runtimeRel)
    coverage.runtimeRel
    (fun generator source target =>
      B.relates_exactly generator source target)
    (finiteRuntimePlanToRuntimePlan domain q) row

end NamedFiniteRuntimeRelationBridge

namespace NamedFiniteGenerativeDatabaseCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}
variable {budget : ExternalOracleBudget Row Base}
variable {q : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator}
variable {coldCost allowance n : Nat}

/-- THEOREM 3: the finite executable result set is exactly the named
Prop-valued runtime-plan denotation for the compiled finite plan. -/
theorem finite_eval_iff_named_runtime_eval
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain q) row := by
  calc
    row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q <->
        RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
          (finiteRuntimeRelProp domain runtimeRel)
          (finiteRuntimePlanToRuntimePlan domain q) row :=
      finiteRuntimePlanToRuntimePlan_sound domain env runtimeRel q row
    _ <->
        RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
          coverage.runtimeRel
          (finiteRuntimePlanToRuntimePlan domain q) row :=
      C.relationBridge.runtimePlan_eval_iff_named q row

/-- THEOREM 4: the named runtime denotation of the compiled finite plan is
sound for finite executable membership. -/
theorem named_runtime_eval_sound_for_finite
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    {row : Row}
    (h :
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain q) row) :
    row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q :=
  (C.finite_eval_iff_named_runtime_eval row).mpr h

/-- THEOREM 5: finite executable membership is complete for the named runtime
denotation of the compiled finite plan. -/
theorem finite_complete_for_named_runtime_eval
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    {row : Row}
    (h : row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q) :
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain q) row :=
  (C.finite_eval_iff_named_runtime_eval row).mp h

/-- THEOREM 6: the finite Kleisli query carried by the named finite
certificate also denotes the named runtime interpretation of the compiled
finite plan. -/
theorem finite_kleisli_iff_named_runtime_eval
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    (row : Row) :
    KleisliFieldAlg.eval (finiteRuntimeEnvProp env)
        C.finiteDb.completenessCost.kleisliAlg row <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain q) row := by
  exact (C.finite_kleisli_complete row).trans
    (C.finite_eval_iff_named_runtime_eval row)

/-- THEOREM 7: the finite calculus formula carried by the named finite
certificate denotes the same named runtime interpretation of the compiled
finite plan. -/
theorem finite_calc_iff_named_runtime_eval
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    (row : Row) :
    KleisliFieldCalc.eval (finiteRuntimeEnvProp env)
        C.finiteDb.completenessCost.calcFormula row <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain q) row := by
  exact (C.finite_calc_complete row).trans
    (C.finite_eval_iff_named_runtime_eval row)

end NamedFiniteGenerativeDatabaseCertificate

/-!
  Summary:
  - `RuntimeGenerativePlan.eval_rel_congr` proves the generic structural fact:
    runtime-plan denotation respects pointwise equality of generator relations.
  - A `NamedFiniteRuntimeRelationBridge` therefore lifts from one generator
    edge to every compiled finite runtime query tree.
  - A `NamedFiniteGenerativeDatabaseCertificate` now exposes the exact result
    theorem users actually care about: executable finite membership iff named
    Prop-valued runtime denotation.
-/
