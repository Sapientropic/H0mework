import H0mework.Realization.Logic.QuantifiedUpdate
import H0mework.Checks.Realization.OperationRelations

/-! Actual joint witnesses prevent old-shadow choice and spurious history splicing. -/

set_option autoImplicit false

namespace SaturationMonoid.SourceOperationDynamics.Controls

open SourceOperationEffects SourceOperationRelations SourceOperationRelations.Controls
open SourceOperationLogic
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedScalarDifferentialResidual

noncomputable section

abbrev ScalarWord := Formal ScalarValue ScalarVar ()

theorem actual_joint_witnesses_branch_from_one_old_scope :
    oldRead one one (jointWitness one one (0 : ScalarWord)) =
      oldRead one one (jointWitness one one accidentalRelation) ∧
    newRead one one (jointWitness one one (0 : ScalarWord)) ≠
      newRead one one (jointWitness one one accidentalRelation) ∧
    (0 : NewScope (s := ()) one one) ∈ post one one {0} ∧
    q (evaluation (one + one)) accidentalRelation ∈ post one one {0} ∧
    (0 : OldScope (s := ()) one) ∉ pre one one {0} := by
  have oldZero : q (evaluation one) accidentalRelation = 0 :=
    (canonicalResidual_eq_zero_iff _ _).mpr accidental_old_relation_zero
  have newNonzero := actual_increment_generates_nonzero_residual
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change q (evaluation one) (0 : ScalarWord) = q (evaluation one) accidentalRelation
    rw [map_zero, oldZero]
  · change q (evaluation (one + one)) (0 : ScalarWord) ≠
      q (evaluation (one + one)) accidentalRelation
    rw [map_zero]
    exact Ne.symm newNonzero
  · simpa only [map_zero] using source_post one one (0 : ScalarWord) {0} (by simp)
  · exact source_post one one accidentalRelation {0} oldZero
  · intro allZero
    have holds : q (evaluation one) accidentalRelation ∈ pre one one {0} := by
      rw [oldZero]
      exact allZero
    exact newNonzero (source_pre one one accidentalRelation {0} holds)

def variableWord : ScalarWord := Finsupp.single xTerm 1

/-- Each local step has its own actual source. Equal middle shadows do not identify those sources. -/
theorem equal_middle_shadows_do_not_supply_a_single_history_source :
    (0 : Scope (evaluation (s := ()) (0 : Env ScalarValue ScalarVar))) ∈
      postAlong (q (evaluation one)) (q (evaluation (0 : Env ScalarValue ScalarVar))) {0} ∧
    q (evaluation one) variableWord ∈
      postAlong (q (evaluation (0 : Env ScalarValue ScalarVar))) (q (evaluation one)) {0} ∧
    evaluation one variableWord = 1 ∧
    (¬ ∃ source : ScalarWord,
      evaluation one source = 0 ∧
      evaluation (0 : Env ScalarValue ScalarVar) source = 0 ∧
      evaluation one source = 1) := by
  have variableAtZero : evaluation (0 : Env ScalarValue ScalarVar) variableWord = 0 := by
    simp [evaluation, variableWord, xTerm, Expr.eval]
  have variableAtOne : evaluation one variableWord = 1 := by
    simp [evaluation, variableWord, xTerm, one, Expr.eval]
  have middleZero : q (evaluation (0 : Env ScalarValue ScalarVar)) variableWord = 0 :=
    (canonicalResidual_eq_zero_iff _ _).mpr variableAtZero
  refine ⟨?_, ?_, variableAtOne, ?_⟩
  · exact ⟨(0 : ScalarWord), by simp, map_zero _⟩
  · exact ⟨variableWord, middleZero, rfl⟩
  · rintro ⟨source, startsAtZero, _, endsAtOne⟩
    have contradiction := startsAtZero.symm.trans endsAtOne
    norm_num at contradiction

end

end SaturationMonoid.SourceOperationDynamics.Controls
