import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMOriginalClockResidueBalance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
open SaturationMonoid.PhysicsCore
open SourcePropagationNativeActionHessian ActualEMAction PreparationVacuumMixedFieldReturn
open scoped Matrix BigOperators

private def auxiliaryTerm (t : NativeJetIndex × NativeJetIndex × ℝ) : Bool :=
  decide (217≤t.1.2.val ∧ 217≤t.2.1.2.val)

theorem actual_native_auxiliary_terms :
    nativeCompleteLiteralTerms.filter auxiliaryTerm=literalGaugeBBTerms := by
  have gravity : literalGravityTerms.filter auxiliaryTerm=[] := by rfl
  have scalar : literalScalarTerms.filter auxiliaryTerm=[] := by rfl
  have dirac : literalDiracTerms.filter auxiliaryTerm=[] := by
    have support : literalDiracTerms.all (fun t => !auxiliaryTerm t)=true := by decide +kernel
    apply List.filter_eq_nil_iff.mpr
    intro t member
    have value := List.all_eq_true.mp support t member
    cases h : auxiliaryTerm t <;> simp [h] at value ⊢
  have gauge : literalGaugeTerms.filter auxiliaryTerm=literalGaugeBBTerms := by
    run_tac
      let proof ← Lean.Meta.mkEqRefl (Lean.mkConst ``literalGaugeBBTerms)
      (← Lean.Elab.Tactic.getMainGoal).assign proof
      Lean.Elab.Tactic.replaceMainGoal []
  rw [nativeCompleteLiteralTerms,List.filter_append,List.filter_append,List.filter_append,
    gravity,scalar,dirac,List.nil_append,List.append_nil,List.append_nil]
  exact gauge

end LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
