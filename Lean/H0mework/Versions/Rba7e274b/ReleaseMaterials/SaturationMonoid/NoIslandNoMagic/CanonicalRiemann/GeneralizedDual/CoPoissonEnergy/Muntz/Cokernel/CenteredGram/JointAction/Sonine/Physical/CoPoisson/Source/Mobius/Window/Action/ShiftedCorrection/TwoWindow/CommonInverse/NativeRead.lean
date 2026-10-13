import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.NativeRead
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory OriginalJointFluxSource
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
def JointSource.Laws {coordinate : BurnolCompletedMellinCoordinate} {h : ℝ}
    (source : JointSource coordinate h) : Prop :=
  (type_of% source.lowerAction) ∧ (type_of% source.upperAction) ∧
  (type_of% source.lowerPhysical) ∧ (type_of% source.upperPhysical) ∧
  (type_of% source.jointPrice) ∧ (type_of% source.forcingAction) ∧
  (type_of% source.inverseSource) ∧ (type_of% source.partnerSource) ∧
  (type_of% source.lowerSource) ∧ (type_of% source.upperSource)

theorem JointSource.consume_laws {coordinate : BurnolCompletedMellinCoordinate} {h : ℝ}
    (source : JointSource coordinate h) : source.Laws :=
  ⟨source.lowerAction,source.upperAction,source.lowerPhysical,source.upperPhysical,source.jointPrice,source.forcingAction,
    source.inverseSource,source.partnerSource,source.lowerSource,source.upperSource⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_native_common_inverse_read (ordinal : Nat) (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
        (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
      OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
        (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
      inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
        (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal).1.2=
      -(generatedJointSource (Prior.coordinate observation nontrivial half) h nonnegative).price+
      inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
        (FiniteMobiusResolventFlux.D (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.inheritedIncrement observation nontrivial half depth ordinal+
          _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal)) := by
  rw [generated_joint_source_price]
  exact OriginalTwoWindowInverseForcing.actual_native_full_forcing_action_read observation nontrivial half depth ordinal h nonnegative bounded

theorem consume_actual_native_common_inverse_read (ordinal : Nat) :
    (type_of% (actual_native_common_inverse_read observation nontrivial half depth ordinal (Real.log stageZeroSonineQ)
      (by apply Real.log_nonneg;change 1≤Real.sqrt 3;exact Real.one_le_sqrt.mpr (by norm_num))
      ((le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small))) ∧
    (type_of% (original_fixed_residual_common_inverse_price observation nontrivial half)) ∧
    (generatedJointSource (Prior.coordinate observation nontrivial half) (Real.log stageZeroSonineQ)
      (by apply Real.log_nonneg;change 1≤Real.sqrt 3;exact Real.one_le_sqrt.mpr (by norm_num))).Laws ∧
    (type_of% (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_defect_whole observation nontrivial half depth ordinal)) ∧
    (type_of% (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_defect_next observation nontrivial half depth ordinal)) ∧
    (type_of% (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_action_payment observation nontrivial half depth ordinal)) ∧
    (type_of% (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_source_word_inventory observation nontrivial half depth ordinal)) ∧
    (type_of% (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_math_boundary_in_born observation nontrivial half depth ordinal)) := by
  let source:=generatedJointSource (Prior.coordinate observation nontrivial half) (Real.log stageZeroSonineQ)
    (by apply Real.log_nonneg;change 1≤Real.sqrt 3;exact Real.one_le_sqrt.mpr (by norm_num))
  exact ⟨actual_native_common_inverse_read observation nontrivial half depth ordinal _
      (by apply Real.log_nonneg;change 1≤Real.sqrt 3;exact Real.one_le_sqrt.mpr (by norm_num))
      ((le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small),
    original_fixed_residual_common_inverse_price observation nontrivial half,
    source.consume_laws,
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_defect_whole observation nontrivial half depth ordinal,
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_defect_next observation nontrivial half depth ordinal,
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_action_payment observation nontrivial half depth ordinal,
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_source_word_inventory observation nontrivial half depth ordinal,
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_math_boundary_in_born observation nontrivial half depth ordinal⟩

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
