import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.CorrectionUpdate
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.NativeRead

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint
open Complex MeasureTheory OriginalJointFluxSource
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open scoped InnerProductSpace

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_native_upper_wave_update_read (ordinal : Nat) (h nextShift : ℝ)
    (nonnegative : 0≤h) (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    inner ℂ (upperWaveNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal).1.1=
      inner ℂ (upperWaveNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.inheritedIncrement observation nontrivial half depth ordinal+_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal) := by
  rw [_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_native_physical_field]
  change inner ℂ _ ((burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half):BurnolL2)+_+_)=_
  rw [add_assoc,inner_add_right,
    actual_wave_update_original_K_read _ observation.mathlibZero h nextShift nonnegative ordered bounded,zero_add]

theorem actual_native_upper_field_update_price (ordinal : Nat) (h nextShift : ℝ)
    (nonnegative : 0≤h) (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    inner ℂ (upperFieldNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal).1.1+
      inner ℂ (upperCorrectionNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half):BurnolL2)=
      inner ℂ (upperFieldNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.inheritedIncrement observation nontrivial half depth ordinal+_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal) := by
  rw [_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_native_physical_field]
  change inner ℂ _ ((burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half):BurnolL2)+_+_)+_=_
  rw [add_assoc,inner_add_right,
    actual_field_update_original_K_price _ observation.mathlibZero h nextShift nonnegative ordered bounded]
  ring

theorem actual_native_upper_defect_update_read (ordinal : Nat) (h nextShift : ℝ) :
    inner ℂ (upperFieldNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal).1.2=
      inner ℂ (upperFieldNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (FiniteMobiusResolventFlux.rankedSourceDefect observation nontrivial half)+
      inner ℂ (upperFieldNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (FiniteMobiusResolventFlux.D (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.inheritedIncrement observation nontrivial half depth ordinal+
          _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal)) :=
  _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_defect_source_consumer observation nontrivial half depth ordinal _

theorem consume_actual_native_upper_update (ordinal : Nat) (h nextShift : ℝ)
    (nonnegative : 0≤h) (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    (type_of% (actual_native_upper_wave_update_read observation nontrivial half depth ordinal h nextShift nonnegative ordered bounded)) ∧
    (type_of% (actual_native_upper_field_update_price observation nontrivial half depth ordinal h nextShift nonnegative ordered bounded)) ∧
    (type_of% (actual_native_upper_defect_update_read observation nontrivial half depth ordinal h nextShift)) ∧
    (type_of% (actual_field_update_projections (Prior.coordinate observation nontrivial half) h nextShift nonnegative ordered)) ∧
    (type_of% (actual_inverse_correction_update (Prior.coordinate observation nontrivial half) h nextShift nonnegative ordered bounded)) ∧
    (type_of% (InverseEuler.consume_actual_native_euler_reaction_read observation nontrivial half depth ordinal)) :=
  ⟨actual_native_upper_wave_update_read observation nontrivial half depth ordinal h nextShift nonnegative ordered bounded,
    actual_native_upper_field_update_price observation nontrivial half depth ordinal h nextShift nonnegative ordered bounded,
    actual_native_upper_defect_update_read observation nontrivial half depth ordinal h nextShift,
    actual_field_update_projections (Prior.coordinate observation nontrivial half) h nextShift nonnegative ordered,
    actual_inverse_correction_update (Prior.coordinate observation nontrivial half) h nextShift nonnegative ordered bounded,
    InverseEuler.consume_actual_native_euler_reaction_read observation nontrivial half depth ordinal⟩

end OriginalCommonInverseForcing.SourceJoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
