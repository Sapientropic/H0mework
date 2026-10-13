import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.JointRead
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.NativeUpdate

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

theorem actual_native_update_joint_price (ordinal : Nat) (h nextShift : ℝ)
    (nonnegative : 0≤h) (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    inner ℂ (upperWaveNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
      (burnolMultiplicativeDilation nextShift (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal).1.1+
        burnolMultiplicativeDilation (-nextShift) (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal).1.1)=
      upperUpdateJointSourcePrice (Prior.coordinate observation nontrivial half) h nextShift+
      inner ℂ (upperWaveNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (burnolMultiplicativeDilation nextShift (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.inheritedIncrement observation nontrivial half depth ordinal+_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal)+
          burnolMultiplicativeDilation (-nextShift) (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.inheritedIncrement observation nontrivial half depth ordinal+_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal)) := by
  rw [_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_native_physical_field]
  change inner ℂ _ (burnolMultiplicativeDilation nextShift ((burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half):BurnolL2)+_+_)+
    burnolMultiplicativeDilation (-nextShift) ((burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half):BurnolL2)+_+_))=_
  simp only [map_add,inner_add_right]
  have paid:=actual_update_original_K_joint_action (Prior.coordinate observation nontrivial half)
    observation.mathlibZero h nextShift nonnegative ordered bounded
  simp only [inner_add_right] at paid
  linear_combination paid

theorem actual_native_field_counting_price (ordinal : Nat) (h nextShift : ℝ)
    (nonnegative : 0≤h) (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    inner ℂ (upperFieldNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal).1.1=
      -(upperHigherSourcePrice (Prior.coordinate observation nontrivial half) nextShift-
          upperHigherSourcePrice (Prior.coordinate observation nontrivial half) h)+
      inner ℂ (upperFieldNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.inheritedIncrement observation nontrivial half depth ordinal+
          _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal) := by
  rw [_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_native_physical_field]
  change inner ℂ _ ((burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half):BurnolL2)+_+_)=_
  rw [add_assoc,inner_add_right,actual_field_update_higher_price _ observation.mathlibZero h nextShift nonnegative ordered bounded]

theorem actual_native_effect_joint_read (ordinal : Nat) (h nextShift : ℝ) :
    inner ℂ (upperWaveNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
      (burnolMultiplicativeDilation nextShift (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualEffect observation nontrivial half depth ordinal).1.1+
        burnolMultiplicativeDilation (-nextShift) (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualEffect observation nontrivial half depth ordinal).1.1)=
      inner ℂ (upperWaveNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (burnolMultiplicativeDilation nextShift (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal)+
          burnolMultiplicativeDilation (-nextShift) (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal)) := by
  rfl

theorem actual_native_defect_joint_read (ordinal : Nat) (h nextShift : ℝ) :
    inner ℂ (upperWaveNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
      (burnolMultiplicativeDilation nextShift (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal).1.2+
        burnolMultiplicativeDilation (-nextShift) (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal).1.2)=
      inner ℂ (upperWaveNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (burnolMultiplicativeDilation nextShift (FiniteMobiusResolventFlux.rankedSourceDefect observation nontrivial half)+
          burnolMultiplicativeDilation (-nextShift) (FiniteMobiusResolventFlux.rankedSourceDefect observation nontrivial half))+
      inner ℂ (upperWaveNativeUpdate (Prior.coordinate observation nontrivial half) h nextShift)
        (burnolMultiplicativeDilation nextShift (FiniteMobiusResolventFlux.D (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.inheritedIncrement observation nontrivial half depth ordinal+_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal))+
          burnolMultiplicativeDilation (-nextShift) (FiniteMobiusResolventFlux.D (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.inheritedIncrement observation nontrivial half depth ordinal+_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal))) := by
  rw [_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction.actual_native_ranked_defect]
  simp only [map_add,inner_add_right]
  ring

theorem consume_actual_native_joint_source_update (ordinal : Nat) (h nextShift : ℝ)
    (nonnegative : 0≤h) (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    (type_of% (actual_native_update_joint_price observation nontrivial half depth ordinal h nextShift nonnegative ordered bounded)) ∧
    (type_of% (actual_native_field_counting_price observation nontrivial half depth ordinal h nextShift nonnegative ordered bounded)) ∧
    (type_of% (actual_native_effect_joint_read observation nontrivial half depth ordinal h nextShift)) ∧
    (type_of% (actual_native_defect_joint_read observation nontrivial half depth ordinal h nextShift)) ∧
    (type_of% (actual_upper_first_source_energy (Prior.coordinate observation nontrivial half) nextShift (nonnegative.trans ordered) bounded)) ∧
    (type_of% (actual_correction_update_higher_price (Prior.coordinate observation nontrivial half) h nextShift nonnegative ordered)) ∧
    (type_of% (consume_actual_native_upper_update observation nontrivial half depth ordinal h nextShift nonnegative ordered bounded)) :=
  ⟨actual_native_update_joint_price observation nontrivial half depth ordinal h nextShift nonnegative ordered bounded,
    actual_native_field_counting_price observation nontrivial half depth ordinal h nextShift nonnegative ordered bounded,
    actual_native_effect_joint_read observation nontrivial half depth ordinal h nextShift,
    actual_native_defect_joint_read observation nontrivial half depth ordinal h nextShift,
    actual_upper_first_source_energy (Prior.coordinate observation nontrivial half) nextShift (nonnegative.trans ordered) bounded,
    actual_correction_update_higher_price (Prior.coordinate observation nontrivial half) h nextShift nonnegative ordered,
    consume_actual_native_upper_update observation nontrivial half depth ordinal h nextShift nonnegative ordered bounded⟩

end OriginalCommonInverseForcing.SourceJoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

