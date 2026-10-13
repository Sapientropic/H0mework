import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWard.Feedback

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace Pairing
export OriginalRieszFinitePairing (forcing_pair_source sourcePairRead evaluatorSource kernelSelfSource fixed_residual_source)
end Pairing

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem fixed_source_shift_nonnegative : 0 ≤ Prior.sourceShift := by
  change 0 ≤ Real.log stageZeroSonineQ
  apply Real.log_nonneg
  change 1 ≤ Real.sqrt 3
  exact Real.one_le_sqrt.mpr (by norm_num)

theorem original_self_source_pair :
    inner ℂ (Prior.originalK observation nontrivial half) (finiteForcePair observation nontrivial half) =
      -star (Pairing.sourcePairRead (Prior.coordinate observation nontrivial half) Prior.sourceShift) := by
  have generated := Pairing.forcing_pair_source (Prior.coordinate observation nontrivial half)
    Prior.sourceShift fixed_source_shift_nonnegative
  change inner ℂ (finiteForcePair observation nontrivial half) (Prior.originalK observation nontrivial half) = _ at generated
  calc
    _ = star (inner ℂ (finiteForcePair observation nontrivial half) (Prior.originalK observation nontrivial half)) :=
      (inner_conj_symm _ _).symm
    _ = _ := by rw [generated, star_neg]

-- The installed right-half receipt is the same source-coordinate restriction.
theorem original_fixed_residual_source :
    -(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual =
      Pairing.evaluatorSource (Prior.coordinate observation nontrivial half) Prior.sourceShift := by
  rw [installedOriginalKReceiptAt_eq_source]
  exact Pairing.fixed_residual_source (Prior.coordinate observation nontrivial half) observation.mathlibZero

theorem actual_self_K_pair_read (ordinal : Nat) :
    inner ℂ (Prior.originalK observation nontrivial half) (actualSelfRead observation nontrivial half depth ordinal).1 =
      (-star (Pairing.sourcePairRead (Prior.coordinate observation nontrivial half) Prior.sourceShift)) *
        inner ℂ (Prior.originalK observation nontrivial half) (Prior.originalK observation nontrivial half) := by
  rw [actual_self_K_price, original_self_source_pair]

theorem actual_self_FourierK_pair_read (ordinal : Nat) :
    inner ℂ (Prior.originalFourierK observation nontrivial half) (actualSelfRead observation nontrivial half depth ordinal).2 =
      (-star (Pairing.sourcePairRead (Prior.coordinate observation nontrivial half) Prior.sourceShift)) *
        inner ℂ (Prior.originalFourierK observation nontrivial half) (Prior.originalFourierK observation nontrivial half) := by
  rw [actual_self_FourierK_price]
  have unitary := fourierL2.inner_map_map (Prior.originalK observation nontrivial half)
    (finiteForcePair observation nontrivial half)
  change inner ℂ (Prior.originalFourierK observation nontrivial half)
    (fourierL2 (finiteForcePair observation nontrivial half)) = _ at unitary
  rw [unitary, original_self_source_pair]

-- Each physical face retains its own unit price in the exact original residual read.
theorem actual_fixed_residual_K_read (ordinal : Nat) :
    (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual) *
      inner ℂ (Prior.originalK observation nontrivial half) (Prior.originalK observation nontrivial half) =
    ((pairedMellinTranslationCharacter (Prior.coordinate observation nontrivial half).value Prior.sourceShift -
      pairedMellinTranslationCharacter (star (Prior.coordinate observation nontrivial half).value) Prior.sourceShift) *
        Pairing.kernelSelfSource (Prior.coordinate observation nontrivial half)) *
      inner ℂ (Prior.originalK observation nontrivial half) (Prior.originalK observation nontrivial half) -
        (1 / 2 : ℂ) * inner ℂ (Prior.originalK observation nontrivial half)
          (actualSelfRead observation nontrivial half depth ordinal).1 := by
  rw [original_fixed_residual_source, actual_self_K_pair_read]
  unfold Pairing.evaluatorSource
  ring

theorem actual_fixed_residual_FourierK_read (ordinal : Nat) :
    (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual) *
      inner ℂ (Prior.originalFourierK observation nontrivial half) (Prior.originalFourierK observation nontrivial half) =
    ((pairedMellinTranslationCharacter (Prior.coordinate observation nontrivial half).value Prior.sourceShift -
      pairedMellinTranslationCharacter (star (Prior.coordinate observation nontrivial half).value) Prior.sourceShift) *
        Pairing.kernelSelfSource (Prior.coordinate observation nontrivial half)) *
      inner ℂ (Prior.originalFourierK observation nontrivial half) (Prior.originalFourierK observation nontrivial half) -
        (1 / 2 : ℂ) * inner ℂ (Prior.originalFourierK observation nontrivial half)
          (actualSelfRead observation nontrivial half depth ordinal).2 := by
  rw [original_fixed_residual_source, actual_self_FourierK_pair_read]
  unfold Pairing.evaluatorSource
  ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
