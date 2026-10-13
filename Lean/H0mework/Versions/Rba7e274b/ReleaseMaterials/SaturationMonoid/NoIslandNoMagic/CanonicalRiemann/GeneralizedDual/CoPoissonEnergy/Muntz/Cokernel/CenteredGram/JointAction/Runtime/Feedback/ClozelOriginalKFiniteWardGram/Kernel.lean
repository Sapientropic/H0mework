import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalTwoDirection.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWardGram
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace Original
export OriginalRieszFiniteSource (forcingIntegral original_finite_action)
end Original
namespace Pairing
export OriginalRieszFinitePairing (forcing_pair_source sourcePairRead evaluatorSource kernelSelfSource original_kernel_self_source)
end Pairing

variable (coordinate : BurnolCompletedMellinCoordinate)

def displacement (shift : ℝ) : BurnolL2 :=
  Original.forcingIntegral coordinate shift +
    (fullMellinTranslationCharacter (star coordinate.value) shift - 1) •
      (burnolCompletedMellinRieszVector coordinate : BurnolL2)

theorem displacement_action (shift : ℝ) :
    displacement coordinate shift =
      burnolMultiplicativeDilation shift (burnolCompletedMellinRieszVector coordinate : BurnolL2) -
        (burnolCompletedMellinRieszVector coordinate : BurnolL2) := by
  rw [Original.original_finite_action]
  unfold displacement
  module

def sourceGram (left right : ℝ) : ℂ :=
  inner ℂ (displacement coordinate left) (displacement coordinate right)

def sourceEnergy (shift : ℝ) : ℂ := sourceGram coordinate shift shift

theorem displacement_negative (shift : ℝ) :
    displacement coordinate (-shift) =
      -burnolMultiplicativeDilation (-shift) (displacement coordinate shift) := by
  rw [displacement_action, displacement_action, map_sub, burnolMultiplicativeDilation_add,
    neg_add_cancel, burnolMultiplicativeDilation_zero]
  abel

theorem source_energy_negative (shift : ℝ) : sourceEnergy coordinate (-shift) = sourceEnergy coordinate shift := by
  change inner ℂ (displacement coordinate (-shift)) (displacement coordinate (-shift)) = _
  rw [displacement_negative, inner_neg_left, inner_neg_right, neg_neg]
  exact (burnolMultiplicativeDilation (-shift)).inner_map_map _ _

theorem source_energy_fourier (shift : ℝ) :
    inner ℂ (fourierL2 (displacement coordinate shift)) (fourierL2 (displacement coordinate shift)) =
      sourceEnergy coordinate shift := fourierL2.inner_map_map _ _

theorem source_energy_real (shift : ℝ) : (sourceEnergy coordinate shift).im = 0 := by
  exact inner_self_im (𝕜 := ℂ) (displacement coordinate shift)

theorem source_energy_nonnegative (shift : ℝ) : 0 ≤ (sourceEnergy coordinate shift).re := by
  exact inner_self_nonneg (𝕜 := ℂ) (x := displacement coordinate shift)

theorem source_energy_norm (shift : ℝ) :
    (sourceEnergy coordinate shift).re = ‖displacement coordinate shift‖ ^ 2 := by
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (displacement coordinate shift)

theorem source_energy_unit_budget (shift : ℝ) :
    (sourceEnergy coordinate shift).re ≤ 4 * (Pairing.kernelSelfSource coordinate).re := by
  have vectorBound : ‖displacement coordinate shift‖ ≤
      2 * ‖(burnolCompletedMellinRieszVector coordinate : BurnolL2)‖ := by
    rw [displacement_action]
    exact (norm_sub_le _ _).trans (by rw [(burnolMultiplicativeDilation shift).norm_map]; ring_nf; rfl)
  have positive := norm_nonneg (displacement coordinate shift)
  have boundPositive := norm_nonneg (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  rw [source_energy_norm, ← Pairing.original_kernel_self_source]
  have unit : (inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (burnolCompletedMellinRieszVector coordinate : BurnolL2)).re =
      ‖(burnolCompletedMellinRieszVector coordinate : BurnolL2)‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [unit]
  nlinarith

private theorem inverse_inner (shift : ℝ) :
    inner ℂ (burnolMultiplicativeDilation shift (burnolCompletedMellinRieszVector coordinate : BurnolL2))
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (burnolMultiplicativeDilation (-shift) (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := by
  have actual := (burnolMultiplicativeDilation shift).inner_map_map
    (burnolCompletedMellinRieszVector coordinate : BurnolL2)
    (burnolMultiplicativeDilation (-shift) (burnolCompletedMellinRieszVector coordinate : BurnolL2))
  rw [burnolMultiplicativeDilation_add, add_neg_cancel, burnolMultiplicativeDilation_zero] at actual
  exact actual

theorem source_force_energy_ward (shift : ℝ) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (Original.forcingIntegral coordinate shift + Original.forcingIntegral coordinate (-shift)) =
    (2 : ℂ) * (1 - pairedMellinTranslationCharacter (star coordinate.value) shift) *
      Pairing.kernelSelfSource coordinate - sourceEnergy coordinate shift := by
  have plus := Original.original_finite_action coordinate shift
  have minus := Original.original_finite_action coordinate (-shift)
  have character := reciprocalMellinTranslationCharacter_eq_negativeShift (star coordinate.value) shift
  have energy : sourceEnergy coordinate shift =
      (2 : ℂ) * Pairing.kernelSelfSource coordinate -
        inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
          (burnolMultiplicativeDilation shift (burnolCompletedMellinRieszVector coordinate : BurnolL2)) -
        inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
          (burnolMultiplicativeDilation (-shift) (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := by
    change inner ℂ (displacement coordinate shift) (displacement coordinate shift) = _
    rw [displacement_action, inner_sub_left, inner_sub_right, inner_sub_right,
      (burnolMultiplicativeDilation shift).inner_map_map, inverse_inner, Pairing.original_kernel_self_source]
    ring
  have plusRead := congrArg (fun value : BurnolL2 => inner ℂ
    (burnolCompletedMellinRieszVector coordinate : BurnolL2) value) plus
  have minusRead := congrArg (fun value : BurnolL2 => inner ℂ
    (burnolCompletedMellinRieszVector coordinate : BurnolL2) value) minus
  simp only [inner_add_right, inner_smul_right, Pairing.original_kernel_self_source] at plusRead minusRead
  rw [energy, inner_add_right]
  unfold pairedMellinTranslationCharacter
  rw [character]
  linear_combination -plusRead - minusRead

theorem source_evaluator_energy_ward (shift : ℝ) (nonnegative : 0 ≤ shift) :
    Pairing.evaluatorSource coordinate shift =
      (pairedMellinTranslationCharacter coordinate.value shift - 1) * Pairing.kernelSelfSource coordinate +
        (1 / 2 : ℂ) * sourceEnergy coordinate shift := by
  have paired := Pairing.forcing_pair_source coordinate shift nonnegative
  have read : inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (Original.forcingIntegral coordinate shift + Original.forcingIntegral coordinate (-shift)) =
      -star (Pairing.sourcePairRead coordinate shift) := by
    calc
      _ = star (inner ℂ (Original.forcingIntegral coordinate shift + Original.forcingIntegral coordinate (-shift))
        (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := (inner_conj_symm _ _).symm
      _ = _ := by rw [paired, star_neg]
  have energy := source_force_energy_ward coordinate shift
  unfold Pairing.evaluatorSource
  linear_combination (1 / 2 : ℂ) * (read - energy)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWardGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
