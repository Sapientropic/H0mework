import H0mework.Versions.X.Fock.HistoryConditional.CopyHistoryMaterialRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeHistory

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton
local instance : MeasurableSpace (Finset Nat.Primes) := ⊤
local instance : MeasurableSingletonClass (Finset Nat.Primes) := ⟨fun _ => trivial⟩

theorem head_read (bound state : Nat) : (read bound state).headD ∅ = SourceCopyNativeKeys.key (state + 1) := by
  simp [read, List.ofFn_succ]

theorem full_information_zero (runtime : LivingRuntimeState process) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
      (fun actor : Actors runtime => read (inventoryBound runtime) actor.val)
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) = 0 :=
  (SourceConditionalNativePosterior.information_iff_recovers runtime (read (inventoryBound runtime))).mpr
    (decoder_recovers runtime)

theorem snapshot_gap_positive (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) :
    0 < SourceConditionalMergeLoss.gap runtime (read (inventoryBound runtime)) (fun samples => samples.headD ∅) := by
  let left : Actors runtime := ⟨1, by omega⟩
  let right : Actors runtime := ⟨2, by omega⟩
  apply SourceConditionalMergeLoss.gap_positive_of_collision runtime (read (inventoryBound runtime)) (fun samples => samples.headD ∅) left right
  · rw [head_read, head_read]
    change SourceCopyNativeKeys.key 2 = SourceCopyNativeKeys.key 3
    decide
  · intro same
    have recovered := read_injective (inventoryBound runtime) same
    have wrong := congrArg Fin.val recovered
    change (1 : Nat) = 2 at wrong
    omega

theorem snapshot_information_positive (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) :
    0 < SourceConditionalInformationLoss.amount runtime (read (inventoryBound runtime)) (fun samples => samples.headD ∅) :=
  (SourceConditionalInformationLoss.amount_positive_iff_gap runtime _ _).mpr (snapshot_gap_positive runtime enough)

theorem snapshot_budget (runtime : LivingRuntimeState process) :
    SourceConditionalInventory.cost (inventoryBound runtime)
      (fun actor : Actors runtime => SourceCopyNativeKeys.key (actor.val + 1)) / (inventoryBound runtime + 1 : ℝ) +
      (Real.exp (2 * SourceConditionalInformationLoss.amount runtime (read (inventoryBound runtime)) (fun samples => samples.headD ∅)) - 1) / 12 ≤
        SourceConditionalMergeLoss.gap runtime (read (inventoryBound runtime)) (fun samples => samples.headD ∅) := by
  have paid := SourceConditionalInformationLoss.recovery_budget runtime (read (inventoryBound runtime)) (fun samples => samples.headD ∅)
  simp only [head_read, full_information_zero, zero_add, decoder_recovers,
    ← SourceConditionalInventory.values_original, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero] at paid
  exact paid

end
end SourceCopyNativeHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
