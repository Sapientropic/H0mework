import H0mework.Versions.X.Fock.HistoryConditional.StabilityMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalStream

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (observation values born bornObservation count)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

abbrev Data := (Field parity → ℝ) × (Field parity → SourceJointClockGraph.Carrier)

def seed (depth : Nat) : Data :=
  (fun value => if observation 0 depth 0 = value then 1 else 0,
   fun value => if observation 0 depth 0 = value then values 0 0 else 0)

def advance (bound depth : Nat) (previous : Data) : Data :=
  (fun value => previous.1 value + if bornObservation bound depth = value then 1 else 0,
   fun value => if bornObservation bound depth = value then
     previous.2 value + ((previous.1 value + 1 : ℝ) : ℂ)⁻¹ • (born bound - previous.2 value)
   else previous.2 value)

def generate (depth : Nat) : Nat → Data :=
  Nat.rec (seed depth) (fun bound previous => advance bound depth previous)

theorem generated_next (bound depth : Nat) : generate depth (bound + 1) = advance bound depth (generate depth bound) := rfl

theorem seed_count (depth : Nat) : (seed depth).1 = count 0 depth := by
  funext value
  rw [SourceConditionalInnovation.count_sum]
  change (if observation 0 depth 0 = value then (1 : ℝ) else 0) =
    ∑ i : Fin 1, if observation 0 depth i = value then (1 : ℝ) else 0
  exact (Fin.sum_univ_one (fun i : Fin 1 => if observation 0 depth i = value then (1 : ℝ) else 0)).symm

theorem seed_decoder (depth : Nat) : (seed depth).2 = SourceConditionalInnovation.decoder 0 depth := by
  funext value
  by_cases same : observation 0 depth 0 = value
  · have supported : value ∈ ((historyPMF 0).map (observation 0 depth)).support := by
      rw [← same]
      exact SourceWeightedRecovery.observed_supported _ _ 0 (SourceUniformFibreVariance.source_positive 0 0)
    rw [SourceConditionalInnovation.decoder_mean 0 depth value supported]
    have constant : ∀ i : Fin (0 + 1), observation 0 depth i = value := by
      intro i
      have zero : i = 0 := Fin.eq_zero i
      exact zero ▸ same
    rw [SourceConditionalInventory.conditional,
      SourceWeightedRecovery.ObservationRefinement.conditional_constant _ _ value constant supported]
    change (if observation 0 depth 0 = value then values 0 0 else 0) =
      ∑ i : Fin 1, ((historyPMF 0 i).toReal : ℂ) • values 0 i
    rw [if_pos same, Fin.sum_univ_one, historyPMF_apply]
    norm_num
  · have absent : value ∉ ((historyPMF 0).map (observation 0 depth)).support := by
      intro supported
      obtain ⟨i, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have zero : i = 0 := Fin.eq_zero i
      exact same (zero ▸ equal)
    rw [SourceConditionalInnovation.decoder_missing 0 depth value absent]
    exact if_neg same

theorem advance_source (bound depth : Nat) :
    advance bound depth (count bound depth, SourceConditionalInnovation.decoder bound depth) =
      (count (bound + 1) depth, SourceConditionalInnovation.decoder (bound + 1) depth) := by
  apply Prod.ext
  · funext value
    exact (SourceConditionalInnovation.count_append bound depth value).symm
  · exact SourceConditionalInnovation.update_decoder bound depth

theorem generated_source (bound depth : Nat) :
    generate depth bound = (count bound depth, SourceConditionalInnovation.decoder bound depth) := by
  induction bound with
  | zero => exact Prod.ext (seed_count depth) (seed_decoder depth)
  | succ bound previous => rw [generated_next, previous, advance_source]

end
end SourceConditionalStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
