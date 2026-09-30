import H0mework.Fock.CopyGraph.FibreSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphFibreUpdate

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceGeneratedAtomicObservation SourceOwnedObservationHistory
open SourceUniformFibreVariance SourceHistoryGrowth
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead taggedRead oldAction newAction)
open SourceGraphBirth (fresh innovation)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

omit [MeasurableSpace Observed] [MeasurableSingletonClass Observed] in
theorem prior_tag_supported (depth : Nat) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    (read (depth + 1), true) ∈ (observed (historyPMF (depth + 1)) (taggedRead depth read)).support := by
  obtain ⟨actor, _, same⟩ := (PMF.mem_support_map_iff (oldRead depth read) (historyPMF depth) (read (depth + 1))).mp supported
  have tag : taggedRead depth read (includeActor (Nat.le_succ depth) actor) = (read (depth + 1), true) := by
    apply Prod.ext
    · exact same
    · change decide (actor.val < depth + 1) = true
      exact decide_eq_true_eq.mpr actor.isLt
  exact tag ▸ observed_supported (historyPMF (depth + 1)) (taggedRead depth read)
    (includeActor (Nat.le_succ depth) actor) (source_positive (depth + 1) _)

theorem lift_decoder (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (newRead depth read))) :
    SourceGraphRefinement.lift (depth + 1) (taggedRead depth read) Prod.fst value =
      decoderValue (historyPMF (depth + 1)) (taggedRead depth read) (fun atom => value atom.1) :=
  (pullback (historyPMF (depth + 1)) (taggedRead depth read)).injective
    ((SourceGraphRefinement.lift_source (depth + 1) (taggedRead depth read) Prod.fst value).trans
      (SourceGraphRefinement.decoder_source (depth + 1) (taggedRead depth read) Prod.fst value).symm)

theorem lift_at (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (newRead depth read))) (atom : Observed × Bool)
    (supported : atom ∈ (observed (historyPMF (depth + 1)) (taggedRead depth read)).support) :
    SourceGraphRefinement.lift (depth + 1) (taggedRead depth read) Prod.fst value atom = value atom.1 := by
  rw [lift_decoder, decoderValue_at _ _ _ _ supported]

theorem prior_arrival (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : Space (observed (historyPMF (depth + 1)) (taggedRead depth read))) :
    arrival depth index read supported (oldAction depth index read (SourceGraphBirth.priorValue depth read value)) =
      value (read (depth + 1), true) := by
  change ((Real.sqrt (fraction depth (depth + 1)))⁻¹ : ℂ) •
    (evalAtContinuous (observed (historyPMF depth) (oldRead depth read)) (read (depth + 1)) supported)
      (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read)
        (oldAction depth index read (SourceGraphBirth.priorValue depth read value))) = _
  rw [SourceConditionalGraphDecoder.decode_action]
  change ((Real.sqrt (fraction depth (depth + 1)))⁻¹ : ℂ) • SourceGraphBirth.priorValue depth read value (read (depth + 1)) = _
  rw [SourceGraphBirth.priorValue, decoderValue_at _ _ _ _ supported]
  simp only [Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (fraction_pos depth (depth + 1))).ne'), one_mul]

theorem raw_action_decomposition (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (newRead depth read))) :
    newAction depth index read value =
      oldAction depth index read (SourceGraphBirth.priorValue depth read
        (SourceGraphRefinement.lift (depth + 1) (taggedRead depth read) Prod.fst value)) +
      value (read (depth + 1)) • fresh depth index := by
  have original := SourceGraphBirth.action_decomposition depth index read
    (SourceGraphRefinement.lift (depth + 1) (taggedRead depth read) Prod.fst value)
  rw [lift_at depth read value (taggedRead depth read (Fin.last (depth + 1)))
    (observed_supported _ _ (Fin.last (depth + 1)) (source_positive (depth + 1) _))] at original
  have source := (SourceGraphRefinement.action_lift (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (taggedRead depth read) Prod.fst value).symm.trans original
  with_unfolding_all exact source

theorem arrival_raw (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : Space (observed (historyPMF (depth + 1)) (newRead depth read))) :
    arrival depth index read supported (newAction depth index read value) = value (read (depth + 1)) * beta depth index read supported := by
  have original := congrArg (arrival depth index read supported) (raw_action_decomposition depth index read value)
  rw [map_add, map_smul, prior_arrival, lift_at depth read value (read (depth + 1), true) (prior_tag_supported depth read supported)] at original
  rw [original, beta]
  ring

theorem innovation_raw_pairing (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (newRead depth read))) :
    inner ℂ (innovation depth index read) (newAction depth index read value) =
      value (read (depth + 1)) * ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ) := by
  rw [raw_action_decomposition, inner_add_right, SourceGraphBirth.innovation_old_orthogonal, zero_add,
    inner_smul_right, innovation_fresh_pairing]

theorem normal_raw_orthogonal (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : Space (observed (historyPMF (depth + 1)) (newRead depth read))) :
    inner ℂ (normal depth index read supported) (newAction depth index read value) = 0 := by
  rw [normal_pairing, arrival_raw, innovation_raw_pairing]
  field_simp [SourceGraphBirth.denominator_ne_zero depth index read]
  rw [div_self (SourceGraphBirth.denominator_ne_zero depth index read), sub_self, mul_zero]

end
end SourceGraphFibreUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
