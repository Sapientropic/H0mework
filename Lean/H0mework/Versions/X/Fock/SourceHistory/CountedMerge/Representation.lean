import H0mework.Versions.X.Fock.SourceHistory.CountedMerge.Table

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedMerge

open SourceRetainedReceiver (Raw Frame rawAt)
open SourceConditionalNativeMerge (inventoryCount)
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

omit [DecidableEq Fine] in
private theorem counted_weight (bound stride : Nat) (frame : Frame Fine bound stride)
    (forget : Fine → Coarse) (coarse : Coarse) (key : Fine) (inside : key ∈ frame.keys) :
    (inventoryCount frame.keys forget bound frame.native coarse : ℚ) *
      SourceRetainedCoarsening.weight bound stride frame forget coarse key =
        if forget key = coarse then ((frame.native key).1 : ℚ) else 0 := by
  by_cases selected : forget key = coarse
  · simp only [SourceRetainedCoarsening.weight, if_pos selected]
    by_cases empty : inventoryCount frame.keys forget bound frame.native coarse = 0
    · have term : (if forget key = coarse then (frame.native key).1 else 0) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun item _ => Nat.zero_le (if forget item = coarse then (frame.native item).1 else 0))).mp empty key inside
      have zero : (frame.native key).1 = 0 := by simpa only [if_pos selected] using term
      simp only [empty, zero, Nat.cast_zero, zero_div, mul_zero]
    · rw [← mul_div_assoc, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr empty)]
  · simp only [SourceRetainedCoarsening.weight, if_neg selected, mul_zero]

private theorem counted_blend (bound stride : Nat) (frame : Frame Fine bound stride)
    (forget : Fine → Coarse) (coarse : Coarse) :
    (inventoryCount frame.keys forget bound frame.native coarse : ℚ) •
      SourceRetainedCoarsening.blend bound stride frame forget coarse =
        ∑ key ∈ frame.keys, if forget key = coarse then
          ((frame.native key).1 : ℚ) • rawAt bound stride frame key else 0 := by
  rw [SourceRetainedCoarsening.blend, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro key inside
  rw [smul_smul, counted_weight bound stride frame forget coarse key inside]
  by_cases selected : forget key = coarse <;> simp only [selected, ↓reduceIte, zero_smul]

private theorem mergeEntry_represents (bound stride : Nat) (table : SourceCountedObservation.Table Fine)
    (frame : Frame Fine bound stride) (source : SourceCountedObservation.Simulates bound stride table frame)
    (forget : Fine → Coarse) (coarse : Coarse) :
    SourceCountedObservation.Represents bound stride (mergeEntry table forget coarse)
      ((SourceRetainedCoarsening.merge bound stride frame forget).native coarse).1
      (rawAt bound stride (SourceRetainedCoarsening.merge bound stride frame forget) coarse) := by
  have keys := SourceCountedObservation.inventory_source bound stride table frame source
  have weighted := counted_blend bound stride frame forget coarse
  refine ⟨?_, ?_, ?_, ?_⟩
  · change SourceCountedObservation.total table forget coarse = inventoryCount frame.keys forget bound frame.native coarse
    simp only [SourceCountedObservation.total, keys, (source.rows _).count_eq]
  · intro position
    rw [mergeEntry_coordinate, keys]
    simp only [(source.rows _).hilbert_eq]
    change (∑ key ∈ frame.keys, if forget key = coarse then
        ((frame.native key).1 : ℚ) * SourceReceivedConditionalStep.coordinateAt bound stride (rawAt bound stride frame key) position else 0) =
      (inventoryCount frame.keys forget bound frame.native coarse : ℚ) *
        SourceReceivedConditionalStep.coordinateAt bound stride
          (rawAt bound stride (SourceRetainedCoarsening.merge bound stride frame forget) coarse) position
    rw [SourceRetainedCoarsening.raw_merge]
    by_cases included : position < (bound + 1) * (stride + 1)
    · have projected := congrArg (fun raw : Raw bound stride => raw.1 ⟨position, included⟩) weighted
      simpa [SourceReceivedConditionalStep.coordinateAt, included, Prod.fst_sum, Finset.sum_apply,
        apply_ite, ite_apply, Pi.smul_apply, smul_eq_mul] using projected.symm
    · simp only [SourceReceivedConditionalStep.coordinateAt, dif_neg included, mul_zero, ite_self, Finset.sum_const_zero]
  · change (∑ key ∈ table.keys.toFinset, if forget key = coarse then (SourceCountedObservation.lookup table key).mass else 0) = _
    rw [keys]
    simp only [(source.rows _).mass_eq]
    change (∑ key ∈ frame.keys, if forget key = coarse then
        ((frame.native key).1 : ℚ) * (rawAt bound stride frame key).2.1 else 0) =
      (inventoryCount frame.keys forget bound frame.native coarse : ℚ) *
        (rawAt bound stride (SourceRetainedCoarsening.merge bound stride frame forget) coarse).2.1
    rw [SourceRetainedCoarsening.raw_merge]
    have projected := congrArg (fun raw : Raw bound stride => raw.2.1) weighted
    simpa [Prod.fst_sum, Prod.snd_sum, apply_ite] using projected.symm
  · change (∑ key ∈ table.keys.toFinset, if forget key = coarse then (SourceCountedObservation.lookup table key).clock else 0) = _
    rw [keys]
    simp only [(source.rows _).clock_eq]
    change (∑ key ∈ frame.keys, if forget key = coarse then
        ((frame.native key).1 : ℚ) * (rawAt bound stride frame key).2.2 else 0) =
      (inventoryCount frame.keys forget bound frame.native coarse : ℚ) *
        (rawAt bound stride (SourceRetainedCoarsening.merge bound stride frame forget) coarse).2.2
    rw [SourceRetainedCoarsening.raw_merge]
    have projected := congrArg (fun raw : Raw bound stride => raw.2.2) weighted
    simpa [Prod.snd_sum, apply_ite] using projected.symm

theorem merge_simulates (bound stride : Nat) (table : SourceCountedObservation.Table Fine)
    (frame : Frame Fine bound stride) (source : SourceCountedObservation.Simulates bound stride table frame)
    (forget : Fine → Coarse) :
    SourceCountedObservation.Simulates bound stride (mergeTable table forget)
      (SourceRetainedCoarsening.merge bound stride frame forget) := by
  have keys := SourceCountedObservation.inventory_source bound stride table frame source
  refine ⟨?_, ?_⟩
  · intro coarse
    rw [merge_keys, keys]
    rfl
  · intro coarse
    rw [lookup_merge, keys]
    by_cases present : coarse ∈ frame.keys.image forget
    · rw [if_pos present]
      exact mergeEntry_represents bound stride table frame source forget coarse
    · rw [if_neg present]
      have countZero : ((SourceRetainedCoarsening.merge bound stride frame forget).native coarse).1 = 0 := by
        change inventoryCount frame.keys forget bound frame.native coarse = 0
        apply Finset.sum_eq_zero
        intro key inside
        exact if_neg (fun same => present (Finset.mem_image.mpr ⟨key, inside, same⟩))
      have rawZero : rawAt bound stride (SourceRetainedCoarsening.merge bound stride frame forget) coarse = 0 := by
        unfold rawAt
        exact dif_neg present
      rw [countZero, rawZero]
      exact SourceCountedObservation.empty_represents bound stride

end SourceCountedMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
