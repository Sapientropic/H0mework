import H0mework.Fock.HistoryConditional.NativeMergeInventory
import H0mework.Fock.FibreExactState.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

-- The finite key carrier is received data; absent source rows contribute zero.
def merge [Fintype Fine] (forget : Fine → Coarse) (bound : Nat)
    (previous : SourceConditionalNativeObservers.State Fine bound) : SourceConditionalNativeObservers.State Coarse bound :=
  SourceConditionalNativeMerge.inventoryMerge Finset.univ forget bound previous

theorem old_count (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat)
    (previous : SourceConditionalNativeObservers.State Fine bound) (key : Coarse) :
    SourceConditionalNativeMerge.inventoryCount
      (SourceUniformFibreVariance.outputs bound (fun actor => read actor.val)) forget bound previous key =
      SourceConditionalNativeMerge.count read forget bound previous key := rfl

theorem outside_row (read : Nat → Fine) (bound : Nat) (key : Fine)
    (absent : key ∉ SourceUniformFibreVariance.outputs bound (fun actor => read actor.val)) :
    SourceConditionalNativeObservers.generate read bound key = (0, fun _ => 0) := by
  apply SourceConditionalNativeObservers.generated_outside
  intro actor same
  exact absent (Finset.mem_image.mpr ⟨actor, Finset.mem_univ _, same.symm⟩)

theorem count_source [Fintype Fine] (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) (value : Coarse) :
    SourceConditionalNativeMerge.inventoryCount Finset.univ forget bound
      (SourceConditionalNativeObservers.generate read bound) value =
        SourceConditionalNativeMerge.count read forget bound
          (SourceConditionalNativeObservers.generate read bound) value := by
  rw [← old_count]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro key _ absent
  rw [outside_row read bound key absent]
  simp

theorem source_native [Fintype Fine] (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) :
    merge forget bound (SourceConditionalNativeObservers.generate read bound) =
      SourceConditionalNativeMerge.merge read forget bound (SourceConditionalNativeObservers.generate read bound) := by
  funext value
  apply Prod.ext
  · exact count_source read forget bound value
  · funext actor
    change (∑ key : Fine, if forget key = value then
      ((SourceConditionalNativeObservers.generate read bound key).1 : ℚ) /
        SourceConditionalNativeMerge.inventoryCount Finset.univ forget bound (SourceConditionalNativeObservers.generate read bound) value *
          (SourceConditionalNativeObservers.generate read bound key).2 actor else 0) = _
    rw [count_source read forget bound value]
    symm
    dsimp only [SourceConditionalNativeMerge.merge, SourceConditionalNativeMerge.inventoryMerge]
    change (∑ key ∈ SourceUniformFibreVariance.outputs bound (fun index => read index.val),
      if forget key = value then ((SourceConditionalNativeObservers.generate read bound key).1 : ℚ) /
        SourceConditionalNativeMerge.count read forget bound (SourceConditionalNativeObservers.generate read bound) value *
          (SourceConditionalNativeObservers.generate read bound key).2 actor else 0) = _
    apply Finset.sum_subset (Finset.subset_univ _)
    intro key _ absent
    rw [outside_row read bound key absent]
    simp

theorem source_generated [Fintype Fine] (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) :
    merge forget bound (SourceConditionalNativeObservers.generate read bound) =
      SourceConditionalNativeObservers.generate (forget ∘ read) bound := by
  rw [source_native]
  exact SourceConditionalNativeMerge.merged_generated read forget bound

end SourceReceivedConditionalMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
