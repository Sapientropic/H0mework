import H0mework.Versions.X.Fock.HistoryPolynomial.CopySource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyProgram

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def recover (depth : Nat) (index : Index depth) :
    SourceOperationNative.Carrier process →ₗ[ℤ] SourceOperationNative.Carrier process :=
  Finsupp.lcomapDomain (indexAfter depth index) (index_injective depth index)

def residual (depth : Nat) (index : Index depth) :
    SourceOperationNative.Carrier process →ₗ[ℤ] SourceOperationNative.Carrier process :=
  LinearMap.id - (action depth index).comp (recover depth index)

theorem recover_source (depth : Nat) (index : Index depth) (word : SourceOperationNative.Carrier process) :
    recover depth index (action depth index word) = word :=
  Finsupp.leftInverse_lcomapDomain_mapDomain (indexAfter depth index) (index_injective depth index) word

theorem recovery_reads (depth : Nat) (index : Index depth)
    (word : SourceOperationNative.Carrier process) (state : Nat) :
    recover depth index word state = word (indexAfter depth index state) := rfl

theorem reconstruct (depth : Nat) (index : Index depth) (word : SourceOperationNative.Carrier process) :
    action depth index (recover depth index word) + residual depth index word = word := by
  change action depth index (recover depth index word) +
    (word - action depth index (recover depth index word)) = word
  rw [add_comm]
  exact sub_add_cancel _ _

theorem residual_source (depth : Nat) (index : Index depth) (word : SourceOperationNative.Carrier process) :
    residual depth index (action depth index word) = 0 := by
  change action depth index word - action depth index (recover depth index (action depth index word)) = 0
  rw [recover_source, sub_self]

theorem action_coefficient (depth : Nat) (index : Index depth)
    (word : SourceOperationNative.Carrier process) (state : Nat) :
    action depth index word (indexAfter depth index state) = word state :=
  Finsupp.mapDomain_apply (index_injective depth index) word state

theorem action_outside (depth : Nat) (index : Index depth)
    (word : SourceOperationNative.Carrier process) (state : Nat)
    (outside : state ∉ Set.range (indexAfter depth index)) :
    action depth index word state = 0 :=
  Finsupp.mapDomain_of_notMem_range word state outside

theorem residual_inside (depth : Nat) (index : Index depth)
    (word : SourceOperationNative.Carrier process) (state : Nat) :
    residual depth index word (indexAfter depth index state) = 0 := by
  change word _ - action depth index (recover depth index word) _ = 0
  rw [action_coefficient, recovery_reads, sub_self]

theorem residual_outside (depth : Nat) (index : Index depth)
    (word : SourceOperationNative.Carrier process) (state : Nat)
    (outside : state ∉ Set.range (indexAfter depth index)) :
    residual depth index word state = word state := by
  change word state - action depth index (recover depth index word) state = word state
  rw [action_outside depth index _ state outside, sub_zero]

theorem original_fibre (depth : Nat) (index : Index depth)
    (target proposal : SourceOperationNative.Carrier process) :
    action depth index proposal = target ↔ proposal = recover depth index target ∧ residual depth index target = 0 := by
  constructor
  · rintro rfl
    exact ⟨(recover_source depth index proposal).symm, residual_source depth index proposal⟩
  · rintro ⟨rfl, vanished⟩
    simpa only [vanished, add_zero] using reconstruct depth index target

theorem index_range (depth : Nat) (index : Index depth) (state : Nat) :
    state ∈ Set.range (indexAfter depth index) ↔ scale depth index ∣ state + 1 := by
  constructor
  · rintro ⟨prior, rfl⟩
    rw [index_exact]
    exact dvd_mul_left _ _
  · rintro ⟨prior, equation⟩
    have nonzero : prior ≠ 0 := by
      intro zero
      rw [zero, Nat.mul_zero] at equation
      omega
    refine ⟨prior - 1, ?_⟩
    apply Nat.add_right_cancel (m := 1)
    rw [index_exact, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr nonzero), Nat.mul_comm]
    exact equation.symm

theorem exact_image (depth : Nat) (index : Index depth) (word : SourceOperationNative.Carrier process) :
    word ∈ (action depth index).range ↔
      ∀ state : Nat, ¬ scale depth index ∣ state + 1 → word state = 0 := by
  constructor
  · rintro ⟨prior, rfl⟩ state outside
    exact action_outside depth index prior state (fun inside => outside ((index_range depth index state).mp inside))
  · intro support
    refine ⟨recover depth index word, ?_⟩
    apply Finsupp.ext
    intro state
    by_cases inside : state ∈ Set.range (indexAfter depth index)
    · obtain ⟨prior, rfl⟩ := inside
      rw [action_coefficient, recovery_reads]
    · rw [action_outside depth index _ state inside]
      exact (support state (fun divides => inside ((index_range depth index state).mpr divides))).symm

end
end SourceCopyProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
