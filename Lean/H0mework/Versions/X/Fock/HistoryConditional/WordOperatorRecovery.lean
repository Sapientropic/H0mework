import H0mework.Versions.X.Fock.HistoryConditional.WordOperatorSource
import H0mework.Fock.HistoryConditional.WordOperatorIndex

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledWordOperator

open SourceGeneratedActionWords
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def recover (depth : Nat) (word : List (Fock.Letter depth)) :
    SourceOperationNative.Carrier process →ₗ[ℤ] SourceOperationNative.Carrier process :=
  Finsupp.lcomapDomain (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)))
    (index_injective (word.map SourceCopyNativeWord.encode))

def residual (depth : Nat) (word : List (Fock.Letter depth)) :
    SourceOperationNative.Carrier process →ₗ[ℤ] SourceOperationNative.Carrier process :=
  LinearMap.id - (action depth word).comp (recover depth word)

theorem recover_source (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    recover depth word (action depth word source) = source :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ (index_injective (word.map SourceCopyNativeWord.encode)) source

theorem recovery_reads (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) (state : Nat) :
    recover depth word source state =
      source (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) state) := rfl

theorem action_coefficient (depth : Nat) (word : List (Fock.Letter depth))
    (source : SourceOperationNative.Carrier process) (state : Nat) :
    action depth word source (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) state) =
      source state :=
  Finsupp.mapDomain_apply (index_injective (word.map SourceCopyNativeWord.encode)) source state

theorem action_outside (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process)
    (state : Nat) (outside : state ∉ Set.range (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)))) :
    action depth word source state = 0 :=
  Finsupp.mapDomain_of_notMem_range source state outside

theorem reconstruct (depth : Nat) (word : List (Fock.Letter depth)) (target : SourceOperationNative.Carrier process) :
    action depth word (recover depth word target) + residual depth word target = target := by
  change action depth word (recover depth word target) +
    (target - action depth word (recover depth word target)) = target
  rw [add_comm]
  exact sub_add_cancel _ _

theorem residual_source (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    residual depth word (action depth word source) = 0 := by
  change action depth word source - action depth word (recover depth word (action depth word source)) = 0
  rw [recover_source, sub_self]

theorem original_fibre (depth : Nat) (word : List (Fock.Letter depth)) (target proposal : SourceOperationNative.Carrier process) :
    action depth word proposal = target ↔ proposal = recover depth word target ∧ residual depth word target = 0 := by
  constructor
  · rintro rfl
    exact ⟨(recover_source depth word proposal).symm, residual_source depth word proposal⟩
  · rintro ⟨rfl, vanished⟩
    simpa only [vanished, add_zero] using reconstruct depth word target

theorem residual_inside (depth : Nat) (word : List (Fock.Letter depth)) (target : SourceOperationNative.Carrier process) (state : Nat) :
    residual depth word target (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) state) = 0 := by
  change target _ - action depth word (recover depth word target) _ = 0
  rw [action_coefficient, recovery_reads, sub_self]

theorem residual_outside (depth : Nat) (word : List (Fock.Letter depth)) (target : SourceOperationNative.Carrier process)
    (state : Nat) (outside : state ∉ Set.range (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)))) :
    residual depth word target state = target state := by
  change target state - action depth word (recover depth word target) state = target state
  rw [action_outside depth word _ state outside, sub_zero]

end
end SourceCompiledWordOperator
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
