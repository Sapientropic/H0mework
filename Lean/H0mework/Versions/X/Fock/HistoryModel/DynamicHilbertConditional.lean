import H0mework.Versions.X.Fock.HistoryModel.DynamicHilbertTransfer

/-! Full actor conditionals return to the original Current law before any conditional mean is read. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic.Hilbert

open SourceGeneratedRuntimeHistoryProbability SourceConditionalHistory
open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

def actor (bound : Nat) (index : Fin (bound + 1)) : Current :=
  (runtimeAt index.val).current.visit.current

theorem actor_law (bound : Nat) : (historyPMF bound).map (actor bound) = Fock.sourceLaw bound :=
  (Fock.sourceLaw_actual bound).symm

theorem full_original_conditional (depth bound : Nat) (atom : Complete.Carrier depth)
    (supported : atom ∈ (law depth bound).support) :
    ∃ originalSupported : atom ∈ (observed (Fock.sourceLaw bound) (Complete.point depth)).support,
      (conditional (historyPMF bound) (read depth bound) atom supported).map (actor bound) =
        conditional (Fock.sourceLaw bound) (Complete.point depth) atom originalSupported := by
  have generated := conditional_pushforward (historyPMF bound) (read depth bound) (actor bound)
    (Complete.point depth) id (fun _ => rfl) Function.injective_id atom supported
  simpa only [actor_law, id_eq] using generated

theorem whole_actor_mixture (depth bound : Nat) (atom : Complete.Carrier depth)
    (supported : atom ∈ (observed (law (depth + 1) bound) (previous depth)).support) :
    ∃ oldSupported : atom ∈ (law depth bound).support,
      Coarsening.mixture (historyPMF bound) (read (depth + 1) bound) (previous depth) atom supported =
        conditional (historyPMF bound) (read depth bound) atom oldSupported := by
  have square : previous depth ∘ read (depth + 1) bound = read depth bound := funext (read_previous depth bound)
  have generated := Coarsening.mixture_is_conditional (historyPMF bound) (read (depth + 1) bound)
    (previous depth) atom supported
  simpa only [square] using generated

theorem actual_new_atom (depth : Nat) :
    read (depth + 1) (depth + 1) (Fin.last (depth + 1)) = Complete.nativeNext depth :=
  (Complete.next_actual depth).symm

theorem actual_old_atom (depth : Nat) :
    read depth (depth + 1) (Fin.last (depth + 1)) = previous depth (Complete.nativeNext depth) :=
  (read_previous depth (depth + 1) (Fin.last (depth + 1))).symm.trans
    (congrArg (previous depth) (actual_new_atom depth))

theorem actual_whole_support (depth : Nat)
    (supported : read depth (depth + 1) (Fin.last (depth + 1)) ∈ (law depth (depth + 1)).support)
    (index : Fin (depth + 2)) :
    index ∈ (conditional (historyPMF (depth + 1)) (read depth (depth + 1))
      (read depth (depth + 1) (Fin.last (depth + 1))) supported).support ↔
      read (depth + 1) (depth + 1) index - Complete.nativeNext depth ∈ LinearMap.ker (previous depth) := by
  rw [conditional_support]
  change (read depth (depth + 1) index = read depth (depth + 1) (Fin.last (depth + 1)) ∧
    index ∈ (historyPMF (depth + 1)).support) ↔ _
  simp only [historyPMF, PMF.mem_support_uniformOfFintype, and_true]
  rw [actual_old_atom, ← read_previous depth (depth + 1) index]
  simpa only [previous_native_next] using whole_next_fibre depth (read (depth + 1) (depth + 1) index)

end
end SourceGeneratedActionWords.Fock.Dynamic.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
