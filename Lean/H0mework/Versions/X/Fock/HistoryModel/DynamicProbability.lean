import H0mework.Versions.X.Fock.HistoryModel.DynamicRead

/-! The full original next history is coarsened through the source-generated old-word restriction with its entire mixture retained. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem full_history_pushforward (depth : Nat) :
    (observed (Fock.sourceLaw (depth + 1)) (Complete.point (depth + 1))).map (previous depth) =
      observed (Fock.sourceLaw (depth + 1)) (Complete.point depth) :=
  (PMF.map_comp (Complete.point (depth + 1)) (Fock.sourceLaw (depth + 1)) (previous depth)).trans
    (congrArg (fun read : Current → Complete.Carrier depth => (Fock.sourceLaw (depth + 1)).map read)
      (funext (previous_point depth)))

theorem complete_coarsening (depth : Nat) (value : Complete.Carrier depth)
    (supported : value ∈ (observed (observed (Fock.sourceLaw (depth + 1)) (Complete.point (depth + 1))) (previous depth)).support) :
    ∃ oldSupported : value ∈ (observed (Fock.sourceLaw (depth + 1)) (Complete.point depth)).support,
      Coarsening.mixture (Fock.sourceLaw (depth + 1)) (Complete.point (depth + 1)) (previous depth) value supported =
        conditional (Fock.sourceLaw (depth + 1)) (Complete.point depth) value oldSupported := by
  have composite : previous depth ∘ Complete.point (depth + 1) = Complete.point depth := funext (previous_point depth)
  have generated := Coarsening.mixture_is_conditional (Fock.sourceLaw (depth + 1))
    (Complete.point (depth + 1)) (previous depth) value supported
  simpa only [composite] using generated

theorem actual_next_supported (depth : Nat) : Complete.nativeNext depth ∈
    (observed (Fock.sourceLaw (depth + 1)) (Complete.point (depth + 1))).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨((runtimeAt (depth + 1)).current.visit.current : Current), Fock.current_supported (depth + 1), ?_⟩
  exact (Complete.next_actual depth).symm

theorem previous_next_supported (depth : Nat) : previous depth (Complete.nativeNext depth) ∈
    (observed (observed (Fock.sourceLaw (depth + 1)) (Complete.point (depth + 1))) (previous depth)).support :=
  (PMF.mem_support_map_iff _ _ _).mpr ⟨Complete.nativeNext depth, actual_next_supported depth, rfl⟩

theorem actual_next_coarsening (depth : Nat) :
    ∃ supported : previous depth (Complete.nativeNext depth) ∈
        (observed (Fock.sourceLaw (depth + 1)) (Complete.point depth)).support,
      Coarsening.mixture (Fock.sourceLaw (depth + 1)) (Complete.point (depth + 1)) (previous depth)
        (previous depth (Complete.nativeNext depth)) (previous_next_supported depth) =
        conditional (Fock.sourceLaw (depth + 1)) (Complete.point depth) (previous depth (Complete.nativeNext depth)) supported :=
  complete_coarsening depth (previous depth (Complete.nativeNext depth)) (previous_next_supported depth)

end
end SourceGeneratedActionWords.Fock.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
