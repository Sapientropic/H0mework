import H0mework.Versions.R2.Fock.PrimeField.RecoveryMaterial
import H0mework.Versions.R2.Fock.SourceHistory.PrimeFieldActionRegression

/-! Actual identical current prime fields cannot replace the source-paid history query. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual

noncomputable section

theorem current_read_collision : rawField 3 = rawField 2 :=
  SourceFactorizationAction.Fock.Controls.same_field

theorem no_current_only_clock (bound : Nat) (containsGap : 2 ≤ bound) :
    ¬ ∃ decode : IntegralOneParticle → ℂ,
      ∀ index : Fin (bound + 1), decode (rawField (index.val + 1)) = (index.val : ℂ) := by
  rintro ⟨decode, recovers⟩
  let first : Fin (bound + 1) := ⟨1, by omega⟩
  let second : Fin (bound + 1) := ⟨2, by omega⟩
  have same := congrArg decode current_read_collision
  have atFirst : decode (rawField 2) = (1 : ℂ) := by simpa [first] using recovers first
  have atSecond : decode (rawField 3) = (2 : ℂ) := by simpa [second] using recovers second
  rw [atFirst, atSecond] at same
  norm_num at same

theorem delay_positive (owner : GlobalParentOwner) (index : Nat) : 0 < delay owner index := by
  have above := selected_above owner index
  have position := selected_position owner index
  omega

theorem delayed_query_separates_gap (bound : Nat) (containsGap : 2 ≤ bound) :
    let first : Fin (bound + 1) := ⟨1, by omega⟩
    let second : Fin (bound + 1) := ⟨2, by omega⟩
    observe sourceOwner bound first ≠ observe sourceOwner bound second := by
  dsimp only
  intro same
  have actual := observe_injective sourceOwner bound same
  have indices := congrArg Fin.val actual
  norm_num at indices

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
