import H0mework.Versions.X.Fock.PrimeField.RecoveryFresh

/-! A source-generated prime birth separates exactly one original native source index. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock

noncomputable section

theorem point_separation (owner : GlobalParentOwner) (index state : Nat) :
    primeRead (selectedPrime owner index) (rawField (state + delay owner index + 1)) -
      primeRead (selectedPrime owner index) (rawField (state + delay owner index)) =
        if state = index then 1 else 0 := by
  rw [primeRead_source, primeRead_source]
  have position := selected_position owner index
  by_cases same : state = index
  · rw [if_pos (by omega), if_neg (by omega), if_pos same]
    rfl
  · by_cases earlier : state < index
    · rw [if_neg (by omega), if_neg (by omega), if_neg same]
      rfl
    · rw [if_pos (by omega), if_pos (by omega), if_neg same]
      rfl

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
