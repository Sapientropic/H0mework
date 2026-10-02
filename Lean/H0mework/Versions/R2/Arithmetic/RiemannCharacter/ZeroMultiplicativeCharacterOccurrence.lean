import H0mework.Realization.Topology.PositiveRealCharacter
import H0mework.Versions.R2.Arithmetic.RiemannInverseFibre.GeneratedZeroRead
import H0mework.Versions.R2.Arithmetic.UnitArithmetic.CoordinateProjectionObstruction

/-!
# The zero-owned global multiplicative character occurrence

The selected and reversal complex power characters are mapped from the
already generated analytic zero occurrence.  Finite-prime and Archimedean
faces will read this payload; neither face generates a second character.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace Character

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open RootedAccountedUnfolding
open SourceGeneratedPositiveRealCharacter

noncomputable section

structure MultiplicativeCharacterPair where
  selected : Units NNReal →* ℂ
  reversal : Units NNReal →* ℂ

def MultiplicativeCharacterPair.generate (coordinate : ℂ) :
    MultiplicativeCharacterPair where
  selected := complexPowerCharacter coordinate
  reversal := complexPowerCharacter (coordinateReversal coordinate)

abbrev ZeroMultiplicativeCharacterPayload :=
  Σ _zero : GeneratedZeroObservationPayload, MultiplicativeCharacterPair

/-- The character pair is a dependent face of the same analytic zero
occurrence. -/
def zeroOwnedMultiplicativeCharacterOccurrence
    (observation : GeneratedRiemannZeroObservation) :
    RootedAccountedUnfolding ZeroMultiplicativeCharacterPayload :=
  (zeroObservationReadoutOccurrence observation).map fun zero =>
    ⟨zero, MultiplicativeCharacterPair.generate zero.2.coordinate⟩

theorem zeroOwnedMultiplicativeCharacterOccurrence_projects
    (observation : GeneratedRiemannZeroObservation) :
    (zeroOwnedMultiplicativeCharacterOccurrence observation).map Sigma.fst =
      zeroObservationReadoutOccurrence observation := by
  rw [zeroOwnedMultiplicativeCharacterOccurrence,
    RootedAccountedUnfolding.map_map]
  change (zeroObservationReadoutOccurrence observation).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem zeroOwnedMultiplicativeCharacterOccurrence_projects_to_seed
    (observation : GeneratedRiemannZeroObservation) :
    (((((zeroOwnedMultiplicativeCharacterOccurrence observation).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Prod.fst) =
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence := by
  rw [zeroOwnedMultiplicativeCharacterOccurrence_projects,
    zeroObservationReadoutOccurrence_projects_to_seed]

@[simp]
theorem zeroOwnedMultiplicativeCharacterOccurrence_root_selected
    (observation : GeneratedRiemannZeroObservation) :
    (zeroOwnedMultiplicativeCharacterOccurrence observation).root.2.selected =
      complexPowerCharacter observation.coordinate := by
  rfl

@[simp]
theorem zeroOwnedMultiplicativeCharacterOccurrence_root_reversal
    (observation : GeneratedRiemannZeroObservation) :
    (zeroOwnedMultiplicativeCharacterOccurrence observation).root.2.reversal =
      complexPowerCharacter (coordinateReversal observation.coordinate) := by
  rfl

end

end Character
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
