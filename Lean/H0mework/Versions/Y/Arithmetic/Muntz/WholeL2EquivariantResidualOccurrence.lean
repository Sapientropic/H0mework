import H0mework.Versions.Y.Arithmetic.Muntz.WholeL2EquivariantResidual
import H0mework.Versions.Y.Arithmetic.MellinBoundary.ProperMellinLowHighRelativeOccurrence

/-!
# Same-zero rooted admission of the equivariant residual

The canonical generalized-dual residual is installed by mapping the existing
same-zero low/high occurrence.  Its payload retains that exact source root and
adds only the canonical residual coordinate; no sibling root is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open QRich
open RootedAccountedUnfolding
open SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

abbrev WholeL2EquivariantResidualPayload :=
  Σ source : ProperMellinLowHighRelativePayload,
    EquivariantExtensionResidual
      (quarterMellinL2Feature (source.1.2.coordinate / 2))
      quarterScaleThreeEnergyAction
      ((positiveMellinQuarterNoGoScale : ℂ) ^
        ((1 / 4 : ℂ) - source.1.2.coordinate / 2))

def zeroOwnedWholeL2EquivariantResidualOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    RootedAccountedUnfolding WholeL2EquivariantResidualPayload :=
  (zeroOwnedProperMellinLowHighRelativeOccurrence
    observation nontrivial).map fun source =>
      ⟨source,
        wholeL2EquivariantResidualAtCoordinate
          source.1.2.coordinate⟩

theorem zeroOwnedWholeL2EquivariantResidualOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedWholeL2EquivariantResidualOccurrence
        observation nontrivial).map Sigma.fst =
      zeroOwnedProperMellinLowHighRelativeOccurrence
        observation nontrivial := by
  rw [zeroOwnedWholeL2EquivariantResidualOccurrence,
    RootedAccountedUnfolding.map_map]
  change (zeroOwnedProperMellinLowHighRelativeOccurrence
    observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

@[simp] theorem zeroOwnedWholeL2EquivariantResidualOccurrence_root_value
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedWholeL2EquivariantResidualOccurrence
      observation nontrivial).root.2 =
        zeroOwnedWholeL2EquivariantResidual observation :=
  rfl

theorem zeroOwnedWholeL2EquivariantResidualOccurrence_root_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedWholeL2EquivariantResidualOccurrence
      observation nontrivial).root.2 ≠ 0 := by
  rw [zeroOwnedWholeL2EquivariantResidualOccurrence_root_value]
  exact zeroOwnedWholeL2EquivariantResidual_ne_zero
    observation nontrivial

/-! This rooted residual is a disposition of the failed bounded face.  It
does not generate the still-missing source-owned rigged spectral
annihilation. -/

end
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
