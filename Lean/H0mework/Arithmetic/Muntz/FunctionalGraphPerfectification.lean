import H0mework.Realization.Graph.Completion
import H0mework.Arithmetic.Muntz.WholeL2EquivariantResidualOccurrence

/-!
# A1c specialization of functional graph perfectification

The same-zero Mellin test functional has a nonzero residual relative to the
old whole-`L²` bounded dual.  The generic graph construction enlarges that
actual feature by the functional itself, generates a complete Hilbert
ambient, and gives the functional its unique continuous coordinate.  The
new dependent face is obtained by mapping the existing rooted residual
occurrence; no root, zero law, or endpoint equality is added.
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
open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

abbrev ZeroOwnedQuarterFunctionalGraphAmbient
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :=
  GraphHilbertAmbient
    (quarterMellinL2Feature (observation.coordinate / 2))
    (quarterMellinL2Functional (observation.coordinate / 2))

def zeroOwnedQuarterFunctionalGraphFeature
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    QuarterMellinL2Test (observation.coordinate / 2) →ₗ[ℂ]
      ZeroOwnedQuarterFunctionalGraphAmbient observation :=
  canonicalHilbertMap
    (graphFeature
      (quarterMellinL2Feature (observation.coordinate / 2))
      (quarterMellinL2Functional (observation.coordinate / 2)))

def zeroOwnedQuarterFunctionalGraphCoordinate
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    ZeroOwnedQuarterFunctionalGraphAmbient observation →L[ℂ] ℂ :=
  graphHilbertFunctional
    (quarterMellinL2Feature (observation.coordinate / 2))
    (quarterMellinL2Functional (observation.coordinate / 2))

@[simp] theorem zeroOwnedQuarterFunctionalGraphCoordinate_readback
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (test : QuarterMellinL2Test (observation.coordinate / 2)) :
    zeroOwnedQuarterFunctionalGraphCoordinate observation
        (zeroOwnedQuarterFunctionalGraphFeature observation test) =
      quarterMellinL2Functional
        (observation.coordinate / 2) test :=
  graphHilbertFunctional_source_readback _ _ test

theorem zeroOwnedQuarterFunctionalGraphResidual_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    canonicalExtensionResidual
        (zeroOwnedQuarterFunctionalGraphFeature observation)
        (quarterMellinL2Functional (observation.coordinate / 2)) = 0 :=
  graphExtensionResidual_zero _ _

/-- Coordinate of a rooted old-residual payload. -/
def residualPayloadCoordinate
    (payload : WholeL2EquivariantResidualPayload) : ℂ :=
  payload.1.1.2.coordinate

abbrev WholeL2FunctionalGraphPayload :=
  Σ source : WholeL2EquivariantResidualPayload,
    GraphHilbertAmbient
      (quarterMellinL2Feature (residualPayloadCoordinate source / 2))
      (quarterMellinL2Functional (residualPayloadCoordinate source / 2)) →L[ℂ] ℂ

def zeroOwnedQuarterFunctionalGraphOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    RootedAccountedUnfolding WholeL2FunctionalGraphPayload :=
  (zeroOwnedWholeL2EquivariantResidualOccurrence
    observation nontrivial).map fun source =>
      ⟨source,
        graphHilbertFunctional
          (quarterMellinL2Feature (residualPayloadCoordinate source / 2))
          (quarterMellinL2Functional (residualPayloadCoordinate source / 2))⟩

theorem zeroOwnedQuarterFunctionalGraphOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedQuarterFunctionalGraphOccurrence
        observation nontrivial).map Sigma.fst =
      zeroOwnedWholeL2EquivariantResidualOccurrence
        observation nontrivial := by
  rw [zeroOwnedQuarterFunctionalGraphOccurrence,
    RootedAccountedUnfolding.map_map]
  change (zeroOwnedWholeL2EquivariantResidualOccurrence
    observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

@[simp] theorem zeroOwnedQuarterFunctionalGraphOccurrence_root_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (test : QuarterMellinL2Test (observation.coordinate / 2)) :
    (zeroOwnedQuarterFunctionalGraphOccurrence
        observation nontrivial).root.2
      ((zeroOwnedQuarterFunctionalGraphFeature observation) test) =
        quarterMellinL2Functional (observation.coordinate / 2) test := by
  exact zeroOwnedQuarterFunctionalGraphCoordinate_readback observation test

/-! The graph face pays functional continuity and keeps the old nonextension
coordinate in its source payload.  It does not generate graph-action
isometry, generalized spectral annihilation, or endpoint path equality. -/

end
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
