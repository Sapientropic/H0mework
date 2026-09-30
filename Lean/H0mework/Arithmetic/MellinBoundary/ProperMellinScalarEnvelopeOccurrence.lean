import H0mework.Arithmetic.MellinBoundary.ProperMellinScalarEnvelope

/-!
# Zero-rooted proper Mellin exact-envelope occurrence

The complex scalar envelope is installed as a dependent face of the exact
generated-zero observation.  Mapping the face away recovers that occurrence
and hence its analytic germ and arithmetic seed.  The source-generated zero
element and normalized low readout are then derived at the root; no sibling
analytic root is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ProperMellinScalarEnvelopeOccurrence

open RootedAccountedUnfolding
open ProperMellinScalarEnvelope
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram

noncomputable section

/-- Private source-generated face: the only envelope carried here is the
canonical envelope of the actual proper Mellin evaluation. -/
structure Face : Type 6 where
  private mk ::
  envelope :
    SourceGeneratedScalarExactEnvelope.UniversalPerfectEnvelope
      ProperMellinScalarEnvelope.evaluation

namespace Face

def generate : Face :=
  ⟨ProperMellinScalarEnvelope.exactEnvelope⟩

end Face

abbrev Payload := GeneratedZeroObservationPayload × Face

/-- The proper Mellin scalar envelope as a child of the same generated-zero
occurrence. -/
def occurrence (observation : GeneratedRiemannZeroObservation) :
    RootedAccountedUnfolding Payload :=
  (zeroObservationReadoutOccurrence observation).map
    (fun zero => (zero, Face.generate))

theorem occurrence_projects
    (observation : GeneratedRiemannZeroObservation) :
    (occurrence observation).map Prod.fst =
      zeroObservationReadoutOccurrence observation := by
  rw [occurrence, RootedAccountedUnfolding.map_map]
  change (zeroObservationReadoutOccurrence observation).map id =
    zeroObservationReadoutOccurrence observation
  exact RootedAccountedUnfolding.map_id _

theorem occurrence_projects_to_seed
    (observation : GeneratedRiemannZeroObservation) :
    (((((occurrence observation).map Prod.fst).map Sigma.fst).map
        Sigma.fst).map Prod.fst) = seedOccurrence := by
  rw [occurrence_projects,
    zeroObservationReadoutOccurrence_projects_to_seed]

@[simp] theorem occurrence_root_coordinate
    (observation : GeneratedRiemannZeroObservation) :
    (occurrence observation).root.1.2.coordinate = observation.coordinate :=
  rfl

@[simp] theorem occurrence_root_envelope
    (observation : GeneratedRiemannZeroObservation) :
    (occurrence observation).root.2.envelope =
      ProperMellinScalarEnvelope.exactEnvelope :=
  rfl

theorem occurrence_root_selected_maps_to_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceGeneratedScalarPerfectification.canonicalMap
        ProperMellinScalarEnvelope.evaluation
        (generatedZeroSelectedMellinL1Element
          (occurrence observation).root.1.2 nontrivial) = 0 := by
  exact ProperMellinScalarEnvelope.selectedElement_maps_to_zero
    (occurrence observation).root.1.2 nontrivial

theorem occurrence_root_generatedDual_nontrivial
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Nontrivial ProperMellinScalarEnvelope.GeneratedDual :=
  ProperMellinScalarEnvelope.generatedDual_nontrivial
    (occurrence observation).root.1.2 nontrivial

end
end ProperMellinScalarEnvelopeOccurrence
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
