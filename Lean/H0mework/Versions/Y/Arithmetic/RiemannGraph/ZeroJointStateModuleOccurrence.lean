import H0mework.Versions.Y.Arithmetic.RiemannGraph.IntegralGraphOrbit
import H0mework.Versions.Y.Arithmetic.RiemannGraph.ZeroRieszGraphTargetState

/-!
# Same-zero integral-topological joint state occurrence

The actual integral graph orbits and the canonical selected/reversal Riesz
states are installed as one dependent face of the existing
zero/character/Müntz occurrence.  The state fields consume `source.2`
directly; projection back to that source is literal.  No current-zero,
centered-Gram realization, separator, or RH field is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram

open RootedAccountedUnfolding
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedHilbertCokernel
open ThetaJRoleRepresentation

noncomputable section

/-- Selected canonical state formed from the Riesz class actually present
in the occurrence payload. -/
def selectedRieszGraphTargetStateFromSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial) : JointGraphTarget :=
  graphHilbertAmbientRealization
      (quarterMellinL2Feature (selectedCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional (selectedCoPoissonMuntzParameter observation))
    (quotientOrthogonalEquiv
      (selectedRelationGraphMap observation nontrivial) source.2.1)

def reversalRieszGraphTargetStateFromSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial) : JointGraphTarget :=
  graphHilbertAmbientRealization
      (quarterMellinL2Feature (reversalCoPoissonMuntzParameter observation))
      (quarterMellinL2Functional (reversalCoPoissonMuntzParameter observation))
    (quotientOrthogonalEquiv
      (reversalRelationGraphMap observation nontrivial) source.2.2)

/-- One state module with discrete charge orbits and coherent spectral
states. -/
structure GeneratedJointStateModuleFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : Type 2 where
  private mk ::
  selectedIntegralOrbit : IntegralScaleCarrier →ₗ[ℤ] JointGraphTarget
  reversalIntegralOrbit : IntegralScaleCarrier →ₗ[ℤ] JointGraphTarget
  selectedSpectralState : JointGraphTarget
  reversalSpectralState : JointGraphTarget

def generateJointStateModuleFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial) :
    GeneratedJointStateModuleFace observation nontrivial :=
  ⟨selectedIntegralGraphOrbit observation nontrivial,
    reversalIntegralGraphOrbit observation nontrivial,
    selectedRieszGraphTargetStateFromSource
      observation nontrivial source,
    reversalRieszGraphTargetStateFromSource
      observation nontrivial source⟩

abbrev ZeroOwnedJointStateModulePayload
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  Σ _source : ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial,
    GeneratedJointStateModuleFace observation nontrivial

/-- Unique same-source installation of the integral/topological state
module face. -/
def zeroOwnedJointStateModuleOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    RootedAccountedUnfolding
      (ZeroOwnedJointStateModulePayload observation nontrivial) :=
  (zeroOwnedCharacterMuntzCokernelOccurrence observation nontrivial).map
    fun source =>
      ⟨source, generateJointStateModuleFace
        observation nontrivial source⟩

theorem zeroOwnedJointStateModuleOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedJointStateModuleOccurrence
      observation nontrivial).map Sigma.fst =
      zeroOwnedCharacterMuntzCokernelOccurrence observation nontrivial := by
  rw [zeroOwnedJointStateModuleOccurrence, RootedAccountedUnfolding.map_map]
  change (zeroOwnedCharacterMuntzCokernelOccurrence
    observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

@[simp] theorem zeroOwnedJointStateModuleOccurrence_root_selectedOrbit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((zeroOwnedJointStateModuleOccurrence observation nontrivial).root.2).selectedIntegralOrbit =
      selectedIntegralGraphOrbit observation nontrivial :=
  rfl

@[simp] theorem zeroOwnedJointStateModuleOccurrence_root_reversalOrbit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((zeroOwnedJointStateModuleOccurrence observation nontrivial).root.2).reversalIntegralOrbit =
      reversalIntegralGraphOrbit observation nontrivial :=
  rfl

@[simp] theorem zeroOwnedJointStateModuleOccurrence_root_selectedState
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((zeroOwnedJointStateModuleOccurrence observation nontrivial).root.2).selectedSpectralState =
      selectedRieszGraphTargetState observation nontrivial :=
  rfl

@[simp] theorem zeroOwnedJointStateModuleOccurrence_root_reversalState
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((zeroOwnedJointStateModuleOccurrence observation nontrivial).root.2).reversalSpectralState =
      reversalRieszGraphTargetState observation nontrivial :=
  rfl

theorem zeroOwnedJointStateModuleOccurrence_root_selectedState_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((zeroOwnedJointStateModuleOccurrence observation nontrivial).root.2).selectedSpectralState
        ≠ 0 := by
  rw [zeroOwnedJointStateModuleOccurrence_root_selectedState]
  exact selectedRieszGraphTargetState_ne_zero observation nontrivial

theorem zeroOwnedJointStateModuleOccurrence_root_reversalState_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((zeroOwnedJointStateModuleOccurrence observation nontrivial).root.2).reversalSpectralState
        ≠ 0 := by
  rw [zeroOwnedJointStateModuleOccurrence_root_reversalState]
  exact reversalRieszGraphTargetState_ne_zero observation nontrivial

end


end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
