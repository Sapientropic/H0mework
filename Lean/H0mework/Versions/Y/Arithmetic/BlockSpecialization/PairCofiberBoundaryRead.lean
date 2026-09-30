import H0mework.Versions.Y.Arithmetic.BlockSpecialization.PairLocalRelationActionCokernel
import H0mework.Versions.Y.Arithmetic.BlockSpecialization.CokernelGlobalOccurrence

/-!
# Common endpoint read from the action cofiber

The endpoint element of the whole action cofiber is a shifted source
section.  Its source coordinate is restricted to one finite stage, passed
through the already installed differential, and only then quotiented by the
analytic `1 - M` relation range.  This is exactly the same class obtained by
projecting the nonzero global symbolic endpoint class and applying the
canonical dependent-face map.

The raw `fst` cofiber coordinate vanishes on this endpoint.  Its vanishing
therefore cannot be substituted for the nonzero global relation class; the
missing differential is a genuine premise-preserving step.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalRiemannPairCofiberBoundaryRead

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalOccurrence
open CanonicalRiemannPairLocalRelationActionCokernel
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

/-- The only lawful degree-one relation read of the shifted endpoint:
`snd`, actual restriction, actual differential. -/
def pairCofiberBoundaryReadRaw (stage : Nat) :
    PairBlockActionCofiber.X 1 →ₗ[PairCoefficientRing]
      (PairBlockLocalState stage).X 1 :=
  ((PairBlockLocalState stage).d 0 1).hom.comp
    (((pairBlockGlobalRestriction stage).f 0).hom.comp
      ((CochainComplex.mappingCocone.snd
        pairBlockGlobalEulerOperator).v 1 0 (by omega)).hom)

def pairCofiberBoundaryRead (stage : Nat) :
    PairBlockActionCofiber.X 1 →ₗ[PairCoefficientRing]
      PairLocalRelationActionCokernel stage :=
  (pairLocalRelationActionCokernelProjection stage).comp
    (pairCofiberBoundaryReadRaw stage)

theorem pairCofiberBoundaryReadRaw_endpoint (stage : Nat) :
    pairCofiberBoundaryReadRaw stage pairBlockEndpointCofiberElement =
      localPairEndpointBoundary stage := by
  unfold pairCofiberBoundaryReadRaw
  change ((PairBlockLocalState stage).d 0 1).hom
    (((pairBlockGlobalRestriction stage).f 0).hom
      pairBlockEndpointSourceReadback) = _
  rw [pairBlockEndpointSourceReadback_eq_section,
    pairBlockGlobalRestriction_endpointSection]
  rfl

theorem pairCofiberBoundaryRead_endpoint (stage : Nat) :
    pairCofiberBoundaryRead stage pairBlockEndpointCofiberElement =
      pairLocalRelationActionCokernelProjection stage
        (localPairEndpointBoundary stage) := by
  unfold pairCofiberBoundaryRead
  rw [LinearMap.comp_apply, pairCofiberBoundaryReadRaw_endpoint]

/-- The global symbolic relation class and the whole action-cofiber endpoint
have one common local analytic read at every actual finite stage. -/
theorem globalEndpointClass_pairCofiber_common_local_read (stage : Nat) :
    formalClassToPairLocal stage
        ((limit.π localRelationActionCokernelDiagram
          (Opposite.op stage)).hom globalEndpointBoundaryCokernelClass) =
      pairCofiberBoundaryRead stage pairBlockEndpointCofiberElement := by
  rw [globalEndpointBoundaryCokernelClass_restriction,
    formalClassToPairLocal_endpointClass,
    pairCofiberBoundaryRead_endpoint]

abbrev PairEndpointCommonReadPayload (stage : Nat) :=
  FactorizationPayload ×
    ((GlobalRelationActionCokernel × PairBlockActionCofiber.X 1) ×
      PairLocalRelationActionCokernel stage)

/-- One source occurrence carrying both sibling inputs and their common
analytic relation read. -/
def pairEndpointCommonReadOccurrence (stage : Nat) :
    RootedAccountedUnfolding (PairEndpointCommonReadPayload stage) :=
  seedOccurrence.map fun owner =>
    (owner,
      ((globalEndpointBoundaryCokernelClass,
          pairBlockEndpointCofiberElement),
        pairCofiberBoundaryRead stage pairBlockEndpointCofiberElement))

theorem pairEndpointCommonReadOccurrence_projects_global (stage : Nat) :
    (pairEndpointCommonReadOccurrence stage).map
        (fun payload => (payload.1, payload.2.1.1)) =
      globalEndpointBoundaryCokernelOccurrence := by
  unfold pairEndpointCommonReadOccurrence
    globalEndpointBoundaryCokernelOccurrence
  rw [RootedAccountedUnfolding.map_map]
  rfl

theorem pairEndpointCommonReadOccurrence_projects_cofiber (stage : Nat) :
    (pairEndpointCommonReadOccurrence stage).map
        (fun payload => (payload.1, payload.2.1.2)) =
      CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement.pairBlockEndpointCofiberOccurrence := by
  unfold pairEndpointCommonReadOccurrence
    CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement.pairBlockEndpointCofiberOccurrence
  rw [RootedAccountedUnfolding.map_map]
  rfl

theorem pairBlockEndpointCofiberElement_fst_zero :
    ((CochainComplex.mappingCocone.fst
      pairBlockGlobalEulerOperator).f 1).hom
        pairBlockEndpointCofiberElement = 0 := by
  have coordinate := CochainComplex.mappingCocone.inr_v_fst_f
    pairBlockGlobalEulerOperator 0 1 (by omega)
  exact ConcreteCategory.congr_hom coordinate
    pairBlockGlobalEndpointSection

/-- The raw `fst` coordinate cannot be a faithful detector for the existing
global relation class: it vanishes while that source class is certified
nonzero by its arithmetic dependent face. -/
theorem fst_vanishing_not_globalEndpointClass_vanishing :
    ¬ (((CochainComplex.mappingCocone.fst
        pairBlockGlobalEulerOperator).f 1).hom
          pairBlockEndpointCofiberElement = 0 ↔
        globalEndpointBoundaryCokernelClass = 0) := by
  intro equivalence
  exact existingGlobalEndpointBoundaryCokernelClass_ne_zero
    (equivalence.mp pairBlockEndpointCofiberElement_fst_zero)

theorem preserves_same_owner_inputs_common_read_and_fst_no_go (stage : Nat) :
    (pairEndpointCommonReadOccurrence stage).map
        (fun payload => (payload.1, payload.2.1.1)) =
        globalEndpointBoundaryCokernelOccurrence ∧
      (pairEndpointCommonReadOccurrence stage).map
        (fun payload => (payload.1, payload.2.1.2)) =
        CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement.pairBlockEndpointCofiberOccurrence ∧
      formalClassToPairLocal stage
          ((limit.π localRelationActionCokernelDiagram
            (Opposite.op stage)).hom globalEndpointBoundaryCokernelClass) =
        pairCofiberBoundaryRead stage pairBlockEndpointCofiberElement ∧
      ¬ (((CochainComplex.mappingCocone.fst
          pairBlockGlobalEulerOperator).f 1).hom
            pairBlockEndpointCofiberElement = 0 ↔
          globalEndpointBoundaryCokernelClass = 0) := by
  exact ⟨pairEndpointCommonReadOccurrence_projects_global stage,
    pairEndpointCommonReadOccurrence_projects_cofiber stage,
    globalEndpointClass_pairCofiber_common_local_read stage,
    fst_vanishing_not_globalEndpointClass_vanishing⟩

end
end CanonicalRiemannPairCofiberBoundaryRead
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
