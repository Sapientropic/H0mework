import H0mework.Versions.R2.Arithmetic.EulerDerived.EndpointDeterminantSupport

/-!
# Derived Koszul cycle of the determinant-supported endpoint boundary

The adjugate calculation is retained before passing to a cokernel.  Pairing
its canonical preimage with the unscaled endpoint boundary produces the
literal cycle

`(adj(boundary), boundary) ∈ ker [1-M, -D]`.

Thus the determinant support generates a derived zero-fibre class whose
second coordinate is the actual unscaled boundary.  No inverse, selected
point, normalization, divisibility, or fixedness law enters this producer.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDerivedKoszulCycle

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDeterminantSupport

noncomputable section

abbrev Relation (stage : Nat) :=
  BlockWholeRelation seedOccurrence.root stage

def blockDeterminantMultiplication (stage : Nat) :
    Relation stage →ₗ[BlockCoordinateRing] Relation stage :=
  LinearMap.lsmul BlockCoordinateRing (Relation stage)
    (blockDeterminantSection seedOccurrence.root stage)

/-- The two-term derived zero-fibre differential `[1-M,-D]`. -/
def endpointBoundaryKoszulDifferential (stage : Nat) :
    Relation stage × Relation stage →ₗ[BlockCoordinateRing]
      Relation stage :=
  LinearMap.coprod
    (blockWholeRelationEulerOperator seedOccurrence.root stage)
    (-blockDeterminantMultiplication stage)

def endpointBoundaryKoszulPair (stage : Nat) :
    Relation stage × Relation stage :=
  (blockEndpointBoundaryDeterminantPreimage stage,
    localBlockEndpointBoundaryRelation stage)

theorem endpointBoundaryKoszulPair_cycle (stage : Nat) :
    endpointBoundaryKoszulDifferential stage
        (endpointBoundaryKoszulPair stage) = 0 := by
  unfold endpointBoundaryKoszulDifferential endpointBoundaryKoszulPair
    blockDeterminantMultiplication
  simp only [LinearMap.coprod_apply, LinearMap.neg_apply,
    LinearMap.lsmul_apply]
  rw [blockWholeRelationEulerOperator_adjugate_preimage]
  exact add_neg_cancel _

abbrev EndpointBoundaryDerivedKoszulKernel (stage : Nat) :=
  LinearMap.ker (endpointBoundaryKoszulDifferential stage)

/-- The canonical derived class.  Its second coordinate is deliberately the
unscaled endpoint boundary, not `D • boundary`. -/
def endpointBoundaryDerivedKoszulCycle (stage : Nat) :
    EndpointBoundaryDerivedKoszulKernel stage :=
  ⟨endpointBoundaryKoszulPair stage,
    endpointBoundaryKoszulPair_cycle stage⟩

@[simp] theorem endpointBoundaryDerivedKoszulCycle_unscaled_boundary
    (stage : Nat) :
    (endpointBoundaryDerivedKoszulCycle stage).1.2 =
      localBlockEndpointBoundaryRelation stage :=
  rfl

def endpointBoundaryDerivedKoszulOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload × EndpointBoundaryDerivedKoszulKernel stage) :=
  seedOccurrence.map fun owner =>
    (owner, endpointBoundaryDerivedKoszulCycle stage)

theorem endpointBoundaryDerivedKoszulOccurrence_projects (stage : Nat) :
    (endpointBoundaryDerivedKoszulOccurrence stage).map Prod.fst =
      seedOccurrence := by
  unfold endpointBoundaryDerivedKoszulOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_exact_D_adjugate_and_unscaled_boundary_cycle
    (stage : Nat) :
    (endpointBoundaryDerivedKoszulOccurrence stage).map Prod.fst =
        seedOccurrence ∧
      endpointBoundaryKoszulDifferential stage
          (endpointBoundaryKoszulPair stage) = 0 ∧
      (endpointBoundaryDerivedKoszulCycle stage).1.2 =
        localBlockEndpointBoundaryRelation stage := by
  exact ⟨endpointBoundaryDerivedKoszulOccurrence_projects stage,
    endpointBoundaryKoszulPair_cycle stage, rfl⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDerivedKoszulCycle
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
