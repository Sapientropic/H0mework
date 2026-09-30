import H0mework.Versions.Y.Arithmetic.EulerDerived.EndpointKoszulCycle

/-!
# Canonical whole-complex adjugate of the prime-dual Euler operator

The canonical block adjugate is generated before any cokernel or zero-fibre
base change.  Its complementary determinant factors act simultaneously on
the whole vertex and relation carriers, commute with the actual
factorization differential, and satisfy `T ∘ adj = D · id` in both degrees.
The relation component sends the literal endpoint boundary to the already
generated determinant preimage.

No inverse, point, zero, divisibility, fixedness, or coordinate premise enters
this producer.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugate

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDeterminantSupport
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDerivedKoszulCycle
open CategoryTheory

noncomputable section

def blockAdjugateOtherFactorProduct (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage) :
    BlockCoordinateRing :=
  (Finset.univ.erase primeIndex).prod
    (blockLocalFactor seedOccurrence.root stage)

theorem blockLocalFactor_mul_adjugateOtherFactorProduct
    (stage : Nat) (primeIndex : StagePrime seedOccurrence.root stage) :
    blockLocalFactor seedOccurrence.root stage primeIndex *
        blockAdjugateOtherFactorProduct stage primeIndex =
      blockDeterminantSection seedOccurrence.root stage := by
  rw [blockDeterminantSection_eq_actual_product]
  exact Finset.mul_prod_erase (Finset.univ)
    (blockLocalFactor seedOccurrence.root stage)
    (Finset.mem_univ primeIndex)

/-- The canonical full adjugate of `1-M`, written blockwise and multiplied
by all complementary determinant factors. -/
def blockInnerAdjugate (stage : Nat) :
    BlockInner seedOccurrence.root stage →ₗ[BlockCoordinateRing]
      BlockInner seedOccurrence.root stage where
  toFun value index :=
    blockAdjugateOtherFactorProduct stage index.1 *
      ((1 - blockA
          ((stageFactorization seedOccurrence.root stage).actualPrime index.1)) *
          value index +
        blockB
          ((stageFactorization seedOccurrence.root stage).actualPrime index.1) *
          value (index.1, index.2.rev))
  map_add' left right := by
    funext index
    simp only [Pi.add_apply]
    ring
  map_smul' scalar value := by
    funext index
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem blockEulerOperator_comp_adjugate (stage : Nat) :
    (blockEulerOperator seedOccurrence.root stage).comp
        (blockInnerAdjugate stage) =
      LinearMap.lsmul BlockCoordinateRing
        (BlockInner seedOccurrence.root stage)
        (blockDeterminantSection seedOccurrence.root stage) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨primeIndex, dualIndex⟩
  have factor := blockLocalFactor_mul_adjugateOtherFactorProduct
    stage primeIndex
  fin_cases dualIndex <;>
    simp [blockEulerOperator, blockInnerAction, blockInnerAdjugate,
      LinearMap.lsmul_apply] <;>
    rw [← factor] <;>
    unfold blockLocalFactor <;>
    ring

theorem blockAdjugate_comp_eulerOperator (stage : Nat) :
    (blockInnerAdjugate stage).comp
        (blockEulerOperator seedOccurrence.root stage) =
      LinearMap.lsmul BlockCoordinateRing
        (BlockInner seedOccurrence.root stage)
        (blockDeterminantSection seedOccurrence.root stage) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨primeIndex, dualIndex⟩
  have factor := blockLocalFactor_mul_adjugateOtherFactorProduct
    stage primeIndex
  fin_cases dualIndex <;>
    simp [blockEulerOperator, blockInnerAction, blockInnerAdjugate,
      LinearMap.lsmul_apply] <;>
    rw [← factor] <;>
    unfold blockLocalFactor <;>
    ring

theorem blockInnerAdjugate_reversal_square (stage : Nat) :
    (blockInnerReversal seedOccurrence.root stage).comp
        (blockInnerAdjugate stage) =
      (blockInnerAdjugate stage).comp
        (blockInnerReversal seedOccurrence.root stage) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨primeIndex, dualIndex⟩
  fin_cases dualIndex <;>
    simp [blockInnerReversal, blockInnerAdjugate]

theorem blockInnerAntiInvariant_adjugate_square (stage : Nat) :
    (blockInnerAntiInvariant seedOccurrence.root stage).comp
        (blockInnerAdjugate stage) =
      (blockInnerAdjugate stage).comp
        (blockInnerAntiInvariant seedOccurrence.root stage) := by
  unfold blockInnerAntiInvariant
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id,
    blockInnerAdjugate_reversal_square]

def blockWholeVertexAdjugate (stage : Nat) :
    BlockWholeVertex seedOccurrence.root stage →ₗ[BlockCoordinateRing]
      BlockWholeVertex seedOccurrence.root stage where
  toFun value role := blockInnerAdjugate stage (value role)
  map_add' left right := by
    funext role
    exact (blockInnerAdjugate stage).map_add (left role) (right role)
  map_smul' scalar value := by
    funext role
    exact (blockInnerAdjugate stage).map_smul scalar (value role)

def blockWholeRelationAdjugate (stage : Nat) :
    BlockWholeRelation seedOccurrence.root stage →ₗ[BlockCoordinateRing]
      BlockWholeRelation seedOccurrence.root stage where
  toFun value row := blockInnerAdjugate stage (value row)
  map_add' left right := by
    funext row
    exact (blockInnerAdjugate stage).map_add (left row) (right row)
  map_smul' scalar value := by
    funext row
    exact (blockInnerAdjugate stage).map_smul scalar (value row)

theorem blockFactorizationDifferential_adjugate_square (stage : Nat) :
    (blockFactorizationDifferential seedOccurrence.root stage).comp
        (blockWholeVertexAdjugate stage) =
      (blockWholeRelationAdjugate stage).comp
        (blockFactorizationDifferential seedOccurrence.root stage) := by
  apply LinearMap.ext
  intro value
  funext row
  have wholeSquare :
      blockInnerAntiInvariant seedOccurrence.root stage
          (blockInnerAdjugate stage (value none)) =
        blockInnerAdjugate stage
          (blockInnerAntiInvariant seedOccurrence.root stage (value none)) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun
      (blockInnerAntiInvariant_adjugate_square stage) (value none)
  have quotientSquare :
      blockInnerAntiInvariant seedOccurrence.root stage
          (blockInnerAdjugate stage (value (some row))) =
        blockInnerAdjugate stage
          (blockInnerAntiInvariant seedOccurrence.root stage
            (value (some row))) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun
      (blockInnerAntiInvariant_adjugate_square stage) (value (some row))
  change
    blockInnerAntiInvariant seedOccurrence.root stage
          (blockInnerAdjugate stage (value none)) -
        _ • blockInnerAntiInvariant seedOccurrence.root stage
          (blockInnerAdjugate stage (value (some row))) =
      blockInnerAdjugate stage
        (blockInnerAntiInvariant seedOccurrence.root stage (value none) -
          _ • blockInnerAntiInvariant seedOccurrence.root stage
            (value (some row)))
  rw [wholeSquare, quotientSquare, map_sub, map_smul]

def blockWholeVertexDeterminantMultiplication (stage : Nat) :
    BlockWholeVertex seedOccurrence.root stage →ₗ[BlockCoordinateRing]
      BlockWholeVertex seedOccurrence.root stage :=
  LinearMap.lsmul BlockCoordinateRing _
    (blockDeterminantSection seedOccurrence.root stage)

def blockWholeRelationDeterminantMultiplication (stage : Nat) :
    BlockWholeRelation seedOccurrence.root stage →ₗ[BlockCoordinateRing]
      BlockWholeRelation seedOccurrence.root stage :=
  LinearMap.lsmul BlockCoordinateRing _
    (blockDeterminantSection seedOccurrence.root stage)

theorem blockWholeVertexEulerOperator_comp_adjugate (stage : Nat) :
    (blockWholeVertexEulerOperator seedOccurrence.root stage).comp
        (blockWholeVertexAdjugate stage) =
      blockWholeVertexDeterminantMultiplication stage := by
  apply LinearMap.ext
  intro value
  funext role
  exact LinearMap.congr_fun (blockEulerOperator_comp_adjugate stage)
    (value role)

theorem blockWholeRelationEulerOperator_comp_adjugate (stage : Nat) :
    (blockWholeRelationEulerOperator seedOccurrence.root stage).comp
        (blockWholeRelationAdjugate stage) =
      blockWholeRelationDeterminantMultiplication stage := by
  apply LinearMap.ext
  intro value
  funext row
  exact LinearMap.congr_fun (blockEulerOperator_comp_adjugate stage)
    (value row)

noncomputable def blockDirectAdjugate (stage : Nat) :
    blockDirectComplex seedOccurrence.root stage ⟶
      blockDirectComplex seedOccurrence.root stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (blockWholeVertexAdjugate stage)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom (blockWholeRelationAdjugate stage)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      apply ModuleCat.hom_ext
      exact blockFactorizationDifferential_adjugate_square stage
    · simp [blockDirectComplex, blockDirectDifferential, sourceZero]

noncomputable def blockDirectEulerOperator (stage : Nat) :
    blockDirectComplex seedOccurrence.root stage ⟶
      blockDirectComplex seedOccurrence.root stage :=
  𝟙 _ - blockDirectEulerAction seedOccurrence.root stage

noncomputable def blockDirectDeterminantMultiplication (stage : Nat) :
    blockDirectComplex seedOccurrence.root stage ⟶
      blockDirectComplex seedOccurrence.root stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (blockWholeVertexDeterminantMultiplication stage)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom (blockWholeRelationDeterminantMultiplication stage)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro value
      exact (blockFactorizationDifferential seedOccurrence.root stage).map_smul
        (blockDeterminantSection seedOccurrence.root stage) value
    · simp [blockDirectComplex, blockDirectDifferential, sourceZero]

theorem blockDirectEulerOperator_comp_adjugate (stage : Nat) :
    blockDirectAdjugate stage ≫ blockDirectEulerOperator stage =
      blockDirectDeterminantMultiplication stage := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (blockWholeVertexEulerOperator_comp_adjugate stage) value
  · by_cases degreeOne : degree = 1
    · subst degree
      exact LinearMap.congr_fun
        (blockWholeRelationEulerOperator_comp_adjugate stage) value
    · let targetSubsingleton : Subsingleton
          ((blockDirectComplex seedOccurrence.root stage).X degree) := by
        change Subsingleton (BlockDirectObject seedOccurrence.root stage degree)
        simp [BlockDirectObject, degreeZero, degreeOne]
        exact ⟨fun left right => funext fun index => Fin.elim0 index⟩
      exact @Subsingleton.elim _ targetSubsingleton _ _

theorem blockWholeRelationAdjugate_endpointBoundary (stage : Nat) :
    blockWholeRelationAdjugate stage
        (localBlockEndpointBoundaryRelation stage) =
      blockEndpointBoundaryDeterminantPreimage stage := by
  funext row index
  rcases index with ⟨primeIndex, dualIndex⟩
  fin_cases dualIndex <;>
    simp [blockWholeRelationAdjugate, blockInnerAdjugate,
      localBlockEndpointBoundaryRelation,
      localBlockEndpointAntiInvariant,
      blockWholeAntiInvariantProjection,
      blockInnerAntiInvariant, blockInnerReversal,
      localBlockEndpointVertexMap, blockLeftEndpointBase,
      blockEndpointBoundaryDeterminantPreimage,
      blockAntiAdjugateCofactor,
      blockLocalDeterminantFactor, blockLocalFactor,
      blockAdjugateOtherFactorProduct,
      blockInvariantOperatorFactor, blockInvariantEigenvalue] <;>
    ring

def blockWholeComplexAdjugateOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        ((blockDirectComplex seedOccurrence.root stage ⟶
            blockDirectComplex seedOccurrence.root stage) ×
          (blockDirectComplex seedOccurrence.root stage ⟶
            blockDirectComplex seedOccurrence.root stage) ×
          (blockDirectComplex seedOccurrence.root stage ⟶
            blockDirectComplex seedOccurrence.root stage))) :=
  (blockWholeComplexActionOccurrence seedOccurrence.root stage).map
    fun readout =>
      (readout.1, (readout.2, blockDirectAdjugate stage,
        blockDirectDeterminantMultiplication stage))

theorem blockWholeComplexAdjugateOccurrence_projects_action (stage : Nat) :
    (blockWholeComplexAdjugateOccurrence stage).map
        (fun readout => (readout.1, readout.2.1)) =
      blockWholeComplexActionOccurrence seedOccurrence.root stage := by
  unfold blockWholeComplexAdjugateOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (blockWholeComplexActionOccurrence seedOccurrence.root stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem blockWholeComplexAdjugateOccurrence_projects_source (stage : Nat) :
    (blockWholeComplexAdjugateOccurrence stage).map Prod.fst =
      stageOccurrenceFrom seedOccurrence.root stage := by
  rw [← blockWholeComplexActionOccurrence_projects
    seedOccurrence.root stage,
    ← blockWholeComplexAdjugateOccurrence_projects_action stage,
    RootedAccountedUnfolding.map_map]
  rfl

theorem preserves_exact_whole_action_adjugate_determinant_and_endpoint
    (stage : Nat) :
    (blockWholeComplexAdjugateOccurrence stage).map Prod.fst =
        stageOccurrenceFrom seedOccurrence.root stage ∧
      blockDirectAdjugate stage ≫ blockDirectEulerOperator stage =
        blockDirectDeterminantMultiplication stage ∧
      (blockFactorizationDifferential seedOccurrence.root stage).comp
          (blockWholeVertexAdjugate stage) =
        (blockWholeRelationAdjugate stage).comp
          (blockFactorizationDifferential seedOccurrence.root stage) ∧
      blockWholeRelationAdjugate stage
          (localBlockEndpointBoundaryRelation stage) =
        blockEndpointBoundaryDeterminantPreimage stage := by
  exact ⟨blockWholeComplexAdjugateOccurrence_projects_source stage,
    blockDirectEulerOperator_comp_adjugate stage,
    blockFactorizationDifferential_adjugate_square stage,
    blockWholeRelationAdjugate_endpointBoundary stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugate
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
