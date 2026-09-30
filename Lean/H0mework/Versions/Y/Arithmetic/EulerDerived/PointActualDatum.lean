import H0mework.Realization.MappingCone.TotalFibreSymmetry
import H0mework.Versions.Y.Arithmetic.EulerDerived.SolutionCofinal

/-!
# Source-only boundary/cochain datum of a generated block point

This narrow core exposes the two coupled coordinates of a corrected derived
point without importing determinant-point fixedness or a Riemann consumer:

* the strict degree-one source boundary;
* the degree `-1` endpoint cochain whose coboundary is that boundary.

The compatibility module with the historical wider import surface re-exports
these declarations under the same namespace.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedPointActualDatum

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionCofinal
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugate
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberEndpointAtom
open CochainMappingCoconeDeterminantAdjugateTotalFiber
open CochainMappingCoconeMappedBoundaryAtomOver
open CochainMappingCoconeTotalFiberSymmetry

noncomputable section

/-- The strict source coordinate of one local derived point. -/
noncomputable def localDerivedStrictSource (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    ScalarSingleOne (R := BlockCoordinateRing) ⟶ LocalWholeComplex stage :=
  point ≫ CochainComplex.mappingCocone.fst (localTotalInclusion stage)

theorem localCorrectedEndpoint_strictSource (stage : Nat)
    (endpoint : (LocalWholeComplex stage).X 0) :
    localDerivedStrictSource stage
        (localCorrectedEndpointPoint stage endpoint) =
      cycleMorphism (localSourceEndpointBoundaryCycle stage endpoint) := by
  exact localCorrectedEndpointPoint_fst stage endpoint

/-- The generated total-fibre projection whose second Koszul coordinate is
the literal whole-relation complex. -/
noncomputable def localTotalEndpointProjection (stage : Nat) :
    LocalTotalFiber stage ⟶ LocalWholeComplex stage :=
  CochainComplex.mappingCocone.fst
      (totalRow (blockDirectEulerOperator stage)
        (blockDirectDeterminantMultiplication stage)) ≫
    biprod.snd

@[reassoc (attr := simp)] theorem localTotalEndpointProjection_section
    (stage : Nat) :
    localTotalInclusion stage ≫ localTotalEndpointProjection stage =
      𝟙 (LocalWholeComplex stage) := by
  unfold localTotalEndpointProjection
  exact localTotalInclusion_endpoint_readback stage

/-- The shifted endpoint coordinate remains a cochain; replacing it by a
strict degree-zero point would discard the actual source boundary. -/
noncomputable def localDerivedEndpointCochain (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    Cochain (ScalarSingleOne (R := BlockCoordinateRing))
      (LocalWholeComplex stage) (-1) :=
  (Cochain.ofHom point).comp
    ((CochainComplex.mappingCocone.snd
      (localTotalInclusion stage)).comp
        (Cochain.ofHom (localTotalEndpointProjection stage))
          (add_zero (-1)))
    (zero_add (-1))

/-- The mapping-cocone differential keeps the two coordinates coupled. -/
theorem localDerivedEndpointCochain_delta (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    δ (-1) 0 (localDerivedEndpointCochain stage point) =
      -Cochain.ofHom (localDerivedStrictSource stage point) := by
  unfold localDerivedEndpointCochain localDerivedStrictSource
  rw [δ_ofHom_comp, δ_comp_ofHom]
  have sndDelta := mappingCocone_delta_snd (localTotalInclusion stage)
  rw [add_eq_zero_iff_eq_neg] at sndDelta
  rw [sndDelta]
  simp only [Cochain.comp_neg, Cochain.neg_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.ofHom_comp]
  have sectionCochain :
      (Cochain.ofHom (localTotalInclusion stage)).comp
          (Cochain.ofHom (localTotalEndpointProjection stage))
            (zero_add 0) =
        Cochain.ofHom (𝟙 (LocalWholeComplex stage)) := by
    rw [← Cochain.ofHom_comp,
      localTotalEndpointProjection_section]
  rw [sectionCochain]
  simp

def scalarSingleOneGenerator :
    (ScalarSingleOne (R := BlockCoordinateRing)).X 1 := by
  exact (HomologicalComplex.singleObjXSelf
    (ComplexShape.up ℤ) 1
      (ScalarUnit (R := BlockCoordinateRing))).inv.hom 1

/-- The complete datum reads the original endpoint before any anti-invariant
or complex-coordinate projection. -/
theorem localCorrectedEndpoint_endpointCochain (stage : Nat)
    (endpoint : (LocalWholeComplex stage).X 0) :
    (localDerivedEndpointCochain stage
        (localCorrectedEndpointPoint stage endpoint)).v 1 0 (by omega)
          scalarSingleOneGenerator = -endpoint := by
  change ((localTotalEndpointProjection stage).f 0).hom
    ((((localCorrectedEndpointPoint stage endpoint).f 1 ≫
      (CochainComplex.mappingCocone.snd
        (localTotalInclusion stage)).v 1 0 (by omega)).hom)
      scalarSingleOneGenerator) = -endpoint
  change ((localTotalEndpointProjection stage).f 0).hom
    ((((localCorrectedEndpointPoint stage endpoint).f 1 ≫
      (CochainComplex.mappingCocone.snd
        (localTotalInclusion stage)).v 1 0 (by omega)).hom)
      (1 : BlockCoordinateRing)) = -endpoint
  rw [localCorrectedEndpointPoint_snd_one]
  rw [map_neg]
  unfold localTotalEndpointProjection
  change -localTotalEndpointReadback stage endpoint = -endpoint
  rw [localTotalEndpointReadback_eq]

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedPointActualDatum
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
