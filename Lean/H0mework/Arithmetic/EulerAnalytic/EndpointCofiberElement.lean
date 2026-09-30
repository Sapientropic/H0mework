import H0mework.Realization.MappingCone.Degreewise
import H0mework.Arithmetic.EulerAnalytic.GlobalActionCofiber

/-!
# The analytic endpoint element in the global block-action cofiber

The source-owned endpoint chain enters the already generated action cofiber
through its tautological inclusion.  A small ring-polymorphic adapter reads
the generic mapping-cocone naturality at that literal element.  No cycle,
action-zero law, fixedness, or endpoint equality is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open CochainComplex.HomComplex
open CategoryTheory
open HomologicalComplex
open scoped ChangeOfRings

noncomputable section

/-- Ring-polymorphic form of the frozen `inr` naturality calculation. -/
theorem mappingCoconeMap_inr_over
    {R : Type*} [CommRing R]
    {K L : CochainComplex (ModuleCat R) ℤ}
    (arrow : K ⟶ L) (left : K ⟶ K) (right : L ⟶ L)
    (square : left ≫ arrow = arrow ≫ right) :
    (CochainComplex.mappingCocone.inr arrow).1.comp
        (Cochain.ofHom
          (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow arrow left right square)) (add_zero 1) =
      (Cochain.ofHom right).comp
        (CochainComplex.mappingCocone.inr arrow).1 (zero_add 1) := by
  ext sourceDegree targetDegree degree_eq : 1
  rw [Cochain.comp_v _ _ (add_zero 1)
      sourceDegree targetDegree targetDegree degree_eq
        (add_zero targetDegree),
    Cochain.comp_v _ _ (zero_add 1)
      sourceDegree sourceDegree targetDegree
        (add_zero sourceDegree) degree_eq]
  simp only [Cochain.ofHom_v]
  apply CochainMappingCoconeDegreewiseKernel.degree_hom_ext_at
    arrow targetDegree sourceDegree (by omega)
  · have generated := congrArg (fun map ↦ map.f targetDegree)
      (CochainMappingCoconeFunctoriality.mappingCoconeMap_fst
        arrow arrow left right square)
    simp only [HomologicalComplex.comp_f] at generated
    rw [Category.assoc, generated]
    simp
  · have generated := Cochain.congr_v
      (CochainMappingCoconeFunctoriality.mappingCoconeMap_snd
        arrow arrow left right square)
      targetDegree sourceDegree (by omega)
    have generatedComponent :
        (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow arrow left right square).f targetDegree ≫
            (CochainComplex.mappingCocone.snd arrow).v
              targetDegree sourceDegree (by omega) =
          (CochainComplex.mappingCocone.snd arrow).v
              targetDegree sourceDegree (by omega) ≫
            right.f sourceDegree := by
      simpa [Cochain.comp_v] using generated
    rw [Category.assoc, generatedComponent]
    simp [Category.assoc]

def pairBlockEndpointCofiberElement : PairBlockActionCofiber.X 1 :=
  (pairBlockTautologicalInclusion.1.v 0 1 (by omega)).hom
    pairBlockGlobalEndpointSection

def pairBlockReversedEndpointSection : PairBlockGlobalState.X 0 :=
  universalLeftCoordinate installedOwner
      ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
        globalBlockRightEndpoint +
    universalRightCoordinate installedOwner
      ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
        globalBlockLeftEndpoint

theorem pairBlockEndpointCofiberElement_reversal :
    (pairBlockCofiberReversal.f 1).hom
        pairBlockEndpointCofiberElement =
      (pairBlockTautologicalInclusion.1.v 0 1 (by omega)).hom
        pairBlockReversedEndpointSection := by
  have naturality := mappingCoconeMap_inr_over
    pairBlockGlobalEulerOperator pairBlockGlobalReversal
      pairBlockGlobalReversal pairBlockGlobalReversal_operator_square
  have component := Cochain.congr_v naturality 0 1 (by omega)
  have componentHom := congrArg ModuleCat.Hom.hom component
  have applied := LinearMap.congr_fun componentHom
    pairBlockGlobalEndpointSection
  change (pairBlockCofiberReversal.f 1).hom
      ((pairBlockTautologicalInclusion.1.v 0 1 (by omega)).hom
        pairBlockGlobalEndpointSection) =
    (pairBlockTautologicalInclusion.1.v 0 1 (by omega)).hom
      ((pairBlockGlobalReversal.f 0).hom
        pairBlockGlobalEndpointSection) at applied
  rw [pairBlockGlobalReversal_endpointSection] at applied
  exact applied

def pairBlockEndpointCofiberOccurrence : RootedAccountedUnfolding
    (FactorizationPayload × PairBlockActionCofiber.X 1) :=
  seedOccurrence.map fun owner => (owner, pairBlockEndpointCofiberElement)

theorem pairBlockEndpointCofiberOccurrence_projects :
    pairBlockEndpointCofiberOccurrence.map Prod.fst = seedOccurrence := by
  unfold pairBlockEndpointCofiberOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_exact_owner_endpoint_element_and_reversal :
    pairBlockGlobalActionCofiberFace.root = seedOccurrence ∧
      pairBlockEndpointCofiberOccurrence.map Prod.fst = seedOccurrence ∧
      (pairBlockCofiberReversal.f 1).hom
          pairBlockEndpointCofiberElement =
        (pairBlockTautologicalInclusion.1.v 0 1 (by omega)).hom
          pairBlockReversedEndpointSection := by
  exact ⟨pairBlockGlobalActionCofiberFace.preserves_actual_transition.1,
    pairBlockEndpointCofiberOccurrence_projects,
    pairBlockEndpointCofiberElement_reversal⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
