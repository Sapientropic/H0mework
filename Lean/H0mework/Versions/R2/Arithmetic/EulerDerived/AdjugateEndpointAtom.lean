import H0mework.Realization.MappingCone.MappedBoundaryAtom
import H0mework.Realization.MappingCone.Functoriality
import H0mework.Versions.R2.Arithmetic.EulerDerived.AdjugateSuccessor

/-!
# Actual endpoint atom in the whole adjugate total fibre

For an actual whole-complex endpoint, its source differential is a canonical
degree-one cycle.  The already generated determinant-adjugate total inclusion
maps this cycle to the differential of the corresponding total-fibre endpoint.
The generic mapped-boundary construction therefore generates the corrected
endpoint point.  No cycle, total-fibre point, determinant equation, or endpoint
fixedness is supplied by a caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberEndpointAtom

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex.HomComplex
open CochainMappingCoconeDeterminantAdjugateInclusion
open CochainMappingCoconeDeterminantAdjugateTotalFiber
open CochainMappingCoconeFunctoriality
open CochainMappingCoconeMappedBoundaryAtomOver
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugate
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberSuccessor
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant

noncomputable section

/-- The actual differential of a whole-complex endpoint, retained in the
canonical cycle object. -/
noncomputable def localSourceEndpointBoundaryCycle
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    (LocalWholeComplex stage).cycles 1 :=
  ((LocalWholeComplex stage).toCycles 0 1).hom endpoint

theorem localSourceEndpointBoundaryCycle_underlying
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    ((LocalWholeComplex stage).iCycles 1).hom
        (localSourceEndpointBoundaryCycle stage endpoint) =
      ((LocalWholeComplex stage).d 0 1).hom endpoint := by
  exact ConcreteCategory.congr_hom
    ((LocalWholeComplex stage).toCycles_i 0 1) endpoint

/-- Chain-map naturality is the entire domain incidence required by the
generic mapped-boundary constructor. -/
theorem localTotalEndpointElement_mappedBoundary
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    ((LocalTotalFiber stage).d 0 1).hom
        (localTotalEndpointElement stage endpoint) =
      ((LocalTotalFiber stage).iCycles 1).hom
        ((cyclesMap (localTotalInclusion stage) 1).hom
          (localSourceEndpointBoundaryCycle stage endpoint)) := by
  have differentialNaturality := ConcreteCategory.congr_hom
    ((localTotalInclusion stage).comm 0 1) endpoint
  have cycleNaturality := ConcreteCategory.congr_hom
    (cyclesMap_i (localTotalInclusion stage) 1)
      (localSourceEndpointBoundaryCycle stage endpoint)
  calc
    ((LocalTotalFiber stage).d 0 1).hom
        (localTotalEndpointElement stage endpoint) =
      ((localTotalInclusion stage).f 1).hom
        (((LocalWholeComplex stage).d 0 1).hom endpoint) := by
          simpa only [localTotalEndpointElement,
            ConcreteCategory.comp_apply] using differentialNaturality
    _ = ((localTotalInclusion stage).f 1).hom
        (((LocalWholeComplex stage).iCycles 1).hom
          (localSourceEndpointBoundaryCycle stage endpoint)) := by
            rw [localSourceEndpointBoundaryCycle_underlying]
    _ = ((LocalTotalFiber stage).iCycles 1).hom
        ((cyclesMap (localTotalInclusion stage) 1).hom
          (localSourceEndpointBoundaryCycle stage endpoint)) := by
            simpa only [ConcreteCategory.comp_apply] using cycleNaturality.symm

/-- The exact cycle/boundary/incidence packet consumed by the frozen generic
mapped-boundary atom. -/
noncomputable def localCorrectedEndpointPointAt
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    MappedBoundaryPointAt (localTotalInclusion stage) where
  cycle := localSourceEndpointBoundaryCycle stage endpoint
  boundary := localTotalEndpointElement stage endpoint
  mapped := localTotalEndpointElement_mappedBoundary stage endpoint

/-- Framework-generated corrected endpoint point in the fibre of the actual
determinant-adjugate total inclusion. -/
noncomputable def localCorrectedEndpointPoint
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    ScalarSingleOne ⟶
      CochainComplex.mappingCocone (localTotalInclusion stage) :=
  (localCorrectedEndpointPointAt stage endpoint).ofPoint

@[reassoc (attr := simp)] theorem localCorrectedEndpointPoint_fst
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    localCorrectedEndpointPoint stage endpoint ≫
        CochainComplex.mappingCocone.fst (localTotalInclusion stage) =
      cycleMorphism (localSourceEndpointBoundaryCycle stage endpoint) :=
  MappedBoundaryPointAt.ofPoint_fst
    (localCorrectedEndpointPointAt stage endpoint)

@[reassoc] theorem localCorrectedEndpointPoint_snd
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    (localCorrectedEndpointPoint stage endpoint).f 1 ≫
        (CochainComplex.mappingCocone.snd
          (localTotalInclusion stage)).v 1 0 (by omega) =
      -boundaryGenerator (localTotalEndpointElement stage endpoint) :=
  MappedBoundaryPointAt.ofPoint_snd
    (localCorrectedEndpointPointAt stage endpoint)

/-- The nested total-fibre readback is still the literal source endpoint. -/
theorem localCorrectedEndpointPoint_totalEndpointReadback
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    localTotalEndpointReadback stage endpoint = endpoint :=
  localTotalEndpointReadback_eq stage endpoint

/-- Evaluating the shifted mapping-cocone coordinate at the scalar generator
recovers the negative total-fibre endpoint, with no hidden normalization. -/
theorem localCorrectedEndpointPoint_snd_one
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    (((localCorrectedEndpointPoint stage endpoint).f 1 ≫
        (CochainComplex.mappingCocone.snd
          (localTotalInclusion stage)).v 1 0 (by omega)).hom
          (1 : BlockCoordinateRing)) =
      -localTotalEndpointElement stage endpoint := by
  rw [localCorrectedEndpointPoint_snd]
  change -((boundaryGenerator
    (localTotalEndpointElement stage endpoint)).hom
      (1 : BlockCoordinateRing)) = _
  unfold boundaryGenerator
  rw [elementHom_one]

/-- Reading the nested total-fibre endpoint coordinate after the atom's
mapping-cocone sign gives precisely the negative original endpoint. -/
theorem localCorrectedEndpointPoint_rawEndpointReadback
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    ((biprod.snd : LocalWholeComplex stage ⊞ LocalWholeComplex stage ⟶
        LocalWholeComplex stage).f 0).hom
      (((CochainComplex.mappingCocone.fst
        (totalRow (blockDirectEulerOperator stage)
          (blockDirectDeterminantMultiplication stage))).f 0).hom
        (-localTotalEndpointElement stage endpoint)) =
      -endpoint := by
  rw [map_neg, map_neg]
  change -localTotalEndpointReadback stage endpoint = -endpoint
  rw [localTotalEndpointReadback_eq]

theorem preserves_actual_total_inclusion_mapped_boundary_and_endpoint
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    ((LocalWholeComplex stage).iCycles 1).hom
        (localSourceEndpointBoundaryCycle stage endpoint) =
        ((LocalWholeComplex stage).d 0 1).hom endpoint ∧
      ((LocalTotalFiber stage).d 0 1).hom
          (localTotalEndpointElement stage endpoint) =
        ((LocalTotalFiber stage).iCycles 1).hom
          ((cyclesMap (localTotalInclusion stage) 1).hom
            (localSourceEndpointBoundaryCycle stage endpoint)) ∧
      localTotalEndpointReadback stage endpoint = endpoint :=
  ⟨localSourceEndpointBoundaryCycle_underlying stage endpoint,
    localTotalEndpointElement_mappedBoundary stage endpoint,
    localTotalEndpointReadback_eq stage endpoint⟩

/-- The actual whole-complex successor sends the source boundary cycle to
the boundary cycle of the strictly restricted endpoint. -/
theorem localSourceEndpointBoundaryCycle_successor
    (stage : Nat)
    (endpoint : (LocalWholeComplex (stage + 1)).X 0) :
    (cyclesMap (blockDirectRestriction seedOccurrence.root stage) 1).hom
        (localSourceEndpointBoundaryCycle (stage + 1) endpoint) =
      localSourceEndpointBoundaryCycle stage
        (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
          endpoint) := by
  apply (ModuleCat.mono_iff_injective
    ((LocalWholeComplex stage).iCycles 1)).mp inferInstance
  have cycleNaturality := ConcreteCategory.congr_hom
    (cyclesMap_i (blockDirectRestriction seedOccurrence.root stage) 1)
      (localSourceEndpointBoundaryCycle (stage + 1) endpoint)
  have differentialNaturality := ConcreteCategory.congr_hom
    ((blockDirectRestriction seedOccurrence.root stage).comm 0 1) endpoint
  calc
    ((LocalWholeComplex stage).iCycles 1).hom
        ((cyclesMap (blockDirectRestriction seedOccurrence.root stage) 1).hom
          (localSourceEndpointBoundaryCycle (stage + 1) endpoint)) =
      ((blockDirectRestriction seedOccurrence.root stage).f 1).hom
        (((LocalWholeComplex (stage + 1)).iCycles 1).hom
          (localSourceEndpointBoundaryCycle (stage + 1) endpoint)) := by
            simpa only [ConcreteCategory.comp_apply] using cycleNaturality
    _ = ((blockDirectRestriction seedOccurrence.root stage).f 1).hom
        (((LocalWholeComplex (stage + 1)).d 0 1).hom endpoint) := by
          rw [localSourceEndpointBoundaryCycle_underlying]
    _ = ((LocalWholeComplex stage).d 0 1).hom
        (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
          endpoint) := by
            simpa only [ConcreteCategory.comp_apply] using
              differentialNaturality.symm
    _ = ((LocalWholeComplex stage).iCycles 1).hom
        (localSourceEndpointBoundaryCycle stage
          (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
            endpoint)) := by
              rw [localSourceEndpointBoundaryCycle_underlying]

/-- The shear-generated total-fibre successor sends the actual total endpoint
to the total endpoint of the raw restricted source endpoint. -/
theorem localTotalEndpointElement_successor
    (stage : Nat)
    (endpoint : (LocalWholeComplex (stage + 1)).X 0) :
    ((localTotalFiberRestriction stage).f 0).hom
        (localTotalEndpointElement (stage + 1) endpoint) =
      localTotalEndpointElement stage
        (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
          endpoint) := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun map => map.f 0) (localTotalInclusion_successor stage))
      endpoint

/-- Consequently the nested pair projection reads the literal restricted
endpoint.  This is the raw-coordinate kill test for the shear successor. -/
theorem localTotalEndpointElement_successor_rawEndpointReadback
    (stage : Nat)
    (endpoint : (LocalWholeComplex (stage + 1)).X 0) :
    ((biprod.snd : LocalWholeComplex stage ⊞ LocalWholeComplex stage ⟶
        LocalWholeComplex stage).f 0).hom
      (((CochainComplex.mappingCocone.fst
        (totalRow (blockDirectEulerOperator stage)
          (blockDirectDeterminantMultiplication stage))).f 0).hom
        (((localTotalFiberRestriction stage).f 0).hom
          (localTotalEndpointElement (stage + 1) endpoint))) =
      ((blockDirectRestriction seedOccurrence.root stage).f 0).hom
        endpoint := by
  rw [localTotalEndpointElement_successor]
  exact localTotalEndpointReadback_eq stage _

theorem preserves_actual_mapped_boundary_successor_and_raw_endpoint
    (stage : Nat)
    (endpoint : (LocalWholeComplex (stage + 1)).X 0) :
    (cyclesMap (blockDirectRestriction seedOccurrence.root stage) 1).hom
        (localSourceEndpointBoundaryCycle (stage + 1) endpoint) =
      localSourceEndpointBoundaryCycle stage
        (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
          endpoint) ∧
      ((localTotalFiberRestriction stage).f 0).hom
          (localTotalEndpointElement (stage + 1) endpoint) =
        localTotalEndpointElement stage
          (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
            endpoint) ∧
      (localTotalFiberShearSuccessor stage).pairTransition ≫
          (biprod.snd : LocalWholeComplex stage ⊞ LocalWholeComplex stage ⟶
            LocalWholeComplex stage) =
        (biprod.snd : LocalWholeComplex (stage + 1) ⊞
            LocalWholeComplex (stage + 1) ⟶
              LocalWholeComplex (stage + 1)) ≫
          blockDirectRestriction seedOccurrence.root stage :=
  ⟨localSourceEndpointBoundaryCycle_successor stage endpoint,
    localTotalEndpointElement_successor stage endpoint,
    localTotalFiberRestriction_preserves_raw_endpoint stage⟩

/-- The actual inclusion square induces the corrected-endpoint fibre
successor.  Both legs are source generated: the whole-complex restriction and
the determinant-adjugate shear transition. -/
noncomputable def localCorrectedEndpointRestriction (stage : Nat) :
    CochainComplex.mappingCocone (localTotalInclusion (stage + 1)) ⟶
      CochainComplex.mappingCocone (localTotalInclusion stage) :=
  mappingCoconeMap
    (localTotalInclusion (stage + 1)) (localTotalInclusion stage)
    (blockDirectRestriction seedOccurrence.root stage)
    (localTotalFiberRestriction stage)
    (localTotalInclusion_successor stage).symm

@[reassoc (attr := simp)] theorem localCorrectedEndpointRestriction_fst
    (stage : Nat) :
    localCorrectedEndpointRestriction stage ≫
        CochainComplex.mappingCocone.fst (localTotalInclusion stage) =
      CochainComplex.mappingCocone.fst
          (localTotalInclusion (stage + 1)) ≫
        blockDirectRestriction seedOccurrence.root stage :=
  mappingCoconeMap_fst
    (localTotalInclusion (stage + 1)) (localTotalInclusion stage)
    (blockDirectRestriction seedOccurrence.root stage)
    (localTotalFiberRestriction stage)
    (localTotalInclusion_successor stage).symm

theorem localCorrectedEndpointRestriction_snd (stage : Nat) :
    (Cochain.ofHom (localCorrectedEndpointRestriction stage)).comp
        (CochainComplex.mappingCocone.snd
          (localTotalInclusion stage)) (zero_add (-1)) =
      (CochainComplex.mappingCocone.snd
        (localTotalInclusion (stage + 1))).comp
          (Cochain.ofHom (localTotalFiberRestriction stage))
            (add_zero (-1)) :=
  mappingCoconeMap_snd
    (localTotalInclusion (stage + 1)) (localTotalInclusion stage)
    (blockDirectRestriction seedOccurrence.root stage)
    (localTotalFiberRestriction stage)
    (localTotalInclusion_successor stage).symm

theorem localEndpointCycleGenerator_successor
    (stage : Nat)
    (endpoint : (LocalWholeComplex (stage + 1)).X 0) :
    cycleGenerator (localSourceEndpointBoundaryCycle (stage + 1) endpoint) ≫
        (blockDirectRestriction seedOccurrence.root stage).f 1 =
      cycleGenerator (localSourceEndpointBoundaryCycle stage
        (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
          endpoint)) := by
  unfold cycleGenerator
  rw [Category.assoc,
    ← cyclesMap_i (blockDirectRestriction seedOccurrence.root stage) 1,
    ← Category.assoc, elementHom_comp,
    localSourceEndpointBoundaryCycle_successor]

theorem localEndpointCycleMorphism_successor
    (stage : Nat)
    (endpoint : (LocalWholeComplex (stage + 1)).X 0) :
    cycleMorphism (localSourceEndpointBoundaryCycle (stage + 1) endpoint) ≫
        blockDirectRestriction seedOccurrence.root stage =
      cycleMorphism (localSourceEndpointBoundaryCycle stage
        (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
          endpoint)) := by
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp]
  have highCochain :
      Cochain.ofHom
          (cycleMorphism
            (localSourceEndpointBoundaryCycle (stage + 1) endpoint)) =
        Cochain.fromSingleMk
          (cycleGenerator
            (localSourceEndpointBoundaryCycle (stage + 1) endpoint))
          (by norm_num) := by
    unfold cycleMorphism
    exact Cocycle.cochain_ofHom_homOf_eq_coe _
  have lowCochain :
      Cochain.ofHom
          (cycleMorphism (localSourceEndpointBoundaryCycle stage
            (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
              endpoint))) =
        Cochain.fromSingleMk
          (cycleGenerator (localSourceEndpointBoundaryCycle stage
            (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
              endpoint))) (by norm_num) := by
    unfold cycleMorphism
    exact Cocycle.cochain_ofHom_homOf_eq_coe _
  rw [highCochain, lowCochain,
    ← Cochain.fromSingleMk_postcomp,
    localEndpointCycleGenerator_successor]

/-- The source-cycle coordinate of the generated corrected endpoint is
strictly natural under the actual successor. -/
theorem localCorrectedEndpointPoint_successor_fst
    (stage : Nat)
    (endpoint : (LocalWholeComplex (stage + 1)).X 0) :
    (localCorrectedEndpointPoint (stage + 1) endpoint ≫
        localCorrectedEndpointRestriction stage) ≫
          CochainComplex.mappingCocone.fst
            (localTotalInclusion stage) =
      localCorrectedEndpointPoint stage
          (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
            endpoint) ≫
        CochainComplex.mappingCocone.fst
          (localTotalInclusion stage) := by
  rw [Category.assoc, localCorrectedEndpointRestriction_fst,
    ← Category.assoc, localCorrectedEndpointPoint_fst,
    localEndpointCycleMorphism_successor,
    localCorrectedEndpointPoint_fst]

/-- The shifted target coordinate is also strictly natural; the shear keeps
the raw total endpoint rather than multiplying it by the relative
determinant. -/
theorem localCorrectedEndpointPoint_successor_snd
    (stage : Nat)
    (endpoint : (LocalWholeComplex (stage + 1)).X 0) :
    ((localCorrectedEndpointPoint (stage + 1) endpoint ≫
        localCorrectedEndpointRestriction stage).f 1) ≫
          (CochainComplex.mappingCocone.snd
            (localTotalInclusion stage)).v 1 0 (by omega) =
      (localCorrectedEndpointPoint stage
        (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
          endpoint)).f 1 ≫
          (CochainComplex.mappingCocone.snd
            (localTotalInclusion stage)).v 1 0 (by omega) := by
  have transitionSnd := Cochain.congr_v
    (localCorrectedEndpointRestriction_snd stage) 1 0 (by omega)
  have transitionSndComponent :
      (localCorrectedEndpointRestriction stage).f 1 ≫
          (CochainComplex.mappingCocone.snd
            (localTotalInclusion stage)).v 1 0 (by omega) =
        (CochainComplex.mappingCocone.snd
          (localTotalInclusion (stage + 1))).v 1 0 (by omega) ≫
            (localTotalFiberRestriction stage).f 0 := by
    simpa [Cochain.comp_v] using transitionSnd
  simp only [HomologicalComplex.comp_f]
  calc
    ((localCorrectedEndpointPoint (stage + 1) endpoint).f 1 ≫
        (localCorrectedEndpointRestriction stage).f 1) ≫
          (CochainComplex.mappingCocone.snd
            (localTotalInclusion stage)).v 1 0 (by omega) =
      (localCorrectedEndpointPoint (stage + 1) endpoint).f 1 ≫
        ((localCorrectedEndpointRestriction stage).f 1 ≫
          (CochainComplex.mappingCocone.snd
            (localTotalInclusion stage)).v 1 0 (by omega)) :=
        Category.assoc _ _ _
    _ = (localCorrectedEndpointPoint (stage + 1) endpoint).f 1 ≫
        ((CochainComplex.mappingCocone.snd
          (localTotalInclusion (stage + 1))).v 1 0 (by omega) ≫
            (localTotalFiberRestriction stage).f 0) := by
              rw [transitionSndComponent]
    _ = ((localCorrectedEndpointPoint (stage + 1) endpoint).f 1 ≫
        (CochainComplex.mappingCocone.snd
          (localTotalInclusion (stage + 1))).v 1 0 (by omega)) ≫
            (localTotalFiberRestriction stage).f 0 :=
              (Category.assoc _ _ _).symm
    _ = (-boundaryGenerator
        (localTotalEndpointElement (stage + 1) endpoint)) ≫
          (localTotalFiberRestriction stage).f 0 := by
            rw [localCorrectedEndpointPoint_snd]
    _ = -boundaryGenerator
        (((localTotalFiberRestriction stage).f 0).hom
          (localTotalEndpointElement (stage + 1) endpoint)) := by
            unfold boundaryGenerator
            rw [Preadditive.neg_comp, elementHom_comp]
    _ = -boundaryGenerator
        (localTotalEndpointElement stage
          (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
            endpoint)) := by
              rw [localTotalEndpointElement_successor]
    _ = (localCorrectedEndpointPoint stage
        (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
          endpoint)).f 1 ≫
          (CochainComplex.mappingCocone.snd
            (localTotalInclusion stage)).v 1 0 (by omega) := by
              rw [localCorrectedEndpointPoint_snd]

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberEndpointAtom
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
