import H0mework.Foundation.Relations.ScalarCochainMap
import H0mework.Versions.R2.Arithmetic.RiemannMellinOrbit.ProperMellinFullRowIncidence

/-!
# Proper Mellin cycles consume the scalar cochain presentation

The same zero-owned full-row complex now consumes the coefficient-neutral
relation/cochain foundation over `ℂ`.  The proper-`L¹` pair is lifted to the
canonical presented degree-one carrier, its presentation reads back to the
actual cycle, and the generated presented differential sends it to zero.

This closes scalar relation/cochain admission.  It deliberately does not
identify the cycle kernel with the stronger full-row C-readback kernel; that
remaining distinction is preserved by the existing readback formula.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace QRich
namespace ProperMellinScalarRelationIncidence

open CategoryTheory
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open ScalarRelationPresentation
open ScalarCochainRelation

noncomputable section

abbrev IncidenceOccurrence :=
  zeroOwnedProperMellinPointFullRowIncidenceOccurrence

/-- The actual point-full-row complex is exposed from the same incidence
occurrence; it is not rebuilt from a sibling seed occurrence. -/
noncomputable def complexAt (stage : Nat)
    (payload : ProperMellinPointFullRowIncidencePayloadAt stage) :
    CochainComplex (ModuleCat ℂ) ℤ :=
  PointFullRowVerticalTotal (zeroPayloadDeterminantPoint payload.1) stage

noncomputable def complexOccurrence
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    RootedAccountedUnfolding
      (CochainComplex (ModuleCat ℂ) ℤ) :=
  (IncidenceOccurrence observation stage).map (complexAt stage)

def relationFace
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    ScalarCochainRelation.RootFace
      (IncidenceOccurrence observation stage)
      (complexAt stage) :=
  ScalarCochainRelation.RootFace.generate

theorem relationFace_preserves_incidence_root
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    (relationFace observation stage).root =
      IncidenceOccurrence observation stage :=
  rfl

theorem relationFace_complexOccurrence_is_incidence_map
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    (relationFace observation stage).complexOccurrence =
      complexOccurrence observation stage :=
  rfl

@[simp] theorem relationFace_complex
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    (relationFace observation stage).complex =
      PointFullRowVerticalTotal
        (zeroPayloadDeterminantPoint
          (IncidenceOccurrence observation stage).root.1) stage :=
  rfl

noncomputable def actualDegreeOneMap
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    ProperMellinL1Pair →ₗ[ℂ]
      (((relationFace observation stage).complex.X 1 : Type)) :=
  (((relationFace observation stage).complex.iCycles 1).hom).comp
    ((IncidenceOccurrence observation stage).root.2.cycleMap)

/-- Lift the actual proper-Mellin cycle to the canonical scalar relation
presentation of degree one. -/
noncomputable def presentedDegreeOneMap
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    ProperMellinL1Pair →ₗ[ℂ]
      ScalarRelationPresentation.PresentedCarrier ℂ
        ((relationFace observation stage).complex.X 1) :=
  (ScalarRelationPresentation.presentedGeneratorMap
    ((relationFace observation stage).complex.X 1)).comp
      (actualDegreeOneMap observation stage)

theorem presentedDegreeOneMap_readback
    (observation : GeneratedRiemannZeroObservation) (stage : Nat)
    (value : ProperMellinL1Pair) :
    ScalarRelationPresentation.presentedEvaluation
        ((relationFace observation stage).complex.X 1)
        (presentedDegreeOneMap observation stage value) =
      actualDegreeOneMap observation stage value := by
  rw [presentedDegreeOneMap, LinearMap.comp_apply]
  exact ScalarRelationPresentation.presentedEvaluation_generator
    ((relationFace observation stage).complex.X 1)
    (actualDegreeOneMap observation stage value)

/-- The generated presented differential sees the same degree-one cycle. -/
theorem presentedDegreeOneMap_differential_zero
    (observation : GeneratedRiemannZeroObservation) (stage : Nat)
    (value : ProperMellinL1Pair) :
    (relationFace observation stage).differentialPresentedMap 1 2
        (presentedDegreeOneMap observation stage value) = 0 := by
  apply (ScalarRelationPresentation.presentedEquiv
    ((relationFace observation stage).complex.X 2)).injective
  rw [(relationFace observation stage).differential_presentedMap_commutes]
  rw [show ScalarRelationPresentation.presentedEquiv
      ((relationFace observation stage).complex.X 1)
        (presentedDegreeOneMap observation stage value) =
      actualDegreeOneMap observation stage value by
    exact presentedDegreeOneMap_readback observation stage value]
  simp only [map_zero]
  change ((relationFace observation stage).complex.d 1 2).hom
      (actualDegreeOneMap observation stage value) = 0
  rw [actualDegreeOneMap, LinearMap.comp_apply,
    zeroOwnedProperMellinPointFullRowIncidenceOccurrence_root_cycleMap]
  change ((PointFullRowVerticalTotal
      (zeroPayloadDeterminantPoint
        (IncidenceOccurrence observation stage).root.1) stage).d 1 2).hom
      (((PointFullRowVerticalTotal
        (zeroPayloadDeterminantPoint
          (IncidenceOccurrence observation stage).root.1) stage).iCycles 1).hom
        (properMellinL1PointFullRowCycle
          (zeroPayloadDeterminantPoint
            (IncidenceOccurrence observation stage).root.1) stage value)) = 0
  rw [properMellinL1PointFullRowCycle, LinearMap.comp_apply,
    pointFullRowHomCycle_inclusion]
  have comm := ConcreteCategory.congr_hom
    ((properMellinL1PointFullRowHom
      (zeroPayloadDeterminantPoint
        (IncidenceOccurrence observation stage).root.1) stage value).comm 1 2)
    (pointFullRowSourceGenerator
      (zeroPayloadDeterminantPoint
        (IncidenceOccurrence observation stage).root.1))
  simpa using comm

theorem presentedDegreeOneMap_readback_formula
    (observation : GeneratedRiemannZeroObservation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (value : ProperMellinL1Pair) :
    pointFullRowCycleCReadback
        (zeroPayloadDeterminantPoint
          (IncidenceOccurrence observation stage).root.1)
        stage row
        ((IncidenceOccurrence observation stage).root.2.cycleMap value) =
      -(quotientCoefficient row : ℂ) *
        (positiveMellinL1Integral value.1 -
          positiveMellinL1Integral value.2) :=
  zeroOwnedProperMellinPointFullRowIncidenceOccurrence_root_readback
    observation stage row value

theorem occurrence_projects_to_seed
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    ((((IncidenceOccurrence observation stage).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Prod.fst = seedOccurrence :=
  zeroOwnedProperMellinPointFullRowIncidenceOccurrence_projects_to_seed
    observation stage

end
end ProperMellinScalarRelationIncidence
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
