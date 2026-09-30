import H0mework.Versions.Y.Arithmetic.Mellin.ProperMellinL1
import H0mework.Versions.Y.Arithmetic.RiemannMellinOrbit.FourierTarget

/-!
# Proper Mellin material in the actual point-full-row cycle kernel

The paired proper weighted `L¹` carrier enters the existing point-specialized
q-rich full-row total through its two actual continuous integrals and the
installed `ZMod 2` coefficient action.  Evaluation at the existing source
generator is a degree-one cycle because the target map is already a cochain
map; no finite-generation premise or parallel cyclic model is introduced.

The final occurrence is a dependent child of the exact zero-observation
occurrence.  It stores the generated cycle map and its projection provenance,
not a radial, separator, fixedness, or zero-readback field.
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

open CategoryTheory
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionPointSpecialization
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization
open InverseZeroFibre

noncomputable section

abbrev ProperMellinL1Pair := PositiveMellinL1 × PositiveMellinL1

def properMellinL1PairIntegral : ProperMellinL1Pair →ₗ[ℂ] ClozelJPair where
  toFun value :=
    (positiveMellinL1Integral value.1,
      positiveMellinL1Integral value.2)
  map_add' left right := by
    ext <;> simp
  map_smul' scalar value := by
    ext <;> simp

def properMellinL1PairCoefficients :
    ProperMellinL1Pair →ₗ[ℂ] ZModTwoCarrier :=
  clozelJPairToZModTwo.toLinearMap.comp properMellinL1PairIntegral

noncomputable def properMellinL1PointFullRowHom
    (point : DeterminantLinePoint) (stage : Nat) :
    ProperMellinL1Pair →ₗ[ℂ]
      ((PointExtensionFunctor point).obj PairDerivedScalarSingleOne ⟶
        PointFullRowVerticalTotal point stage) :=
  (pointQRichZModTwoCombination point stage).comp
    properMellinL1PairCoefficients

@[simp] theorem properMellinL1PairCoefficients_zero
    (value : ProperMellinL1Pair) :
    properMellinL1PairCoefficients value 0 =
      positiveMellinL1Integral value.1 :=
  rfl

@[simp] theorem properMellinL1PairCoefficients_one
    (value : ProperMellinL1Pair) :
    properMellinL1PairCoefficients value 1 =
      positiveMellinL1Integral value.2 :=
  rfl

theorem properMellinL1PointFullRowHom_readback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (value : ProperMellinL1Pair) :
    pointFullRowHomCReadback point stage row
        (properMellinL1PointFullRowHom point stage value) =
      -(quotientCoefficient row : ℂ) *
        (positiveMellinL1Integral value.1 -
          positiveMellinL1Integral value.2) := by
  rw [properMellinL1PointFullRowHom, LinearMap.comp_apply,
    pointQRichZModTwoCombination_readback]
  rfl

abbrev PointFullRowDegreeOneCycles
    (point : DeterminantLinePoint) (stage : Nat) :=
  ((PointFullRowVerticalTotal point stage).cycles 1 : Type)

noncomputable def pointFullRowHomDegreeOne
    (point : DeterminantLinePoint) (stage : Nat) :
    (((PointExtensionFunctor point).obj PairDerivedScalarSingleOne ⟶
        PointFullRowVerticalTotal point stage)) →ₗ[ℂ]
      ((PointFullRowVerticalTotal point stage).X 1 : Type) where
  toFun source :=
    (source.f 1).hom (pointFullRowSourceGenerator point)
  map_add' left right := by
    simp
  map_smul' scalar source := by
    simp

theorem pointFullRowHomDegreeOne_d
    (point : DeterminantLinePoint) (stage : Nat) :
    ModuleCat.ofHom (pointFullRowHomDegreeOne point stage) ≫
        (PointFullRowVerticalTotal point stage).d 1 2 = 0 := by
  ext source
  change ((PointFullRowVerticalTotal point stage).d 1 2).hom
      ((source.f 1).hom (pointFullRowSourceGenerator point)) = 0
  have comm := ConcreteCategory.congr_hom (source.comm 1 2)
    (pointFullRowSourceGenerator point)
  simpa using comm

noncomputable def pointFullRowHomCycle
    (point : DeterminantLinePoint) (stage : Nat) :
    (((PointExtensionFunctor point).obj PairDerivedScalarSingleOne ⟶
        PointFullRowVerticalTotal point stage)) →ₗ[ℂ]
      PointFullRowDegreeOneCycles point stage :=
  ((PointFullRowVerticalTotal point stage).liftCycles
    (ModuleCat.ofHom (pointFullRowHomDegreeOne point stage)) 2 (by simp)
    (pointFullRowHomDegreeOne_d point stage)).hom

theorem pointFullRowHomCycle_inclusion
    (point : DeterminantLinePoint) (stage : Nat)
    (source : (PointExtensionFunctor point).obj PairDerivedScalarSingleOne ⟶
      PointFullRowVerticalTotal point stage) :
    ((PointFullRowVerticalTotal point stage).iCycles 1).hom
        (pointFullRowHomCycle point stage source) =
      (source.f 1).hom (pointFullRowSourceGenerator point) := by
  exact ConcreteCategory.congr_hom
    ((PointFullRowVerticalTotal point stage).liftCycles_i
      (ModuleCat.ofHom (pointFullRowHomDegreeOne point stage)) 2 (by simp)
      (pointFullRowHomDegreeOne_d point stage)) source

noncomputable def properMellinL1PointFullRowCycle
    (point : DeterminantLinePoint) (stage : Nat) :
    ProperMellinL1Pair →ₗ[ℂ] PointFullRowDegreeOneCycles point stage :=
  (pointFullRowHomCycle point stage).comp
    (properMellinL1PointFullRowHom point stage)

noncomputable def pointFullRowCycleCReadback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    PointFullRowDegreeOneCycles point stage →ₗ[ℂ] ℂ :=
  (pointFullRowCReadback point stage row).comp
    ((PointFullRowVerticalTotal point stage).iCycles 1).hom

theorem properMellinL1PointFullRowCycle_readback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (value : ProperMellinL1Pair) :
    pointFullRowCycleCReadback point stage row
        (properMellinL1PointFullRowCycle point stage value) =
      -(quotientCoefficient row : ℂ) *
        (positiveMellinL1Integral value.1 -
          positiveMellinL1Integral value.2) := by
  rw [pointFullRowCycleCReadback, LinearMap.comp_apply,
    properMellinL1PointFullRowCycle, LinearMap.comp_apply,
    pointFullRowHomCycle_inclusion]
  exact properMellinL1PointFullRowHom_readback point stage row value

/-! ## Same-zero occurrence child -/

def zeroPayloadDeterminantPoint
    (payload : GeneratedZeroObservationPayload) : DeterminantLinePoint :=
  mathlibZeroPoint payload.2.coordinate payload.2.mathlibZero

abbrev ZeroPayloadPointFullRowDegreeOneCycles
    (payload : GeneratedZeroObservationPayload) (stage : Nat) :=
  PointFullRowDegreeOneCycles (zeroPayloadDeterminantPoint payload) stage

structure GeneratedProperMellinPointFullRowIncidenceAt
    (payload : GeneratedZeroObservationPayload) (stage : Nat) : Type 5 where
  private mk ::
  cycleMap : ProperMellinL1Pair →ₗ[ℂ]
    ZeroPayloadPointFullRowDegreeOneCycles payload stage
  cycleMap_eq : cycleMap =
    properMellinL1PointFullRowCycle
      (zeroPayloadDeterminantPoint payload) stage

namespace GeneratedProperMellinPointFullRowIncidenceAt

noncomputable def generate
    (payload : GeneratedZeroObservationPayload) (stage : Nat) :
    GeneratedProperMellinPointFullRowIncidenceAt payload stage where
  cycleMap := properMellinL1PointFullRowCycle
    (zeroPayloadDeterminantPoint payload) stage
  cycleMap_eq := rfl

@[simp] theorem generate_cycleMap
    (payload : GeneratedZeroObservationPayload) (stage : Nat) :
    (generate payload stage).cycleMap =
      properMellinL1PointFullRowCycle
        (zeroPayloadDeterminantPoint payload) stage :=
  rfl

end GeneratedProperMellinPointFullRowIncidenceAt

abbrev ProperMellinPointFullRowIncidencePayloadAt (stage : Nat) :=
  Σ payload : GeneratedZeroObservationPayload,
    GeneratedProperMellinPointFullRowIncidenceAt payload stage

noncomputable def zeroOwnedProperMellinPointFullRowIncidenceOccurrence
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    RootedAccountedUnfolding
      (ProperMellinPointFullRowIncidencePayloadAt stage) :=
  (zeroObservationReadoutOccurrence observation).map fun payload =>
    ⟨payload,
      GeneratedProperMellinPointFullRowIncidenceAt.generate payload stage⟩

theorem zeroOwnedProperMellinPointFullRowIncidenceOccurrence_projects
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    (zeroOwnedProperMellinPointFullRowIncidenceOccurrence
        observation stage).map Sigma.fst =
      zeroObservationReadoutOccurrence observation := by
  rw [zeroOwnedProperMellinPointFullRowIncidenceOccurrence,
    RootedAccountedUnfolding.map_map]
  change (zeroObservationReadoutOccurrence observation).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem zeroOwnedProperMellinPointFullRowIncidenceOccurrence_projects_to_seed
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    ((((zeroOwnedProperMellinPointFullRowIncidenceOccurrence
        observation stage).map Sigma.fst).map Sigma.fst).map Sigma.fst).map
          Prod.fst = seedOccurrence := by
  rw [zeroOwnedProperMellinPointFullRowIncidenceOccurrence_projects,
    zeroObservationReadoutOccurrence_projects,
    generatedRiemannAnalyticContinuationOccurrence_projects,
    globalGermOccurrence_projects]

@[simp] theorem zeroOwnedProperMellinPointFullRowIncidenceOccurrence_root_cycleMap
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    (zeroOwnedProperMellinPointFullRowIncidenceOccurrence
        observation stage).root.2.cycleMap =
      properMellinL1PointFullRowCycle
        (zeroPayloadDeterminantPoint
          (zeroOwnedProperMellinPointFullRowIncidenceOccurrence
            observation stage).root.1) stage :=
  rfl

theorem zeroOwnedProperMellinPointFullRowIncidenceOccurrence_root_point
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    zeroPayloadDeterminantPoint
        (zeroOwnedProperMellinPointFullRowIncidenceOccurrence
          observation stage).root.1 =
      mathlibZeroPoint observation.coordinate observation.mathlibZero := by
  rfl

theorem zeroOwnedProperMellinPointFullRowIncidenceOccurrence_root_readback
    (observation : GeneratedRiemannZeroObservation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (value : ProperMellinL1Pair) :
    pointFullRowCycleCReadback
        (zeroPayloadDeterminantPoint
          (zeroOwnedProperMellinPointFullRowIncidenceOccurrence
            observation stage).root.1)
        stage row
        ((zeroOwnedProperMellinPointFullRowIncidenceOccurrence
          observation stage).root.2.cycleMap value) =
      -(quotientCoefficient row : ℂ) *
        (positiveMellinL1Integral value.1 -
          positiveMellinL1Integral value.2) := by
  rw [zeroOwnedProperMellinPointFullRowIncidenceOccurrence_root_cycleMap]
  exact properMellinL1PointFullRowCycle_readback _ stage row value

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
