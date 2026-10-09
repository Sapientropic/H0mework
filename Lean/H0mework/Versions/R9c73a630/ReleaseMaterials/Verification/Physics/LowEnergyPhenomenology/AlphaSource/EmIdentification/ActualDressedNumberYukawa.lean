import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberGradeRange

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberSector
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open GaussCoreHilbert GaussCoreDifferential GaussCoreLabel GaussFockLabel
open NativeHistoryGrade GaussYukawaCoefficient GaussYukawaGrade GaussNativePotential
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open CanonicalGradedSpatial (Localizer)
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open PreparationVacuumFieldConstraintResponse
open PreparationVacuumUncutYukawa PreparationVacuumPhysicalHalfAxis
open GaussHistoryHilbert
open scoped BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] numberTwoGrade actualA actualC

private theorem uncut_N2_range (f : Field289) (phi : CanonicalGradedSpatial.Localizer) (r : ℝ) (g h : Fin 57)
    (generated : ∀ (scalar : Scalar) (psi : FockFiber),
      fiberPiece (2,h) (sourceMap scalar (fiberPiece (2,g) psi))=sourceMap scalar (fiberPiece (2,g) psi)) :
    numberTwoGrade h*uncutOperator f phi r*numberTwoGrade g=uncutOperator f phi r*numberTwoGrade g := by
  apply GaussYukawaGrade.core_ext
  intro test
  simp only [mul_apply_eq_comp]
  rw [show numberTwoGrade g (embed test)=embed (GaussCoreLabel.project (2,g) test) from
    by simpa only [numberTwoGrade] using (GaussCoreLabel.embed_project (2,g) test).symm]
  rw [uncutOperator_core]
  rw [show numberTwoGrade h (embed _)=embed (GaussCoreLabel.project (2,h) _) from
    by simpa only [numberTwoGrade] using (GaussCoreLabel.embed_project (2,h) _).symm]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change fiberPiece (2,h) ((_:ℂ) • sourceMap (scalarField (fieldCoordinateCurve f r z))
    (fiberPiece (2,g) (test z)))=_
  rw [map_smul,generated]
  rfl

theorem uncut_N2G0_range (f : Field289) (phi : CanonicalGradedSpatial.Localizer) (r : ℝ) :
    numberTwoGrade 1*uncutOperator f phi r*numberTwoGrade 0=uncutOperator f phi r*numberTwoGrade 0 :=
  uncut_N2_range f phi r 0 1 original_yukawa_N2G0_range

theorem uncut_N2G1_range (f : Field289) (phi : CanonicalGradedSpatial.Localizer) (r : ℝ) :
    numberTwoGrade 2*uncutOperator f phi r*numberTwoGrade 1=uncutOperator f phi r*numberTwoGrade 1 :=
  uncut_N2_range f phi r 1 2 original_yukawa_N2G1_range

theorem uncut_N2G2_zero (f : Field289) (phi : CanonicalGradedSpatial.Localizer) (r : ℝ) :
    uncutOperator f phi r*numberTwoGrade 2=0 := by
  apply GaussYukawaGrade.core_ext
  intro test
  simp only [mul_apply_eq_comp,zero_apply]
  rw [show numberTwoGrade 2 (embed test)=embed (GaussCoreLabel.project (2,2) test) from
    by simpa only [numberTwoGrade] using (GaussCoreLabel.embed_project (2,2) test).symm]
  rw [uncutOperator_core,←map_zero embed]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change (_:ℂ) • sourceMap (scalarField (fieldCoordinateCurve f r z)) (fiberPiece (2,2) (test z))=0
  rw [original_yukawa_N2G2_zero,smul_zero]

theorem actualA_N2G0_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    numberTwoGrade 1*actualA p F*numberTwoGrade 0=actualA p F*numberTwoGrade 0 := by
  simpa only [actualA] using uncut_N2G0_range 0 (PreparationVacuumYukawaTransport.finiteRetainer p F) 0

theorem actualA_N2G1_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    numberTwoGrade 2*actualA p F*numberTwoGrade 1=actualA p F*numberTwoGrade 1 := by
  simpa only [actualA] using uncut_N2G1_range 0 (PreparationVacuumYukawaTransport.finiteRetainer p F) 0

theorem actualA_N2G2_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    actualA p F*numberTwoGrade 2=0 := by
  simpa only [actualA] using uncut_N2G2_zero 0 (PreparationVacuumYukawaTransport.finiteRetainer p F) 0

theorem actualC_numberTwoGrade (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (g : Fin 57) :
    Commute (numberTwoGrade g) (actualC p F) := by
  simpa only [numberTwoGrade,actualC] using CanonicalPhysicalSpatial.compression_blocks p F (2,g)

end LowEnergy.GaussComposite.ActualDressedNumberSector
