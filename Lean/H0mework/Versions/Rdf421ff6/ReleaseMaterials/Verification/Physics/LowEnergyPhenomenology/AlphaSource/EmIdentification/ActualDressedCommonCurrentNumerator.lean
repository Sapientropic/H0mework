import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualDressedVisiblePoleOwn.ActualDressedRationalVisiblePole
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonIRResponse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualDressedCorrectedElectronReadOwn.ActualDressedCorrectedElectronRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonDenominatorNonzero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedVisiblePole
open ActualDressedUniformMaterialCoefficients ActualDressedCorrectedElectronRead
open ActualDressedCorrectedGreen ActualDressedFullCoulomb ActualDressedFrequencyHalf
open ActualDressedPhysicalRayNumerator ActualEMResponseSplit ActualEMCurrentSplit
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualCompositeFieldCurrent LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonDenominator correctedGreen correctedResponse
  ActualCompositeFieldCurrent.compositeCurrent frequencyResponsePencil physicalRayClearedPencil physicalRayDenominator

/-- Probe momenta and the four original spectral legs are fixed before IR/clock coefficients vary. -/
def commonCurrentNumerator (background : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Parameters :=
  commonDenominator background n *
    dotProduct (fun i => MvPolynomial.C (ActualCompositeFieldCurrent.compositeCurrent pd dL dR i))
      ((commonClearedPencil background n).adjugate *ᵥ
        (fun j => MvPolynomial.C (ActualCompositeFieldCurrent.compositeCurrent ps sL sR j)))

def commonDeterminant (background : DressedEvent) (n : PhysicalMomentum) : Parameters :=
  (commonClearedPencil background n).det

private theorem ring_map_matrix_eval (v : Fin 3 → ℂ) (H : Matrix (Fin 289) (Fin 289) Parameters) :
    (MvPolynomial.eval v).mapMatrix H = H.map (MvPolynomial.eval v) := by
  ext i j
  rfl

theorem actual_common_signed_clear_relation (background : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) :
    MvPolynomial.eval (irValues eps sigma s) (materialDenominator background n) ≠ 0 ∧
      MvPolynomial.eval (irValues eps sigma s) (commonDenominator background n) •
        physicalRayClearedPencil background eps s sigma n =
      physicalRayDenominator background eps s sigma n •
        (commonClearedPencil background n).map (MvPolynomial.eval (irValues eps sigma s)) := by
  refine ⟨material_denominator_nonzero background n eps sigma s, ?_⟩
  rw [← actual_physical_ray_pencil_clear background eps s sigma n positive,
    ← actual_common_ir_pencil_clear background n eps sigma s positive, smul_smul, smul_smul, mul_comm]

theorem actual_common_signed_determinant_relation (background : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) :
    (MvPolynomial.eval (irValues eps sigma s) (commonDenominator background n))^289 *
      correctedDet background eps s sigma n =
    (physicalRayDenominator background eps s sigma n)^289 *
      MvPolynomial.eval (irValues eps sigma s) (commonDeterminant background n) := by
  have paid := congrArg Matrix.det (actual_common_signed_clear_relation background eps sigma s n positive).2
  simpa only [Matrix.det_smul, Fintype.card_fin, correctedDet, commonDeterminant,
    RingHom.map_det, ring_map_matrix_eval] using paid

theorem actual_common_determinant_nonzero (background : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet background eps s sigma n ≠ 0) :
    MvPolynomial.eval (irValues eps sigma s) (commonDeterminant background n) ≠ 0 := by
  have denominator := ActualDressedUniformClockNonzero.actual_common_ir_denominator_nonzero
    background n eps sigma s positive
  have relation := actual_common_signed_determinant_relation background eps sigma s n positive
  intro zero
  rw [zero, mul_zero] at relation
  exact mul_ne_zero (pow_ne_zero 289 denominator) regular relation

private theorem evaluate_constant_read (H : Matrix (Fin 289) (Fin 289) Parameters)
    (v : Fin 3 → ℂ) (fd fs : Fin 289 → ℂ) :
    MvPolynomial.eval v
      (dotProduct (fun i => MvPolynomial.C (fd i)) (H *ᵥ (fun j => MvPolynomial.C (fs j)))) =
        dotProduct fd ((H.map (MvPolynomial.eval v))*ᵥfs) := by
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, MvPolynomial.eval_C, Matrix.map_apply]

theorem common_current_numerator_eval (background : DressedEvent) (eps sigma s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    MvPolynomial.eval (irValues eps sigma s) (commonCurrentNumerator background n pd ps dL dR sL sR) =
      MvPolynomial.eval (irValues eps sigma s) (commonDenominator background n) *
        dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR)
          (((commonClearedPencil background n).map (MvPolynomial.eval (irValues eps sigma s))).adjugate *ᵥ
            ActualCompositeFieldCurrent.compositeCurrent ps sL sR) := by
  unfold commonCurrentNumerator
  rw [map_mul, evaluate_constant_read]
  have mapped := (MvPolynomial.eval (irValues eps sigma s)).map_adjugate (commonClearedPencil background n)
  rw [ring_map_matrix_eval, ring_map_matrix_eval] at mapped
  rw [mapped]

theorem common_determinant_eval (background : DressedEvent) (eps sigma s : ℝ) (n : PhysicalMomentum) :
    MvPolynomial.eval (irValues eps sigma s) (commonDeterminant background n) =
      ((commonClearedPencil background n).map (MvPolynomial.eval (irValues eps sigma s))).det := by
  exact ((MvPolynomial.eval (irValues eps sigma s)).map_det _).trans
    (congrArg Matrix.det (ring_map_matrix_eval (irValues eps sigma s) (commonClearedPencil background n)))

theorem actual_common_green_adjugate (background : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet background eps s sigma n ≠ 0) :
    MvPolynomial.eval (irValues eps sigma s) (commonDeterminant background n) •
      correctedGreen background eps s sigma n =
        MvPolynomial.eval (irValues eps sigma s) (commonDenominator background n) •
          ((commonClearedPencil background n).map (MvPolynomial.eval (irValues eps sigma s))).adjugate := by
  rw [common_determinant_eval]
  exact adjugate_green_identity _ _ _ _
    (actual_common_ir_pencil_clear background n eps sigma s positive)
    (actual_corrected_green_inverse background eps s sigma n positive regular).1

theorem actual_common_current_read_clear (background : DressedEvent) (eps sigma s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (positive : 0 < sigma)
    (regular : correctedDet background eps s sigma n ≠ 0) :
    MvPolynomial.eval (irValues eps sigma s) (commonDeterminant background n) *
      correctedProbeRead background eps s sigma n pd ps dL dR sL sR =
        MvPolynomial.eval (irValues eps sigma s) (commonCurrentNumerator background n pd ps dL dR sL sR) := by
  rw [common_determinant_eval, common_current_numerator_eval, corrected_probe_read_original]
  unfold correctedResponse
  exact adjugate_full_read _ _ _ _ _ _
    (actual_common_ir_pencil_clear background n eps sigma s positive)
    (actual_corrected_green_inverse background eps s sigma n positive regular).1

theorem actual_common_current_read_fraction (background : DressedEvent) (eps sigma s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (positive : 0 < sigma)
    (regular : correctedDet background eps s sigma n ≠ 0) :
    correctedProbeRead background eps s sigma n pd ps dL dR sL sR =
      MvPolynomial.eval (irValues eps sigma s) (commonCurrentNumerator background n pd ps dL dR sL sR) /
        MvPolynomial.eval (irValues eps sigma s) (commonDeterminant background n) := by
  apply (eq_div_iff (actual_common_determinant_nonzero background eps sigma s n positive regular)).mpr
  exact (mul_comm _ _).trans
    (actual_common_current_read_clear background eps sigma s n pd ps dL dR sL sR positive regular)

theorem actual_common_numerator_four_parts (background : DressedEvent) (eps sigma s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    let A := ((commonClearedPencil background n).map (MvPolynomial.eval (irValues eps sigma s))).adjugate
    let fd := ActualCompositeFieldCurrent.compositeCurrent pd dL dR
    let fs := ActualCompositeFieldCurrent.compositeCurrent ps sL sR
    MvPolynomial.eval (irValues eps sigma s) (commonCurrentNumerator background n pd ps dL dR sL sR) =
      MvPolynomial.eval (irValues eps sigma s) (commonDenominator background n) *
        (emPureObservation A fd fs+
          emCurrentObservation A (emCurrentForce fd) (emCurrentResidual fs)+
          emCurrentObservation A (emCurrentResidual fd) (emCurrentForce fs)+
          emCurrentObservation A (emCurrentResidual fd) (emCurrentResidual fs)) := by
  dsimp only
  rw [common_current_numerator_eval]
  exact congrArg (fun x : ℂ => MvPolynomial.eval (irValues eps sigma s) (commonDenominator background n)*x)
    (em_response_four_parts _ _ _)

end LowEnergy.GaussComposite.ActualDressedVisiblePole
