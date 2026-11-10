import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleEMNoetherCalibration
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationMovingNoetherPreparedContact
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldSourceFrame
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeNoetherPhysicalObserver
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSignedVolumeObservation

/-! The original h-normalized raw EM Noether reader on the fixed event frame:
finite Riesz reader priced by the source signed-volume bound, plus its explicit
canonical/density calibration decomposition. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussFockPair CanonicalGradedSpatialSource
open ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumUncutYukawa PreparationVacuumSourcePreparedResponse
open GaussComposite.SourceGraph
open ActualDressedUniformMaterialCoefficients ActualElectronPhysicalJointInverse
open ActualElectronWholeChargeSoft CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open SourceFamilyHilbert SourceFamilyOperator
open SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open LowEnergy.ActualDressedVisiblePole
open PreparationVacuumFieldConstraintResponse
open ActualDressedTemporalForm SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert
open PreparationVacuumRawJointFeedback PreparationPhysicalFirstTemporalChargeReturn
open PreparationPhysicalSignedVolumeWeightReturn ActualElectronNoetherDensity
open PhysicalEMGaugeRealization PhysicalEMVoltage
open PreparationVacuumNoetherChart PreparationVacuumFullFieldRiesz
open GaussComposite.ActualDressedFullCoulomb GaussComposite.ActualElectronWholeNoetherObserver
open ActualQuantitativePreparedFrameOwn
open MeasureTheory Filter
open scoped InnerProductSpace Topology
local instance rawemLabelFintype : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

attribute [local irreducible] actualElectronPhysicalSeed actualElectronPhysicalResponse
  materialJointNumerator jointGenerator jointResolvent jointPolynomial compressionPolynomial
  physicalN3InputEnergyRead physicalN3InputEnergyNumerator
  physicalN3OutputEnergyNumerator physicalN3OutputEnergyGerm actualElectronPhysicalUnit
  physicalN3OutputPoleOrder physicalN3OutputPoleLeading physicalN3OutputPoleUnit
  actualElectronPhysicalChargeCorrection chargeReader actualElectronPhysicalState
  actualElectronPhysicalChargeVertex actualElectronPhysicalChargeRead
  physicalN3PolePhase physicalN3PoleEnergyRadius
  physicalN3PoleEnergyScale physicalN3PoleApproachEnergy physicalN3PoleApproachUnit
  prepared sourceProfile physicalN3PoleEMDensityCore finiteRiesz

/-- The original event Noether reader at `h = 0` on the EM gauge field is the
actual signed coframe-volume reader on the independent-dual charge matrix. -/
theorem physical_n3_noether_em_signed_volume (p : PhysicalMomentum)
    (G : GaussUnitaryHistory.Index) :
    noetherReader (emGaugeField 0) p G 0 =
      sourceSignedVolumeReader emGaugeChargeMatrix G := by
  unfold noetherReader sourceSignedVolumeReader
  exact congrArg (finiteRiesz G) (funext fun i => funext fun j =>
    (noetherForm_source (emGaugeField 0) p (frameTest G i) (frameTest G j)).trans
      (actual_em_signed_density_form p (frameTest G i) (frameTest G j)))

/-- The original `-h⁻¹`-normalized raw EM action reader on the fixed event frame. -/
def physicalN3RawEMReader (event : DressedEvent) : H→L[ℂ]H :=
  (-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
    noetherReader (emGaugeField 0) event.momentum event.frame 0

/-- The source-generated price: `h⁻¹` times the signed-volume finite frame price. -/
def physicalN3RawEMPrice (event : DressedEvent) : ℝ :=
  (Stage10.ActionNormalization.phaseMomentum)⁻¹ *
    finitePrice event.frame (fun i j =>
      sourceSignedVolumeForm emGaugeChargeMatrix
        (frameTest event.frame i) (frameTest event.frame j))

/-- The raw reader is priced on the whole `H` by the source signed-volume bound. -/
theorem physical_n3_raw_em_reader_price (event : DressedEvent) :
    ‖physicalN3RawEMReader event‖ ≤ physicalN3RawEMPrice event := by
  unfold physicalN3RawEMReader physicalN3RawEMPrice
  have hpos : (0:ℝ) < Stage10.ActionNormalization.phaseMomentum :=
    Stage10.ActionNormalization.phaseMomentum_positive
  have hreader : ‖noetherReader (emGaugeField 0) event.momentum event.frame 0‖
      ≤ finitePrice event.frame (fun i j =>
          sourceSignedVolumeForm emGaugeChargeMatrix
            (frameTest event.frame i) (frameTest event.frame j)) := by
    rw [physical_n3_noether_em_signed_volume]
    exact sourceSignedVolumeReader_bound emGaugeChargeMatrix event.frame
  calc ‖(-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
        noetherReader (emGaugeField 0) event.momentum event.frame 0‖
      = ‖(-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹)‖ *
        ‖noetherReader (emGaugeField 0) event.momentum event.frame 0‖ := norm_smul _ _
    _ = (Stage10.ActionNormalization.phaseMomentum)⁻¹ *
        ‖noetherReader (emGaugeField 0) event.momentum event.frame 0‖ := by
        rw [norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hpos.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left hreader
        (inv_nonneg.mpr hpos.le)

/-- The source price is nonnegative. -/
theorem physical_n3_raw_em_price_nonneg (event : DressedEvent) :
    0 ≤ physicalN3RawEMPrice event :=
  mul_nonneg (inv_nonneg.mpr Stage10.ActionNormalization.phaseMomentum_positive.le)
    (finitePrice_nonnegative _ _)

/-- The canonical EM action finite reader on the same event frame. -/
def physicalN3EMCanonicalReader (event : DressedEvent) : H→L[ℂ]H :=
  finiteRiesz event.frame (fun i j =>
    emActionForm event.momentum (frameTest event.frame i) (frameTest event.frame j))

/-- The explicit finite-reader density calibration on the same event frame. -/
def physicalN3EMDensityReader (event : DressedEvent) : H→L[ℂ]H :=
  finiteRiesz event.frame (fun i j =>
    sourcePair (frameTest event.frame i)
      (physicalN3PoleEMDensityCore (frameTest event.frame j)))

/-- The raw EM reader minus the source charge reader: the actual finite-reader
calibration defect. -/
def physicalN3EMCalibrationReader (event : DressedEvent) : H→L[ℂ]H :=
  physicalN3RawEMReader event - chargeReader sourcePhaseGaugeLie

/-- The calibration price: raw source price plus the charge reader norm. -/
def physicalN3EMCalibrationPrice (event : DressedEvent) : ℝ :=
  physicalN3RawEMPrice event + ‖chargeReader sourcePhaseGaugeLie‖

private theorem rawem_finiteRiesz_smul (F : GaussUnitaryHistory.Index) (c : ℂ)
    (entries : FrameIndex F → FrameIndex F → ℂ) :
    c • finiteRiesz F entries =
      finiteRiesz F (fun i j => c * entries i j) := by
  simp only [finiteRiesz, Finset.smul_sum, smul_smul]

private theorem rawem_finiteRiesz_add (F : GaussUnitaryHistory.Index)
    (e1 e2 : FrameIndex F → FrameIndex F → ℂ) :
    finiteRiesz F e1 + finiteRiesz F e2 =
      finiteRiesz F (fun i j => e1 i j + e2 i j) := by
  simp only [finiteRiesz, add_smul, Finset.sum_add_distrib]

/-- The actual calibration reader decomposes as the explicit density reader plus
the canonical-reader-minus-charge defect, through the literal raw-density core
identity on every original frame entry. -/
theorem physical_n3_em_calibration_reader_source (event : DressedEvent) :
    physicalN3EMCalibrationReader event =
      physicalN3EMDensityReader event +
        (physicalN3EMCanonicalReader event - chargeReader sourcePhaseGaugeLie) := by
  have hentries : (fun i : FrameIndex event.frame => fun j =>
        -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
          noetherForm (emGaugeField 0) event.momentum
            (frameTest event.frame i) (frameTest event.frame j) 0) =
      (fun i j =>
        sourcePair (frameTest event.frame i)
          (physicalN3PoleEMDensityCore (frameTest event.frame j)) +
        emActionForm event.momentum (frameTest event.frame i)
          (frameTest event.frame j)) := by
    funext i j
    calc -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
          noetherForm (emGaugeField 0) event.momentum
            (frameTest event.frame i) (frameTest event.frame j) 0
        = -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
          rawForm (emGaugeField 0) event.momentum
            (frameTest event.frame i) (frameTest event.frame j) 0 :=
          congrArg (fun s : ℂ =>
            -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ * s)
            (noetherForm_source (emGaugeField 0) event.momentum
              (frameTest event.frame i) (frameTest event.frame j))
      _ = emActionForm event.momentum (frameTest event.frame i)
            (frameTest event.frame j) +
          sourcePair (frameTest event.frame i)
            (physicalN3PoleEMDensityCore (frameTest event.frame j)) :=
          physical_n3_pole_em_raw_density_core event.momentum _ _
      _ = _ := add_comm _ _
  show (-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
      finiteRiesz event.frame (fun i j =>
        noetherForm (emGaugeField 0) event.momentum
          (frameTest event.frame i) (frameTest event.frame j) 0) -
      chargeReader sourcePhaseGaugeLie =
    finiteRiesz event.frame (fun i j =>
        sourcePair (frameTest event.frame i)
          (physicalN3PoleEMDensityCore (frameTest event.frame j))) +
      (finiteRiesz event.frame (fun i j =>
          emActionForm event.momentum (frameTest event.frame i)
            (frameTest event.frame j)) -
        chargeReader sourcePhaseGaugeLie)
  have hraw : (-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
        finiteRiesz event.frame (fun i j =>
          noetherForm (emGaugeField 0) event.momentum
            (frameTest event.frame i) (frameTest event.frame j) 0) =
      finiteRiesz event.frame (fun i j =>
        sourcePair (frameTest event.frame i)
          (physicalN3PoleEMDensityCore (frameTest event.frame j))) +
        finiteRiesz event.frame (fun i j =>
          emActionForm event.momentum (frameTest event.frame i)
            (frameTest event.frame j)) := by
    calc (-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
          finiteRiesz event.frame (fun i j =>
            noetherForm (emGaugeField 0) event.momentum
              (frameTest event.frame i) (frameTest event.frame j) 0)
        = finiteRiesz event.frame (fun i j =>
            -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
              noetherForm (emGaugeField 0) event.momentum
                (frameTest event.frame i) (frameTest event.frame j) 0) :=
          rawem_finiteRiesz_smul _ _ _
      _ = finiteRiesz event.frame (fun i j =>
            sourcePair (frameTest event.frame i)
              (physicalN3PoleEMDensityCore (frameTest event.frame j)) +
            emActionForm event.momentum (frameTest event.frame i)
              (frameTest event.frame j)) :=
          congrArg (finiteRiesz event.frame) hentries
      _ = _ := (rawem_finiteRiesz_add _ _ _).symm
  calc (-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
        finiteRiesz event.frame (fun i j =>
          noetherForm (emGaugeField 0) event.momentum
            (frameTest event.frame i) (frameTest event.frame j) 0) -
        chargeReader sourcePhaseGaugeLie
      = (finiteRiesz event.frame (fun i j =>
          sourcePair (frameTest event.frame i)
            (physicalN3PoleEMDensityCore (frameTest event.frame j))) +
        finiteRiesz event.frame (fun i j =>
          emActionForm event.momentum (frameTest event.frame i)
            (frameTest event.frame j))) -
        chargeReader sourcePhaseGaugeLie :=
        congrArg (fun T : H→L[ℂ]H => T - chargeReader sourcePhaseGaugeLie) hraw
    _ = _ := add_sub_assoc _ _ _

/-- The calibration reader is priced by the raw source price plus the charge
reader norm, without a supplied bound. -/
theorem physical_n3_em_calibration_reader_price (event : DressedEvent) :
    ‖physicalN3EMCalibrationReader event‖ ≤ physicalN3EMCalibrationPrice event := by
  show ‖physicalN3RawEMReader event - chargeReader sourcePhaseGaugeLie‖ ≤
    physicalN3RawEMPrice event + ‖chargeReader sourcePhaseGaugeLie‖
  calc ‖physicalN3RawEMReader event - chargeReader sourcePhaseGaugeLie‖
      ≤ ‖physicalN3RawEMReader event‖ + ‖chargeReader sourcePhaseGaugeLie‖ :=
        norm_sub_le _ _
    _ ≤ physicalN3RawEMPrice event + ‖chargeReader sourcePhaseGaugeLie‖ :=
        add_le_add (physical_n3_raw_em_reader_price event) le_rfl

/-- The calibration price is nonnegative. -/
theorem physical_n3_em_calibration_price_nonneg (event : DressedEvent) :
    0 ≤ physicalN3EMCalibrationPrice event :=
  add_nonneg (physical_n3_raw_em_price_nonneg event) (norm_nonneg _)

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
