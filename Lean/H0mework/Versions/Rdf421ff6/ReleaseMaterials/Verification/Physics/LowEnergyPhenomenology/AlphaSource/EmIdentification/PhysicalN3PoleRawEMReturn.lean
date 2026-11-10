import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3RawEMReader

/-! The raw EM calibration on the completed pole families: state/approach reads
of the fixed event calibration reader, source-generated prices and errors, and
the actual corrected raw charge pair on independently prepared sections. -/
set_option autoImplicit false
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

attribute [local irreducible] actualElectronPhysicalSeed actualElectronPhysicalResponse
  materialJointNumerator jointGenerator jointResolvent jointPolynomial compressionPolynomial
  physicalN3InputEnergyRead physicalN3InputEnergyNumerator
  physicalN3OutputEnergyNumerator physicalN3OutputEnergyGerm actualElectronPhysicalUnit
  physicalN3OutputPoleOrder physicalN3OutputPoleLeading physicalN3OutputPoleUnit
  actualElectronPhysicalChargeCorrection chargeReader actualElectronPhysicalState
  actualElectronPhysicalChargeVertex actualElectronPhysicalChargeRead
  physicalN3PolePhase physicalN3PoleEnergyRadius
  physicalN3PoleEnergyScale physicalN3PoleApproachEnergy physicalN3PoleApproachUnit
  prepared sourceProfile physicalN3PoleEMDensityCore GaussUnitaryHistory.reader
  physicalN3PoleState physicalN3PoleApproachState physicalN3RawEMReader
  physicalN3EMCalibrationReader physicalN3RawEMPrice physicalN3EMCalibrationPrice

/-- The lifted constant reader keeps the original operator norm. -/
private theorem rawem_reader_bound {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I) (A : E→L[ℂ]E) :
    ‖lift u (SourceFamilyOperator.constant A)‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  exact SourceBoundaryGram.lift_bound_explicit u (SourceFamilyOperator.constant A) ‖A‖
    (norm_nonneg A) (fun _ y=>A.le_opNorm y) x

private theorem rawem_native_reader_bound (A : H→L[ℂ]H) :
    ‖GaussUnitaryHistory.reader A‖ ≤ ‖A‖ := by
  unfold GaussUnitaryHistory.reader
  exact rawem_reader_bound (E := H) GaussUnitaryHistory.sourceFilter A

private theorem rawem_unit_operator_price {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (A : E→L[ℂ]E) (x : E) (hx : ‖x‖=1) :
    ‖A x‖ ≤ ‖A‖ := by
  simpa only [hx, mul_one] using A.le_opNorm x

private theorem rawem_unit_pair_price {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E→L[ℂ]E) (x y : E) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    ‖inner ℂ x (A y)‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖x‖ * ‖A y‖ := norm_inner_le_norm _ _
    _ = ‖A y‖ := by rw [hx, one_mul]
    _ ≤ ‖A‖ := rawem_unit_operator_price A y hy

/-- Two-endpoint pairing error between unit states, generic carrier. -/
private theorem rawem_pair_error {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E→L[ℂ]E) (aL xL aR xR : E)
    (hxL : ‖xL‖ = 1) (haR : ‖aR‖ = 1) :
    ‖inner ℂ aL (A aR) - inner ℂ xL (A xR)‖ ≤
      ‖A‖ * (‖aL - xL‖ + ‖aR - xR‖) := by
  have hsplit : inner ℂ aL (A aR) - inner ℂ xL (A xR) =
      inner ℂ (aL - xL) (A aR) + inner ℂ xL (A (aR - xR)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [hsplit]
  calc _ ≤ ‖inner ℂ (aL - xL) (A aR)‖ + ‖inner ℂ xL (A (aR - xR))‖ :=
        norm_add_le _ _
    _ ≤ ‖aL - xL‖ * (‖A‖ * ‖aR‖) + ‖xL‖ * (‖A‖ * ‖aR - xR‖) := by
        apply add_le_add
        · exact (norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (A.le_opNorm aR) (norm_nonneg _))
        · exact (norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (A.le_opNorm (aR - xR)) (norm_nonneg _))
    _ = _ := by rw [hxL, haR]; ring

/-- The actual finite-reader calibration state: the event calibration defect
read on the completed pole state. -/
def physicalN3PoleEMCalibrationState (event : DressedEvent) (p : PhysicalMomentum)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection p leg) : ElectronHistory :=
  GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)
    (physicalN3PoleState p leg poles)

/-- The same calibration read on the completed approach state. -/
def physicalN3PoleEMApproachCalibration (event : DressedEvent) (p : PhysicalMomentum)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection p leg) (m : ℕ) :
    ElectronHistory :=
  GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)
    (physicalN3PoleApproachState p leg poles m)

/-- The completed calibration read is priced by the source calibration price. -/
theorem physical_n3_pole_em_calibration_bound (event : DressedEvent)
    (p : PhysicalMomentum) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection p leg) :
    ‖physicalN3PoleEMCalibrationState event p leg poles‖
      ≤ physicalN3EMCalibrationPrice event := by
  exact (rawem_unit_operator_price (E := ElectronHistory)
    (GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event))
    (physicalN3PoleState p leg poles) (physical_n3_pole_state_norm p leg poles)).trans
      ((rawem_native_reader_bound (physicalN3EMCalibrationReader event)).trans
        (physical_n3_em_calibration_reader_price event))

/-- The approach calibration read stays within the source soft budget. -/
theorem physical_n3_pole_em_calibration_error (event : DressedEvent)
    (p : PhysicalMomentum) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection p leg) (m : ℕ) :
    ‖physicalN3PoleEMApproachCalibration event p leg poles m -
      physicalN3PoleEMCalibrationState event p leg poles‖
      ≤ physicalN3EMCalibrationPrice event * actualSoftBudget m := by
  unfold physicalN3PoleEMApproachCalibration physicalN3PoleEMCalibrationState
  calc ‖GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)
        (physicalN3PoleApproachState p leg poles m) -
      GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)
        (physicalN3PoleState p leg poles)‖
      = ‖GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)
          (physicalN3PoleApproachState p leg poles m -
          physicalN3PoleState p leg poles)‖ :=
        congrArg Norm.norm
          (map_sub (GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)) _ _).symm
    _ ≤ ‖GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)‖ *
        ‖physicalN3PoleApproachState p leg poles m -
          physicalN3PoleState p leg poles‖ :=
        (GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)).le_opNorm
          (physicalN3PoleApproachState p leg poles m - physicalN3PoleState p leg poles)
    _ ≤ physicalN3EMCalibrationPrice event * actualSoftBudget m :=
        mul_le_mul
          ((rawem_native_reader_bound (physicalN3EMCalibrationReader event)).trans
            (physical_n3_em_calibration_reader_price event))
          (physical_n3_pole_state_error p leg poles m) (norm_nonneg _)
          (physical_n3_em_calibration_price_nonneg event)

/-- The completed approach calibration returns to the completed pole calibration
through the fixed actual event reader. -/
theorem physical_n3_pole_em_calibration_return (event : DressedEvent)
    (p : PhysicalMomentum) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection p leg) :
    Tendsto (fun m : ℕ => physicalN3PoleEMApproachCalibration event p leg poles m)
      atTop (𝓝 (physicalN3PoleEMCalibrationState event p leg poles)) :=
  ((GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)).continuous.tendsto _).comp
    (physical_n3_pole_state_return p leg poles)

/-- The actual raw EM charge read on the completed pole state: sign-unit plus
the original Rmix correction plus the explicit event calibration state. -/
theorem physical_n3_pole_raw_em_charge (event : DressedEvent)
    (p : PhysicalMomentum) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection p leg) :
    GaussUnitaryHistory.reader (physicalN3RawEMReader event)
        (physicalN3PoleState p leg poles) =
      actualElectronSign leg • physicalN3PoleState p leg poles +
        physicalN3PoleCorrection p leg poles +
        physicalN3PoleEMCalibrationState event p leg poles := by
  have hsplit : physicalN3RawEMReader event =
      chargeReader sourcePhaseGaugeLie + physicalN3EMCalibrationReader event := by
    unfold physicalN3EMCalibrationReader
    abel
  have hread : GaussUnitaryHistory.reader (physicalN3RawEMReader event) =
      GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie) +
        GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event) :=
    (congrArg GaussUnitaryHistory.reader hsplit).trans
      (GaussUnitaryHistory.reader_add _ _)
  unfold physicalN3PoleEMCalibrationState
  calc GaussUnitaryHistory.reader (physicalN3RawEMReader event)
        (physicalN3PoleState p leg poles)
      = GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie)
          (physicalN3PoleState p leg poles) +
        GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)
          (physicalN3PoleState p leg poles) := by
        exact (congrArg (fun A : ElectronHistory→L[ℂ]ElectronHistory =>
          A (physicalN3PoleState p leg poles)) hread).trans
            (add_apply _ _ _)
    _ = actualElectronSign leg • physicalN3PoleState p leg poles +
          physicalN3PoleCorrection p leg poles +
        GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)
          (physicalN3PoleState p leg poles) :=
        congrArg (fun t : ElectronHistory => t +
          GaussUnitaryHistory.reader (physicalN3EMCalibrationReader event)
            (physicalN3PoleState p leg poles))
          (physical_n3_pole_charge_equation p leg poles)

/-- The actual corrected raw pole pairing on independently prepared left/right
momenta, legs and sections: sign-weighted pole overlap plus the paired retained
right Rmix correction and right event calibration state. -/
theorem physical_n3_pole_raw_em_paired_charge (event : DressedEvent)
    (pL pR : PhysicalMomentum) (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right) :
    inner ℂ (physicalN3PoleState pL left polesL)
        (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
          (physicalN3PoleState pR right polesR)) =
      actualElectronSign right *
          inner ℂ (physicalN3PoleState pL left polesL)
            (physicalN3PoleState pR right polesR) +
        inner ℂ (physicalN3PoleState pL left polesL)
          (physicalN3PoleCorrection pR right polesR +
            physicalN3PoleEMCalibrationState event pR right polesR) := by
  have h := physical_n3_pole_raw_em_charge event pR right polesR
  calc inner ℂ (physicalN3PoleState pL left polesL)
        (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
          (physicalN3PoleState pR right polesR))
      = inner ℂ (physicalN3PoleState pL left polesL)
          (actualElectronSign right • physicalN3PoleState pR right polesR +
            physicalN3PoleCorrection pR right polesR +
            physicalN3PoleEMCalibrationState event pR right polesR) :=
        congrArg (inner ℂ (physicalN3PoleState pL left polesL)) h
    _ = inner ℂ (physicalN3PoleState pL left polesL)
            (actualElectronSign right • physicalN3PoleState pR right polesR) +
          inner ℂ (physicalN3PoleState pL left polesL)
            (physicalN3PoleCorrection pR right polesR) +
          inner ℂ (physicalN3PoleState pL left polesL)
            (physicalN3PoleEMCalibrationState event pR right polesR) :=
        (inner_add_right _ _ _).trans
          (congrArg (fun t : ℂ => t +
            inner ℂ (physicalN3PoleState pL left polesL)
              (physicalN3PoleEMCalibrationState event pR right polesR))
            (inner_add_right _ _ _))
    _ = actualElectronSign right *
            inner ℂ (physicalN3PoleState pL left polesL)
              (physicalN3PoleState pR right polesR) +
          inner ℂ (physicalN3PoleState pL left polesL)
            (physicalN3PoleCorrection pR right polesR) +
          inner ℂ (physicalN3PoleState pL left polesL)
            (physicalN3PoleEMCalibrationState event pR right polesR) :=
        congrArg (fun t : ℂ => t +
            inner ℂ (physicalN3PoleState pL left polesL)
              (physicalN3PoleCorrection pR right polesR) +
            inner ℂ (physicalN3PoleState pL left polesL)
              (physicalN3PoleEMCalibrationState event pR right polesR))
          (inner_smul_right _ _ _)
    _ = _ := by rw [inner_add_right]; ring

/-- The source price of the raw pole pairing: the fixed event raw price times the
left pole-state norm, without a supplied bound. -/
theorem physical_n3_pole_raw_em_pair_price (event : DressedEvent)
    (pL pR : PhysicalMomentum) (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right) :
    ‖inner ℂ (physicalN3PoleState pL left polesL)
        (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
          (physicalN3PoleState pR right polesR))‖
      ≤ physicalN3RawEMPrice event := by
  exact (rawem_unit_pair_price (E := ElectronHistory)
    (GaussUnitaryHistory.reader (physicalN3RawEMReader event))
    (physicalN3PoleState pL left polesL) (physicalN3PoleState pR right polesR)
    (physical_n3_pole_state_norm pL left polesL)
    (physical_n3_pole_state_norm pR right polesR)).trans
      ((rawem_native_reader_bound (physicalN3RawEMReader event)).trans
        (physical_n3_raw_em_reader_price event))

/-- The per-frame raw EM pairing: the left approach unit paired with the actual
raw event reader on the right approach unit. -/
def physicalN3PoleRawEMFrameRead (event : DressedEvent)
    (pL pR : PhysicalMomentum) (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) : ℂ :=
  inner ℂ (physicalN3PoleApproachUnit pL F left (polesL F) m)
    (physicalN3RawEMReader event
      (physicalN3PoleApproachUnit pR F right (polesR F) m))

/-- The completed-approach raw EM pairing through the original whole-H reader. -/
def physicalN3PoleRawEMHistoryRead (event : DressedEvent)
    (pL pR : PhysicalMomentum) (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right) (m : ℕ) : ℂ :=
  inner ℂ (physicalN3PoleApproachState pL left polesL m)
    (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
      (physicalN3PoleApproachState pR right polesR m))

/-- The per-frame raw pairings return through the original `sourceFilter` to the
completed raw read. -/
theorem physical_n3_pole_raw_em_source_return (event : DressedEvent)
    (pL pR : PhysicalMomentum) (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right) (m : ℕ) :
    Tendsto (fun F => physicalN3PoleRawEMFrameRead event pL pR left right
        polesL polesR m F)
      GaussUnitaryHistory.sourceFilter
      (𝓝 (physicalN3PoleRawEMHistoryRead event pL pR left right polesL polesR m)) := by
  unfold physicalN3PoleRawEMHistoryRead physicalN3PoleApproachState
    physicalN3PoleRawEMFrameRead
  rw [GaussUnitaryHistory.reader, SourceFamilyOperator.lift_coe, inner_coe]
  exact pair_tendsto GaussUnitaryHistory.sourceFilter
    (physicalN3PoleApproachFamily pL left polesL m)
    (act GaussUnitaryHistory.sourceFilter
      (SourceFamilyOperator.constant (physicalN3RawEMReader event))
      (physicalN3PoleApproachFamily pR right polesR m))

/-- The completed raw history read stays within twice the source raw price times
the shared soft budget. -/
theorem physical_n3_pole_raw_em_history_error (event : DressedEvent)
    (pL pR : PhysicalMomentum) (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right) (m : ℕ) :
    ‖physicalN3PoleRawEMHistoryRead event pL pR left right polesL polesR m -
      inner ℂ (physicalN3PoleState pL left polesL)
        (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
          (physicalN3PoleState pR right polesR))‖
      ≤ 2 * physicalN3RawEMPrice event * actualSoftBudget m := by
  unfold physicalN3PoleRawEMHistoryRead
  calc ‖inner ℂ (physicalN3PoleApproachState pL left polesL m)
          (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
            (physicalN3PoleApproachState pR right polesR m)) -
        inner ℂ (physicalN3PoleState pL left polesL)
          (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
            (physicalN3PoleState pR right polesR))‖
      ≤ ‖GaussUnitaryHistory.reader (physicalN3RawEMReader event)‖ *
          (‖physicalN3PoleApproachState pL left polesL m -
            physicalN3PoleState pL left polesL‖ +
          ‖physicalN3PoleApproachState pR right polesR m -
            physicalN3PoleState pR right polesR‖) :=
        rawem_pair_error _ _ _ _ _
          (physical_n3_pole_state_norm pL left polesL)
          (physical_n3_pole_approach_state_norm pR right polesR m)
    _ ≤ physicalN3RawEMPrice event * (actualSoftBudget m + actualSoftBudget m) :=
        mul_le_mul
          ((rawem_native_reader_bound (physicalN3RawEMReader event)).trans
            (physical_n3_raw_em_reader_price event))
          (add_le_add (physical_n3_pole_state_error pL left polesL m)
            (physical_n3_pole_state_error pR right polesR m))
          (add_nonneg (norm_nonneg _) (norm_nonneg _))
          (physical_n3_raw_em_price_nonneg event)
    _ = _ := by ring

/-- The raw completed read returns to the actual corrected raw pole pairing. -/
theorem physical_n3_pole_raw_em_pole_return (event : DressedEvent)
    (pL pR : PhysicalMomentum) (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right) :
    Tendsto (fun m => physicalN3PoleRawEMHistoryRead event pL pR left right
        polesL polesR m)
      atTop
      (𝓝 (actualElectronSign right *
          inner ℂ (physicalN3PoleState pL left polesL)
            (physicalN3PoleState pR right polesR) +
        inner ℂ (physicalN3PoleState pL left polesL)
          (physicalN3PoleCorrection pR right polesR +
            physicalN3PoleEMCalibrationState event pR right polesR))) := by
  have h : Tendsto (fun m => physicalN3PoleRawEMHistoryRead event pL pR left right
        polesL polesR m)
      atTop
      (𝓝 (inner ℂ (physicalN3PoleState pL left polesL)
          (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
            (physicalN3PoleState pR right polesR)))) := by
    unfold physicalN3PoleRawEMHistoryRead
    exact (physical_n3_pole_state_return pL left polesL).inner
      (((GaussUnitaryHistory.reader (physicalN3RawEMReader event)).continuous.tendsto _).comp
        (physical_n3_pole_state_return pR right polesR))
  rwa [physical_n3_pole_raw_em_paired_charge] at h

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
