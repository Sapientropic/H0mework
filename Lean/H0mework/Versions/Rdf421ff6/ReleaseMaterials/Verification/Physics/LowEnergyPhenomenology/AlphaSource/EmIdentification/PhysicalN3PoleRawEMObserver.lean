import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleRawEMReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleHistoryWindow

/-! The fixed-event raw EM observer: the unphased original approach unit read of
the actual normalized raw EM operator minus the same read on the original
prepared background, returning through the genuine event frame and energy
approach to the pole observer. -/
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
  prepared sourceProfile physicalN3PoleEMDensityCore physicalN3PoleState
  physicalN3PoleApproachState

private theorem rawem_noether_scale {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E→L[ℂ]E) (c : ℂ) (x b : E) :
    inner ℂ x (((-c) • A) x) - inner ℂ b (((-c) • A) b) =
      -c * inner ℂ x (A x) + c * inner ℂ b (A b) := by
  rw [smul_apply, smul_apply, inner_smul_right, inner_smul_right]
  ring

private theorem rawem_diagonal_charge {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E→L[ℂ]E) (x d : E) (s bg : ℂ) (hx : ‖x‖=1)
    (h : inner ℂ x (A x) = s * inner ℂ x x + inner ℂ x d) :
    inner ℂ x (A x) - bg = s + inner ℂ x d - bg := by
  rw [h, inner_self_eq_norm_sq_to_K, hx]
  simp

/-- The per-frame original raw observer: the unphased actual physical unit at the
generated approach energy, minus the same original normalized raw read on the
original prepared background. The source phase is unphased here; it cancels only
diagonally in the family transport. -/
def physicalN3PoleRawEMFrameObserver (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg)
    (m : ℕ) (F : GaussUnitaryHistory.Index) : ℂ :=
  inner ℂ (actualElectronPhysicalUnit event.momentum F
      (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)
    (physicalN3RawEMReader event
      (actualElectronPhysicalUnit event.momentum F
        (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)) -
  inner ℂ (prepared (sourceProfile event.epsilon event.precision))
    (physicalN3RawEMReader event
      (prepared (sourceProfile event.epsilon event.precision)))

/-- The completed approach observer: the raw EM history read on the diagonal
minus the same read on the original prepared background. -/
def physicalN3PoleRawEMHistoryObserver (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (m : ℕ) : ℂ :=
  inner ℂ (physicalN3PoleApproachState event.momentum leg poles m)
    (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
      (physicalN3PoleApproachState event.momentum leg poles m)) -
  inner ℂ (actualNoetherBackground event)
    (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
      (actualNoetherBackground event))

/-- The pole observer: the raw EM read on the completed pole state minus the same
original prepared-background read. -/
def physicalN3PoleRawEMPoleObserver (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) : ℂ :=
  inner ℂ (physicalN3PoleState event.momentum leg poles)
    (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
      (physicalN3PoleState event.momentum leg poles)) -
  inner ℂ (actualNoetherBackground event)
    (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
      (actualNoetherBackground event))

/-- The literal original frame observer equals `-h⁻¹` times the unphased
approach-unit read of the original event Noether reader, plus `h⁻¹` times the
same read on the original prepared background. -/
theorem physical_n3_pole_raw_em_original_frame (event : DressedEvent)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection event.momentum leg)
    (m : ℕ) (F : GaussUnitaryHistory.Index) :
    physicalN3PoleRawEMFrameObserver event leg poles m F =
      -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
        inner ℂ (actualElectronPhysicalUnit event.momentum F
            (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)
          (noetherReader (emGaugeField 0) event.momentum event.frame 0
            (actualElectronPhysicalUnit event.momentum F
              (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)) +
      (Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
        inner ℂ (prepared (sourceProfile event.epsilon event.precision))
          (noetherReader (emGaugeField 0) event.momentum event.frame 0
            (prepared (sourceProfile event.epsilon event.precision))) := by
  unfold physicalN3PoleRawEMFrameObserver physicalN3RawEMReader
  exact rawem_noether_scale (E := H)
    (noetherReader (emGaugeField 0) event.momentum event.frame 0)
    (Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹
    (actualElectronPhysicalUnit event.momentum F
      (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)
    (prepared (sourceProfile event.epsilon event.precision))

/-- Constant families embed into the completion exactly as the `embed` isometry. -/
private theorem rawem_embed_constant {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I) (x : E) :
    SourceFamilyHilbert.embed u x =
      (SourceFamilyHilbert.constant u x : SourceFamilyHilbert.Hilbert E u) := rfl

private theorem rawem_observer_reader_bound {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I) (A : E→L[ℂ]E) :
    ‖lift u (SourceFamilyOperator.constant A)‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  exact SourceBoundaryGram.lift_bound_explicit u (SourceFamilyOperator.constant A) ‖A‖
    (norm_nonneg A) (fun _ y => A.le_opNorm y) x

private theorem rawem_observer_native_bound (A : H→L[ℂ]H) :
    ‖GaussUnitaryHistory.reader A‖ ≤ ‖A‖ := by
  unfold GaussUnitaryHistory.reader
  exact rawem_observer_reader_bound (E := H) GaussUnitaryHistory.sourceFilter A

/-- The whole-family observer read returns through the original ultrafilter. -/
private theorem rawem_family_observer_return {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I)
    (U b : SourceFamilyHilbert.Family E u) (A : SourceFamilyOperator.Operator I E) :
    Tendsto (fun F => inner ℂ (SourceFamilyHilbert.value U F)
        (A.component F (SourceFamilyHilbert.value U F)) -
      inner ℂ (SourceFamilyHilbert.value b F)
        (A.component F (SourceFamilyHilbert.value b F))) u
      (𝓝 (inner ℂ (U : SourceFamilyHilbert.Hilbert E u)
          (lift u A (U : SourceFamilyHilbert.Hilbert E u)) -
        inner ℂ (b : SourceFamilyHilbert.Hilbert E u)
          (lift u A (b : SourceFamilyHilbert.Hilbert E u)))) := by
  rw [lift_coe,lift_coe,inner_coe,inner_coe]
  exact (pair_tendsto u U (act u A U)).sub (pair_tendsto u b (act u A b))

/-- Unit-modulus scalars drop out of the diagonal pairing. -/
private theorem rawem_phase_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ζ : ℂ) (hζ : ‖ζ‖ = 1) (A : E→L[ℂ]E) (v : E) :
    inner ℂ (ζ • v) (A (ζ • v)) = inner ℂ v (A v) := by
  have hmul : ζ * (starRingEnd ℂ) ζ = 1 := by
    simpa [hζ] using RCLike.mul_conj ζ
  rw [map_smul, inner_smul_right, inner_smul_left, ← mul_assoc, hmul, one_mul]

/-- The per-frame raw observers return through the original `sourceFilter` to the
completed history observer; the source phase cancels diagonally per frame. -/
theorem physical_n3_pole_raw_em_observer_source_return (event : DressedEvent)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection event.momentum leg)
    (m : ℕ) :
    Tendsto (fun F => physicalN3PoleRawEMFrameObserver event leg poles m F)
      GaussUnitaryHistory.sourceFilter
      (𝓝 (physicalN3PoleRawEMHistoryObserver event leg poles m)) := by
  unfold physicalN3PoleRawEMHistoryObserver physicalN3PoleApproachState
    actualNoetherBackground GaussUnitaryHistory.inclusion GaussUnitaryHistory.reader
  refine (rawem_family_observer_return (E := H) GaussUnitaryHistory.sourceFilter
    (physicalN3PoleApproachFamily event.momentum leg poles m)
    (SourceFamilyHilbert.constant GaussUnitaryHistory.sourceFilter
      (prepared (sourceProfile event.epsilon event.precision)))
    (SourceFamilyOperator.constant (physicalN3RawEMReader event))).congr' ?_
  apply Eventually.of_forall
  intro F
  have hunit : physicalN3PoleApproachUnit event.momentum F leg (poles F) m =
      physicalN3PolePhase event.momentum F leg (poles F) •
        actualElectronPhysicalUnit event.momentum F
          (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg :=
    physicalN3PoleApproachUnit.eq_def _ _ _ _ _
  have hph : inner ℂ (physicalN3PoleApproachUnit event.momentum F leg (poles F) m)
      (physicalN3RawEMReader event
        (physicalN3PoleApproachUnit event.momentum F leg (poles F) m)) =
    inner ℂ (actualElectronPhysicalUnit event.momentum F
        (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)
      (physicalN3RawEMReader event
        (actualElectronPhysicalUnit event.momentum F
          (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)) :=
    (congrArg (fun v : H => inner ℂ v (physicalN3RawEMReader event v)) hunit).trans
      (rawem_phase_inner (physicalN3PolePhase event.momentum F leg (poles F))
        (physical_n3_pole_phase_norm event.momentum F leg (poles F)) _ _)
  unfold physicalN3PoleRawEMFrameObserver
  show inner ℂ (physicalN3PoleApproachUnit event.momentum F leg (poles F) m)
        (physicalN3RawEMReader event
          (physicalN3PoleApproachUnit event.momentum F leg (poles F) m)) -
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (physicalN3RawEMReader event
          (prepared (sourceProfile event.epsilon event.precision))) = _
  exact congrArg (fun z : ℂ => z -
    inner ℂ (prepared (sourceProfile event.epsilon event.precision))
      (physicalN3RawEMReader event
        (prepared (sourceProfile event.epsilon event.precision)))) hph

/-- The fixed-operator diagonal observer error between unit states: the shared
background read cancels only in the difference and remains in both reads. -/
private theorem rawem_observer_diagonal_error {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E→L[ℂ]E) (a x b : E) (ha : ‖a‖ = 1) (hx : ‖x‖ = 1) :
    ‖(inner ℂ a (A a) - inner ℂ b (A b)) - (inner ℂ x (A x) - inner ℂ b (A b))‖
      ≤ 2 * ‖A‖ * ‖a - x‖ := by
  have hsplit : inner ℂ a (A a) - inner ℂ x (A x) =
      inner ℂ (a - x) (A a) + inner ℂ x (A (a - x)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  have hd : (inner ℂ a (A a) - inner ℂ b (A b)) - (inner ℂ x (A x) - inner ℂ b (A b)) =
      inner ℂ a (A a) - inner ℂ x (A x) := by
    abel
  rw [hd, hsplit]
  calc _ ≤ ‖inner ℂ (a - x) (A a)‖ + ‖inner ℂ x (A (a - x))‖ := norm_add_le _ _
    _ ≤ ‖a - x‖ * ‖A a‖ + ‖x‖ * ‖A (a - x)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖a - x‖ * (‖A‖ * ‖a‖) + ‖x‖ * (‖A‖ * ‖a - x‖) :=
        add_le_add (mul_le_mul_of_nonneg_left (A.le_opNorm a) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (A.le_opNorm (a - x)) (norm_nonneg _))
    _ = _ := by rw [ha, hx]; ring

/-- The completed approach observer stays within twice the lifted raw price times
the source soft budget. -/
theorem physical_n3_pole_raw_em_observer_error (event : DressedEvent)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection event.momentum leg)
    (m : ℕ) :
    ‖physicalN3PoleRawEMHistoryObserver event leg poles m -
      physicalN3PoleRawEMPoleObserver event leg poles‖
      ≤ 2 * physicalN3RawEMPrice event * actualSoftBudget m := by
  have hRW : ‖GaussUnitaryHistory.reader (physicalN3RawEMReader event)‖
      ≤ physicalN3RawEMPrice event :=
    (rawem_observer_native_bound (physicalN3RawEMReader event)).trans
      (physical_n3_raw_em_reader_price event)
  have herr := physical_n3_pole_state_error event.momentum leg poles m
  unfold physicalN3PoleRawEMHistoryObserver physicalN3PoleRawEMPoleObserver
  calc _ ≤ 2 * ‖GaussUnitaryHistory.reader (physicalN3RawEMReader event)‖ *
        ‖physicalN3PoleApproachState event.momentum leg poles m -
          physicalN3PoleState event.momentum leg poles‖ :=
        rawem_observer_diagonal_error _ _ _ _
          (physical_n3_pole_approach_state_norm event.momentum leg poles m)
          (physical_n3_pole_state_norm event.momentum leg poles)
    _ ≤ 2 * ‖GaussUnitaryHistory.reader (physicalN3RawEMReader event)‖ *
        actualSoftBudget m :=
        mul_le_mul_of_nonneg_left herr
          (mul_nonneg (by norm_num) (norm_nonneg _))
    _ ≤ _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRW (by norm_num))
          (actual_soft_budget_positive m).le

/-- The approach observer returns to the pole observer through the fixed actual
event operator. -/
theorem physical_n3_pole_raw_em_observer_return (event : DressedEvent)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection event.momentum leg) :
    Tendsto (fun m => physicalN3PoleRawEMHistoryObserver event leg poles m) atTop
      (𝓝 (physicalN3PoleRawEMPoleObserver event leg poles)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  have hC : Tendsto (fun m =>
      2 * physicalN3RawEMPrice event * actualSoftBudget m) atTop (𝓝 0) := by
    have := actual_soft_budget_tendsto.const_mul (2 * physicalN3RawEMPrice event)
    simpa using this
  exact (hC.eventually (eventually_lt_nhds positive)).mono (fun m small => by
    rw [dist_eq_norm]
    exact (physical_n3_pole_raw_em_observer_error event leg poles m).trans_lt small)

/-- The pole observer pays the actual raw pole charge minus the same original
prepared-background read: sign plus the paired original Rmix correction and
event calibration state, minus the original background raw read. -/
theorem physical_n3_pole_raw_em_observer_charge (event : DressedEvent)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection event.momentum leg) :
    physicalN3PoleRawEMPoleObserver event leg poles =
      actualElectronSign leg +
        inner ℂ (physicalN3PoleState event.momentum leg poles)
          (physicalN3PoleCorrection event.momentum leg poles +
            physicalN3PoleEMCalibrationState event event.momentum leg poles) -
        inner ℂ (actualNoetherBackground event)
          (GaussUnitaryHistory.reader (physicalN3RawEMReader event)
            (actualNoetherBackground event)) := by
  unfold physicalN3PoleRawEMPoleObserver
  exact rawem_diagonal_charge (E := ElectronHistory)
    (GaussUnitaryHistory.reader (physicalN3RawEMReader event))
    (physicalN3PoleState event.momentum leg poles)
    (physicalN3PoleCorrection event.momentum leg poles +
      physicalN3PoleEMCalibrationState event event.momentum leg poles)
    (actualElectronSign leg)
    (inner ℂ (actualNoetherBackground event)
      (GaussUnitaryHistory.reader (physicalN3RawEMReader event) (actualNoetherBackground event)))
    (physical_n3_pole_state_norm event.momentum leg poles)
    (physical_n3_pole_raw_em_paired_charge event event.momentum event.momentum
      leg leg poles poles)

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
