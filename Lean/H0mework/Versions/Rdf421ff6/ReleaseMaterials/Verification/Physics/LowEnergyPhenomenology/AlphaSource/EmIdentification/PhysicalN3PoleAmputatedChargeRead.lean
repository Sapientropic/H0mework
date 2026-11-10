import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleSourceFilter
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeAdaptivePhysicalSoftReturn

/-! The original two-Green amputated charge vertex evaluated on the generated
source pole families: the actual left-generator adjoint reads the two-inverse
vertex with each endpoint at its own adaptive pole energy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumUncutYukawa PreparationVacuumSourcePreparedResponse
open GaussComposite.SourceGraph
open ActualDressedUniformMaterialCoefficients ActualElectronPhysicalJointInverse
open ActualElectronWholeChargeSoft CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open SourceFamilyHilbert SourceFamilyOperator
open SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open LowEnergy.ActualDressedVisiblePole
open Filter
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
  prepared sourceProfile

/-- The lifted constant reader keeps the original operator norm. -/
private theorem amputated_reader_bound {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I) (A : E→L[ℂ]E) :
    ‖SourceFamilyOperator.lift u (SourceFamilyOperator.constant A)‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  exact SourceBoundaryGram.lift_bound_explicit u (SourceFamilyOperator.constant A) ‖A‖
    (norm_nonneg A) (fun _ y=>A.le_opNorm y) x

/-- Unit-modulus scalars drop out of the diagonal pairing. -/
private theorem amputated_phase_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ζ : ℂ) (hζ : ‖ζ‖ = 1) (A : E→L[ℂ]E) (v : E) :
    inner ℂ (ζ • v) (A (ζ • v)) = inner ℂ v (A v) := by
  have hmul : ζ * (starRingEnd ℂ) ζ = 1 := by
    simpa [hζ] using RCLike.mul_conj ζ
  rw [map_smul, inner_smul_right, inner_smul_left, ← mul_assoc, hmul, one_mul]

/-- The amputated two-Green pairing: the adjointed left generator acting through the
vertex on the right-generated vector equals the charge read, generically. -/
private theorem amputated_pairing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (gL gR A Q : E→L[ℂ]E)
    (h : gL * A * gR = Q)
    (uL uR : E) :
    inner ℂ (gL.adjoint uL) (A (gR uR)) = inner ℂ uL (Q uR) := by
  have h1 : inner ℂ (gL.adjoint uL) (A (gR uR)) =
      inner ℂ uL (gL (A (gR uR))) :=
    ContinuousLinearMap.adjoint_inner_left _ _ _
  have h2 : inner ℂ uL (gL (A (gR uR))) =
      inner ℂ uL ((gL * A * gR) uR) :=
    congrArg (inner ℂ uL)
      (show gL (A (gR uR)) = (gL * A * gR) uR from rfl)
  rw [h1, h2, h]

/-- Two-endpoint pairing error between unit states, generic carrier. -/
private theorem amputated_pair_error {E : Type*} [NormedAddCommGroup E]
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

/-- The per-frame amputated charge read at the generated approach energies: the true
left generator adjoint on the left approach unit, the actual two-inverse vertex at
k = pL - pR on the right-generated approach unit. -/
def physicalN3PoleAmputatedChargeFrameRead (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) : ℂ :=
  let zL := physicalN3PoleApproachEnergy pL F left (polesL F) m
  let wR := physicalN3PoleApproachEnergy pR F right (polesR F) m
  inner ℂ
    ((jointGenerator pL F zL 0).adjoint
      (physicalN3PoleApproachUnit pL F left (polesL F) m))
    (actualElectronPhysicalChargeVertex pR (pL - pR) F zL wR
      (jointGenerator pR F wR 0
        (physicalN3PoleApproachUnit pR F right (polesR F) m)))

/-- The amputated read collapses to the charge pairing by the actual amputation of
the two physical inverses at the generated nonreal energies. -/
theorem physical_n3_pole_amputated_charge_value (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) :
    physicalN3PoleAmputatedChargeFrameRead pL pR left right polesL polesR m F =
      inner ℂ (physicalN3PoleApproachUnit pL F left (polesL F) m)
        (chargeReader sourcePhaseGaugeLie
          (physicalN3PoleApproachUnit pR F right (polesR F) m)) := by
  unfold physicalN3PoleAmputatedChargeFrameRead
  have hk : pR + (pL - pR) = pL := by abel
  have hamp := actual_electron_physical_charge_amputation pR (pL - pR) F
    (physicalN3PoleApproachEnergy pL F left (polesL F) m)
    (physicalN3PoleApproachEnergy pR F right (polesR F) m)
    (physical_n3_pole_energy_nonreal pL F left (polesL F) m)
    (physical_n3_pole_energy_nonreal pR F right (polesR F) m)
  rw [show jointGenerator (pR + (pL - pR)) F
      (physicalN3PoleApproachEnergy pL F left (polesL F) m) 0 =
      jointGenerator pL F (physicalN3PoleApproachEnergy pL F left (polesL F) m) 0 from
        congrArg (fun q : PhysicalMomentum =>
          jointGenerator q F
            (physicalN3PoleApproachEnergy pL F left (polesL F) m) 0) hk] at hamp
  exact amputated_pairing _ _ _ _ hamp _ _

/-- The amputated read is bounded by the charge-reader norm, using the two source
unit norms after the exact amputation. -/
theorem physical_n3_pole_amputated_charge_price (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) :
    ‖physicalN3PoleAmputatedChargeFrameRead pL pR left right polesL polesR m F‖
      ≤ ‖chargeReader sourcePhaseGaugeLie‖ := by
  rw [physical_n3_pole_amputated_charge_value]
  calc ‖inner ℂ (physicalN3PoleApproachUnit pL F left (polesL F) m)
        (chargeReader sourcePhaseGaugeLie
          (physicalN3PoleApproachUnit pR F right (polesR F) m))‖
      ≤ ‖physicalN3PoleApproachUnit pL F left (polesL F) m‖ *
        ‖chargeReader sourcePhaseGaugeLie
          (physicalN3PoleApproachUnit pR F right (polesR F) m)‖ :=
        norm_inner_le_norm _ _
    _ ≤ 1 * (‖chargeReader sourcePhaseGaugeLie‖ * 1) := by
        apply mul_le_mul
        · rw [physical_n3_pole_approach_unit_norm]
        · exact ((chargeReader sourcePhaseGaugeLie).le_opNorm _).trans
            (by rw [physical_n3_pole_approach_unit_norm, mul_one])
        · exact norm_nonneg _
        · exact zero_le_one
    _ = _ := by ring

/-- The completed approach-state charge read at step `m`. -/
def physicalN3PoleAmputatedChargeHistoryRead (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) : ℂ :=
  inner ℂ (physicalN3PoleApproachState pL left polesL m)
    (GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie)
      (physicalN3PoleApproachState pR right polesR m))

/-- The per-frame amputated reads return through the original `sourceFilter` to the
completed approach-state charge read. -/
theorem physical_n3_pole_amputated_charge_source_return (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) :
    Tendsto (fun F => physicalN3PoleAmputatedChargeFrameRead pL pR left right polesL
        polesR m F)
      GaussUnitaryHistory.sourceFilter
      (𝓝 (physicalN3PoleAmputatedChargeHistoryRead pL pR left right polesL polesR m)) := by
  unfold physicalN3PoleAmputatedChargeHistoryRead physicalN3PoleApproachState
  rw [GaussUnitaryHistory.reader, SourceFamilyOperator.lift_coe, inner_coe]
  exact (pair_tendsto GaussUnitaryHistory.sourceFilter
    (physicalN3PoleApproachFamily pL left polesL m)
    (act GaussUnitaryHistory.sourceFilter
      (SourceFamilyOperator.constant (chargeReader sourcePhaseGaugeLie))
      (physicalN3PoleApproachFamily pR right polesR m))).congr'
    (Eventually.of_forall fun F =>
      (physical_n3_pole_amputated_charge_value pL pR left right polesL polesR m F).symm)

/-- The completed two-endpoint charge difference between approach and pole states is
`2‖Q‖·budget`, generically at the completed-reader level. -/
theorem physical_n3_pole_amputated_charge_history_error (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) :
    ‖physicalN3PoleAmputatedChargeHistoryRead pL pR left right polesL polesR m -
      inner ℂ (physicalN3PoleState pL left polesL)
        (GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie)
          (physicalN3PoleState pR right polesR))‖
      ≤ 2 * ‖chargeReader sourcePhaseGaugeLie‖ * actualSoftBudget m := by
  have hRW : ‖GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie)‖
      ≤ ‖chargeReader sourcePhaseGaugeLie‖ :=
    amputated_reader_bound GaussUnitaryHistory.sourceFilter _
  have herrL := physical_n3_pole_state_error pL left polesL m
  have herrR := physical_n3_pole_state_error pR right polesR m
  unfold physicalN3PoleAmputatedChargeHistoryRead
  calc _ ≤ ‖GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie)‖ *
          (‖physicalN3PoleApproachState pL left polesL m -
            physicalN3PoleState pL left polesL‖ +
          ‖physicalN3PoleApproachState pR right polesR m -
            physicalN3PoleState pR right polesR‖) :=
        amputated_pair_error _ _ _ _ _
          (physical_n3_pole_state_norm pL left polesL)
          (physical_n3_pole_approach_state_norm pR right polesR m)
    _ ≤ ‖GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie)‖ *
          (actualSoftBudget m + actualSoftBudget m) :=
        mul_le_mul_of_nonneg_left (add_le_add herrL herrR) (norm_nonneg _)
    _ = 2 * ‖GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie)‖ *
          actualSoftBudget m := by ring
    _ ≤ _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRW (by norm_num))
          (actual_soft_budget_positive m).le

/-- The approach charge reads converge to the pole-side charge: the original sign
times the retained completed overlap plus the whole right Rmix correction. The sign
is not the output charge. -/
theorem physical_n3_pole_amputated_charge_pole_return (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right) :
    Tendsto (fun m => physicalN3PoleAmputatedChargeHistoryRead pL pR left right polesL
        polesR m) atTop
      (𝓝 (actualElectronSign right *
          inner ℂ (physicalN3PoleState pL left polesL)
            (physicalN3PoleState pR right polesR) +
        inner ℂ (physicalN3PoleState pL left polesL)
          (physicalN3PoleCorrection pR right polesR))) := by
  have hlim : Tendsto
      (fun m => physicalN3PoleAmputatedChargeHistoryRead pL pR left right polesL
        polesR m) atTop
      (𝓝 (inner ℂ (physicalN3PoleState pL left polesL)
        (GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie)
          (physicalN3PoleState pR right polesR)))) := by
    apply Metric.tendsto_nhds.mpr
    intro epsilon positive
    have hC : Tendsto (fun m =>
        2 * ‖chargeReader sourcePhaseGaugeLie‖ * actualSoftBudget m) atTop (𝓝 0) := by
      have := actual_soft_budget_tendsto.const_mul
        (2 * ‖chargeReader sourcePhaseGaugeLie‖)
      simpa using this
    exact (hC.eventually (eventually_lt_nhds positive)).mono (fun m small => by
      rw [dist_eq_norm]
      exact (physical_n3_pole_amputated_charge_history_error pL pR left right polesL
        polesR m).trans_lt small)
  rwa [physical_n3_pole_paired_charge pL pR left right polesL polesR] at hlim

/-- At zero transfer the frame read is exactly the original external charge read at
the generated approach energy on the same leg and source. -/
theorem physical_n3_pole_zero_transfer_charge_value (p : PhysicalMomentum)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection p leg)
    (m : ℕ) (F : GaussUnitaryHistory.Index) :
    physicalN3PoleAmputatedChargeFrameRead p p leg leg poles poles m F =
      actualElectronPhysicalChargeRead p F
        (physicalN3PoleApproachEnergy p F leg (poles F) m) leg := by
  rw [physical_n3_pole_amputated_charge_value]
  unfold actualElectronPhysicalChargeRead
  have hu : physicalN3PoleApproachUnit p F leg (poles F) m =
      physicalN3PolePhase p F leg (poles F) •
        actualElectronPhysicalUnit p F
          (physicalN3PoleApproachEnergy p F leg (poles F) m) leg :=
    physicalN3PoleApproachUnit.eq_def _ _ _ _ _
  exact (congrArg (fun v : H => inner ℂ v
      (chargeReader sourcePhaseGaugeLie v)) hu).trans
    (amputated_phase_inner (physicalN3PolePhase p F leg (poles F))
      (physical_n3_pole_phase_norm p F leg (poles F))
      (chargeReader sourcePhaseGaugeLie)
      (actualElectronPhysicalUnit p F
        (physicalN3PoleApproachEnergy p F leg (poles F) m) leg))

/-- The generic charge-split pairing: if `Q uR = s•uR + c`, the diagonal read is the
sign-weighted overlap plus the correction pairing. -/
private theorem amputated_charge_split {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (Q : E→L[ℂ]E) (uL uR c : E) (s : ℂ)
    (hQ : Q uR = s • uR + c) :
    inner ℂ uL (Q uR) = s * inner ℂ uL uR + inner ℂ uL c := by
  rw [hQ, inner_add_right, inner_smul_right]

/-- The frame read of the retained right Rmix correction: the left approach unit
paired against the generated phase times the original charge correction at the
generated nonreal approach energy. -/
def physicalN3PoleAmputatedCorrectionFrameRead (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) : ℂ :=
  inner ℂ (physicalN3PoleApproachUnit pL F left (polesL F) m)
    (physicalN3PolePhase pR F right (polesR F) •
      actualElectronPhysicalChargeCorrection pR F
        (physicalN3PoleApproachEnergy pR F right (polesR F) m) right)

/-- The amputated vertex read splits as the original sign times the source-unit
overlap plus the actual right Rmix correction read; the correction value is the
already-certified generated Rmix bridge, not an input endpoint equation. -/
theorem physical_n3_pole_amputated_charge_frame_correction (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) :
    physicalN3PoleAmputatedChargeFrameRead pL pR left right polesL polesR m F =
      actualElectronSign right *
        inner ℂ (physicalN3PoleApproachUnit pL F left (polesL F) m)
          (physicalN3PoleApproachUnit pR F right (polesR F) m) +
      physicalN3PoleAmputatedCorrectionFrameRead pL pR left right polesL polesR m F := by
  rw [physical_n3_pole_amputated_charge_value]
  unfold physicalN3PoleAmputatedCorrectionFrameRead
  have hv' : chargeReader sourcePhaseGaugeLie
        (physicalN3PoleApproachUnit pR F right (polesR F) m) -
      actualElectronSign right •
        physicalN3PoleApproachUnit pR F right (polesR F) m =
      physicalN3PolePhase pR F right (polesR F) •
        actualElectronPhysicalChargeCorrection pR F
          (physicalN3PoleApproachEnergy pR F right (polesR F) m) right :=
    physical_n3_pole_approach_correction_value pR right polesR m F
  have hQ : chargeReader sourcePhaseGaugeLie
        (physicalN3PoleApproachUnit pR F right (polesR F) m) =
      actualElectronSign right •
        physicalN3PoleApproachUnit pR F right (polesR F) m +
      physicalN3PolePhase pR F right (polesR F) •
        actualElectronPhysicalChargeCorrection pR F
          (physicalN3PoleApproachEnergy pR F right (polesR F) m) right := by
    rw [← hv', add_comm, sub_add_cancel]
  exact amputated_charge_split (chargeReader sourcePhaseGaugeLie) _ _ _ _ hQ

/-- The actual Rmix frame reads return through the original `sourceFilter` to the
completed approach-state correction pairing. -/
theorem physical_n3_pole_amputated_correction_source_return (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) :
    Tendsto (fun F => physicalN3PoleAmputatedCorrectionFrameRead pL pR left right
        polesL polesR m F)
      GaussUnitaryHistory.sourceFilter
      (𝓝 (inner ℂ (physicalN3PoleApproachState pL left polesL m)
        (physicalN3PoleApproachCorrection pR right polesR m))) := by
  unfold physicalN3PoleApproachState physicalN3PoleApproachCorrection
  rw [inner_coe]
  exact (pair_tendsto GaussUnitaryHistory.sourceFilter
    (physicalN3PoleApproachFamily pL left polesL m)
    (physicalN3PoleApproachCorrectionFamily pR right polesR m)).congr'
    (Eventually.of_forall fun F =>
      congrArg (fun v : H => inner ℂ
        (physicalN3PoleApproachUnit pL F left (polesL F) m) v)
        (physical_n3_pole_approach_correction_value pR right polesR m F))

/-- The completed approach-pairing returns to the pole-state paired against the
retained original right correction, consuming both certified strong returns. -/
theorem physical_n3_pole_amputated_correction_pole_return (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right) :
    Tendsto (fun m => inner ℂ (physicalN3PoleApproachState pL left polesL m)
        (physicalN3PoleApproachCorrection pR right polesR m)) atTop
      (𝓝 (inner ℂ (physicalN3PoleState pL left polesL)
        (physicalN3PoleCorrection pR right polesR))) :=
  (physical_n3_pole_state_return pL left polesL).inner
    (physical_n3_pole_correction_return pR right polesR)

/-- The literal zero-transfer charge return: the history read converges to
`sign + inner(poleState, poleCorrection)`. This is not the Thomson limit or a
physical EM coupling identification. -/
theorem physical_n3_pole_zero_transfer_charge_return (p : PhysicalMomentum)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection p leg) :
    Tendsto (fun m => physicalN3PoleAmputatedChargeHistoryRead p p leg leg poles
        poles m) atTop
      (𝓝 (actualElectronSign leg +
        inner ℂ (physicalN3PoleState p leg poles)
          (physicalN3PoleCorrection p leg poles))) := by
  have h := physical_n3_pole_amputated_charge_pole_return p p leg leg poles poles
  have htarget : actualElectronSign leg *
      inner ℂ (physicalN3PoleState p leg poles) (physicalN3PoleState p leg poles) +
    inner ℂ (physicalN3PoleState p leg poles)
      (physicalN3PoleCorrection p leg poles) =
      actualElectronSign leg +
    inner ℂ (physicalN3PoleState p leg poles)
      (physicalN3PoleCorrection p leg poles) := by
    rw [inner_self_eq_norm_sq_to_K, physical_n3_pole_state_norm]
    norm_num
  rw [← htarget]
  exact h

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
