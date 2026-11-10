import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3EMIRSplit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3ChargeEndpoint

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedN3EMChargeRead
open CanonicalGradedSpatialSource ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator
open LowEnergy.GaussComposite.ActualDressedVisiblePole
open ActualSourcePreparedEMEnclosure ActualSourcePreparedN3EMConsumer ActualSourcePreparedN3IRNumerator
open ActualSourcePreparedN3EMIRSplit ActualSourcePreparedN3ChargeEndpoint
open ActualCompositeFieldCurrent ActualEMCurrentSplit ActualEMResponseSplit PhysicalN3SourceEnergy
open ActualDressedNoetherCoulombUnit ActualDressedZeroDamping ActualDressedEMTensorClock
open LowEnergy.ActualDressedVisiblePole Polynomial Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceN3ArmNumerator commonDeterminant commonDenominator

def sourceN3ArmDampingFraction (fieldEvent detector source : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (dEM sEM : Bool) : RatFunc ℂ :=
  readFraction (dampingSlice epsilon
    (sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles dEM sEM))
      (dampingDeterminant fieldEvent epsilon n)

/-- Reduction keeps the four source arms independent, so cancellation of full
pole terms cannot silently remove a mixed or residual contribution. -/
theorem source_n3_damping_four_arms (fieldEvent detector source : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) :
    sourceN3DampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles =
      sourceN3ArmDampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles true true +
      sourceN3ArmDampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles true false +
      sourceN3ArmDampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles false true +
      sourceN3ArmDampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles false false := by
  unfold sourceN3DampingFraction
  rw [source_n3_numerator_four_arms]
  simp only [sourceN3ArmDampingFraction, readFraction, map_add, add_div]

theorem source_n3_arm_damping_read (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (dEM sEM : Bool) (positive : 0 < sigma)
    (chart : (dampingDeterminant fieldEvent epsilon n).eval (sigma : ℂ) ≠ 0) :
    let R := sourceN3ArmDampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles dEM sEM
    sourceN3ArmRead fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles dEM sEM =
      R.num.eval (sigma : ℂ)/R.denom.eval (sigma : ℂ) := by
  have commonRegular : MvPolynomial.eval (irValues epsilon sigma 0) (commonDeterminant fieldEvent n) ≠ 0 := by
    rw [← damping_slice_eval]
    exact chart
  have regular := actual_common_chart_original fieldEvent epsilon sigma 0 n positive commonRegular
  have read := source_n3_arm_read_fraction fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles dEM sEM positive regular
  refine read.trans ?_
  change _ = (readFraction (dampingSlice epsilon
    (sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles dEM sEM))
      (dampingSlice epsilon (commonDeterminant fieldEvent n))).num.eval (sigma : ℂ) / _
  rw [← damping_slice_eval, ← damping_slice_eval]
  exact (reduced_read_at_regular _ _ (sigma : ℂ) chart).symm

private theorem positive_complex_punctured :
    Tendsto (fun sigma : ℝ => (sigma : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero] using (ne_of_gt positive)

/-- The physical Noether EM read uses its own source scalar pole order, not
the order of the complete N3 read or of the full matrix. -/
theorem source_n3_em_clock_order_return (fieldEvent detector source : DressedEvent)
    (epsilon : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (nonzero : dampingDeterminant fieldEvent epsilon n ≠ 0) :
    let R := sourceN3ArmDampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles true true
    Tendsto (fun sigma : ℝ => (sigma : ℂ)^poleOrder R 0 *
      dotProduct (physicalN3PoleNoetherCurrent detector dLeg dPoles)
        ((noetherPairScale^2 • sourcePreparedEMTensorRead fieldEvent epsilon sigma n) *ᵥ
          physicalN3PoleNoetherCurrent source sLeg sPoles))
      (𝓝[>] 0) (𝓝 (leadingPoleCoefficient R 0)) := by
  let R := sourceN3ArmDampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles true true
  have base := (pole_order_limit R 0).comp positive_complex_punctured
  simp only [Function.comp_def, sub_zero] at base
  apply Tendsto.congr' ?_ base
  have inclusion : Ioi (0 : ℝ) ⊆ ({0}ᶜ) := by
    intro sigma positive
    simpa only [mem_compl_iff, mem_singleton_iff] using (ne_of_gt positive)
  have chart := (source_static_punctured_chart _ nonzero).filter_mono (nhdsWithin_mono 0 inclusion)
  filter_upwards [chart, self_mem_nhdsWithin] with sigma regular positive
  have original : MvPolynomial.eval (irValues epsilon sigma 0) (commonDeterminant fieldEvent n) ≠ 0 := by
    rw [← damping_slice_eval]
    exact regular
  have inverse := actual_common_chart_original fieldEvent epsilon sigma 0 n positive original
  have read := source_n3_arm_damping_read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles true true positive regular
  rw [source_n3_em_arm_noether_read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles positive inverse] at read
  exact congrArg (fun v : ℂ => (sigma : ℂ)^poleOrder R 0*v) read.symm

def sourceN3TemporalEMCoefficient (fieldEvent : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) : ℂ :=
  noetherPairScale^2 * sourcePreparedEMTensorRead fieldEvent epsilon sigma n 0 0

def sourceN3OtherEMRead (fieldEvent detector source : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : ℂ :=
  ∑ mu : Fin 4, ∑ nu : Fin 4, if mu=0 ∧ nu=0 then 0 else
    physicalN3PoleNoetherCurrent detector dLeg dPoles mu *
      (noetherPairScale^2 * sourcePreparedEMTensorRead fieldEvent epsilon sigma n mu nu) *
        physicalN3PoleNoetherCurrent source sLeg sPoles nu

private theorem temporal_tensor_split (T : Matrix (Fin 4) (Fin 4) ℂ) (qd qs : Fin 4 → ℂ) :
    dotProduct qd (T*ᵥqs) = qd 0*T 0 0*qs 0 +
      ∑ mu : Fin 4, ∑ nu : Fin 4, if mu=0 ∧ nu=0 then 0 else qd mu*T mu nu*qs nu := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  ring

/-- Actual EM temporal charges are the same-state amputated pole charges plus
the source calibration/background defects; all other fifteen EM terms remain. -/
theorem source_n3_em_charge_endpoint_read (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (positive : 0 < sigma)
    (regular : correctedDet fieldEvent epsilon 0 sigma n ≠ 0) :
    sourceN3ArmRead fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles true true =
      (sourceN3AmputatedPoleCharge detector dLeg dPoles + sourceN3ChargeReadDefect detector dLeg dPoles) *
        (sourceN3AmputatedPoleCharge source sLeg sPoles + sourceN3ChargeReadDefect source sLeg sPoles) *
          sourceN3TemporalEMCoefficient fieldEvent epsilon sigma n +
      sourceN3OtherEMRead fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles := by
  rw [source_n3_em_arm_noether_read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles positive regular,
    temporal_tensor_split]
  simp only [Matrix.smul_apply, smul_eq_mul, source_n3_noether_charge_endpoint]
  unfold sourceN3TemporalEMCoefficient sourceN3OtherEMRead
  ring

theorem source_n3_em_charge_matching_price (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (positive : 0 < sigma)
    (regular : correctedDet fieldEvent epsilon 0 sigma n ≠ 0) :
    ‖sourceN3ArmRead fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles true true -
      (sourceN3AmputatedPoleCharge detector dLeg dPoles * sourceN3AmputatedPoleCharge source sLeg sPoles *
        sourceN3TemporalEMCoefficient fieldEvent epsilon sigma n +
        sourceN3OtherEMRead fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles)‖ ≤
      sourceN3ChargePairPrice detector source dLeg sLeg dPoles sPoles *
        ‖sourceN3TemporalEMCoefficient fieldEvent epsilon sigma n‖ := by
  rw [source_n3_em_charge_endpoint_read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles positive regular]
  have pair := source_n3_charge_pair_price detector source dLeg sLeg dPoles sPoles
  rw [source_n3_noether_charge_endpoint, source_n3_noether_charge_endpoint] at pair
  have difference (a b c d t other : ℂ) : (a+b)*(c+d)*t+other-(a*c*t+other) =
      ((a+b)*(c+d)-a*c)*t := by ring
  rw [difference, norm_mul]
  exact mul_le_mul_of_nonneg_right pair (norm_nonneg _)

end LowEnergy.GaussComposite.ActualSourcePreparedN3EMChargeRead
