import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.KPaired
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockEuler

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open scoped Topology InnerProductSpace
open private dual_weighted from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open private drive_raw_read original_outer_slope_continuousAt from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
local notation "q" => (1 / 4 : ℝ)
local notation "r" => junctionPoint
local notation "h" => junctionShift
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "H" => burnolUnitCountingPrimitiveL2

private theorem weighted_forward_graph (upper : ℝ) (large : 4 ≤ upper) (f : ℝ → ℂ)
    (derivative : ∀ u ∈ Icc 4 upper, HasDerivAt f (deriv f u) u)
    (regular : ContinuousOn (deriv f) (Icc 4 upper)) (measured : Measurable f) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (burnolWeightedReciprocalStepSource 4 upper f (deriv f))) atTop
      (𝓝 (WeightedProgram.program 4 upper f (deriv f) H)) := by
  have actual := weightedPrefix_tendsto 4 upper f (deriv f) (by norm_num) regular
  change Tendsto (weightedPrefix 4 upper f (deriv f)) atTop
    (𝓝 (WeightedProgram.program 4 upper f (deriv f) H)) at actual
  apply actual.congr'
  apply Eventually.of_forall
  intro N
  exact weighted_prefix_eq_finite_sub_continuous 4 upper f (deriv f) N
    (by norm_num) large derivative regular (measurable_deriv f) measured

private theorem weighted_reverse_graph (upper : ℝ) (large : 4 ≤ upper) (f : ℝ → ℂ)
    (regular : ContinuousOn (deriv f) (Icc 4 upper)) :
    Tendsto (fun N : ℕ => DualSource.source N (burnolWeightedReciprocalStepSource 4 upper f (deriv f))) atTop
      (𝓝 (WeightedProgram.program 4 upper f (deriv f) (poissonPair H))) := by
  have actual := WeightedProgram.program_tendsto 4 upper f (deriv f) (by norm_num) regular
    (fun N => DualSource.source N burnolUnitReciprocalPrimitiveL2) (poissonPair H) actual_reverse_primitive
  exact actual.congr' (Eventually.of_forall (fun N => (dual_weighted N upper large f (deriv f) regular).symm))

private theorem outer_derivative (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (positive : 0 < x) : HasDerivAt (originalOuter c i) (originalOuterSlope c i x) x := by
  fin_cases i
  · change HasDerivAt (burnolRieszStatePositiveOuterRaw c) (positionExteriorDerivative c x) x
    rw [funext (position_exterior_return_read c)]
    exact ((burnolMellinTailPower_hasDerivAt (star c.value) positive).const_mul (1 / 2 : ℂ)).sub
      ((burnolRieszReturnRaw_hasDerivAt c x).add_const
        (burnolQuarterMeanCoefficient (burnolTruncatedFourier (burnolRieszSingleFourierSource c : Hq))))
  · exact (sourceRaw_hasDerivAt c x positive.ne').add_const (fourierMean c)

private theorem outer_measurable (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    Measurable (originalOuter c i) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x outside
  have nonzero : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using outside
  fin_cases i
  · change ContinuousWithinAt (burnolRieszStatePositiveOuterRaw c) _ x
    rw [funext (position_exterior_return_read c)]
    exact ((continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const x (-star c.value) (Or.inr nonzero))).sub
      ((burnolRieszReturnRaw_continuous c).continuousAt.add continuousAt_const)).continuousWithinAt
  · exact ((burnolRieszSingleFourierSourceRaw_continuousAt c nonzero).add continuousAt_const).continuousWithinAt

def pairedDriveConstant (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : ℂ := driveInnerRaw c i 0

def pairedDriveCollarRaw (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) : ℂ :=
  driveOuterRaw c i x - pairedDriveConstant c i

def pairedDriveWeight (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : ℝ → ℂ :=
  weight (pairedDriveCollarRaw c i)

private def pairedDriveWeightSlope (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (u : ℝ) : ℂ :=
  -((u : ℂ)⁻¹ ^ 2) * (pairedDriveCollarRaw c i u⁻¹ + (u⁻¹ : ℝ) * driveOuterSlope c i u⁻¹)

private theorem collar_derivative (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (positive : 0 < x) :
    HasDerivAt (pairedDriveCollarRaw c i) (driveOuterSlope c i x) x := by
  have original := (outer_derivative c i (Real.exp h * x) (mul_pos (Real.exp_pos _) positive)).scomp x
    ((hasDerivAt_id x).const_mul (Real.exp h))
  have actual := ((((original.const_mul (Real.exp (h / 2) : ℂ)).add_const
    ((Real.exp (-h / 2) : ℂ) * originalGap c i)).div_const (2 : ℂ)).sub_const
      (sourceMean c i)).sub_const (pairedDriveConstant c i)
  convert! actual using 1
  dsimp [pairedDriveCollarRaw, driveOuterRaw, driveOuterSlope]
  ring

private theorem weight_derivative (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (u : ℝ) (positive : 0 < u) :
    HasDerivAt (pairedDriveWeight c i) (pairedDriveWeightSlope c i u) u := by
  have original := Complex.ofRealCLM.hasDerivAt.mul (collar_derivative c i u⁻¹ (inv_pos.mpr positive))
  have actual := original.scomp u ((hasDerivAt_id u).inv positive.ne')
  convert! actual using 1
  · funext v
    simp only [pairedDriveWeight, weight, Function.comp_apply, Pi.mul_apply, Complex.ofReal_inv,
      Complex.ofRealCLM_apply, div_eq_mul_inv]
    ring
  · simp only [pairedDriveWeightSlope, Complex.real_smul, Complex.ofRealCLM_apply, id_eq]
    push_cast
    simp only [div_eq_mul_inv, inv_pow]
    ring

private theorem drive_weight_measurable (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    Measurable (pairedDriveWeight c i) := by
  have outside : Measurable (driveOuterRaw c i) := by
    unfold driveOuterRaw
    exact (((measurable_const.mul ((outer_measurable c i).comp (measurable_const.mul measurable_id))).add
      measurable_const).div_const 2).sub_const _
  exact (outside.sub_const _).comp measurable_inv |>.div Complex.measurable_ofReal

private theorem drive_weight_regular (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    ContinuousOn (deriv (pairedDriveWeight c i)) (Icc 4 r⁻¹) := by
  have explicit : ContinuousOn (pairedDriveWeightSlope c i) (Icc 4 r⁻¹) := by
    intro u inside
    have positive : 0 < u := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) inside.1
    have reciprocal := continuousAt_inv₀ positive.ne'
    have value := (collar_derivative c i u⁻¹ (inv_pos.mpr positive)).continuousAt.comp reciprocal
    have slope : ContinuousAt (driveOuterSlope c i) u⁻¹ := by
      unfold driveOuterSlope
      exact (continuousAt_const.mul continuousAt_const).mul
        ((original_outer_slope_continuousAt c i (Real.exp h * u⁻¹)
          (mul_pos (Real.exp_pos _) (inv_pos.mpr positive))).comp (by fun_prop))
    have cast : ContinuousAt (fun x : ℝ => (x : ℂ)) u := Complex.continuous_ofReal.continuousAt
    exact ((cast.inv₀ (Complex.ofReal_ne_zero.mpr positive.ne')).pow 2 |>.neg |>.mul
      (value.add ((Complex.continuous_ofReal.continuousAt.comp reciprocal).mul (slope.comp reciprocal)))).continuousWithinAt
  exact explicit.congr (fun u inside => (weight_derivative c i u (by linarith [inside.1])).deriv)

private theorem upper_large : 4 ≤ r⁻¹ := by
  rw [show (4 : ℝ) = q⁻¹ by norm_num, inv_le_inv₀ (by norm_num : (0 : ℝ) < q) junctionPoint_bounds.1]
  exact junctionPoint_bounds.2.le

def pairedDriveCollarSource (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : BurnolL2 :=
  burnolWeightedReciprocalStepSource 4 r⁻¹ (pairedDriveWeight c i) (deriv (pairedDriveWeight c i))

/-- The constant and the genuine collar jump belong to one original paired drive. -/
theorem actual_paired_drive_source (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    E (sourceDrive c i : Hq) = pairedDriveConstant c i • ConstantDual.seed + pairedDriveCollarSource c i := by
  have profile := weighted_source_coeFn 4 r⁻¹ (pairedDriveWeight c i) (deriv (pairedDriveWeight c i))
    (by norm_num) upper_large (fun u inside => (weight_derivative c i u (by linarith [inside.1])).differentiableAt.hasDerivAt)
    (drive_weight_regular c i) (measurable_deriv _)
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (drive_raw_read c i)
  apply Lp.ext
  filter_upwards [burnolQuarterZeroExtension_coe (sourceDrive c i : Hq), localRead, profile,
    Lp.coeFn_add (pairedDriveConstant c i • ConstantDual.seed) (pairedDriveCollarSource c i),
    Lp.coeFn_smul (pairedDriveConstant c i) ConstantDual.seed, ConstantDual.seed_coeFn,
    volume.ae_ne (0 : ℝ)] with x extended source collar addition scalar constant nonzero
  change (pairedDriveCollarSource c i : ℝ → ℂ) x = _ at collar
  rw [addition, Pi.add_apply, scalar, Pi.smul_apply, smul_eq_mul, constant, extended, collar]
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have lower : 4 ≤ |x|⁻¹ ↔ |x| ≤ q := by
    rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 4) positive]
    norm_num only [inv_eq_one_div]
  have upper : |x|⁻¹ < r⁻¹ ↔ r < |x| := (inv_lt_inv₀ positive junctionPoint_bounds.1)
  simp only [burnolReciprocalStepSourceRaw, lower, upper]
  by_cases inside : |x| ≤ q
  · have member : x ∈ symmetricInterval q := abs_le.mp inside
    rw [indicator_of_mem member, source member, ConstantDual.seedRaw, if_pos inside, mul_one]
    by_cases inner : |x| ≤ r
    · rw [driveRaw, if_pos inner, if_neg (fun active => (not_lt_of_ge inner) active.2), mul_zero, add_zero]
      rfl
    · rw [driveRaw, if_neg inner, if_pos ⟨inside, lt_of_not_ge inner⟩]
      simp only [pairedDriveWeight, weight, inv_inv, Complex.ofReal_inv, div_eq_mul_inv]
      rw [mul_inv_cancel_right₀ (Complex.ofReal_ne_zero.mpr positive.ne')]
      unfold pairedDriveCollarRaw
      ring
  · have outside : x ∉ symmetricInterval q := fun member => inside (abs_le.mpr member)
    rw [indicator_of_notMem outside, ConstantDual.seedRaw, if_neg inside,
      if_neg (fun active => inside active.1), mul_zero, mul_zero, add_zero]

def pairedDriveForward (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : BurnolL2 :=
  pairedDriveConstant c i • ConstantForward.value +
    WeightedProgram.program 4 r⁻¹ (pairedDriveWeight c i) (deriv (pairedDriveWeight c i)) H

def pairedDriveReverse (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : BurnolL2 :=
  pairedDriveConstant c i • ConstantDual.value +
    WeightedProgram.program 4 r⁻¹ (pairedDriveWeight c i) (deriv (pairedDriveWeight c i)) (poissonPair H)

theorem actual_paired_drive_forward (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (E (sourceDrive c i : Hq))) atTop
      (𝓝 (pairedDriveForward c i)) := by
  have source := (ConstantForward.original_tendsto.const_smul (pairedDriveConstant c i)).add
    (weighted_forward_graph r⁻¹ upper_large (pairedDriveWeight c i)
      (fun u inside => (weight_derivative c i u (by linarith [inside.1])).differentiableAt.hasDerivAt)
      (drive_weight_regular c i) (drive_weight_measurable c i))
  exact source.congr' (Eventually.of_forall (fun N => by
    change _ = CountingDual.sourceCLM N (E (sourceDrive c i : Hq))
    rw [actual_paired_drive_source, map_add, map_smul]
    rfl))

theorem actual_paired_drive_reverse (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    Tendsto (fun N : ℕ => DualSource.source N (E (sourceDrive c i : Hq))) atTop
      (𝓝 (pairedDriveReverse c i)) := by
  have source := (ConstantDual.original_tendsto.const_smul (pairedDriveConstant c i)).add
    (weighted_reverse_graph r⁻¹ upper_large (pairedDriveWeight c i) (drive_weight_regular c i))
  exact source.congr' (Eventually.of_forall (fun N => by
    rw [actual_paired_drive_source]
    simp only [CountingDual.dual_eq_adjoint, map_add, map_smul]
    rfl))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
