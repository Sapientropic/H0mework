import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.ConstantColumn
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.BoundaryCosineSource
import H0mework.Versions.R7e4da746.Arithmetic.TruncatedFourier.DilationAction
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Core

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace ConstantFourierEulerVelocity

open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
open FixedWindowFourierReaction
attribute [local instance 1100] Module.complexToReal NormedSpace.complexToReal

local notation "T" => burnolRechartedTruncatedFourierOperator
local notation "c" => burnolRadiusBoundaryCosineState
local notation "q" => (1 / 4 : ℝ)
local notation "μunit" => (Measure.restrict (volume : Measure ℝ) (symmetricInterval 1))
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

open private burnolRadiusRechartedTruncatedFourierRaw_eq_kernelIntegral
  burnolRadiusRechartedFirstVariationRaw_eq_kernelIntegral from
  H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.Operator.ClozelBurnolRechartedIntegralRemainder

private theorem endpoint_pair (r x : ℝ) :
    Complex.exp (-2 * (Real.pi : ℂ) * I * (r : ℂ)^2 * (x : ℂ)) +
      Complex.exp (2 * (Real.pi : ℂ) * I * (r : ℂ)^2 * (x : ℂ)) =
        burnolRadiusBoundaryCosineRaw r x := by
  unfold burnolRadiusBoundaryCosineRaw
  push_cast
  rw [Complex.two_cos, add_comm]
  congr 1 <;> congr 1 <;> ring

private theorem constant_raw_ward (r x : ℝ) :
    (r : ℂ) * burnolRadiusRechartedFirstVariationRaw r e x +
      burnolRadiusRechartedTruncatedFourierRaw r e x =
        (2 * r : ℂ) * burnolRadiusBoundaryCosineRaw r x := by
  let phase : ℝ → ℂ := fun y => Complex.exp
    (-2 * (Real.pi : ℂ) * I * (r : ℂ)^2 * (x : ℂ) * (y : ℂ))
  let density : ℝ → ℂ := fun y => phase y *
    (1 - 2 * (Real.pi : ℂ) * I * (r : ℂ)^2 * (x : ℂ) * (y : ℂ))
  let primitive : ℝ → ℂ := fun y => (y : ℂ) * phase y
  have phaseContinuous : Continuous phase := by dsimp [phase]; fun_prop
  have densityContinuous : Continuous density := by dsimp [density]; fun_prop
  have derivative (y : ℝ) : HasDerivAt primitive (density y) y := by
    have dp := (((Complex.ofRealCLM.hasDerivAt (x := y)).const_mul
      (-2 * (Real.pi : ℂ) * I * (r : ℂ)^2 * (x : ℂ))).cexp)
    have actual := (Complex.ofRealCLM.hasDerivAt (x := y)).mul dp
    convert! actual using 1
    first | rfl |
      (simp only [density, phase, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]; ring)
  have boundary := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => derivative y) (densityContinuous.intervalIntegrable (-1) 1)
  have dRead : burnolRadiusRechartedFirstVariationRaw r e x =
      ∫ y : ℝ in (-1)..1, burnolUnitRechartedKernelDerivative r x y := by
    rw [burnolRadiusRechartedFirstVariationRaw_eq_kernelIntegral,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [intervalConstant_coeFn 1] with y read
    change e y = 1 at read
    rw [read, mul_one]
  have tRead : burnolRadiusRechartedTruncatedFourierRaw r e x =
      ∫ y : ℝ in (-1)..1, burnolUnitRechartedKernel r x y := by
    rw [burnolRadiusRechartedTruncatedFourierRaw_eq_kernelIntegral,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [intervalConstant_coeFn 1] with y read
    change e y = 1 at read
    rw [read, mul_one]
  have dc : Continuous (fun y => (r : ℂ) * burnolUnitRechartedKernelDerivative r x y) := by
    unfold burnolUnitRechartedKernelDerivative; fun_prop
  have tc : Continuous (burnolUnitRechartedKernel r x) := by
    unfold burnolUnitRechartedKernel; fun_prop
  rw [dRead, tRead, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (dc.intervalIntegrable (-1) 1) (tc.intervalIntegrable (-1) 1)]
  calc
    _ = (2 * r : ℂ) * ∫ y : ℝ in (-1)..1, density y := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      simp only [density, phase, burnolUnitRechartedKernelDerivative, burnolUnitRechartedKernel]
      ring
    _ = _ := by
      rw [boundary]
      dsimp only [primitive, phase]
      norm_num only [Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg, neg_mul, neg_neg]
      simp only [one_mul, sub_neg_eq_add]
      have source := endpoint_pair r x
      simp only [neg_mul] at source
      rw [source]

/-- The actual constant column generates both endpoint traces of the radius derivative. -/
theorem constant_column_ward (r : ℝ) (positive : 0 < r) :
    (r : ℂ) • burnolRadiusRechartedTruncatedFourierDerivative positive e + T r e =
      (2 * r : ℂ) • c r := by
  rw [burnolRechartedTruncatedFourierOperator_of_pos positive]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      ((r : ℂ) • burnolRadiusRechartedTruncatedFourierDerivative positive e)
      (burnolRadiusRechartedTruncatedFourier positive e),
    Lp.coeFn_smul (r : ℂ) (burnolRadiusRechartedTruncatedFourierDerivative positive e),
    burnolRadiusRechartedTruncatedFourierDerivative_coe positive e,
    burnolRadiusRechartedTruncatedFourier_coe positive e,
    Lp.coeFn_smul (2 * r : ℂ) (c r), burnolRadiusBoundaryCosineState_coe r]
      with x addRead scalar derivativeRead valueRead rhs cosineRead
  rw [addRead, Pi.add_apply, scalar, rhs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [derivativeRead, valueRead, cosineRead]
  exact constant_raw_ward r x

/-- The full source flow is the existing fixed-window dilation of the Fourier constant. -/
def fullSource (r : ℝ) (positive : 0 < r) (t : ℝ) : H :=
  (Real.exp (-t / 2) : ℂ) • burnolFixedWindowDilationFourier positive positive t
    ((Real.sqrt r : ℂ) • e)

theorem fullSource_chart (r : ℝ) (positive : 0 < r) (t : ℝ) :
    fullSource r positive t =
      (Real.sqrt r : ℂ) • ((Real.exp (-t/2) : ℂ) •
        T (r * Real.exp (t/2)) e) := by
  unfold fullSource
  rw [burnolFixedWindowDilationFourier_eq_radius]
  have sqrtSquare : Real.sqrt (r*r) = r := by
    rw [← sq, Real.sqrt_sq positive.le]
  simp only [sqrtSquare, map_smul, smul_smul]
  rw [burnolRechartedTruncatedFourierOperator_of_pos (mul_pos positive (Real.exp_pos _))]
  congr 1
  ring

theorem fullSource_hasDerivAt (r : ℝ) (positive : 0 < r) :
    HasDerivAt (fullSource r positive)
      ((Real.sqrt r : ℂ) •
        ((r/2 : ℂ) • burnolRadiusRechartedTruncatedFourierDerivative positive e -
          (1/2 : ℂ) • T r e)) 0 := by
  have radiusDerivative : HasDerivAt (fun t : ℝ => r * Real.exp (t/2)) (r/2) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).div_const 2).exp.const_mul r) using 1
    first | rfl | (norm_num; ring)
  have operatorDerivative := (burnolRechartedTruncatedFourierOperator_hasDerivAt positive).scomp_of_eq
    0 radiusDerivative (by norm_num)
  let evaluation := (ContinuousLinearMap.apply ℂ H e).restrictScalars ℝ
  have valueDerivative : HasDerivAt (fun t => T (r * Real.exp (t/2)) e)
      ((r/2 : ℝ) • burnolRadiusRechartedTruncatedFourierDerivative positive e) 0 :=
    evaluation.hasFDerivAt.comp_hasDerivAt 0 operatorDerivative
  have scalarDerivative : HasDerivAt (fun t : ℝ => (Real.exp (-t/2) : ℂ)) (-1/2 : ℂ) 0 := by
    have realDerivative : HasDerivAt (fun t : ℝ => Real.exp (-t/2)) (-1/2) 0 := by
      convert! (((hasDerivAt_id (0 : ℝ)).neg.div_const 2).exp) using 1
      first | rfl | norm_num
    simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
      using realDerivative.ofReal_comp
  have productDerivative := (scalarDerivative.smul valueDerivative).const_smul (Real.sqrt r : ℂ)
  have source := productDerivative.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t => (fullSource_chart r positive t)))
  apply source.congr_deriv
  simp only [Real.exp_zero, neg_zero, zero_div, mul_one,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  module

/-- The centered velocity retains the constant source and the actual chart clock. -/
theorem centeredSource_hasDerivAt (r : ℝ) (positive : 0 < r) :
    HasDerivAt (fun t => Q (fullSource r positive t))
      ((Real.sqrt r : ℂ) • Q
        ((r/2 : ℂ) • burnolRadiusRechartedTruncatedFourierDerivative positive e -
          (1/2 : ℂ) • T r e)) 0 := by
  have generated := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (fullSource_hasDerivAt r positive)
  change HasDerivAt (fun t => Q (fullSource r positive t)) (Q _) 0 at generated
  simpa only [map_smul] using generated

private theorem quarter_phase_pair_chart :
    quarterChart (OriginalRieszSource.Constructor.compact
        (OriginalRieszSource.Constructor.phase q) (OriginalRieszSource.Constructor.phaseContinuous q) +
      OriginalRieszSource.Constructor.compact
        (OriginalRieszSource.Constructor.phase (-q)) (OriginalRieszSource.Constructor.phaseContinuous (-q))) =
        (1/2 : ℂ) • c q := by
  let plus := OriginalRieszSource.Constructor.compact
    (OriginalRieszSource.Constructor.phase q) (OriginalRieszSource.Constructor.phaseContinuous q)
  let minus := OriginalRieszSource.Constructor.compact
    (OriginalRieszSource.Constructor.phase (-q)) (OriginalRieszSource.Constructor.phaseContinuous (-q))
  let transport := (burnolRadiusScaleEquiv_measurePreserving
    (by norm_num : (0 : ℝ) < q)).quasiMeasurePreserving
  apply Lp.ext
  filter_upwards [burnolRadiusRechart_coe (by norm_num : (0 : ℝ) < q) (plus+minus),
    transport.ae_eq (Measure.ae_smul_measure (Lp.coeFn_add plus minus) (ENNReal.ofReal q⁻¹)),
    transport.ae_eq (Measure.ae_smul_measure
      (OriginalRieszSource.Constructor.compact_read _ (OriginalRieszSource.Constructor.phaseContinuous q))
        (ENNReal.ofReal q⁻¹)),
    transport.ae_eq (Measure.ae_smul_measure
      (OriginalRieszSource.Constructor.compact_read _ (OriginalRieszSource.Constructor.phaseContinuous (-q)))
        (ENNReal.ofReal q⁻¹)),
    Lp.coeFn_smul (1/2 : ℂ) (c q), burnolRadiusBoundaryCosineState_coe q]
    with x chart addRead plusRead minusRead scalar cosineRead
  change (burnolRadiusRechart _ (plus+minus) : ℝ → ℂ) x = _
  change (plus+minus : BurnolQuarterIntervalL2) (q*x) = plus (q*x)+minus (q*x) at addRead
  change plus (q*x) = OriginalRieszSource.Constructor.phase q (q*x) at plusRead
  change minus (q*x) = OriginalRieszSource.Constructor.phase (-q) (q*x) at minusRead
  rw [chart, addRead, plusRead, minusRead, scalar]
  simp only [Pi.smul_apply, smul_eq_mul, cosineRead]
  have phasePair : OriginalRieszSource.Constructor.phase q (q*x) +
      OriginalRieszSource.Constructor.phase (-q) (q*x) = burnolRadiusBoundaryCosineRaw q x := by
    unfold OriginalRieszSource.Constructor.phase
    simp only [Real.fourierChar_apply]
    convert endpoint_pair q x using 1
    congr 1 <;> push_cast <;> ring
  rw [phasePair]
  have sqrtQuarter : Real.sqrt q = 1/2 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [sqrtQuarter]
  norm_num

private theorem quarter_fourier_constant_chart :
    quarterChart (burnolTruncatedFourier (intervalConstant q)) =
      (1/2 : ℂ) • T q e := by
  have transformed : T q (quarterChart (intervalConstant q)) =
      quarterChart (burnolTruncatedFourier (intervalConstant q)) := by
    rw [burnolRechartedTruncatedFourierOperator_of_pos (by norm_num : (0 : ℝ) < q)]
    unfold burnolRadiusRechartedTruncatedFourier
    simp only [ContinuousLinearMap.comp_apply]
    change quarterChart (burnolTruncatedFourier
      (quarterChart.symm (quarterChart (intervalConstant q)))) = _
    rw [quarterChart.symm_apply_apply]
  rw [quarter_constant_chart, map_smul] at transformed
  exact transformed.symm

/-- The generated Euler velocity is the literal original endpoint source, including its mean term. -/
theorem original_eta_velocity :
    quarterChart (OriginalRieszSource.Response.eta : BurnolQuarterIntervalL2) =
      (Real.sqrt q : ℂ) • Q
        ((q/2 : ℂ) • burnolRadiusRechartedTruncatedFourierDerivative (by norm_num : (0 : ℝ) < q) e -
          (1/2 : ℂ) • T q e) := by
  let plus := OriginalRieszSource.Constructor.compact
    (OriginalRieszSource.Constructor.phase q) (OriginalRieszSource.Constructor.phaseContinuous q)
  let minus := OriginalRieszSource.Constructor.compact
    (OriginalRieszSource.Constructor.phase (-q)) (OriginalRieszSource.Constructor.phaseContinuous (-q))
  have ambient : (OriginalRieszSource.Response.eta : BurnolQuarterIntervalL2) =
      burnolQuarterMeanZeroProjection ((q : ℂ) • (plus+minus) - burnolTruncatedFourier (intervalConstant q)) := by
    change burnolQuarterMeanZeroProjection ((q : ℂ) • plus - (1/2 : ℂ) • _) +
      burnolQuarterMeanZeroProjection ((q : ℂ) • minus - (1/2 : ℂ) • _) = _
    rw [← map_add]
    congr 1
    module
  rw [ambient, quarter_projection_chart, map_sub, map_smul, quarter_phase_pair_chart,
    quarter_fourier_constant_chart]
  have source := constant_column_ward q (by norm_num : (0 : ℝ) < q)
  have velocity : (q/2 : ℂ) • burnolRadiusRechartedTruncatedFourierDerivative
      (by norm_num : (0 : ℝ) < q) e - (1/2 : ℂ) • T q e = (q : ℂ) • c q - T q e := by
    calc
      _ = (1/2 : ℂ) • ((q : ℂ) • burnolRadiusRechartedTruncatedFourierDerivative
          (by norm_num : (0 : ℝ) < q) e + T q e) - T q e := by push_cast; module
      _ = _ := by rw [source]; push_cast; module
  rw [velocity, map_sub, map_smul, map_sub, map_smul]
  have sqrtQuarter : Real.sqrt q = 1/2 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [sqrtQuarter]
  norm_num
  module

theorem original_eta_hasDerivAt :
    HasDerivAt (fun t => Q (fullSource q (by norm_num : (0 : ℝ) < q) t))
      (quarterChart (OriginalRieszSource.Response.eta : BurnolQuarterIntervalL2)) 0 := by
  rw [original_eta_velocity]
  exact centeredSource_hasDerivAt q (by norm_num : (0 : ℝ) < q)

/-- The unprojected quarter source is retained so that its removed mean has an actual velocity. -/
def originalSource (t : ℝ) : BurnolQuarterIntervalL2 :=
  quarterChart.symm (fullSource q (by norm_num : (0 : ℝ) < q) t)

theorem originalSource_actual (t : ℝ) :
    originalSource t = (Real.exp (-t/2) : ℂ) • burnolQuarterRestriction
      (burnolMultiplicativeDilation t
        (fourierL2 (burnolQuarterZeroExtension (intervalConstant q)))) := by
  have inputActual : burnolUnitWindowEmbedding (by norm_num : (0 : ℝ) < q)
      ((Real.sqrt q : ℂ) • e) = burnolQuarterZeroExtension (intervalConstant q) := by
    have sqrtQuarter : Real.sqrt q = 1/2 :=
      (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
    unfold burnolUnitWindowEmbedding
    simp only [ContinuousLinearMap.comp_apply]
    change burnolQuarterZeroExtension (quarterChart.symm ((Real.sqrt q : ℂ) • e)) = _
    rw [sqrtQuarter]
    push_cast
    rw [← quarter_constant_chart, quarterChart.symm_apply_apply]
  change quarterChart.symm ((Real.exp (-t/2) : ℂ) • quarterChart
    (burnolQuarterRestriction (burnolMultiplicativeDilation t
      (fourierL2 (burnolUnitWindowEmbedding (by norm_num : (0 : ℝ) < q)
        ((Real.sqrt q : ℂ) • e)))))) = _
  rw [map_smul, quarterChart.symm_apply_apply, inputActual]

def originalVelocity : BurnolQuarterIntervalL2 :=
  quarterChart.symm ((Real.sqrt q : ℂ) •
    ((q/2 : ℂ) • burnolRadiusRechartedTruncatedFourierDerivative
      (by norm_num : (0 : ℝ) < q) e - (1/2 : ℂ) • T q e))

theorem originalSource_hasDerivAt : HasDerivAt originalSource originalVelocity 0 := by
  exact (quarterChart.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 (fullSource_hasDerivAt q (by norm_num : (0 : ℝ) < q))

theorem originalVelocity_centered : OriginalRieszSource.Constructor.zeroMean originalVelocity =
    OriginalRieszSource.Response.eta := by
  apply Subtype.ext
  apply quarterChart.injective
  change quarterChart (burnolQuarterMeanZeroProjection originalVelocity) = _
  rw [quarter_projection_chart, originalVelocity, quarterChart.apply_symm_apply, map_smul,
    original_eta_velocity]

theorem original_mean_hasDerivAt :
    HasDerivAt (fun t => burnolQuarterMeanCoefficient (originalSource t))
      (burnolQuarterMeanCoefficient originalVelocity) 0 := by
  have generated := ((innerSL ℂ (intervalConstant q)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 originalSource_hasDerivAt
  exact generated.div_const (((‖intervalConstant q‖ ^ 2 : ℝ) : ℂ))

theorem original_centered_hasDerivAt :
    HasDerivAt (fun t => OriginalRieszSource.Constructor.zeroMean (originalSource t))
      OriginalRieszSource.Response.eta 0 := by
  have generated := (OriginalRieszSource.Constructor.zeroMean.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 originalSource_hasDerivAt
  change HasDerivAt _ (OriginalRieszSource.Constructor.zeroMean originalVelocity) 0 at generated
  rw [originalVelocity_centered] at generated
  exact generated

theorem original_u_hasDerivAt :
    HasDerivAt (fun t => burnolMeanZeroBlockInverse
      (OriginalRieszSource.Constructor.zeroMean (originalSource t))) OriginalRieszSource.Response.u 0 := by
  exact (burnolMeanZeroBlockInverse.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 original_centered_hasDerivAt

theorem original_v_hasDerivAt :
    HasDerivAt (fun t => burnolMeanZeroTruncatedFourier (burnolMeanZeroBlockInverse
      (OriginalRieszSource.Constructor.zeroMean (originalSource t)))) OriginalRieszSource.Response.v 0 := by
  exact (burnolMeanZeroTruncatedFourier.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 original_u_hasDerivAt

end ConstantFourierEulerVelocity
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
