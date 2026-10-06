import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalGradedGaugeReturn
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.LaplaceMoments

/-! Positive-damping current response is integrated in each original finite
Gauss occurrence before the same family lift. The uniform source bound pays
both the frequency reader and its time-cutoff error without a completed-space
time-measurability premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.CanonicalGradedFrequency
open SourceFiniteUnitary CanonicalGradedVariation
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace Interval
open SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response

section Finite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem continuous_time (C : E →L[ℂ] E) : Continuous (time C) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)

private theorem time_bound (C : E →L[ℂ] E) (hc : IsSelfAdjoint C) (t : ℝ) :
    ‖time C t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [time_norm C hc, one_mul]

theorem variation_prefix (C B : E →L[ℂ] E) (t : ℝ) :
    variation C B t = FullYSourceCutoffVolterra.finitePrefix C B 1 t := by
  let f := FullYSourceCutoffVolterra.interaction C B
  have hf := (FullYSourceCutoffVolterra.interaction_continuous C B).intervalIntegrable
    (μ := volume) 0 t
  let R := (ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip (time C t)
  have h := R.intervalIntegral_comp_comm hf
  change (∫ s in (0 : ℝ)..t, f s * time C t) =
    (∫ s in (0 : ℝ)..t, f s) * time C t at h
  change variation C B t = _
  rw [variation, variationBetween]
  simp only [zero_smul, add_zero]
  calc
    _ = ∫ s in (0 : ℝ)..t, f s * time C t := by
      apply intervalIntegral.integral_congr
      intro s _
      simp only [f, FullYSourceCutoffVolterra.interaction, mul_assoc]
      rw [← time_add]
      rw [show -s+t=t-s by ring]
    _ = _ := by
      rw [h]
      simp only [FullYSourceCutoffVolterra.finitePrefix,
        FullYSourceCutoffVolterra.orderedIntegral, one_mul, f]

theorem variation_continuous (C B : E →L[ℂ] E) : Continuous (variation C B) := by
  change Continuous (fun t => variation C B t)
  simp_rw [variation_prefix]
  exact (FullYSourceCutoffVolterra.orderedIntegral_continuous C B 1).mul (continuous_time C)

def finiteDerivative (C A B : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  variation C B (-t) * A * time C t + time C (-t) * A * variation C B t

theorem finite_current_derivative (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (hb : IsSelfAdjoint B) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => time (C+parameter • B) (-t) * A *
      time (C+parameter • B) t) (finiteDerivative C A B t) 0 := by
  have h := ((parameter_derivative C B hc hb (-t)).mul_const A).mul
    (parameter_derivative C B hc hb t)
  simp only [zero_smul, add_zero] at h
  convert h using 1 <;> rfl

theorem finite_projected_derivative (C A B P : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (hb : IsSelfAdjoint B) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => P*time (C+parameter • B) (-t)*A*time (C+parameter • B) t)
      (P*finiteDerivative C A B t) 0 := by
  have h := (finite_current_derivative C A B hc hb t).const_mul P
  convert h using 1 <;> rfl

theorem finiteDerivative_continuous (C A B : E →L[ℂ] E) : Continuous (finiteDerivative C A B) :=
  (((variation_continuous C B).comp continuous_neg).mul continuous_const |>.mul (continuous_time C)).add
    ((((continuous_time C).comp continuous_neg).mul continuous_const).mul (variation_continuous C B))

theorem finiteDerivative_bound (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C) (t : ℝ) :
    ‖finiteDerivative C A B t‖ ≤ 2*‖A‖*‖B‖*|t| := by
  have left : ‖variation C B (-t) * A * time C t‖ ≤ (|t| * ‖B‖)*‖A‖ := by
    calc
      _ ≤ (‖variation C B (-t)‖*‖A‖)*‖time C t‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ((|t| * ‖B‖)*‖A‖)*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right
          (by simpa only [abs_neg] using variation_bound C B hc (-t)) (norm_nonneg _))
          (time_bound C hc t) (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have right : ‖time C (-t) * A * variation C B t‖ ≤ ‖A‖*(|t| * ‖B‖) := by
    calc
      _ ≤ (‖time C (-t)‖*‖A‖)*‖variation C B t‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖A‖)*(|t| * ‖B‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (time_bound C hc (-t)) (norm_nonneg _))
          (variation_bound C B hc t) (norm_nonneg _) (by positivity)
      _ = _ := by rw [one_mul]
  exact (norm_add_le _ _).trans ((add_le_add left right).trans_eq (by ring))

def weight (frequency damping t : ℝ) : ℂ :=
  Complex.exp (((-damping : ℝ) : ℂ)*t+Complex.I*((frequency*t : ℝ) : ℂ))

theorem weight_norm (frequency damping t : ℝ) : ‖weight frequency damping t‖ = Real.exp (-damping*t) := by
  simp [weight, Complex.norm_exp]

theorem weight_continuous (frequency damping : ℝ) : Continuous (weight frequency damping) := by
  unfold weight
  fun_prop

def envelope (damping t : ℝ) : ℝ := Real.exp (-damping*t)*t
def tail (damping cutoff : ℝ) : ℝ :=
  Real.exp (-damping*cutoff)*(cutoff/damping+1/damping^2)

theorem envelope_integrable (damping : ℝ) (positive : 0<damping) :
    IntegrableOn (envelope damping) (Ioi 0) := by
  change IntegrableOn (fun t : ℝ => Real.exp (-damping*t)*t) (Ioi 0)
  simpa only [pow_one] using damping_moment_integrable 1 damping positive

theorem envelope_integral (damping : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Ioi 0, envelope damping t) = 1/damping^2 := by
  simpa [envelope, inv_pow] using damping_moment_integral 1 damping positive

theorem tail_integral (damping cutoff : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Ioi cutoff, envelope damping t) = tail damping cutoff := by
  have shift := integral_add_right_eq_self (μ := volume)
    ((Ioi cutoff).indicator (envelope damping)) cutoff
  rw [integral_indicator measurableSet_Ioi] at shift
  have identity : (fun t => (Ioi cutoff).indicator (envelope damping) (t+cutoff)) =
      (Ioi 0).indicator (fun t => envelope damping (t+cutoff)) := by
    funext t
    simp only [indicator_apply, mem_Ioi, lt_add_iff_pos_left]
  rw [identity, integral_indicator measurableSet_Ioi] at shift
  rw [← shift]
  have polynomial (t : ℝ) : envelope damping (t+cutoff) =
      Real.exp (-damping*cutoff)*(Real.exp (-damping*t)*t^1+
        Real.exp (-damping*t)*t^0*cutoff) := by
    unfold envelope
    rw [show -damping*(t+cutoff)=-damping*cutoff+(-damping*t) by ring, Real.exp_add]
    ring
  simp_rw [polynomial]
  rw [integral_const_mul, integral_add (damping_moment_integrable 1 damping positive)
    ((damping_moment_integrable 0 damping positive).mul_const cutoff), integral_mul_const,
    damping_moment_integral 1 damping positive, damping_moment_integral 0 damping positive]
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, Nat.factorial_zero, zero_add,
    pow_one, tail, div_eq_mul_inv, inv_pow]
  ring

theorem tail_nonnegative (damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) :
    0≤tail damping cutoff := by
  unfold tail
  positivity

theorem tail_tendsto_zero (damping : ℝ) (positive : 0<damping) :
    Tendsto (tail damping) atTop (𝓝 0) := by
  have h := tendsto_integral_Ioi_zero (f := envelope damping) (μ := volume)
    (b := fun cutoff : ℝ => cutoff) tendsto_id
  simpa only [tail_integral damping _ positive] using h

def integrand (C A B : E →L[ℂ] E) (frequency damping t : ℝ) : E →L[ℂ] E :=
  weight frequency damping t • finiteDerivative C A B t

theorem integrand_continuous (C A B : E →L[ℂ] E) (frequency damping : ℝ) :
    Continuous (integrand C A B frequency damping) :=
  (weight_continuous frequency damping).smul (finiteDerivative_continuous C A B)

theorem integrand_bound (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (frequency damping t : ℝ) (future : 0≤t) :
    ‖integrand C A B frequency damping t‖ ≤ envelope damping t*(2*‖A‖*‖B‖) := by
  rw [integrand, norm_smul, weight_norm]
  exact (mul_le_mul_of_nonneg_left (finiteDerivative_bound C A B hc t) (Real.exp_pos _).le).trans_eq
    (by rw [abs_of_nonneg future]; unfold envelope; ring)

theorem integrand_integrable (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (frequency damping : ℝ) (positive : 0<damping) :
    IntegrableOn (integrand C A B frequency damping) (Ioi 0) := by
  apply ((envelope_integrable damping positive).mul_const (2*‖A‖*‖B‖)).mono'
    (integrand_continuous C A B frequency damping).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact integrand_bound C A B hc frequency damping t ht.le

def finiteResponse (C A B : E →L[ℂ] E) (frequency damping : ℝ) : E →L[ℂ] E :=
  ∫ t : ℝ in Ioi 0, integrand C A B frequency damping t

theorem finiteResponse_bound (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (frequency damping : ℝ) (positive : 0<damping) :
    ‖finiteResponse C A B frequency damping‖ ≤ 2*‖A‖*‖B‖/damping^2 := by
  have h := norm_integral_le_of_norm_le
    ((envelope_integrable damping positive).mul_const (2*‖A‖*‖B‖))
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => integrand_bound C A B hc frequency damping t ht.le))
  rw [integral_mul_const, envelope_integral damping positive] at h
  exact h.trans_eq (by ring)

def finiteTruncation (C A B : E →L[ℂ] E) (frequency damping cutoff : ℝ) : E →L[ℂ] E :=
  ∫ t in (0 : ℝ)..cutoff, integrand C A B frequency damping t

theorem finite_truncation_tail (C A B : E →L[ℂ] E) (hc : IsSelfAdjoint C)
    (frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) :
    ‖finiteResponse C A B frequency damping-finiteTruncation C A B frequency damping cutoff‖ ≤
      tail damping cutoff*(2*‖A‖*‖B‖) := by
  have hi := integrand_integrable C A B hc frequency damping positive
  have ht := hi.mono_set (Ioi_subset_Ioi future)
  have split := intervalIntegral.integral_interval_add_Ioi hi ht
  change ‖(∫ t in Ioi 0, integrand C A B frequency damping t)-
    (∫ t in (0 : ℝ)..cutoff, integrand C A B frequency damping t)‖ ≤ _
  rw [← split, add_sub_cancel_left]
  have bound := norm_integral_le_of_norm_le
    (((envelope_integrable damping positive).mono_set (Ioi_subset_Ioi future)).mul_const (2*‖A‖*‖B‖))
    (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => integrand_bound C A B hc frequency damping t (future.trans ht.le)))
  rw [integral_mul_const, tail_integral damping cutoff positive] at bound
  exact bound

end Finite

private theorem lift_sum_of_triples {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) (A B C D F G : SourceFamilyOperator.Operator I E) :
    SourceFamilyOperator.lift u (SourceFamilyOperator.add
      (SourceFamilyOperator.comp (SourceFamilyOperator.comp A B) C)
      (SourceFamilyOperator.comp (SourceFamilyOperator.comp D F) G)) =
      SourceFamilyOperator.lift u A * SourceFamilyOperator.lift u B * SourceFamilyOperator.lift u C +
        SourceFamilyOperator.lift u D * SourceFamilyOperator.lift u F * SourceFamilyOperator.lift u G := by
  rw [SourceFamilyOperator.lift_add, SourceFamilyOperator.lift_comp, SourceFamilyOperator.lift_comp,
    SourceFamilyOperator.lift_comp, SourceFamilyOperator.lift_comp]
  rfl

open GaussCoreHilbert CanonicalGradedCurrent CanonicalGradedGaugeVariation
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceFamilyOperator
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

def derivativeFamily (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (t : ℝ) : Operator Index H where
  component F := finiteDerivative (GaussGradedCompression.compression F)
    (gaugeReader z mu a) (gaugeReader z nu b) t
  bounded := ⟨2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖*|t|, by positivity, fun F x =>
    ((finiteDerivative _ _ _ t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right
        (finiteDerivative_bound _ _ _ (GaussGradedCompression.compression_selfAdjoint F) t) (norm_nonneg x))⟩

theorem derivativeFamily_return (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (t : ℝ) :
    lift sourceFilter (derivativeFamily z mu nu a b t) = currentDerivative z mu nu a b t := by
  let V := variationFamily GaussGradedCompression.compression
    GaussGradedCompression.compression_selfAdjoint (gaugeReader z nu b)
  let U := GaussGradedUnitary.finiteTime
  let A := constant (gaugeReader z mu a) (I := Index)
  have h := lift_congr sourceFilter (derivativeFamily z mu nu a b t)
    (SourceFamilyOperator.add (comp (comp (V (-t)) A) (U t))
      (comp (comp (U (-t)) A) (V t))) (fun _ => rfl)
  exact h.trans (lift_sum_of_triples sourceFilter (V (-t)) A (U t) (U (-t)) A (V t))

def responseFamily (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := finiteResponse (GaussGradedCompression.compression F)
    (gaugeReader z mu a) (gaugeReader z nu b) frequency damping
  bounded := ⟨2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖/damping^2, by positivity, fun F x =>
    ((finiteResponse _ _ _ frequency damping).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right
        (finiteResponse_bound _ _ _ (GaussGradedCompression.compression_selfAdjoint F) frequency damping positive)
        (norm_nonneg x))⟩

def response (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (responseFamily z mu nu a b frequency damping positive)

theorem response_bound (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (frequency damping : ℝ) (positive : 0<damping) :
    ‖response z mu nu a b frequency damping positive‖ ≤
      2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖/damping^2 :=
  lift_bound sourceFilter _ _ (by positivity) (fun F =>
    finiteResponse_bound _ _ _ (GaussGradedCompression.compression_selfAdjoint F) frequency damping positive)

def tailFamily (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) : Operator Index H where
  component F := finiteResponse (GaussGradedCompression.compression F)
    (gaugeReader z mu a) (gaugeReader z nu b) frequency damping -
      finiteTruncation (GaussGradedCompression.compression F)
        (gaugeReader z mu a) (gaugeReader z nu b) frequency damping cutoff
  bounded := ⟨tail damping cutoff*(2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖),
    mul_nonneg (tail_nonnegative damping cutoff positive future) (by positivity), fun F x =>
      ((finiteResponse (GaussGradedCompression.compression F) (gaugeReader z mu a) (gaugeReader z nu b)
          frequency damping-finiteTruncation (GaussGradedCompression.compression F)
          (gaugeReader z mu a) (gaugeReader z nu b) frequency damping cutoff).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right
          (finite_truncation_tail _ _ _ (GaussGradedCompression.compression_selfAdjoint F)
            frequency damping cutoff positive future) (norm_nonneg x))⟩

def truncationFamily (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) : Operator Index H where
  component F := finiteTruncation (GaussGradedCompression.compression F)
    (gaugeReader z mu a) (gaugeReader z nu b) frequency damping cutoff
  bounded := ⟨2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖/damping^2 +
    tail damping cutoff*(2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖),
    add_nonneg (by positivity) (mul_nonneg (tail_nonnegative damping cutoff positive future) (by positivity)),
    fun F x => by
      let C := GaussGradedCompression.compression F
      let A := gaugeReader z mu a
      let B := gaugeReader z nu b
      have norm_bound : ‖finiteTruncation C A B frequency damping cutoff‖ ≤
          2*‖A‖*‖B‖/damping^2+tail damping cutoff*(2*‖A‖*‖B‖) := by
        have identity : finiteTruncation C A B frequency damping cutoff =
            finiteResponse C A B frequency damping -
              (finiteResponse C A B frequency damping-finiteTruncation C A B frequency damping cutoff) := by abel
        calc
          _ ≤ ‖finiteResponse C A B frequency damping‖+
              ‖finiteResponse C A B frequency damping-finiteTruncation C A B frequency damping cutoff‖ := by
            conv_lhs => rw [identity]
            exact norm_sub_le _ _
          _ ≤ _ := add_le_add
            (finiteResponse_bound C A B (GaussGradedCompression.compression_selfAdjoint F) frequency damping positive)
            (finite_truncation_tail C A B (GaussGradedCompression.compression_selfAdjoint F)
              frequency damping cutoff positive future)
      exact ((finiteTruncation C A B frequency damping cutoff).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right norm_bound (norm_nonneg x))⟩

def truncation (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (truncationFamily z mu nu a b frequency damping cutoff positive future)

theorem tailFamily_return (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) :
    lift sourceFilter (tailFamily z mu nu a b frequency damping cutoff positive future) =
      response z mu nu a b frequency damping positive-
        truncation z mu nu a b frequency damping cutoff positive future := by
  apply SourceFamilyOperator.ext sourceFilter
  intro f
  rw [sub_apply, response, truncation, lift_coe, lift_coe, lift_coe,
    ← UniformSpace.Completion.coe_sub]
  congr 1

theorem response_truncation_tail (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (frequency damping cutoff : ℝ) (positive : 0<damping) (future : 0≤cutoff) :
    ‖response z mu nu a b frequency damping positive-
      truncation z mu nu a b frequency damping cutoff positive future‖ ≤
        tail damping cutoff*(2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖) := by
  rw [← tailFamily_return]
  exact lift_bound sourceFilter _ _
    (mul_nonneg (tail_nonnegative damping cutoff positive future) (by positivity)) (fun F =>
      finite_truncation_tail _ _ _ (GaussGradedCompression.compression_selfAdjoint F)
        frequency damping cutoff positive future)

theorem truncation_tendsto (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (frequency damping : ℝ) (positive : 0<damping) :
    Tendsto (fun n : ℕ => truncation z mu nu a b frequency damping n positive (Nat.cast_nonneg n))
      atTop (𝓝 (response z mu nu a b frequency damping positive)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun n : ℕ => tail damping (n : ℝ)) atTop (𝓝 0) :=
    (tail_tendsto_zero damping positive).comp tendsto_natCast_atTop_atTop
  have bound_limit := ht.mul_const (2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖)
  rw [zero_mul] at bound_limit
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) bound_limit
  rw [norm_sub_rev]
  exact response_truncation_tail z mu nu a b frequency damping n positive (Nat.cast_nonneg n)

theorem response_source_readback (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (frequency damping : ℝ) (positive : 0<damping) (x y : H) :
    Tendsto (fun F : Index => inner ℂ x
      (finiteResponse (GaussGradedCompression.compression F) (gaugeReader z mu a)
        (gaugeReader z nu b) frequency damping y)) sourceFilter
      (𝓝 (inner ℂ (inclusion x) (response z mu nu a b frequency damping positive (inclusion y)))) := by
  change Tendsto _ _ (𝓝 (inner ℂ
    ((SourceFamilyHilbert.constant sourceFilter x) : HistorySpace)
    (lift sourceFilter (responseFamily z mu nu a b frequency damping positive)
      ((SourceFamilyHilbert.constant sourceFilter y) : HistorySpace))))
  rw [lift_coe, SourceFamilyHilbert.inner_coe]
  exact SourceFamilyHilbert.pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter x)
    (act sourceFilter (responseFamily z mu nu a b frequency damping positive)
      (SourceFamilyHilbert.constant sourceFilter y))

def fullFiniteDerivative (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (t : ℝ) (F : Index) : H →L[ℂ] H :=
  deriv (fun parameter : ℝ =>
    CanonicalGradedGaugeReturn.finiteCurrent z mu nu a b cut parameter t F) 0

theorem fullFiniteDerivative_return (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (t : ℝ) (F : Index) :
    fullFiniteDerivative z mu nu a b cut t F = sourceProjection *
      finiteDerivative (GaussGradedCompression.compression F) (gaugeReader z mu a) (gaugeReader z nu b) t := by
  have h := finite_projected_derivative (GaussGradedCompression.compression F)
    (gaugeReader z mu a) (gaugeReader z nu b) sourceProjection
    (GaussGradedCompression.compression_selfAdjoint F) (gaugeReader_selfAdjoint z nu b) t
  exact (h.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun parameter => CanonicalGradedGaugeReturn.finiteCurrent_return z mu nu a b cut parameter t F))).deriv

/-- The derivative is taken on the literal two-leg `C_F + ε J_B + Y_cut`
current before its finite-frequency integral. The source coupling here is +J. -/
def fullFiniteResponse (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (frequency damping : ℝ) (F : Index) : H →L[ℂ] H :=
  ∫ t : ℝ in Ioi 0, weight frequency damping t • fullFiniteDerivative z mu nu a b cut t F

theorem fullFiniteResponse_return (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (frequency damping : ℝ) (positive : 0<damping) (F : Index) :
    fullFiniteResponse z mu nu a b cut frequency damping F = sourceProjection *
      finiteResponse (GaussGradedCompression.compression F) (gaugeReader z mu a) (gaugeReader z nu b)
        frequency damping := by
  let L := ContinuousLinearMap.mul ℂ (H →L[ℂ] H) sourceProjection
  have h := L.integral_comp_comm (integrand_integrable (GaussGradedCompression.compression F)
    (gaugeReader z mu a) (gaugeReader z nu b) (GaussGradedCompression.compression_selfAdjoint F)
    frequency damping positive)
  change (∫ t : ℝ in Ioi 0, sourceProjection *
    integrand (GaussGradedCompression.compression F) (gaugeReader z mu a) (gaugeReader z nu b)
      frequency damping t) = sourceProjection * finiteResponse (GaussGradedCompression.compression F)
        (gaugeReader z mu a) (gaugeReader z nu b) frequency damping at h
  rw [fullFiniteResponse]
  simp_rw [fullFiniteDerivative_return]
  simp only [integrand, mul_smul_comm] at h
  exact h

def fullResponseFamily (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F := fullFiniteResponse z mu nu a b cut frequency damping F
  bounded := ⟨2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖/damping^2, by positivity, fun F x => by
    rw [fullFiniteResponse_return z mu nu a b cut frequency damping positive F]
    change ‖sourceProjection (finiteResponse (GaussGradedCompression.compression F)
      (gaugeReader z mu a) (gaugeReader z nu b) frequency damping x)‖ ≤ _
    exact (NativeHistoryGrade.piece_bound sourceLabel _).trans
      (((finiteResponse _ _ _ frequency damping).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right
          (finiteResponse_bound _ _ _ (GaussGradedCompression.compression_selfAdjoint F)
            frequency damping positive) (norm_nonneg x)))⟩

def fullResponse (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullResponseFamily z mu nu a b cut frequency damping positive)

theorem fullResponse_return (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (frequency damping : ℝ) (positive : 0<damping) :
    fullResponse z mu nu a b cut frequency damping positive =
      historyProjection * response z mu nu a b frequency damping positive :=
  (lift_congr sourceFilter _
    (comp (constant sourceProjection) (responseFamily z mu nu a b frequency damping positive))
    (fun F => fullFiniteResponse_return z mu nu a b cut frequency damping positive F)).trans
      (lift_comp sourceFilter _ _)

theorem fullResponse_cutoff_independent (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (cut other : ℕ) (frequency damping : ℝ) (positive : 0<damping) :
    fullResponse z mu nu a b cut frequency damping positive =
      fullResponse z mu nu a b other frequency damping positive := by
  rw [fullResponse_return, fullResponse_return]

theorem historyProjection_bound : ‖historyProjection‖ ≤ 1 := by
  apply lift_bound sourceFilter (constant sourceProjection) 1 zero_le_one
  intro F
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖sourceProjection x‖ ≤ 1*‖x‖
  rw [one_mul]
  exact NativeHistoryGrade.piece_bound sourceLabel x

theorem fullResponse_bound (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (cut : ℕ) (frequency damping : ℝ) (positive : 0<damping) :
    ‖fullResponse z mu nu a b cut frequency damping positive‖ ≤
      2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖/damping^2 := by
  rw [fullResponse_return]
  exact (norm_mul_le _ _).trans ((mul_le_mul historyProjection_bound
    (response_bound z mu nu a b frequency damping positive) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem fullResponse_truncation_tail (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (cut : ℕ) (frequency damping cutoff : ℝ)
    (positive : 0<damping) (future : 0≤cutoff) :
    ‖fullResponse z mu nu a b cut frequency damping positive - historyProjection *
      truncation z mu nu a b frequency damping cutoff positive future‖ ≤
        tail damping cutoff*(2*‖gaugeReader z mu a‖*‖gaugeReader z nu b‖) := by
  rw [fullResponse_return, ← mul_sub]
  exact (norm_mul_le _ _).trans ((mul_le_mul historyProjection_bound
    (response_truncation_tail z mu nu a b frequency damping cutoff positive future)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem fullResponse_source_readback (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (frequency damping : ℝ) (positive : 0<damping) (x y : H) :
    Tendsto (fun F : Index => inner ℂ x
      (fullFiniteResponse z mu nu a b cut frequency damping F (sourceProjection y))) sourceFilter
      (𝓝 (inner ℂ (inclusion x)
        (fullResponse z mu nu a b cut frequency damping positive (historyProjection (inclusion y))))) := by
  rw [historyProjection, GaussUnitaryHistory.reader_inclusion]
  change Tendsto _ _ (𝓝 (inner ℂ
    ((SourceFamilyHilbert.constant sourceFilter x) : HistorySpace)
    (lift sourceFilter (fullResponseFamily z mu nu a b cut frequency damping positive)
      ((SourceFamilyHilbert.constant sourceFilter (sourceProjection y)) : HistorySpace))))
  rw [lift_coe, SourceFamilyHilbert.inner_coe]
  exact SourceFamilyHilbert.pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter x)
    (act sourceFilter (fullResponseFamily z mu nu a b cut frequency damping positive)
      (SourceFamilyHilbert.constant sourceFilter (sourceProjection y)))

#print axioms finiteResponse_bound
#print axioms derivativeFamily_return
#print axioms response_truncation_tail
#print axioms response_source_readback
#print axioms truncation_tendsto
#print axioms fullFiniteDerivative_return
#print axioms fullResponse_return
#print axioms fullResponse_cutoff_independent
#print axioms fullResponse_truncation_tail
#print axioms fullResponse_source_readback

end LowEnergy.CanonicalGradedFrequency
