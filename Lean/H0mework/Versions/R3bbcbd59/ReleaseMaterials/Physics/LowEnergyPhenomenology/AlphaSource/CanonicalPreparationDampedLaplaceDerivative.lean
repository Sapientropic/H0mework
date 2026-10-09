import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationDampedWeightedTime
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationFieldTransferDerivative

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDampedFieldPerturbation
open SourceFiniteUnitary CanonicalGradedVariation PreparationVacuumFieldPerturbation
open PreparationVacuumFieldPerturbation.Blocks
open MeasureTheory Set Filter
open scoped Topology Interval
open GaussCoreHilbert CanonicalPhysicalSpatial CanonicalGradedSpatialSource CanonicalPhysicalLaplace
open FullYSourceCutoffVolterra GaussUnitaryHistory SourceFamilyOperator SourceFamilyHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily PreparationVacuumCausalFieldResponse
local instance : NormedAlgebra ℚ Op := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : SecondCountableTopologyEither ℝ Op := ⟨Or.inl inferInstance⟩
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem weight_sub_smul {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [SMulCommClass ℂ ℝ E] (w : ℂ) (r : ℝ) (a b d : E) :
    w • (a-b-r • d)=w • a-w • b-r • (w • d) := by
  rw [smul_sub,smul_sub,smul_comm w r]

theorem time_parameter_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (K B : E →L[ℂ] E) (t : ℝ) : time (K+(0:ℝ) • B) t=time K t := by
  rw [zero_smul,add_zero]

theorem weighted_time_remainder {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (K B : E →L[ℂ] E) (w : ℂ) (r t : ℝ) :
    w • (time (K+r • B) t-time K t-r • variation K B t)=
      w • time (K+r • B) t-w • time (K+(0:ℝ) • B) t-r • (w • variation K B t) := by
  rw [time_parameter_zero]
  exact weight_sub_smul _ _ _ _ _

theorem integral_sub_smul {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure X) (a b d : X→E) (r : ℝ) (ha : Integrable a mu) (hb : Integrable b mu) (hd : Integrable d mu) :
    (∫ x,(a x-b x-r • d x) ∂mu)=(∫ x,a x ∂mu)-(∫ x,b x ∂mu)-r • (∫ x,d x ∂mu) := by
  have hsub:=integral_sub (ha.sub hb) (Integrable.smul r hd)
  have hfirst:=integral_sub ha hb
  have hsmul : (∫ x,r • d x ∂mu)=r • (∫ x,d x ∂mu) := integral_smul r d
  convert! hsub.trans (congrArg₂ (fun x y : E=>x-y) hfirst hsmul) using 1

private theorem exponential_product (M eta t b : ℝ) :
    t^2*(M*Real.exp (2*eta*t))*b^2*(M*Real.exp (eta*t))^2=
      (M^3*b^2)*t^2*Real.exp (4*eta*t) := by
  rw [mul_pow,←Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  calc
    _ = M^3*b^2*t^2*(Real.exp (2*eta*t)*Real.exp (2*(eta*t))) := by ring
    _ = _ := by rw [←Real.exp_add];congr 1;congr 1;ring

theorem actual_half_damped_remainder (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (damping r t : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping) :
    ‖time (compression p F+cutoff cut+r • forceGauss f p phi) t-time (compression p F+cutoff cut) t-
      r • variation (compression p F+cutoff cut) (forceGauss f p phi) t‖ ≤
      (sourceEnvelope cut (damping/8)^3*‖forceGauss f p phi‖^2)*t^2*Real.exp ((damping/2)*|t|)*‖r‖^2 := by
  let eta:=damping/8
  let M:=sourceEnvelope cut eta
  have he : 0 < eta := by dsimp [eta];positivity
  have hM : 0 ≤ M := zero_le_one.trans (sourceEnvelope_one_le cut eta he)
  have base (s : ℝ) (hs : |s| ≤ |t|) : ‖time (compression p F+cutoff cut) s‖ ≤ M*Real.exp (eta*|t|) :=
    (original_exponential_envelope p F cut eta he s).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs he.le)) hM)
  have perturbed (s : ℝ) (hs : |s| ≤ |t|) :
      ‖time (compression p F+cutoff cut+r • forceGauss f p phi) s‖ ≤ M*Real.exp (2*eta*|t|) :=
    (original_perturbed_envelope p F cut (forceGauss f p phi) eta r s he small).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs (by positivity))) hM)
  have h:=parameter_remainder_window (compression p F+cutoff cut) (forceGauss f p phi) r |t|
    (M*Real.exp (eta*|t|)) (M*Real.exp (2*eta*|t|)) t
    (mul_nonneg hM (Real.exp_pos _).le) (mul_nonneg hM (Real.exp_pos _).le) le_rfl base perturbed
  apply h.trans_eq
  rw [exponential_product,sq_abs]
  have rate : 4*eta*|t|=(damping/2)*|t| := by dsimp [eta];ring
  rw [rate]

private theorem exp_decay_order (damping t a : ℝ) (_positive : 0 < damping) (future : 0 ≤ t)
    (ha : a ≤ damping/2) :
    Real.exp (-damping*t)*Real.exp (a*t) ≤ Real.exp (-(damping/2)*t) := by
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right ha future]

def laplaceMajorant (damping t : ℝ) : ℝ := dampedPolynomial (damping/2) 2 t

def laplaceMass (damping : ℝ) : ℝ := ∫ t in Ioi 0,laplaceMajorant damping t

theorem laplaceMajorant_integrable (damping : ℝ) (positive : 0 < damping) :
    IntegrableOn (laplaceMajorant damping) (Ioi 0) := dampedPolynomial_integrable (damping/2) (by positivity) 2

theorem laplaceMajorant_nonneg (damping t : ℝ) : 0 ≤ laplaceMajorant damping t :=
  mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

theorem laplaceMass_nonneg (damping : ℝ) : 0 ≤ laplaceMass damping :=
  integral_nonneg (fun t=>laplaceMajorant_nonneg damping t)

def timeLaplaceIntegrand (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r t : ℝ) : Op :=
  CanonicalGradedFrequency.weight frequency damping t • time (compression p F+cutoff cut+r • forceGauss f p phi) t

def derivativeLaplaceIntegrand (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping t : ℝ) : Op :=
  CanonicalGradedFrequency.weight frequency damping t • variation (compression p F+cutoff cut) (forceGauss f p phi) t

def remainderLaplaceIntegrand (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r t : ℝ) : Op :=
  CanonicalGradedFrequency.weight frequency damping t •
    (time (compression p F+cutoff cut+r • forceGauss f p phi) t-time (compression p F+cutoff cut) t-
      r • variation (compression p F+cutoff cut) (forceGauss f p phi) t)

theorem timeLaplace_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r t : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping)
    (future : 0 ≤ t) :
    ‖timeLaplaceIntegrand p F cut f phi frequency damping r t‖ ≤ sourceEnvelope cut (damping/8)*laplaceMajorant damping t := by
  have hM : 0 ≤ sourceEnvelope cut (damping/8) := zero_le_one.trans (sourceEnvelope_one_le cut _ (by positivity))
  rw [timeLaplaceIntegrand,norm_smul,CanonicalGradedFrequency.weight_norm]
  have ht:=actual_damped_time_envelope p F cut f phi damping r t positive small
  rw [abs_of_nonneg future] at ht
  calc
    _ ≤ Real.exp (-damping*t)*(sourceEnvelope cut (damping/8)*Real.exp ((damping/4)*t)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = sourceEnvelope cut (damping/8)*(Real.exp (-damping*t)*Real.exp ((damping/4)*t)) := by ring
    _ ≤ sourceEnvelope cut (damping/8)*Real.exp (-(damping/2)*t) :=
      mul_le_mul_of_nonneg_left (exp_decay_order damping t (damping/4) positive future (by linarith)) hM
    _ ≤ _ := by
      unfold laplaceMajorant dampedPolynomial
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.exp_pos _).le (by nlinarith [sq_nonneg t])) hM

private theorem variation_time_continuous (K B : Op) : Continuous (variation K B) := by
  have same : variation K B=crossTime K K B := by
    funext t
    rw [crossTime_integral]
    simp only [variation,variationBetween,zero_smul,add_zero]
  rw [same]
  exact continuous_iff_continuousAt.mpr (fun t=>(crossTime_derivative K K B t).continuousAt)

theorem derivativeLaplace_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping t : ℝ) (positive : 0 < damping) (future : 0 ≤ t) :
    ‖derivativeLaplaceIntegrand p F cut f phi frequency damping t‖ ≤
      (sourceEnvelope cut (damping/8)^2*‖forceGauss f p phi‖)*laplaceMajorant damping t := by
  let M:=sourceEnvelope cut (damping/8)
  have hM : 0 ≤ M := zero_le_one.trans (sourceEnvelope_one_le cut _ (by positivity))
  have base (s : ℝ) (hs : |s| ≤ t) : ‖time (compression p F+cutoff cut) s‖ ≤ M*Real.exp ((damping/8)*t) :=
    (original_exponential_envelope p F cut (damping/8) (by positivity) s).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs (by positivity))) hM)
  have h:=variationBetween_window (compression p F+cutoff cut) (forceGauss f p phi) 0 t
    (M*Real.exp ((damping/8)*t)) (M*Real.exp ((damping/8)*t)) t
    (mul_nonneg hM (Real.exp_pos _).le) (mul_nonneg hM (Real.exp_pos _).le)
    (by rw [abs_of_nonneg future]) base (by simpa only [zero_smul,add_zero] using base)
  have hv : ‖variation (compression p F+cutoff cut) (forceGauss f p phi) t‖ ≤
      M^2*‖forceGauss f p phi‖*t*Real.exp ((damping/4)*t) := by
    apply h.trans_eq
    rw [abs_of_nonneg future]
    calc
      _ = (M^2*‖forceGauss f p phi‖*t)*(Real.exp ((damping/8)*t)^2) := by ring
      _ = _ := by rw [←Real.exp_nat_mul];simp only [Nat.cast_ofNat];congr 2;ring
  rw [derivativeLaplaceIntegrand,norm_smul,CanonicalGradedFrequency.weight_norm]
  calc
    _ ≤ Real.exp (-damping*t)*(M^2*‖forceGauss f p phi‖*t*Real.exp ((damping/4)*t)) :=
      mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
    _ = (M^2*‖forceGauss f p phi‖)*t*(Real.exp (-damping*t)*Real.exp ((damping/4)*t)) := by ring
    _ ≤ (M^2*‖forceGauss f p phi‖)*t*Real.exp (-(damping/2)*t) :=
      mul_le_mul_of_nonneg_left (exp_decay_order damping t (damping/4) positive future (by linarith))
        (mul_nonneg (mul_nonneg (sq_nonneg M) (norm_nonneg _)) future)
    _ ≤ _ := by
      unfold laplaceMajorant dampedPolynomial
      have ht : t ≤ (t+1)^2 := by nlinarith [sq_nonneg t]
      calc
        _ = (M^2*‖forceGauss f p phi‖)*(t*Real.exp (-(damping/2)*t)) := by ring
        _ ≤ (M^2*‖forceGauss f p phi‖)*((t+1)^2*Real.exp (-(damping/2)*t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (Real.exp_pos (-(damping/2)*t)).le)
            (mul_nonneg (sq_nonneg M) (norm_nonneg (forceGauss f p phi)))
        _ = _ := by dsimp [M];ring

theorem remainderLaplace_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r t : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping)
    (future : 0 ≤ t) :
    ‖remainderLaplaceIntegrand p F cut f phi frequency damping r t‖ ≤
      (sourceEnvelope cut (damping/8)^3*‖forceGauss f p phi‖^2)*‖r‖^2*laplaceMajorant damping t := by
  let K:=sourceEnvelope cut (damping/8)^3*‖forceGauss f p phi‖^2
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg (zero_le_one.trans (sourceEnvelope_one_le cut _ (by positivity))) 3) (sq_nonneg _)
  rw [remainderLaplaceIntegrand,norm_smul,CanonicalGradedFrequency.weight_norm]
  have h:=actual_half_damped_remainder p F cut f phi damping r t positive small
  rw [abs_of_nonneg future] at h
  calc
    _ ≤ Real.exp (-damping*t)*(K*t^2*Real.exp ((damping/2)*t)*‖r‖^2) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = K*‖r‖^2*t^2*(Real.exp (-damping*t)*Real.exp ((damping/2)*t)) := by ring
    _ ≤ K*‖r‖^2*t^2*Real.exp (-(damping/2)*t) :=
      mul_le_mul_of_nonneg_left (exp_decay_order damping t (damping/2) positive future le_rfl)
        (mul_nonneg (mul_nonneg hK (sq_nonneg _)) (sq_nonneg t))
    _ ≤ _ := by
      unfold laplaceMajorant dampedPolynomial
      have ht : t^2 ≤ (t+1)^2 := by nlinarith
      calc
        _ = (K*‖r‖^2)*(t^2*Real.exp (-(damping/2)*t)) := by ring
        _ ≤ (K*‖r‖^2)*((t+1)^2*Real.exp (-(damping/2)*t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (Real.exp_pos (-(damping/2)*t)).le)
            (mul_nonneg hK (sq_nonneg ‖r‖))
        _ = _ := by dsimp [K];ring

theorem timeLaplace_integrable (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping) :
    IntegrableOn (timeLaplaceIntegrand p F cut f phi frequency damping r) (Ioi 0) := by
  have continuous : Continuous (timeLaplaceIntegrand p F cut f phi frequency damping r) :=
    (CanonicalGradedFrequency.weight_continuous frequency damping).smul (time_continuous _)
  apply ((laplaceMajorant_integrable damping positive).const_mul (sourceEnvelope cut (damping/8))).mono' continuous.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact timeLaplace_bound p F cut f phi frequency damping r t positive small ht.le

theorem derivativeLaplace_integrable (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) :
    IntegrableOn (derivativeLaplaceIntegrand p F cut f phi frequency damping) (Ioi 0) := by
  have continuous : Continuous (derivativeLaplaceIntegrand p F cut f phi frequency damping) :=
    (CanonicalGradedFrequency.weight_continuous frequency damping).smul (variation_time_continuous _ _)
  apply ((laplaceMajorant_integrable damping positive).const_mul (sourceEnvelope cut (damping/8)^2*‖forceGauss f p phi‖)).mono' continuous.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact derivativeLaplace_bound p F cut f phi frequency damping t positive ht.le

def finiteTimeLaplace (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r : ℝ) : Op := ∫ t in Ioi 0,timeLaplaceIntegrand p F cut f phi frequency damping r t

def finiteDerivativeLaplace (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping : ℝ) : Op := ∫ t in Ioi 0,derivativeLaplaceIntegrand p F cut f phi frequency damping t

theorem finiteTimeLaplace_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping) :
    ‖finiteTimeLaplace p F cut f phi frequency damping r‖ ≤ sourceEnvelope cut (damping/8)*laplaceMass damping := by
  have h:=norm_integral_le_of_norm_le ((laplaceMajorant_integrable damping positive).const_mul (sourceEnvelope cut (damping/8)))
    (show ∀ᵐ t ∂volume.restrict (Ioi 0),‖timeLaplaceIntegrand p F cut f phi frequency damping r t‖ ≤
      sourceEnvelope cut (damping/8)*laplaceMajorant damping t from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact timeLaplace_bound p F cut f phi frequency damping r t positive small ht.le)
  rw [integral_const_mul] at h
  exact h

theorem finiteDerivativeLaplace_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) :
    ‖finiteDerivativeLaplace p F cut f phi frequency damping‖ ≤
      (sourceEnvelope cut (damping/8)^2*‖forceGauss f p phi‖)*laplaceMass damping := by
  have h:=norm_integral_le_of_norm_le ((laplaceMajorant_integrable damping positive).const_mul
    (sourceEnvelope cut (damping/8)^2*‖forceGauss f p phi‖))
    (show ∀ᵐ t ∂volume.restrict (Ioi 0),‖derivativeLaplaceIntegrand p F cut f phi frequency damping t‖ ≤
      (sourceEnvelope cut (damping/8)^2*‖forceGauss f p phi‖)*laplaceMajorant damping t from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact derivativeLaplace_bound p F cut f phi frequency damping t positive ht.le)
  rw [integral_const_mul] at h
  exact h

theorem finiteLaplace_remainder (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping) :
    ‖finiteTimeLaplace p F cut f phi frequency damping r-finiteTimeLaplace p F cut f phi frequency damping 0-
      r • finiteDerivativeLaplace p F cut f phi frequency damping‖ ≤
      (sourceEnvelope cut (damping/8)^3*‖forceGauss f p phi‖^2*laplaceMass damping)*‖r‖^2 := by
  have zeroSmall : |(0:ℝ)| ≤ actualParameterRadius p cut f phi damping :=
    (abs_zero.trans_le (actual_parameter_neighborhood p cut f phi damping positive).le)
  have hr:=timeLaplace_integrable p F cut f phi frequency damping r positive small
  have h0:=timeLaplace_integrable p F cut f phi frequency damping 0 positive zeroSmall
  have hd:=derivativeLaplace_integrable p F cut f phi frequency damping positive
  have identity : remainderLaplaceIntegrand p F cut f phi frequency damping r=
      (fun t=>timeLaplaceIntegrand p F cut f phi frequency damping r t-
        timeLaplaceIntegrand p F cut f phi frequency damping 0 t-r • derivativeLaplaceIntegrand p F cut f phi frequency damping t) := by
    funext t
    exact weighted_time_remainder (compression p F+cutoff cut) (forceGauss f p phi)
      (CanonicalGradedFrequency.weight frequency damping t) r t
  have integralIdentity : (∫ t in Ioi 0,remainderLaplaceIntegrand p F cut f phi frequency damping r t)=
      finiteTimeLaplace p F cut f phi frequency damping r-finiteTimeLaplace p F cut f phi frequency damping 0-
        r • finiteDerivativeLaplace p F cut f phi frequency damping := by
    rw [identity]
    exact integral_sub_smul (volume.restrict (Ioi 0)) _ _ _ r hr h0 hd
  rw [←integralIdentity]
  have h:=norm_integral_le_of_norm_le ((laplaceMajorant_integrable damping positive).const_mul
    ((sourceEnvelope cut (damping/8)^3*‖forceGauss f p phi‖^2)*‖r‖^2))
    (show ∀ᵐ t ∂volume.restrict (Ioi 0),‖remainderLaplaceIntegrand p F cut f phi frequency damping r t‖ ≤
      (sourceEnvelope cut (damping/8)^3*‖forceGauss f p phi‖^2)*‖r‖^2*laplaceMajorant damping t from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact remainderLaplace_bound p F cut f phi frequency damping r t positive small ht.le)
  rw [integral_const_mul] at h
  exact h.trans_eq (by unfold laplaceMass;ring)

/-- The original parameter curve on its generated open neighbourhood; the zero
extension outside that neighbourhood only totalizes this local analytic map. -/
def laplaceFamily (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) (r : ℝ) : Operator Index H where
  component F:=if |r| ≤ actualParameterRadius p cut f phi damping then finiteTimeLaplace p F cut f phi frequency damping r else 0
  bounded:=⟨sourceEnvelope cut (damping/8)*laplaceMass damping,
    mul_nonneg (zero_le_one.trans (sourceEnvelope_one_le cut _ (by positivity))) (laplaceMass_nonneg damping),fun F v=>by
      split_ifs with small
      · exact ((finiteTimeLaplace p F cut f phi frequency damping r).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (finiteTimeLaplace_bound p F cut f phi frequency damping r positive small) (norm_nonneg v))
      · simp only [zero_apply,norm_zero]
        exact mul_nonneg (mul_nonneg (zero_le_one.trans (sourceEnvelope_one_le cut _ (by positivity))) (laplaceMass_nonneg damping)) (norm_nonneg v)⟩

def derivativeLaplaceFamily (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) : Operator Index H where
  component F:=finiteDerivativeLaplace p F cut f phi frequency damping
  bounded:=⟨(sourceEnvelope cut (damping/8)^2*‖forceGauss f p phi‖)*laplaceMass damping,
    mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (laplaceMass_nonneg damping),fun F v=>
      ((finiteDerivativeLaplace p F cut f phi frequency damping).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (finiteDerivativeLaplace_bound p F cut f phi frequency damping positive) (norm_nonneg v))⟩

def actualLaplace (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) (r : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (laplaceFamily p cut f phi frequency damping positive r)

def actualLaplaceDerivative (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (derivativeLaplaceFamily p cut f phi frequency damping positive)

theorem laplaceFamily_actual (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping) :
    (laplaceFamily p cut f phi frequency damping positive r).component F=finiteTimeLaplace p F cut f phi frequency damping r :=
  if_pos small

def laplaceRemainderBudget (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (damping : ℝ) : ℝ :=
  sourceEnvelope cut (damping/8)^3*‖forceGauss f p phi‖^2*laplaceMass damping

theorem laplaceRemainderBudget_nonneg (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (damping : ℝ) (positive : 0 < damping) : 0 ≤ laplaceRemainderBudget p cut f phi damping :=
  mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans (sourceEnvelope_one_le cut _ (by positivity))) 3) (sq_nonneg _))
    (laplaceMass_nonneg damping)

def laplaceErrorFamily (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping) : Operator Index H where
  component F:=finiteTimeLaplace p F cut f phi frequency damping r-finiteTimeLaplace p F cut f phi frequency damping 0-
    r • finiteDerivativeLaplace p F cut f phi frequency damping
  bounded:=⟨laplaceRemainderBudget p cut f phi damping*‖r‖^2,
    mul_nonneg (laplaceRemainderBudget_nonneg p cut f phi damping positive) (sq_nonneg _),fun F v=>
      ((finiteTimeLaplace p F cut f phi frequency damping r-finiteTimeLaplace p F cut f phi frequency damping 0-
        r • finiteDerivativeLaplace p F cut f phi frequency damping).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (finiteLaplace_remainder p F cut f phi frequency damping r positive small) (norm_nonneg v))⟩

theorem lift_sub_smul {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) (X A B D : Operator I E) (r : ℝ)
    (components : ∀ i,X.component i=A.component i-B.component i-r • D.component i) :
    lift u X=lift u A-lift u B-r • lift u D := by
  apply SourceFamilyOperator.ext u
  intro v
  rw [sub_apply,sub_apply,smul_apply,lift_coe,lift_coe,lift_coe,lift_coe,
    ←UniformSpace.Completion.coe_sub,←UniformSpace.Completion.coe_smul,←UniformSpace.Completion.coe_sub]
  congr 1
  apply Family.ext
  funext i
  change X.component i (value v i)=A.component i (value v i)-B.component i (value v i)-r • D.component i (value v i)
  rw [components]
  rfl

theorem laplace_lift_error (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping) :
    lift sourceFilter (laplaceErrorFamily p cut f phi frequency damping r positive small)=
      actualLaplace p cut f phi frequency damping positive r-actualLaplace p cut f phi frequency damping positive 0-
        r • actualLaplaceDerivative p cut f phi frequency damping positive := by
  change lift sourceFilter (laplaceErrorFamily p cut f phi frequency damping r positive small)=
    lift sourceFilter (laplaceFamily p cut f phi frequency damping positive r)-
      lift sourceFilter (laplaceFamily p cut f phi frequency damping positive 0)-
        r • lift sourceFilter (derivativeLaplaceFamily p cut f phi frequency damping positive)
  apply lift_sub_smul
  intro F
  have zeroSmall : |(0:ℝ)| ≤ actualParameterRadius p cut f phi damping :=
    abs_zero.trans_le (actual_parameter_neighborhood p cut f phi damping positive).le
  rw [laplaceFamily_actual _ _ _ _ _ _ _ _ positive small,laplaceFamily_actual _ _ _ _ _ _ _ _ positive zeroSmall]
  rfl

theorem actualLaplace_remainder (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping) :
    ‖actualLaplace p cut f phi frequency damping positive r-actualLaplace p cut f phi frequency damping positive 0-
      r • actualLaplaceDerivative p cut f phi frequency damping positive‖ ≤ laplaceRemainderBudget p cut f phi damping*‖r‖^2 := by
  rw [←laplace_lift_error _ _ _ _ _ _ _ positive small]
  apply lift_bound sourceFilter _ _ (mul_nonneg (laplaceRemainderBudget_nonneg p cut f phi damping positive) (sq_nonneg _))
  intro F
  exact finiteLaplace_remainder p F cut f phi frequency damping r positive small

theorem actualLaplace_parameter_derivative (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) :
    HasDerivAt (actualLaplace p cut f phi frequency damping positive)
      (actualLaplaceDerivative p cut f phi frequency damping positive) 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero]
  let K:=laplaceRemainderBudget p cut f phi damping
  have convergence : Tendsto (fun r : ℝ=>K*‖r‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using ((continuous_norm:Continuous (fun r:ℝ=>‖r‖)).tendsto 0).const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun r=>mul_nonneg (inv_nonneg.mpr (norm_nonneg r)) (norm_nonneg _))) ?_ convergence
  have small : ∀ᶠ r : ℝ in 𝓝 0,|r| ≤ actualParameterRadius p cut f phi damping := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (actual_parameter_neighborhood p cut f phi damping positive)] with r hr
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hr : |r|<actualParameterRadius p cut f phi damping).le
  filter_upwards [small] with r hr
  have bound:=mul_le_mul_of_nonneg_left (actualLaplace_remainder p cut f phi frequency damping r positive hr) (inv_nonneg.mpr (norm_nonneg r))
  have scalar : ‖r‖⁻¹*(K*‖r‖^2)=K*‖r‖ := by
    by_cases zero : ‖r‖=0
    · simp only [zero,inv_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    · field_simp
  exact bound.trans_eq scalar

end LowEnergy.PreparationVacuumDampedFieldPerturbation
