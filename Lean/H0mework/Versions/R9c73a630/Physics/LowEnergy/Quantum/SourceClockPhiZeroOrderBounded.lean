import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiZeroOrderProfile
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiZeroOrderCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiZeroOrderBounded
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussFockWeights
open GaussNativeEnergy GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockPhiRadiusResponseHessian
open SourceScalarDoubleCurrent SourcePhysicalKineticSquare SourceBoundedClockAbel SourceCoframeVolume SourceClockPhiZeroOrderProfile
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
private abbrev S : End := phiInverseAction
private abbrev Q : End := 1-S
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev B (m ell : ℕ) : End := phiFirstPeak m ell
private abbrev C (m ell : ℕ) : End := phiSecondPeak m ell
private abbrev s (z : SourceCoordinateSlice) : ℝ := phiReciprocal z
private theorem q_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    Q f z=((1-s z:ℝ):ℂ) • f z := by
  change f z-(s z:ℂ) • f z=_
  push_cast
  module
private theorem q_power (k : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (Q^k) f z=(((1-s z)^k:ℝ):ℂ) • f z := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change Q ((Q^k) f) z=_
    rw [q_apply,ih,smul_smul,pow_succ,Complex.ofReal_mul]
    congr 1
    rw [mul_comm]
private theorem theta_apply (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    T m ell f z=(ClockPhiRittJets.theta (s z) m ell:ℂ) • f z := by
  change ((Q^(m+1)) f) z-((Q^(ell+1)) f) z=_
  rw [q_power,q_power]
  unfold ClockPhiRittJets.theta
  push_cast
  module
private theorem beta_apply (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    B m ell f z=(ClockPhiRittJets.beta (s z) m ell:ℂ) • f z := by
  change (ell+1:ℂ) • ((Q^ell) f z)-(m+1:ℂ) • ((Q^m) f z)=_
  rw [q_power,q_power]
  unfold ClockPhiRittJets.beta
  push_cast
  module
private theorem beta2_apply (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    C m ell f z=(ClockPhiRittJets.beta2 (s z) m ell:ℂ) • f z := by
  change (m*(m+1):ℂ) • ((Q^(m-1)) f z)-(ell*(ell+1):ℂ) • ((Q^(ell-1)) f z)=_
  rw [q_power,q_power]
  unfold ClockPhiRittJets.beta2
  push_cast
  module
private theorem inverse_apply (f : QuantumTest) (z : SourceCoordinateSlice) : S f z=(s z:ℂ) • f z := rfl
private theorem inverse_power (k : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (S^k) f z=(s z^k:ℂ) • f z := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change S ((S^k) f) z=_
    rw [inverse_apply,ih,smul_smul,pow_succ]
    congr 1
    rw [mul_comm]

private def Value (z : SourceCoordinateSlice) (A : End) (a : ℝ) : Prop :=
  ∀ f : QuantumTest,A f z=(a:ℂ) • f z
private theorem val_mul {z : SourceCoordinateSlice} {A B : End} {a b : ℝ}
    (hA : Value z A a) (hB : Value z B b) : Value z (A*B) (a*b) := by
  intro f
  change A (B f) z=_
  rw [hA,hB,smul_smul,Complex.ofReal_mul]
private theorem val_add {z : SourceCoordinateSlice} {A B : End} {a b : ℝ}
    (hA : Value z A a) (hB : Value z B b) : Value z (A+B) (a+b) := by
  intro f
  change A f z+B f z=_
  rw [hA,hB,Complex.ofReal_add,add_smul]
private theorem val_sub {z : SourceCoordinateSlice} {A B : End} {a b : ℝ}
    (hA : Value z A a) (hB : Value z B b) : Value z (A-B) (a-b) := by
  intro f
  change A f z-B f z=_
  rw [hA,hB,Complex.ofReal_sub,sub_smul]
private theorem val_neg {z : SourceCoordinateSlice} {A : End} {a : ℝ}
    (hA : Value z A a) : Value z (-A) (-a) := by
  intro f
  change -(A f z)=_
  rw [hA,Complex.ofReal_neg,neg_smul]
private theorem val_scale {z : SourceCoordinateSlice} {A : End} {a : ℝ}
    (hA : Value z A a) (r : ℝ) : Value z ((r:ℂ) • A) (r*a) := by
  intro f
  change (r:ℂ) • A f z=_
  rw [hA,smul_smul,Complex.ofReal_mul]
private theorem radial_value (i j : Fin 2) (m ell : ℕ) (z : SourceCoordinateSlice) :
    Value z (radialProfile i j m ell) (ClockPhiZeroOrderCoefficient.profile (s z) m ell i j) := by
  have hS : Value z S (s z) := fun f=>inverse_apply f z
  have hSS : Value z (S^2) (s z^2) := fun f=>by simpa only [Complex.ofReal_pow] using inverse_power 2 f z
  have hT : Value z (T m ell) (ClockPhiRittJets.theta (s z) m ell) := fun f=>theta_apply m ell f z
  have hB : Value z (B m ell) (ClockPhiRittJets.beta (s z) m ell) := fun f=>beta_apply m ell f z
  have hBS:=val_mul hB hS
  fin_cases i <;> fin_cases j
  · have h:=val_mul (val_sub (val_scale hBS 2) hT) hT
    convert h using 1
    · rfl
    · dsimp [ClockPhiZeroOrderCoefficient.profile]
      ring
  · have h:=val_mul (val_scale (val_mul hS hBS) (-2)) hT
    norm_num only [Complex.ofReal_neg,Complex.ofReal_ofNat] at h
    convert h using 1
    · rfl
    · dsimp [ClockPhiZeroOrderCoefficient.profile]
      ring
  · have h:=val_mul (val_scale (val_mul hS hBS) (-2)) hT
    norm_num only [Complex.ofReal_neg,Complex.ofReal_ofNat] at h
    convert h using 1
    · rfl
    · dsimp [ClockPhiZeroOrderCoefficient.profile]
      ring
  · have h:=val_mul (val_mul hSS (val_add hT (val_scale hBS 2))) hT
    convert h using 1
    · rfl
    · dsimp [ClockPhiZeroOrderCoefficient.profile]
      ring
private theorem derivative_value (i j : Fin 2) (m ell : ℕ) (z : SourceCoordinateSlice) :
    Value z (zeroDerivative i j m ell) (ClockPhiZeroOrderCoefficient.derivative (s z) m ell i j) := by
  have hS : Value z S (s z) := fun f=>inverse_apply f z
  have hSS : Value z (S^2) (s z^2) := fun f=>by simpa only [Complex.ofReal_pow] using inverse_power 2 f z
  have hSSS : Value z (S^3) (s z^3) := fun f=>by simpa only [Complex.ofReal_pow] using inverse_power 3 f z
  have hT : Value z (T m ell) (ClockPhiRittJets.theta (s z) m ell) := fun f=>theta_apply m ell f z
  have hB : Value z (B m ell) (ClockPhiRittJets.beta (s z) m ell) := fun f=>beta_apply m ell f z
  have hC : Value z (C m ell) (ClockPhiRittJets.beta2 (s z) m ell) := fun f=>beta2_apply m ell f z
  have hF:=val_add (val_mul hC hT) (val_mul hB hB)
  fin_cases i <;> fin_cases j
  · have h:=val_scale (val_mul hS hF) 2
    convert h using 1
    · rfl
    · dsimp [ClockPhiZeroOrderCoefficient.derivative]
      ring
  · have h:=val_sub (val_scale (val_mul (val_mul hS hB) hT) (-4)) (val_scale (val_mul hSS hF) 2)
    norm_num only [Complex.ofReal_neg,Complex.ofReal_ofNat] at h
    convert h using 1
    · rfl
    · dsimp [ClockPhiZeroOrderCoefficient.derivative]
      ring
  · have h:=val_sub (val_scale (val_mul (val_mul hS hB) hT) (-4)) (val_scale (val_mul hSS hF) 2)
    norm_num only [Complex.ofReal_neg,Complex.ofReal_ofNat] at h
    convert h using 1
    · rfl
    · dsimp [ClockPhiZeroOrderCoefficient.derivative]
      ring
  · have h:=val_add (val_add (val_scale (val_mul hS (val_mul hT hT)) 2)
      (val_scale (val_mul (val_mul hSS hB) hT) 8)) (val_scale (val_mul hSSS hF) 2)
    convert h using 1
    · rfl
    · dsimp [ClockPhiZeroOrderCoefficient.derivative]
      ring
private theorem radial_apply (i j : Fin 2) (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    radialProfile i j m ell f z=(ClockPhiZeroOrderCoefficient.profile (s z) m ell i j:ℂ) • f z :=
  radial_value i j m ell z f
private theorem derivative_apply (i j : Fin 2) (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    zeroDerivative i j m ell f z=(ClockPhiZeroOrderCoefficient.derivative (s z) m ell i j:ℂ) • f z :=
  derivative_value i j m ell z f

private theorem actual_zero_profile_point (i j : Fin 2) (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    zeroProfile i j m ell f z=(ClockPhiZeroOrderCoefficient.zero (s z) m ell i j:ℂ) • f z := by
  have h1 : Value z (1:End) 1 := by intro g; simp
  have hS : Value z S (s z) := fun g=>inverse_apply g z
  have hS2 : Value z (S^2) (s z^2) :=
    fun g=>by simpa only [Complex.ofReal_pow] using inverse_power 2 g z
  have hS3 : Value z (S^3) (s z^3) :=
    fun g=>by simpa only [Complex.ofReal_pow] using inverse_power 3 g z
  have hD := derivative_value i j m ell z
  have hR := radial_value i j m ell z
  have hZ := val_add
    (val_neg (val_mul (val_mul hS2 (val_sub h1 hS2)) hD))
    (val_mul (val_add (val_scale hS 60) hS3) hR)
  have hz : Value z (zeroPolynomial i j m ell)
      (ClockPhiZeroOrderCoefficient.zero (s z) m ell i j) := by
    convert hZ using 1
    · rfl
    · dsimp [ClockPhiZeroOrderCoefficient.zero]
      ring
  rw [actual_zero_profile_source]
  exact hz f

private def weightedProfile (i j : Fin 2) (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  volume z/(1+volume z)^2*
    ClockPhiZeroOrderCoefficient.zero (phiReciprocal z) m ell i j

private theorem zero_real_smooth (i j : Fin 2) (m ell : ℕ) :
    ContDiff ℝ ∞ (fun x : ℝ => ClockPhiZeroOrderCoefficient.zero x m ell i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [ClockPhiZeroOrderCoefficient.zero,ClockPhiZeroOrderCoefficient.profile,
      ClockPhiZeroOrderCoefficient.derivative,ClockPhiRittJets.theta,
      ClockPhiRittJets.beta,ClockPhiRittJets.beta2] <;>
    fun_prop

private theorem phi_pos (z : SourceCoordinateSlice) : 0 < phiRadius z := by
  unfold phiRadius SourceClockRadiusResponseAffine.affineRadius
  positivity

private theorem reciprocal_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ phiReciprocal z.val :=
  SourceClockRadiusResponseAffine.affine_radius_smooth.contDiffAt.inv (phi_pos z).ne'

private theorem weighted_profile_smooth (i j : Fin 2) (m ell : ℕ)
    (z : physicalChart) : ContDiffAt ℝ ∞ (weightedProfile i j m ell) z.val := by
  have hv : ContDiffAt ℝ ∞ volume z.val := volume_smooth.contDiffAt
  have hden : 1+volume z.val≠0 := ne_of_gt (by have h:=volume_pos z;positivity)
  have hz := (zero_real_smooth i j m ell).contDiffAt.comp z.val (reciprocal_smooth z)
  unfold weightedProfile
  exact (hv.div ((contDiffAt_const.add hv).pow 2)
    (pow_ne_zero 2 hden)).mul hz

private theorem one_le_phi (z : SourceCoordinateSlice) : 1 ≤ phiRadius z := by
  have hp := (phi_pos z).le
  have hs : phiRadius z^2=1+‖scalarField z‖^2/4 :=
    Real.sq_sqrt (by positivity)
  nlinarith only [hp,hs,sq_nonneg ‖scalarField z‖]
private theorem reciprocal_range (z : SourceCoordinateSlice) :
    0 ≤ phiReciprocal z ∧ phiReciprocal z ≤ 1 := by
  exact ⟨(inv_pos.mpr (phi_pos z)).le,
    inv_le_one_of_one_le₀ (one_le_phi z)⟩

private theorem contact_scalar_bound (z : physicalChart) :
    0 ≤ volume z.val/(1+volume z.val)^2 ∧
      volume z.val/(1+volume z.val)^2 ≤ 1/4 := by
  have hv := volume_pos z
  have hd : 0 < (1+volume z.val)^2 := sq_pos_of_pos (by positivity)
  constructor
  · positivity
  · apply (div_le_iff₀ hd).mpr
    nlinarith only [sq_nonneg (volume z.val-1)]

private theorem weighted_profile_bound (i j : Fin 2) (m ell : ℕ)
    (hm : 1 ≤ m) (hml : m ≤ ell) (z : physicalChart) :
    |weightedProfile i j m ell z.val| ≤ 176/(m+2:ℝ) := by
  obtain ⟨hs0,hs1⟩:=reciprocal_range z.val
  have hz := ClockPhiZeroOrderCoefficient.zero_bound
    (phiReciprocal z.val) hs0 hs1 m ell hm hml i j
  obtain ⟨hc0,hc1⟩:=contact_scalar_bound z
  unfold weightedProfile
  rw [abs_mul,abs_of_nonneg hc0]
  calc
    _ ≤ (1/4:ℝ)*(704/(m+2:ℝ)) := by
      exact (mul_le_mul_of_nonneg_left hz hc0).trans
        (mul_le_mul_of_nonneg_right hc1 (by positivity))
    _ = 176/(m+2:ℝ) := by ring

private def weightedFiber (i j : Fin 2) (m ell : ℕ)
    (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (weightedProfile i j m ell z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem fiber_smooth (i j : Fin 2) (m ell : ℕ)
    (z : physicalChart) : ContDiffAt ℝ ∞ (weightedFiber i j m ell) z.val :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
    (weighted_profile_smooth i j m ell z)).smul contDiffAt_const
private theorem fiber_weight (i j : Fin 2) (m ell : ℕ)
    (z : physicalChart) (w : ℕ → ℂ) :
    Commute (weight w) (weightedFiber i j m ell z.val) :=
  (Commute.one_right _).smul_right _
private theorem fiber_bound (i j : Fin 2) (m ell : ℕ)
    (hm : 1 ≤ m) (hml : m ≤ ell) (z : physicalChart) (f : FockFiber) :
    ‖weightedFiber i j m ell z.val f‖ ≤
      (176/(m+2:ℝ))*‖f‖ := by
  change ‖(weightedProfile i j m ell z.val:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (weighted_profile_bound i j m ell hm hml z) (norm_nonneg f)

/-- The actual full Fock/Number-weighted Hilbert extension of χ U Z_{ij}. -/
def weightedZero (i j : Fin 2) (m ell : ℕ)
    (hm : 1 ≤ m) (hml : m ≤ ell) : Op :=
  GaussBoundedMultiplier.extension (weightedFiber i j m ell)
    (fiber_smooth i j m ell) (fiber_weight i j m ell)
    (176/(m+2:ℝ)) (by positivity) (fiber_bound i j m ell hm hml)

theorem actual_weighted_zero_norm (i j : Fin 2) (m ell : ℕ)
    (hm : 1 ≤ m) (hml : m ≤ ell) :
    ‖weightedZero i j m ell hm hml‖ ≤ 176/(m+2:ℝ) :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

private theorem weighted_scalar_identity (i j : Fin 2) (m ell : ℕ)
    (z : SourceCoordinateSlice) :
    weightedProfile i j m ell z=
      clockProfile z*clockProfile z*reciprocalVolume z*
        ClockPhiZeroOrderCoefficient.zero (phiReciprocal z) m ell i j := by
  unfold weightedProfile clockProfile reciprocalVolume
  by_cases hv : volume z=0
  · simp [hv]
  by_cases hd : 1+volume z=0
  · simp [hd]
  field_simp [hv,hd]

/-- Core readback to the original two-seed zero profile, after both actual
volume-clock legs and the original inverse-volume action. -/
theorem actual_weighted_zero_core (i j : Fin 2) (m ell : ℕ)
    (hm : 1 ≤ m) (hml : m ≤ ell) (f : QuantumTest) :
    weightedZero i j m ell hm hml (embed f)=
      embed ((clockCore*clockCore*inverseVolumeAction*
        zeroProfile i j m ell) f) := by
  have he := GaussBoundedMultiplier.extension_core
    (weightedFiber i j m ell) (fiber_smooth i j m ell)
    (fiber_weight i j m ell) (176/(m+2:ℝ))
    (by positivity) (fiber_bound i j m ell hm hml) f
  unfold weightedZero
  rw [he]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change (weightedProfile i j m ell z:ℂ) • f z=
    (clockProfile z:ℂ) • ((clockProfile z:ℂ) •
      ((reciprocalVolume z:ℂ) • (zeroProfile i j m ell f z)))
  rw [actual_zero_profile_point]
  simp only [smul_smul]
  congr 1
  have hreal : weightedProfile i j m ell z=
      clockProfile z*(clockProfile z*(reciprocalVolume z*
        ClockPhiZeroOrderCoefficient.zero (phiReciprocal z) m ell i j)) := by
    simpa only [mul_assoc] using weighted_scalar_identity i j m ell z
  exact_mod_cast hreal

end LowEnergy.SourceClockPhiZeroOrderBounded
