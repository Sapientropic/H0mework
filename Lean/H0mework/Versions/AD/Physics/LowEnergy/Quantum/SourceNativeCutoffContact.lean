import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussRadialMomentum
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCutoffDilationWard
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceActualResolventEnergy
import Mathlib.Data.Nat.Choose.Cast

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceNativeCutoffContact
open GaussCoreHilbert GaussCoreDifferential GaussLiveMomentum GaussRadialDomain
open GaussYukawaCoefficient GaussMomentumAdjoint GaussHistoryHilbert GaussNativeForm
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge GaussRadialMomentum
open MeasureTheory Filter SourceActualResolventEnergy GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open scoped ContDiff RealInnerProductSpace BigOperators

theorem reciprocal_native_bound (v : Ambient) (z : SourceCoordinateSlice) :
    |radialDerivative v z| ≤ (‖v.1‖/2)*(reciprocal z)^2 := by
  have hp := radius_pos z
  have hs := Real.sq_sqrt (show 0 ≤ 1+‖(z.2.1 : Scalar)‖^2/4 by positivity)
  change (radius z)^2 = _ at hs
  have hx : ‖(z.2.1 : Scalar)‖ ≤ 2*radius z := by
    nlinarith [norm_nonneg (z.2.1 : Scalar)]
  rw [radialDerivative,abs_div,abs_neg,
    abs_of_pos (show 0<4*radius z^3 by positivity)]
  apply (div_le_iff₀ (show 0<4*radius z^3 by positivity)).mpr
  calc
    _ ≤ ‖(z.2.1 : Scalar)‖*‖v.1‖ := abs_real_inner_le_norm _ _
    _ ≤ (2*radius z)*‖v.1‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = (‖v.1‖/2)*(reciprocal z)^2*(4*radius z^3) := by
      unfold reciprocal
      field_simp
      ring

/-- The two selected successes in the binomial expansion retain the necessary S² weight. -/
theorem squared_geometric_peak (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n+1 : ℝ)*s^2*(1-s)^n ≤ 2/(n+2 : ℝ) := by
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hterm := Finset.single_le_sum
    (f := fun j => s^j*(1-s)^(n+2-j)*((n+2).choose j : ℝ))
    (fun j _ => by positivity) (show 2 ∈ Finset.range (n+2+1) by simp)
  rw [←add_pow,show s+(1-s)=1 by ring,one_pow] at hterm
  rw [show n+2-2=n by omega,Nat.cast_choose_two] at hterm
  push_cast at hterm
  have hn : 0<(n+2 : ℝ) := by positivity
  apply (le_div_iff₀ hn).mpr
  nlinarith

def theta (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  (1-reciprocal z)^(m+1)-(1-reciprocal z)^(ell+1)

theorem theta_smooth (m ell : ℕ) : ContDiff ℝ ∞ (theta m ell) :=
  ((contDiff_const.sub reciprocal_smooth).pow _).sub
    ((contDiff_const.sub reciprocal_smooth).pow _)

def thetaAction (m ell : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  multiply (theta m ell) (fun _ => (theta_smooth m ell).contDiffAt)

def thetaDerivative (v : Ambient) (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  (((ell+1 : ℕ) : ℝ)*(1-reciprocal z)^ell-
    ((m+1 : ℕ) : ℝ)*(1-reciprocal z)^m)*radialDerivative v z

theorem theta_derivative_smooth (v : Ambient) (m ell : ℕ) :
    ContDiff ℝ ∞ (thetaDerivative v m ell) :=
  (((contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow _)).sub
    (contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow _))).mul
    (radialDerivative_smooth v))

theorem direction_theta (v : Ambient) (m ell : ℕ) (z : physicalChart) :
    fderiv ℝ (theta m ell) z.val (direction v z.val)=thetaDerivative v m ell z.val := by
  have hd := (hasFDerivAt_const (1 : ℝ) z.val).sub
    ((reciprocal_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have h := (hd.pow (m+1)).sub (hd.pow (ell+1))
  have he := h.fderiv
  change fderiv ℝ (theta m ell) z.val=_ at he
  rw [he]
  simp only [sub_apply,smul_apply,smul_eq_mul,zero_sub,neg_apply,
    Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.sub_apply,nsmul_eq_mul]
  rw [direction_reciprocal]
  unfold thetaDerivative
  push_cast
  ring

theorem theta_derivative_bound (v : Ambient) (m ell : ℕ) (hle : m≤ell)
    (z : SourceCoordinateSlice) :
    |thetaDerivative v m ell z| ≤ 2*‖v.1‖/(m+2 : ℝ) := by
  have hs : 0≤reciprocal z := (inv_pos.mpr (radius_pos z)).le
  have hs1 : reciprocal z≤1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0≤1-reciprocal z := sub_nonneg.mpr hs1
  have hm := squared_geometric_peak (reciprocal z) hs hs1 m
  have hell := squared_geometric_peak (reciprocal z) hs hs1 ell
  have hd := reciprocal_native_bound v z
  have hm0 : 0≤(m+1 : ℝ)*(1-reciprocal z)^m := by positivity
  have he0 : 0≤(ell+1 : ℝ)*(1-reciprocal z)^ell := by positivity
  have hab : |(ell+1 : ℝ)*(1-reciprocal z)^ell-(m+1 : ℝ)*(1-reciprocal z)^m|≤
      (ell+1 : ℝ)*(1-reciprocal z)^ell+(m+1 : ℝ)*(1-reciprocal z)^m := by
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg he0,abs_of_nonneg hm0])
  have he := one_div_le_one_div_of_le (by positivity : 0<(m+2 : ℝ))
    (show (m+2 : ℝ)≤(ell+2 : ℝ) by exact_mod_cast Nat.add_le_add_right hle 2)
  have hv : 0≤‖v.1‖/2 := by positivity
  unfold thetaDerivative
  push_cast
  rw [abs_mul]
  calc
    _ ≤ ((ell+1 : ℝ)*(1-reciprocal z)^ell+(m+1 : ℝ)*(1-reciprocal z)^m)*
        ((‖v.1‖/2)*(reciprocal z)^2) := mul_le_mul hab hd (abs_nonneg _) (by positivity)
    _ = (‖v.1‖/2)*((ell+1 : ℝ)*(reciprocal z)^2*(1-reciprocal z)^ell+
        (m+1 : ℝ)*(reciprocal z)^2*(1-reciprocal z)^m) := by ring
    _ ≤ (‖v.1‖/2)*(2/(ell+2 : ℝ)+2/(m+2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hell hm) hv
    _ ≤ 2*‖v.1‖/(m+2 : ℝ) := by
      have hb := mul_le_mul_of_nonneg_left he (by positivity : 0≤‖v.1‖)
      simp only [div_eq_mul_inv,one_mul] at hb ⊢
      nlinarith

def contactFiber (v : Ambient) (m ell : ℕ) (z : SourceCoordinateSlice) :
    FockFiber →L[ℂ] FockFiber :=
  ((-Complex.I)*(thetaDerivative v m ell z : ℂ)) • ContinuousLinearMap.id ℂ FockFiber

theorem contact_smooth (v : Ambient) (m ell : ℕ) : ContDiff ℝ ∞ (contactFiber v m ell) :=
  (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (theta_derivative_smooth v m ell))).smul contDiff_const

def contactAction (v : Ambient) (m ell : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (contactFiber v m ell) (fun _ => (contact_smooth v m ell).contDiffAt)

private theorem theta_action_real (m ell : ℕ) (f : QuantumTest) :
    (thetaAction m ell f : SourceCoordinateSlice → FockFiber)=fun z => theta m ell z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem directional_theta (v : Ambient) (m ell : ℕ) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    directional v (thetaAction m ell f) z=theta m ell z • directional v f z+
      thetaDerivative v m ell z • f z := by
  rw [directional_apply,theta_action_real,
    fderiv_fun_smul ((theta_smooth m ell).differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change theta m ell z • directional v f z+
    fderiv ℝ (theta m ell) z (direction v z) • f z=_
  by_cases hz : z∈physicalChart
  · rw [direction_theta v m ell ⟨z,hz⟩]
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    rw [hf,smul_zero,smul_zero]

theorem native_core_contact (v : Ambient) (m ell : ℕ) (f : QuantumTest) :
    covariantMomentum v (thetaAction m ell f)=
      thetaAction m ell (covariantMomentum v f)+contactAction v m ell f := by
  apply DFunLike.ext
  intro z
  change (-Complex.I) • (directional v (thetaAction m ell f) z+
    connection v z (thetaAction m ell f z))=
    (theta m ell z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))+
      ((-Complex.I)*(thetaDerivative v m ell z : ℂ)) • f z
  rw [directional_theta]
  change (-Complex.I) • (theta m ell z • directional v f z+thetaDerivative v m ell z • f z+
    connection v z ((theta m ell z : ℂ) • f z))=_
  rw [map_smul]
  apply PiLp.ext
  intro word
  simp only [PiLp.smul_apply,PiLp.add_apply,Complex.real_smul]
  change (-Complex.I)*((theta m ell z : ℂ)*directional v f z word+
    (thetaDerivative v m ell z : ℂ)*f z word+(theta m ell z : ℂ)*connection v z (f z) word)=_
  ring

private theorem contact_pair (v : Ambient) (m ell : ℕ) (f g : QuantumTest) :
    GaussFockPair.sourcePair f (contactAction v m ell g)=
      -GaussFockPair.sourcePair (contactAction v m ell f) g := by
  have hK : contactAction v m ell=(-Complex.I) •
      multiply (thetaDerivative v m ell) (fun _ => (theta_derivative_smooth v m ell).contDiffAt) := by
    apply LinearMap.ext
    intro a
    apply DFunLike.ext
    intro z
    apply PiLp.ext
    intro word
    exact mul_assoc _ _ _
  rw [hK]
  change inner ℂ (embed f) (embed ((-Complex.I) • _))=
    -inner ℂ (embed ((-Complex.I) • _)) (embed g)
  rw [map_smul,map_smul,inner_smul_right,inner_smul_left]
  change (-Complex.I)*GaussFockPair.sourcePair f (multiply _ _ g)=_
  rw [multiply_pair]
  simp only [map_neg,Complex.conj_I,neg_neg,neg_mul]
  rfl

private theorem test_pair_ext (f g : QuantumTest)
    (h : ∀ a, GaussFockPair.sourcePair a f=GaussFockPair.sourcePair a g) : f=g := by
  have hz : inner ℂ (embed (f-g)) (embed (f-g))=0 := by
    calc
      _ = GaussFockPair.sourcePair (f-g) f-GaussFockPair.sourcePair (f-g) g := by
        conv_lhs => rw [show embed (f-g)=embed f-embed g from map_sub embed f g]
        exact inner_sub_right _ _ _
      _ = 0 := sub_eq_zero.mpr (h (f-g))
  apply sub_eq_zero.mp
  exact embed_injective (((inner_self_eq_zero (𝕜 := ℂ)).mp hz).trans (map_zero embed).symm)

/-- The independently generated native adjoint has the same scalar contact, in its own order. -/
theorem sharp_core_contact (v : Ambient) (m ell : ℕ) (g : QuantumTest) :
    GaussMomentumAdjoint.adjoint v (thetaAction m ell g)=
      thetaAction m ell (GaussMomentumAdjoint.adjoint v g)+contactAction v m ell g := by
  apply test_pair_ext
  intro f
  have h1 := adjoint_pair v f (thetaAction m ell g)
  have h2 := multiply_pair (theta m ell) (fun _ => (theta_smooth m ell).contDiffAt)
    (covariantMomentum v f) g
  have h3 := adjoint_pair v (thetaAction m ell f) g
  have h4 := multiply_pair (theta m ell) (fun _ => (theta_smooth m ell).contDiffAt)
    f (GaussMomentumAdjoint.adjoint v g)
  have h5 := contact_pair v m ell f g
  rw [native_core_contact] at h3
  change GaussFockPair.sourcePair (thetaAction m ell f) (GaussMomentumAdjoint.adjoint v g)=
    inner ℂ (embed (thetaAction m ell (covariantMomentum v f)+contactAction v m ell f)) (embed g) at h3
  rw [map_add,inner_add_left] at h3
  change GaussFockPair.sourcePair f (GaussMomentumAdjoint.adjoint v (thetaAction m ell g))=
    inner ℂ (embed f) (embed (thetaAction m ell (GaussMomentumAdjoint.adjoint v g)+contactAction v m ell g))
  rw [map_add,inner_add_right]
  change _=GaussFockPair.sourcePair f (thetaAction m ell (GaussMomentumAdjoint.adjoint v g))+
    GaussFockPair.sourcePair f (contactAction v m ell g)
  change GaussFockPair.sourcePair (covariantMomentum v f) (thetaAction m ell g)=
    GaussFockPair.sourcePair (thetaAction m ell (covariantMomentum v f)) g at h2
  change GaussFockPair.sourcePair f (thetaAction m ell (GaussMomentumAdjoint.adjoint v g))=
    GaussFockPair.sourcePair (thetaAction m ell f) (GaussMomentumAdjoint.adjoint v g) at h4
  rw [h1,h2,h4,h3,h5]
  unfold GaussFockPair.sourcePair
  ring

theorem contact_commutes (v : Ambient) (m ell : ℕ) (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (contactFiber v m ell z) :=
  (Commute.one_right _).smul_right _

theorem contact_bound (v : Ambient) (m ell : ℕ) (hle : m≤ell) (z : SourceCoordinateSlice)
    (f : FockFiber) : ‖contactFiber v m ell z f‖≤(2*‖v.1‖/(m+2 : ℝ))*‖f‖ := by
  change ‖((-Complex.I)*(thetaDerivative v m ell z : ℂ)) • f‖≤_
  rw [norm_smul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (theta_derivative_bound v m ell hle z) (norm_nonneg f)

def boundedContact (v : Ambient) (m ell : ℕ) (hle : m≤ell) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (contactFiber v m ell) (fun _ => (contact_smooth v m ell).contDiffAt)
    (fun z => contact_commutes v m ell z) (2*‖v.1‖/(m+2 : ℝ)) (by positivity)
    (fun z => contact_bound v m ell hle z)

theorem bounded_contact_core (v : Ambient) (m ell : ℕ) (hle : m≤ell) (f : QuantumTest) :
    boundedContact v m ell hle (embed f)=embed (contactAction v m ell f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f

theorem bounded_contact_norm (v : Ambient) (m ell : ℕ) (hle : m≤ell) :
    ‖boundedContact v m ell hle‖≤2*‖v.1‖/(m+2 : ℝ) :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

theorem bounded_contact_bound (v : Ambient) (m ell : ℕ) (hle : m≤ell) (x : H) :
    ‖boundedContact v m ell hle x‖≤(2*‖v.1‖/(m+2 : ℝ))*‖x‖ :=
  ((boundedContact v m ell hle).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (bounded_contact_norm v m ell hle) (norm_nonneg x))

private theorem complement_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (((1-inverseAction)^n) f) z=((1-reciprocal z)^n : ℂ) • f z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (((1-inverseAction)^n) f) z-(reciprocal z : ℂ) • (((1-inverseAction)^n) f) z=_
    rw [ih]
    apply PiLp.ext
    intro word
    simp only [PiLp.sub_apply,PiLp.smul_apply]
    rw [pow_succ]
    ring

theorem theta_action_polynomial (m ell : ℕ) :
    thetaAction m ell=(1-inverseAction)^(m+1)-(1-inverseAction)^(ell+1) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (theta m ell z : ℂ) • f z=
    (((1-inverseAction)^(m+1)) f) z-(((1-inverseAction)^(ell+1)) f) z
  rw [complement_power_apply,complement_power_apply]
  unfold theta
  push_cast
  exact sub_smul _ _ _

private theorem complement_power_core (n : ℕ) (f : QuantumTest) :
    embed (((1-inverseAction)^n) f)=((1-inverseRadius)^n) (embed f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change embed (((1-inverseAction)^n) f-inverseAction (((1-inverseAction)^n) f))=
      ((1-inverseRadius)^n) (embed f)-inverseRadius (((1-inverseRadius)^n) (embed f))
    rw [map_sub,←inverse_core,ih]

theorem theta_core (m ell : ℕ) (f : QuantumTest) :
    embed (thetaAction m ell f)=SourceRelativePowerTail.relativeTail m ell (embed f) := by
  rw [theta_action_polynomial]
  simp only [LinearMap.sub_apply,map_sub,complement_power_core,
    SourceRelativePowerTail.relativeTail,SourceRelativePowerTail.sourceComplement,sub_apply]

/-- The actual varying finite-resolvent input is paid without source moments or an F-dependent bound. -/
theorem actual_contact_energy (v : Ambient) (m ell : ℕ) (hle : m≤ell)
    (F : Index) (μ : ℝ) (hμ : 0<μ) (g : H) :
    (∫⁻ w : ℝ, ENNReal.ofReal
      (‖boundedContact v m ell hle (finiteResolvent F (line μ w) g)‖^2))≤
      ENNReal.ofReal ((2*‖v.1‖/(m+2 : ℝ))^2*(Real.pi/μ)*‖g‖^2) := by
  let C := 2*‖v.1‖/(m+2 : ℝ)
  have hb (w : ℝ) : ‖boundedContact v m ell hle (finiteResolvent F (line μ w) g)‖^2≤
      C^2*‖finiteResolvent F (line μ w) g‖^2 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (bounded_contact_bound v m ell hle _) 2).trans_eq
      (mul_pow C _ 2)
  have he : (∫⁻ w : ℝ, ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖g‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! actual_square_lintegral F μ hμ g
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal (C^2)*
        ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (sq_nonneg C)]
      exact ENNReal.ofReal_le_ofReal (hb w)
    _ = ENNReal.ofReal (C^2)*∫⁻ w : ℝ,
        ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [he,←ENNReal.ofReal_mul (sq_nonneg C)]; congr 1; dsimp [C]; ring

end LowEnergy.SourceNativeCutoffContact
