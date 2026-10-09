import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaGradedRadial
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarRadialContact
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourcePhysicalKineticSquare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaGradedEuler
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussLiveMomentum GaussNativeEnergy GaussRadialDomain GaussYukawaCoefficient
open SourceClockYukawaGradedRadial SourceScalarRadialContact SourcePhysicalKineticSquare SourceScalarDoubleCurrent
open GaussCoreLabel NativeHistoryGrade SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace BigOperators
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
local instance labelFintype : Fintype Label := Fintype.ofFinite _

private def alpha : End := (-(sourceTime 0:ℂ)/4) • inverseVolumeAction
private def powerProfile (n : ℕ) : End := (n:ℂ) • (alpha*inverseAction^(n+2))
private def eulerForm (P : End) : End := (1/2:ℂ) •
  (scalarEulerAction*P+P*scalarEulerAction+(61:ℂ) • P)

/-- The full source profile keeps its actual Number/G labels and inverse-volume coefficient. -/
def gradedProfile (sharp : Bool) : End := (-(sourceTime 0:ℂ)/4) •
  (inverseVolumeAction*∑ g : Label,(exponent sharp g:ℂ) • (inverseAction^(exponent sharp g+2)*project g))

private theorem real_real (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)

private theorem alpha_inverse : Commute alpha inverseAction := by
  have h : Commute inverseVolumeAction inverseAction :=
    real_real reciprocalVolume reciprocal reciprocal_volume_smooth (fun _ => reciprocal_smooth.contDiffAt)
  exact h.smul_left _

private theorem real_fock_smul (c : ℝ) (v : FockFiber) : c • v=(c:ℂ) • v := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem inverse_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((inverseAction^n) f) z=(reciprocal z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (reciprocal z:ℂ) • (((inverseAction^n) f) z)=_
    rw [ih,pow_succ',mul_smul]

private def profileCoefficient (n : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  -(sourceTime 0)/4*reciprocalVolume z*(n:ℝ)*reciprocal z^(n+2)
private theorem profile_smooth (n : ℕ) (z : physicalChart) : ContDiffAt ℝ ∞ (profileCoefficient n) z.val :=
  ((contDiffAt_const.mul (reciprocal_volume_smooth z)).mul contDiffAt_const).mul
    (reciprocal_smooth.pow (n+2)).contDiffAt

private theorem power_profile_real (n : ℕ) : powerProfile n=multiply (profileCoefficient n) (profile_smooth n) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold powerProfile
  simp only [LinearMap.smul_apply,Module.End.mul_apply]
  change (n:ℂ) • ((-(sourceTime 0:ℂ)/4) •
    ((reciprocalVolume z:ℂ) • (((inverseAction^(n+2)) f) z)))=_
  rw [inverse_power_apply]
  apply PiLp.ext
  intro word
  change (n:ℂ)*((-(sourceTime 0:ℂ)/4)*((reciprocalVolume z:ℂ)*((reciprocal z:ℂ)^(n+2)*f z word)))=
    (profileCoefficient n z:ℂ)*f z word
  unfold profileCoefficient
  push_cast
  ring

private theorem weight_contact (a : ScalarIndex) :
    multiply scalarWeight scalarWeight_smooth*GaussRadialMomentum.commutatorAction (scalarDirection a)=
      Complex.I • (SourceGammaNativeBudget.scalarColumn a*powerProfile 1) := by
  rw [power_profile_real]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (scalarWeight z:ℂ)*((-Complex.I)*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)*f z word)=
    Complex.I*((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z:ℂ)*
      ((profileCoefficient 1 z:ℂ)*f z word))
  unfold scalarWeight GaussRadialMomentum.radialDerivative SourceClosedCostNativeProbe.coordinate
    profileCoefficient reciprocalVolume reciprocal
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

private theorem contact_weight (a : ScalarIndex) :
    GaussRadialMomentum.commutatorAction (scalarDirection a)*multiply scalarWeight scalarWeight_smooth=
      Complex.I • (powerProfile 1*SourceGammaNativeBudget.scalarColumn a) := by
  rw [power_profile_real]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change ((-Complex.I)*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ))*
      ((scalarWeight z:ℂ)*f z word)=
    Complex.I*((profileCoefficient 1 z:ℂ)*
      ((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z:ℂ)*f z word))
  unfold scalarWeight GaussRadialMomentum.radialDerivative SourceClosedCostNativeProbe.coordinate
    profileCoefficient reciprocalVolume reciprocal
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

private theorem contact_term (A W C Q G P : End)
    (hw : W*C=Complex.I • (Q*G)) (hc : C*W=Complex.I • (G*Q)) :
    A*W*C+C*W*P=Complex.I • (A*Q*G+G*(Q*P)) := by
  calc
    _=A*(W*C)+(C*W)*P := by noncomm_ring
    _=A*(Complex.I • (Q*G))+(Complex.I • (G*Q))*P := by rw [hw,hc]
    _=_ := by simp only [mul_smul_comm,smul_mul_assoc,←smul_add,mul_assoc]

private theorem base_current : GaussRadialHamiltonian.radialAction=eulerForm (powerProfile 1) := by
  have h (a : ScalarIndex) : GaussRadialHamiltonian.radialTerm (scalarDirection a)=
      Complex.I • (GaussMomentumAdjoint.adjoint (scalarDirection a)*
        SourceGammaNativeBudget.scalarColumn a*powerProfile 1+
        powerProfile 1*(SourceGammaNativeBudget.scalarColumn a*covariantMomentum (scalarDirection a))) := by
    simpa only [GaussRadialHamiltonian.radialTerm,←Module.End.mul_eq_comp,mul_assoc] using!
      contact_term (GaussMomentumAdjoint.adjoint (scalarDirection a)) (multiply scalarWeight scalarWeight_smooth)
        (GaussRadialMomentum.commutatorAction (scalarDirection a)) (SourceGammaNativeBudget.scalarColumn a)
        (powerProfile 1) (covariantMomentum (scalarDirection a)) (weight_contact a) (contact_weight a)
  have he : GaussRadialHamiltonian.radialAction=(Complex.I/2) •
      (radialAdjoint*powerProfile 1+powerProfile 1*radialMomentum) := by
    simp only [GaussRadialHamiltonian.radialAction,h,←Finset.smul_sum,smul_smul,Finset.sum_add_distrib,
      ←Finset.sum_mul,←Finset.mul_sum,radialAdjoint,radialMomentum]
    congr 1
    ring
  rw [he,scalar_adjoint_contraction,scalar_native_contraction]
  simp only [smul_mul_assoc,mul_smul_comm,←smul_add,smul_smul]
  have hi : (Complex.I/2)*(-Complex.I)=(1/2:ℂ) := by
    calc _= -(Complex.I*Complex.I)/2 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi]
  unfold eulerForm
  simp only [add_mul,smul_mul_assoc,one_mul]
  module

private theorem euler_inverse : bracket scalarEulerAction inverseAction=inverseAction^3-inverseAction := by
  have hd (z : SourceCoordinateSlice) : fderiv ℝ reciprocal z (scalarEuler z)=reciprocal z^3-reciprocal z := by
    rw [GaussRadialMomentum.reciprocal_derivative]
    change -inner ℝ (z.2.1:Scalar) (z.2.1:Scalar)/(4*radius z^3)=_
    rw [real_inner_self_eq_norm_sq]
    have hs := Real.sq_sqrt (show 0≤1+‖(z.2.1:Scalar)‖^2/4 by positivity)
    change radius z^2=1+‖(z.2.1:Scalar)‖^2/4 at hs
    unfold reciprocal
    field_simp [(radius_pos z).ne']
    nlinarith only [hs]
  have he (f : QuantumTest) (z : SourceCoordinateSlice) :
      scalarEulerAction (inverseAction f) z=reciprocal z • scalarEulerAction f z+
        (reciprocal z^3-reciprocal z) • f z := by
    rw [scalar_euler_apply,GaussRadialMomentum.inverseAction_real,
      fderiv_fun_smul (reciprocal_smooth.differentiable (by simp)).differentiableAt
        (f.contDiff.differentiable (by simp)).differentiableAt]
    change reciprocal z • fderiv ℝ f z (scalarEuler z)+
      fderiv ℝ reciprocal z (scalarEuler z) • f z=_
    rw [hd,scalar_euler_apply]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change scalarEulerAction (inverseAction f) z-inverseAction (scalarEulerAction f) z=
    ((inverseAction^3) f) z-inverseAction f z
  rw [he,inverse_power_apply]
  change reciprocal z • scalarEulerAction f z+(reciprocal z^3-reciprocal z) • f z-
    (reciprocal z:ℂ) • scalarEulerAction f z=
      (reciprocal z:ℂ)^3 • f z-(reciprocal z:ℂ) • f z
  rw [real_fock_smul,real_fock_smul]
  push_cast
  module

private theorem bracket_product (A B C : End) :
    bracket A (B*C)=bracket A B*C+B*bracket A C := by unfold bracket;noncomm_ring

private theorem euler_power (n : ℕ) :
    bracket scalarEulerAction (inverseAction^n)=(n:ℂ) • (inverseAction^n*(inverseAction^2-1)) := by
  induction n with
  | zero => simp [bracket]
  | succ n ih =>
    rw [pow_succ,bracket_product,ih,euler_inverse]
    have he : inverseAction^n*(inverseAction^3-inverseAction)=inverseAction^(n+1)*(inverseAction^2-1) := by
      rw [pow_succ]
      noncomm_ring
    have hn : (inverseAction^n*(inverseAction^2-1))*inverseAction=inverseAction^(n+1)*(inverseAction^2-1) := by
      rw [pow_succ]
      noncomm_ring
    simp only [Nat.cast_succ,add_smul,one_smul,smul_mul_assoc]
    rw [he,hn]
    simp only [pow_succ]

private theorem profile_recursion (n : ℕ) :
    powerProfile n*inverseAction+inverseAction^n*powerProfile 1=powerProfile (n+1) := by
  have hn : (alpha*inverseAction^(n+2))*inverseAction=alpha*inverseAction^(n+3) := by
    rw [mul_assoc,←pow_succ]
  have hb : inverseAction^n*(alpha*inverseAction^3)=alpha*inverseAction^(n+3) := by
    calc
      _=(inverseAction^n*alpha)*inverseAction^3 := by rw [mul_assoc]
      _=(alpha*inverseAction^n)*inverseAction^3 := by rw [(alpha_inverse.pow_right n).symm.eq]
      _=_ := by rw [mul_assoc,←pow_add]
  simp only [powerProfile,Nat.cast_one,one_smul,smul_mul_assoc]
  change (n:ℂ) • ((alpha*inverseAction^(n+2))*inverseAction)+
    inverseAction^n*(alpha*inverseAction^3)=((n+1:ℕ):ℂ) • (alpha*inverseAction^(n+3))
  rw [Nat.cast_add,Nat.cast_one,hn,hb,add_smul,one_smul]

private theorem profile_residual (n : ℕ) :
    powerProfile n*bracket scalarEulerAction inverseAction-
      bracket scalarEulerAction (inverseAction^n)*powerProfile 1=0 := by
  have hA2 : Commute alpha (inverseAction^2-1) :=
    (alpha_inverse.pow_right 2).sub_right (Commute.one_right alpha)
  have hc : inverseAction^n*(inverseAction^2-1)*(alpha*inverseAction^3)=
      alpha*inverseAction^n*((inverseAction^2-1)*inverseAction^3) := by
    calc
      _=(inverseAction^n*((inverseAction^2-1)*alpha))*inverseAction^3 := by noncomm_ring
      _=(inverseAction^n*(alpha*(inverseAction^2-1)))*inverseAction^3 := by rw [hA2.symm.eq]
      _=((inverseAction^n*alpha)*(inverseAction^2-1))*inverseAction^3 := by noncomm_ring
      _=((alpha*inverseAction^n)*(inverseAction^2-1))*inverseAction^3 := by rw [(alpha_inverse.pow_right n).symm.eq]
      _=_ := by noncomm_ring
  have he : (alpha*inverseAction^(n+2))*(inverseAction^3-inverseAction)=
      inverseAction^n*(inverseAction^2-1)*(alpha*inverseAction^3) := by
    rw [hc,pow_add]
    noncomm_ring
  rw [euler_inverse,euler_power]
  simp only [powerProfile,Nat.cast_one,one_smul,smul_mul_assoc]
  rw [he,sub_self]

private theorem euler_form_product (P B G S : End) :
    eulerForm P*S+B*eulerForm G=eulerForm (P*S+B*G)+
      (1/2:ℂ) • (P*bracket scalarEulerAction S-bracket scalarEulerAction B*G) := by
  simp only [eulerForm,bracket,mul_add,mul_sub,add_mul,sub_mul,smul_add,smul_sub,
    smul_mul_assoc,mul_smul_comm,mul_assoc]
  module

private theorem power_current (n : ℕ) : radialPowerCurrent n=eulerForm (powerProfile n) := by
  induction n with
  | zero => simp [radialPowerCurrent,powerProfile,eulerForm]
  | succ n ih =>
    rw [radialPowerCurrent,ih,base_current,euler_form_product,profile_recursion,profile_residual,
      smul_zero,add_zero]

private theorem euler_project (g : Label) : Commute scalarEulerAction (project g) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change scalarEulerAction (project g f) z=project g (scalarEulerAction f) z
  rw [scalar_euler_apply,derivative_project,project_apply,scalar_euler_apply]

private theorem graded_profile_sum (sharp : Bool) :
    gradedProfile sharp=∑ g : Label,powerProfile (exponent sharp g)*project g := by
  simp only [gradedProfile,powerProfile,alpha,Finset.mul_sum,mul_smul_comm,smul_mul_assoc,
    Finset.smul_sum,mul_assoc]
  apply Finset.sum_congr rfl
  intro g _
  exact smul_comm _ _ _

/-- The complete finite source recurrence returns the true scalar61 Euler current on both orientations. -/
theorem original_graded_euler_current (sharp : Bool) :
    gradedRadialCurrent sharp=(1/2:ℂ) •
      (scalarEulerAction*gradedProfile sharp+gradedProfile sharp*scalarEulerAction+(61:ℂ) • gradedProfile sharp) := by
  have h (g : Label) : eulerForm (powerProfile (exponent sharp g))*project g=
      eulerForm (powerProfile (exponent sharp g)*project g) := by
    unfold eulerForm
    simp only [smul_mul_assoc,add_mul,smul_mul_assoc,mul_assoc]
    rw [←(euler_project g).eq]
  rw [gradedRadialCurrent]
  simp_rw [power_current,h]
  rw [graded_profile_sum]
  simp only [eulerForm,Finset.mul_sum,Finset.sum_mul,Finset.smul_sum,smul_add,
    Finset.sum_add_distrib]

private theorem profile_pair (sharp : Bool) (p q : QuantumTest) :
    sourcePair p (gradedProfile sharp q)=sourcePair (gradedProfile sharp p) q := by
  rw [graded_profile_sum]
  simp only [LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro g _
  change sourcePair p (powerProfile (exponent sharp g) (project g q))=
    sourcePair (powerProfile (exponent sharp g) (project g p)) q
  rw [power_profile_real,multiply_pair,project_pair]
  have he := commutes_real g (profileCoefficient (exponent sharp g)) (profile_smooth _) p
  exact congrArg (fun f : QuantumTest => sourcePair f q) he

private theorem pair_add_right (p q r : QuantumTest) : sourcePair p (q+r)=sourcePair p q+sourcePair p r := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_smul_right (c : ℂ) (p q : QuantumTest) : sourcePair p (c • q)=c*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_right]

/-- The real generated profile leaves one complex Euler flux; the true61 divergence cancels internally. -/
theorem original_graded_euler_pair (sharp : Bool) (p q : QuantumTest) :
    sourcePair p (gradedRadialCurrent sharp q)=(1/2:ℂ)*
      (sourcePair (gradedProfile sharp p) (scalarEulerAction q)-sourcePair (scalarEulerAction p) (gradedProfile sharp q)) := by
  rw [original_graded_euler_current]
  simp only [LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,pair_smul_right,pair_add_right]
  have h := scalar_euler_current p (gradedProfile sharp q)
  rw [profile_pair sharp p (scalarEulerAction q)]
  linear_combination (norm := ring) (1/2:ℂ)*h

end LowEnergy.SourceClockYukawaGradedEuler
