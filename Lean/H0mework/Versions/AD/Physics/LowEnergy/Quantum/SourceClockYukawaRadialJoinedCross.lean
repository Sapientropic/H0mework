import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialCross
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialJoinedCross
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open SourceYukawaCoefficientCommutator SourceScalarGaugeForce PositiveScalarWeakBudget PositiveScalarCoefficientDecay
open scoped ContDiff InnerProductSpace BigOperators
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] fullAction compressionCore defectAction

/-- The native joined Z keeps its window and both derivative peaks in one source word. -/
def joinedCore (sharp : Bool) (m ell : ℕ) : End := (-(sourceTime 0:ℂ)/4) •
  (inverseVolumeAction*inverseAction^3*∑ a : ScalarIndex,
    SourceClosedCostNativeProbe.coordinateAction (scalarDirection a)*coefficient sharp a m ell)

private def profileCoefficient (z : SourceCoordinateSlice) : ℝ :=
  -sourceTime 0/4*reciprocalVolume z*reciprocal z^3
private theorem profile_smooth (z : physicalChart) : ContDiffAt ℝ ∞ profileCoefficient z.val :=
  (contDiffAt_const.mul (reciprocal_volume_smooth z)).mul (reciprocal_smooth.pow 3).contDiffAt
private def profile : End := multiply profileCoefficient profile_smooth

private theorem inverse_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((inverseAction^n) f) z=(reciprocal z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (reciprocal z:ℂ) • (((inverseAction^n) f) z)=_
    rw [ih,pow_succ',mul_smul]

private theorem profile_return : profile=(-(sourceTime 0:ℂ)/4) • (inverseVolumeAction*inverseAction^3) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.smul_apply,Module.End.mul_apply]
  change (profileCoefficient z:ℂ) • f z=(-(sourceTime 0:ℂ)/4) •
    ((inverseVolumeAction ((inverseAction^3) f)) z)
  rw [inverseVolumeAction,multiply_apply,inverse_power_apply]
  simp only [smul_smul]
  congr 1
  unfold profileCoefficient
  push_cast
  ring

private theorem real_real (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (fullAction sharp) := by
  unfold fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (sourceMap (scalarField z)) (c z:ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z:ℂ) (f z)).symm

private theorem real_theta (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (m ell : ℕ) :
    Commute (multiply c hc) (SourceMixedNativeReturn.thetaAction m ell) := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact real_real _ _ _ _

private theorem real_constant (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (v : Scalar) :
    Commute (multiply c hc) (constantAction sharp v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (branchMap sharp v) (c z:ℂ) (f z)).symm

private theorem real_contact (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (v : Ambient) (m ell : ℕ) :
    Commute (multiply c hc) (SourceNativeCutoffContact.contactAction v m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z:ℂ) ((-Complex.I)*(SourceNativeCutoffContact.thetaDerivative v m ell z:ℂ)) (f z)

private theorem real_coefficient (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    Commute (multiply c hc) (coefficient sharp a m ell) := by
  unfold coefficient
  exact ((real_constant c hc sharp (scalarDirection a).1).mul_right (real_theta c hc m ell)).add_right
    (((real_full c hc sharp).mul_right (real_contact c hc (scalarDirection a) m ell)).smul_right Complex.I)

private theorem native_joined (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    bracket (covariantMomentum (scalarDirection a)) (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell)=
      (-Complex.I) • coefficient sharp a m ell := by
  have hy : bracket (covariantMomentum (scalarDirection a)) (fullAction sharp)=
      (-Complex.I) • constantAction sharp (scalarDirection a).1 := by
    apply LinearMap.ext
    intro f
    change covariantMomentum (scalarDirection a) (fullAction sharp f)-fullAction sharp (covariantMomentum (scalarDirection a) f)=_
    rw [original_full_momentum,add_sub_cancel_left]
    rfl
  have ht : bracket (covariantMomentum (scalarDirection a)) (SourceMixedNativeReturn.thetaAction m ell)=
      SourceNativeCutoffContact.contactAction (scalarDirection a) m ell := by
    apply LinearMap.ext
    intro f
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
    rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial,
      SourceNativeCutoffContact.native_core_contact,add_sub_cancel_left]
  have hp (P A B : End) : bracket P (A*B)=bracket P A*B+A*bracket P B := by unfold bracket;noncomm_ring
  rw [hp,hy,ht]
  have hi : (-Complex.I)*Complex.I=1 := by rw [neg_mul,Complex.I_mul_I,neg_neg]
  simp only [coefficient,smul_add,smul_mul_assoc,smul_smul,hi,one_smul]

private theorem adjoint_joined (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    bracket (GaussMomentumAdjoint.adjoint (scalarDirection a)) (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell)=
      (-Complex.I) • coefficient sharp a m ell := by
  have ht : bracket (GaussMomentumAdjoint.adjoint (scalarDirection a)) (SourceMixedNativeReturn.thetaAction m ell)=
      SourceNativeCutoffContact.contactAction (scalarDirection a) m ell := by
    apply LinearMap.ext
    intro f
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
    rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial,
      SourceNativeCutoffContact.sharp_core_contact,add_sub_cancel_left]
  have hp (P A B : End) : bracket P (A*B)=bracket P A*B+A*bracket P B := by unfold bracket;noncomm_ring
  rw [hp,native_full_adjoint_commutator,ht]
  have hi : (-Complex.I)*Complex.I=1 := by rw [neg_mul,Complex.I_mul_I,neg_neg]
  simp only [coefficient,smul_add,smul_mul_assoc,smul_smul,hi,one_smul]

private theorem radial_commutes_joined (sharp : Bool) (v : Ambient) (m ell : ℕ) :
    Commute (GaussRadialMomentum.commutatorAction v) (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell) := by
  have hr : GaussRadialMomentum.commutatorAction v=(-Complex.I) •
      multiply (GaussRadialMomentum.radialDerivative v) (fun _ => (GaussRadialMomentum.radialDerivative_smooth v).contDiffAt) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change ((-Complex.I)*(GaussRadialMomentum.radialDerivative v z:ℂ)) • f z=
      (-Complex.I) • ((GaussRadialMomentum.radialDerivative v z:ℂ) • f z)
    exact mul_smul _ _ _
  rw [hr]
  exact ((real_full _ _ sharp).mul_right (real_theta _ _ m ell)).smul_left _

private theorem radial_term_joined (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    bracket (GaussRadialHamiltonian.radialTerm (scalarDirection a)) (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell)=
      (-Complex.I) •
        (coefficient sharp a m ell*multiply scalarWeight scalarWeight_smooth*GaussRadialMomentum.commutatorAction (scalarDirection a)+
        GaussRadialMomentum.commutatorAction (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*coefficient sharp a m ell) := by
  let A : End := fullAction sharp*SourceMixedNativeReturn.thetaAction m ell
  have hw : bracket (multiply scalarWeight scalarWeight_smooth) A=0 :=
    sub_eq_zero.mpr ((real_full _ _ sharp).mul_right (real_theta _ _ m ell)).eq
  have hc : bracket (GaussRadialMomentum.commutatorAction (scalarDirection a)) A=0 :=
    sub_eq_zero.mpr (radial_commutes_joined sharp (scalarDirection a) m ell).eq
  have hp := native_joined sharp a m ell
  have ha := adjoint_joined sharp a m ell
  have prod (P Q A : End) : bracket (P*Q) A=P*bracket Q A+bracket P A*Q := by unfold bracket;noncomm_ring
  have add (P Q A : End) : bracket (P+Q) A=bracket P A+bracket Q A := by unfold bracket;noncomm_ring
  unfold GaussRadialHamiltonian.radialTerm
  change bracket (GaussMomentumAdjoint.adjoint (scalarDirection a)*(multiply scalarWeight scalarWeight_smooth*
      GaussRadialMomentum.commutatorAction (scalarDirection a))+GaussRadialMomentum.commutatorAction (scalarDirection a)*
      (multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a))) A=_
  rw [add,prod,prod,prod,prod,hw,hc,hp,ha]
  simp only [mul_zero,zero_mul,zero_add,add_zero,mul_smul_comm,smul_mul_assoc,mul_assoc,smul_add]

private theorem weight_contact (a : ScalarIndex) :
    multiply scalarWeight scalarWeight_smooth*GaussRadialMomentum.commutatorAction (scalarDirection a)=
      Complex.I • (SourceClosedCostNativeProbe.coordinateAction (scalarDirection a)*profile) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (scalarWeight z:ℂ)*((-Complex.I)*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)*f z word)=
    Complex.I*((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z:ℂ)*((profileCoefficient z:ℂ)*f z word))
  unfold scalarWeight GaussRadialMomentum.radialDerivative SourceClosedCostNativeProbe.coordinate
    profileCoefficient reciprocalVolume reciprocal
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

private theorem contact_weight (a : ScalarIndex) :
    GaussRadialMomentum.commutatorAction (scalarDirection a)*multiply scalarWeight scalarWeight_smooth=
      Complex.I • (profile*SourceClosedCostNativeProbe.coordinateAction (scalarDirection a)) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change ((-Complex.I)*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ))*((scalarWeight z:ℂ)*f z word)=
    Complex.I*((profileCoefficient z:ℂ)*((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z:ℂ)*f z word))
  unfold scalarWeight GaussRadialMomentum.radialDerivative SourceClosedCostNativeProbe.coordinate
    profileCoefficient reciprocalVolume reciprocal
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

private theorem local_row_return (Z Q G : End) (hZQ : Commute Z Q) (hQG : Commute Q G) (hZG : Commute Z G) :
    (-Complex.I) • (Z*(Complex.I • (Q*G))+(Complex.I • (G*Q))*Z)=(2:ℂ) • (G*Q*Z) := by
  have hi : (-Complex.I)*Complex.I=1 := by rw [neg_mul,Complex.I_mul_I,neg_neg]
  simp only [mul_smul_comm,smul_mul_assoc,←smul_add,smul_smul,hi,one_smul]
  have h : Z*(Q*G)=G*Q*Z := by
    calc
      _=(Z*Q)*G := by rw [mul_assoc]
      _=(Q*Z)*G := by rw [hZQ.eq]
      _=Q*(Z*G) := by rw [mul_assoc]
      _=Q*(G*Z) := by rw [hZG.eq]
      _=_ := by rw [←mul_assoc,hQG.eq]
  rw [h]
  module

private theorem radial_row_return (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    bracket (GaussRadialHamiltonian.radialTerm (scalarDirection a)) (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell)=
      (2:ℂ) • (profile*SourceClosedCostNativeProbe.coordinateAction (scalarDirection a)*coefficient sharp a m ell) := by
  rw [radial_term_joined]
  change (-Complex.I) •
    (coefficient sharp a m ell*(multiply scalarWeight scalarWeight_smooth*GaussRadialMomentum.commutatorAction (scalarDirection a))+
    (GaussRadialMomentum.commutatorAction (scalarDirection a)*multiply scalarWeight scalarWeight_smooth)*coefficient sharp a m ell)=_
  rw [weight_contact,contact_weight]
  apply local_row_return
  · exact (real_coefficient _ _ sharp a m ell).symm
  · exact real_real _ _ _ _
  · exact (real_coefficient _ _ sharp a m ell).symm

/-- The original native70 and its independent density transpose return one joined Z word; the 61 divergence exits internally. -/
theorem original_radial_joined_yukawa_cross (sharp : Bool) (m ell : ℕ) :
    bracket GaussRadialHamiltonian.radialAction (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell)=joinedCore sharp m ell := by
  have hsum : bracket GaussRadialHamiltonian.radialAction (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell)=
      (1/2:ℂ) • ∑ a : ScalarIndex,bracket (GaussRadialHamiltonian.radialTerm (scalarDirection a))
        (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell) := by
    simp only [GaussRadialHamiltonian.radialAction,bracket,smul_mul_assoc,mul_smul_comm,←smul_sub,
      Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
  rw [hsum]
  simp_rw [radial_row_return]
  rw [←Finset.smul_sum,smul_smul]
  norm_num
  change (∑ a : ScalarIndex,profile*(SourceClosedCostNativeProbe.coordinateAction (scalarDirection a)*coefficient sharp a m ell))=_
  rw [←Finset.mul_sum,profile_return]
  simp only [smul_mul_assoc,joinedCore,mul_assoc]

/-- The same actual compression retains its whole radial/Y-window defect. -/
theorem actual_corrected_radial_joined_yukawa_cross (sharp : Bool) (m ell : ℕ) (F : Index) :
    bracket (SourceRadiusResponseDecay.radialCurrent F) (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell)=
      joinedCore sharp m ell-bracket (bracket (defectAction F) inverseAction)
        (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell) := by
  have h := original_radial_joined_yukawa_cross sharp m ell
  unfold SourceRadiusResponseDecay.radialCurrent bracket at *
  linear_combination (norm := noncomm_ring) h

end LowEnergy.SourceClockYukawaRadialJoinedCross
