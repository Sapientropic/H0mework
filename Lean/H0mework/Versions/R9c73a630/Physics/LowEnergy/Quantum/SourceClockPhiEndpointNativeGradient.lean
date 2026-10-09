import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseHessian
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponsePositiveSource
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockSourceTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiEndpointNativeGradient
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open GaussNativePotential GaussYukawaCoefficient GaussRadialMomentum GaussNativeMatter GaussQuantumMultiplier
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourcePhysicalKineticSquare SourceClockAcceleration SourceClockReflectedForm
open SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarInverseBulk
open SourceScalarDoubleCurrent SourceScalarPairedTransport
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiRadiusResponseNativeBudget
open SourceClockYukawaCubicCurrent
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev Q : End := 1-S
private abbrev D (a : ScalarIndex) : End := phiDirectionAction (scalarBasis a)
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev B (m ell : ℕ) : End := SourceClockPhiRadiusResponseHessian.phiFirstPeak m ell
private abbrev d (a : ScalarIndex) : End := D a*S^2
attribute [local irreducible] resolventCore compressionCore defectAction diagonalAction

private theorem real_commute (c b : SourceCoordinateSlice → ℝ)
    (hc : ∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hb : ∀z:physicalChart,ContDiffAt ℝ ∞ b z.val) : Commute (multiply c hc) (multiply b hb) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (b z:ℂ) (f z)
private theorem phi_pos (z : SourceCoordinateSlice) : 0 < phiRadius z := by
  unfold phiRadius SourceClockRadiusResponseAffine.affineRadius
  positivity
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul]
  have h : (phiReciprocal z:ℂ)*(phiRadius z:ℂ)=1 := by
    unfold phiReciprocal
    push_cast
    field_simp [(phi_pos z).ne']
  rw [h,one_smul]
private theorem radius_inverse : r*S=(1:End) :=
  (real_commute _ _ _ _).eq.symm.trans inverse_radius
private theorem inverse_D (a : ScalarIndex) : Commute S (D a) := real_commute _ _ _ _
private theorem inverse_d (a : ScalarIndex) : Commute S (d a) :=
  (inverse_D a).mul_right ((Commute.refl S).pow_right 2)
private theorem inverse_P (a : ScalarIndex) :
    bracket (P a) S=(-Complex.I) • d a := by
  have h : bracket (P a) r=Complex.I • D a :=
    (original_phi_radius_native_jet (scalarDirection a)).1
  have hm : bracket (P a) S= -(S*bracket (P a) r*S) := by
    have h1 : S*P a*r*S=S*P a := by
      calc _=S*P a*(r*S) := by noncomm_ring
           _=_ := by rw [radius_inverse,mul_one]
    have h2 : S*r*P a*S=P a*S := by rw [inverse_radius,one_mul]
    calc _= -(S*P a*r*S-S*r*P a*S) := by rw [h1,h2];unfold bracket;abel
         _=_ := by unfold bracket;noncomm_ring
  rw [hm,h]
  have hd : S*D a*S=d a := by
    rw [(inverse_D a).eq]
    change D a*S*S=D a*S^2
    rw [pow_two,mul_assoc]
  simp only [mul_smul_comm,smul_mul_assoc,neg_smul,hd]

private theorem Q_commute {A : End} (h : Commute S A) : Commute Q A :=
  (Commute.one_left A).sub_left h
private theorem first_commute {A : End} (h : Commute S A) (m ell : ℕ) : Commute (B m ell) A :=
  (((Q_commute h).pow_left ell).smul_left _).sub_left (((Q_commute h).pow_left m).smul_left _)
private theorem theta_commute {A : End} (h : Commute S A) (m ell : ℕ) : Commute (T m ell) A :=
  ((Q_commute h).pow_left (m+1)).sub_left ((Q_commute h).pow_left (ell+1))
private theorem bracket_product (A X Y : End) : bracket A (X*Y)=bracket A X*Y+X*bracket A Y := by
  unfold bracket;noncomm_ring
private theorem bracket_sub (A X Y : End) : bracket A (X-Y)=bracket A X-bracket A Y := by
  unfold bracket;noncomm_ring
private theorem bracket_smul (A X : End) (c : ℂ) : bracket A (c • X)=c • bracket A X := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem inverse_Q (a : ScalarIndex) : bracket (P a) Q=Complex.I • d a := by
  rw [bracket_sub]
  have hz : bracket (P a) (1:End)=0 := by simp [bracket]
  rw [hz,inverse_P,zero_sub,neg_smul,neg_neg]
private theorem geometric_successor (a : ScalarIndex) (k : ℕ) :
    bracket (P a) (Q^(k+1))=((k+1:ℂ)*Complex.I) • (Q^k*d a) := by
  induction k with
  | zero => simpa only [zero_add,Nat.cast_zero,pow_one,pow_zero,one_mul] using inverse_Q a
  | succ k ih =>
    rw [show k+1+1=(k+1)+1 from rfl,pow_succ,bracket_product,ih,inverse_Q]
    have hm : (Q^k*d a)*Q=Q^(k+1)*d a := by
      rw [mul_assoc,(Q_commute (inverse_d a)).symm.eq,←mul_assoc,←pow_succ]
    simp only [smul_mul_assoc,mul_smul_comm]
    rw [hm]
    push_cast
    simp only [pow_succ]
    module
private theorem theta_native (a : ScalarIndex) (m ell : ℕ) :
    bracket (P a) (T m ell)=(-Complex.I) • (B m ell*d a) := by
  rw [T,phiThetaAction,bracket_sub,geometric_successor,geometric_successor]
  simp only [B,SourceClockPhiRadiusResponseHessian.phiFirstPeak,sub_mul,smul_mul_assoc,smul_sub,smul_smul]
  module
private theorem theta_square_native (a : ScalarIndex) (m ell : ℕ) :
    bracket (P a) ((T m ell)^2)=(-2*Complex.I) • (T m ell*B m ell*d a) := by
  rw [pow_two,bracket_product,theta_native]
  have hc : Commute (T m ell) (B m ell*d a) :=
    ((first_commute ((theta_commute (Commute.refl S) m ell).symm) m ell).symm.mul_right
      ((theta_commute (inverse_D a) m ell).mul_right ((theta_commute (Commute.refl S) m ell).pow_right 2)))
  simp only [smul_mul_assoc,mul_smul_comm]
  rw [←hc.eq]
  simp only [←mul_assoc]
  module
private theorem inverse_theta_square_native (a : ScalarIndex) (m ell : ℕ) :
    bracket (P a) (S*(T m ell)^2)=(-Complex.I) •
      (d a*(T m ell)^2+(2:ℂ) • (S*T m ell*B m ell*d a)) := by
  rw [bracket_product,inverse_P,theta_square_native]
  simp only [smul_mul_assoc,mul_smul_comm,smul_add,smul_smul]
  module

def endpointNativeGradient (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) (a : ScalarIndex) : QuantumTest :=
  let q := resolventCore F z hz (coreEquiv.symm g)
  let h := resolventCore F z hz (r (coreEquiv.symm g))
  Complex.I • (bracket (P a) ((T m ell)^2) q-
    bracket (P a) (S*(T m ell)^2) h)

private theorem native_gradient_generic (m ell : ℕ) (a : ScalarIndex) (q h : QuantumTest) :
    Complex.I • (bracket (P a) ((T m ell)^2) q-
      bracket (P a) (S*(T m ell)^2) h)=
      D a (((2:ℂ) • (S^3*B m ell) (T m ell (r q-h)))-
        (S^2*(T m ell)^2) h) := by
  have hST : Commute S (T m ell) := (theta_commute (Commute.refl S) m ell).symm
  have hBT : Commute (B m ell) (T m ell) := first_commute hST m ell
  have hBD : Commute (B m ell) (D a) := first_commute (inverse_D a) m ell
  have hTD : Commute (T m ell) (D a) := theta_commute (inverse_D a) m ell
  have hSD : Commute S (D a) := inverse_D a
  have hSr : S*r=(1:End) := inverse_radius
  have hrS : r*S=(1:End) := radius_inverse
  have hSrC : Commute S r := by
    change S*r=r*S
    rw [hSr,hrS]
  have hBr : Commute (B m ell) r := first_commute hSrC m ell
  have hTr : Commute (T m ell) r := theta_commute hSrC m ell
  have hTBD : Commute (T m ell*B m ell) (D a) := hTD.mul_left hBD
  have hTBS : Commute (T m ell*B m ell) S :=
    hST.symm.mul_left (first_commute (Commute.refl S) m ell)
  have h1 : T m ell*B m ell*d a=D a*S^2*(T m ell*B m ell) := by
    change T m ell*B m ell*(D a*S^2)=_
    calc
      _=(T m ell*B m ell)*(D a)*S^2 := by noncomm_ring
      _=D a*(T m ell*B m ell)*S^2 := by rw [hTBD.eq]
      _=D a*S^2*(T m ell*B m ell) := by
        calc
          _=D a*((T m ell*B m ell)*S^2) := by noncomm_ring
          _=D a*(S^2*(T m ell*B m ell)) :=
            congrArg (fun X : End => D a*X) (hTBS.pow_right 2).eq
          _=_ := by noncomm_ring
  have hS3r : S^3*r=S^2 := by
    calc _=S^2*(S*r) := by noncomm_ring
         _=_ := by rw [hSr,mul_one]
  have hq : T m ell*B m ell*d a=D a*S^3*B m ell*T m ell*r := by
    rw [h1]
    have hBTr : Commute (B m ell*T m ell) r := hBr.mul_left hTr
    calc
      D a*S^2*(T m ell*B m ell)=D a*S^2*(B m ell*T m ell) := by rw [hBT.eq]
      _=D a*S^3*B m ell*T m ell*r := by
        have ht : S^3*B m ell*T m ell*r=S^2*(B m ell*T m ell) := by
          calc
            _=S^3*((B m ell*T m ell)*r) := by noncomm_ring
            _=S^3*(r*(B m ell*T m ell)) := by rw [hBTr.eq]
            _=(S^3*r)*(B m ell*T m ell) := by noncomm_ring
            _=_ := by rw [hS3r]
        calc
          _=D a*(S^2*(B m ell*T m ell)) := by noncomm_ring
          _=D a*(S^3*B m ell*T m ell*r) :=
            congrArg (fun X : End => D a*X) ht.symm
          _=_ := by noncomm_ring
  have hh : S*T m ell*B m ell*d a=D a*S^3*B m ell*T m ell := by
    calc
      _=S*(T m ell*B m ell*d a) := by noncomm_ring
      _=S*(D a*S^2*(T m ell*B m ell)) := by rw [h1]
      _=D a*S^3*(T m ell*B m ell) := by
        calc
          _=(S*D a)*S^2*(T m ell*B m ell) := by noncomm_ring
          _=(D a*S)*S^2*(T m ell*B m ell) := by rw [hSD.eq]
          _=_ := by noncomm_ring
      _=D a*S^3*(B m ell*T m ell) :=
        congrArg (fun X : End => D a*S^3*X) hBT.eq.symm
      _=_ := by noncomm_ring
  have hi1 : Complex.I*(-2*Complex.I)=2 := by
    calc _= -2*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  have hi2 : Complex.I*(-Complex.I)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [theta_square_native,inverse_theta_square_native]
  simp only [LinearMap.smul_apply,smul_sub,smul_smul,hi1,hi2,one_smul]
  rw [hq,hh]
  simp only [d,Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply,
    map_sub,map_smul]
  module

/-- The complete native source column keeps the true fixed rho g resolvent leg. -/
theorem actual_endpoint_native_gradient (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) (a : ScalarIndex) :
    endpointNativeGradient m ell F z hz g a=
      D a (((2:ℂ) • (S^3*B m ell) (phiResponseCore m ell F z hz g))-
        (S^2*(T m ell)^2) (resolventCore F z hz (r (coreEquiv.symm g)))) := by
  change Complex.I • (bracket (P a) ((T m ell)^2)
    (resolventCore F z hz (coreEquiv.symm g))-
    bracket (P a) (S*(T m ell)^2)
      (resolventCore F z hz (r (coreEquiv.symm g))))=_
  have hv : phiResponseCore m ell F z hz g=
      T m ell (r (resolventCore F z hz (coreEquiv.symm g))-
        resolventCore F z hz (r (coreEquiv.symm g))) := rfl
  rw [hv]
  exact native_gradient_generic m ell a
    (resolventCore F z hz (coreEquiv.symm g))
    (resolventCore F z hz (r (coreEquiv.symm g)))

private abbrev U : End := inverseVolumeAction
private abbrev n : ℝ := sourceTime 0
private def movingCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  2*phiReciprocal z^3*((ell+1:ℝ)*(1-phiReciprocal z)^ell-
    (m+1:ℝ)*(1-phiReciprocal z)^m)
private def fixedCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  phiReciprocal z^2*((1-phiReciprocal z)^(m+1)-
    (1-phiReciprocal z)^(ell+1))^2
private theorem one_le_phi (z:SourceCoordinateSlice) : 1 ≤ phiRadius z := by
  have hp := (phi_pos z).le
  have hs : phiRadius z^2=1+‖scalarField z‖^2/4 := Real.sq_sqrt (by positivity)
  nlinarith only [hp,hs,sq_nonneg ‖scalarField z‖]
private theorem reciprocal_smooth : ContDiff ℝ ∞ phiReciprocal :=
  SourceClockRadiusResponseAffine.affine_radius_smooth.inv (fun z=>(phi_pos z).ne')
private theorem moving_smooth (m ell : ℕ) : ContDiff ℝ ∞ (movingCoefficient m ell) :=
  (contDiff_const.mul (reciprocal_smooth.pow 3)).mul
    (((contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow ell)).sub
      (contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow m))))
private theorem fixed_smooth (m ell : ℕ) : ContDiff ℝ ∞ (fixedCoefficient m ell) :=
  (reciprocal_smooth.pow 2).mul
    ((((contDiff_const.sub reciprocal_smooth).pow (m+1)).sub
      ((contDiff_const.sub reciprocal_smooth).pow (ell+1))).pow 2)

private theorem cubic_peak (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (k : ℕ) :
    (k+1:ℝ)*s^3*(1-s)^k ≤ 6/((k+2:ℝ)*(k+3:ℝ)) := by
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hterm := Finset.single_le_sum
    (f := fun j => s^j*(1-s)^(k+3-j)*((k+3).choose j:ℝ))
    (fun j _ => by positivity) (show 3∈Finset.range (k+3+1) by simp)
  rw [←add_pow,show s+(1-s)=1 by ring,one_pow] at hterm
  rw [show k+3-3=k by omega] at hterm
  have hc := congrArg (fun j : ℕ => (j:ℝ)) (Nat.add_one_mul_choose_eq (k+2) 2)
  push_cast at hc
  rw [Nat.cast_choose_two] at hc
  push_cast at hc
  have hc' : ((k+3).choose 3:ℝ)=(k+3:ℝ)*(k+2:ℝ)*(k+1:ℝ)/6 := by
    convert (show (((k+2)+1).choose (2+1):ℝ)=
      (k+3:ℝ)*(k+2:ℝ)*(k+1:ℝ)/6 from ?_) using 1
    nlinarith only [hc]
  rw [hc'] at hterm
  have hpos : 0 < (k+2:ℝ)*(k+3:ℝ) := by positivity
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [hterm]

private theorem moving_coefficient_bound (m ell : ℕ) (hml : m ≤ ell)
    (z : SourceCoordinateSlice) :
    |movingCoefficient m ell z| ≤
      24/((m+2:ℝ)*(m+3:ℝ)) := by
  let s := phiReciprocal z
  have hs : 0 ≤ s := (inv_pos.mpr (phi_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_phi z)
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have he := cubic_peak s hs hs1 ell
  have hm := cubic_peak s hs hs1 m
  have hmon : 6/((ell+2:ℝ)*(ell+3:ℝ)) ≤
      6/((m+2:ℝ)*(m+3:ℝ)) := by gcongr
  unfold movingCoefficient
  change |2*s^3*((ell+1:ℝ)*(1-s)^ell-(m+1:ℝ)*(1-s)^m)| ≤ _
  have hnon₁ : 0 ≤ 2*s^3*((ell+1:ℝ)*(1-s)^ell) := by positivity
  have hnon₂ : 0 ≤ 2*s^3*((m+1:ℝ)*(1-s)^m) := by positivity
  have htri := abs_sub (2*s^3*((ell+1:ℝ)*(1-s)^ell))
    (2*s^3*((m+1:ℝ)*(1-s)^m))
  have he2 : 2*s^3*((ell+1:ℝ)*(1-s)^ell) ≤
      12/((ell+2:ℝ)*(ell+3:ℝ)) := by
    calc
      _ = 2*((ell+1:ℝ)*s^3*(1-s)^ell) := by ring
      _ ≤ 2*(6/((ell+2:ℝ)*(ell+3:ℝ))) :=
        mul_le_mul_of_nonneg_left he (by norm_num)
      _ = _ := by ring
  have hm2 : 2*s^3*((m+1:ℝ)*(1-s)^m) ≤
      12/((m+2:ℝ)*(m+3:ℝ)) := by
    calc
      _ = 2*((m+1:ℝ)*s^3*(1-s)^m) := by ring
      _ ≤ 2*(6/((m+2:ℝ)*(m+3:ℝ))) :=
        mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by ring
  have hid : 2*s^3*((ell+1:ℝ)*(1-s)^ell-(m+1:ℝ)*(1-s)^m)=
      2*s^3*((ell+1:ℝ)*(1-s)^ell)-2*s^3*((m+1:ℝ)*(1-s)^m) := by ring
  rw [hid]
  calc
    _ ≤ |2*s^3*((ell+1:ℝ)*(1-s)^ell)|+
        |2*s^3*((m+1:ℝ)*(1-s)^m)| := htri
    _ = 2*s^3*((ell+1:ℝ)*(1-s)^ell)+2*s^3*((m+1:ℝ)*(1-s)^m) := by
      rw [abs_of_nonneg hnon₁,abs_of_nonneg hnon₂]
    _ ≤ 12/((ell+2:ℝ)*(ell+3:ℝ))+
          12/((m+2:ℝ)*(m+3:ℝ)) := add_le_add he2 hm2
    _ ≤ _ := by
      calc
        _ = 2*(6/((ell+2:ℝ)*(ell+3:ℝ))+6/((m+2:ℝ)*(m+3:ℝ))) := by ring
        _ ≤ 2*(6/((m+2:ℝ)*(m+3:ℝ))+6/((m+2:ℝ)*(m+3:ℝ))) :=
          mul_le_mul_of_nonneg_left (add_le_add hmon (le_refl _)) (by norm_num)
        _ = _ := by ring

private theorem fixed_coefficient_bound (m ell : ℕ) (hml : m ≤ ell)
    (z : SourceCoordinateSlice) :
    |fixedCoefficient m ell z| ≤ 1/((m+2:ℝ)*(2*m+3:ℝ)) := by
  let s := phiReciprocal z
  have hs : 0 ≤ s := (inv_pos.mpr (phi_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_phi z)
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hq1 : 1-s ≤ 1 := by linarith
  have he := pow_le_pow_of_le_one hq hq1 (Nat.add_le_add_right hml 1)
  have ht : 0 ≤ (1-s)^(m+1)-(1-s)^(ell+1) := sub_nonneg.mpr he
  have ht' : (1-s)^(m+1)-(1-s)^(ell+1) ≤ (1-s)^(m+1) :=
    sub_le_self _ (pow_nonneg hq _)
  have hsquare : ((1-s)^(m+1)-(1-s)^(ell+1))^2 ≤ (1-s)^(2*m+2) := by
    calc
      _ ≤ ((1-s)^(m+1))^2 := pow_le_pow_left₀ ht ht' 2
      _ = _ := by rw [←pow_mul];congr 1;omega
  have hp := SourceNativeCutoffContact.squared_geometric_peak s hs hs1 (2*m+2)
  have hpos : 0 < (m+2:ℝ)*(2*m+3:ℝ) := by positivity
  have hpn : (2*m+3:ℝ)*s^2*(1-s)^(2*m+2) ≤ 1/(m+2:ℝ) := by
    have hnum : ((2*m+2:ℕ):ℝ)+1=(2*m+3:ℝ) := by push_cast;ring
    have hden : (2:ℝ)/(((2*m+2:ℕ):ℝ)+2)=1/(m+2:ℝ) := by
      push_cast
      have hm : (m+2:ℝ)≠0 := by positivity
      field_simp
      ring
    rwa [hnum,hden] at hp
  have hbound : s^2*(1-s)^(2*m+2) ≤ 1/((m+2:ℝ)*(2*m+3:ℝ)) := by
    apply (le_div_iff₀ hpos).mpr
    have hh := mul_le_mul_of_nonneg_left hpn (show 0 ≤ (m+2:ℝ) by positivity)
    have hi : (m+2:ℝ)*(1/(m+2:ℝ))=1 := by field_simp
    nlinarith only [hh,hi]
  unfold fixedCoefficient
  rw [abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left hsquare (sq_nonneg s)).trans hbound

private theorem real_multiplier_bound (c : SourceCoordinateSlice → ℝ)
    (hc : ContDiff ℝ ∞ c) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z, |c z| ≤ M) (f : QuantumTest) :
    ‖embed ((multiply c (fun _ => hc.contDiffAt)) f)‖ ≤ M*‖embed f‖ := by
  let fiber (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
    (c z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
  have hfs : ContDiff ℝ ∞ fiber :=
    (Complex.ofRealCLM.contDiff.comp hc).smul contDiff_const
  have hcomm (z : physicalChart) (w : ℕ → ℂ) :
      Commute (GaussFockWeights.weight w) (fiber z) :=
    (Commute.one_right _).smul_right _
  have hfbound (z : physicalChart) (x : FockFiber) :
      ‖fiber z x‖ ≤ M*‖x‖ := by
    change ‖(c z:ℂ) • x‖ ≤ _
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg x)
  let op := GaussBoundedMultiplier.extension fiber (fun _ => hfs.contDiffAt)
    hcomm M hM hfbound
  have hcore : op (embed f)=embed ((multiply c (fun _ => hc.contDiffAt)) f) := by
    dsimp [op]
    rw [GaussBoundedMultiplier.extension_core]
    congr 1
  have hnorm : ‖op‖ ≤ M :=
    GaussBoundedMultiplier.extension_norm fiber (fun _ => hfs.contDiffAt)
      hcomm M hM hfbound
  calc
    _ = ‖op (embed f)‖ := by rw [hcore]
    _ ≤ ‖op‖*‖embed f‖ := op.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

private theorem geometric_point (k : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((Q^k) f) z=(((1-phiReciprocal z:ℝ):ℂ)^k) • f z := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change (((Q^k) f) z-(phiReciprocal z:ℂ) • (((Q^k) f) z))=_
    rw [ih,pow_succ',mul_smul]
    push_cast
    module
private theorem inverse_power_point (k : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((S^k) f) z=(phiReciprocal z:ℂ)^k • f z := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change (S ((S^k) f)) z=_
    change (phiReciprocal z:ℂ) • (((S^k) f) z)=_
    rw [ih,pow_succ']
    module
private theorem moving_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (((2:ℂ) • (S^3*B m ell)) f) z=(movingCoefficient m ell z:ℂ) • f z := by
  change (2:ℂ) • ((S^3) ((B m ell) f)) z=_
  rw [inverse_power_point]
  simp only [B,SourceClockPhiRadiusResponseHessian.phiFirstPeak,
    LinearMap.smul_apply,LinearMap.sub_apply]
  change (2:ℂ) • ((phiReciprocal z:ℂ)^3 •
    ((ell+1:ℂ) • ((Q^ell) f) z-(m+1:ℂ) • ((Q^m) f) z))=_
  rw [geometric_point,geometric_point]
  unfold movingCoefficient
  push_cast
  module
private theorem fixed_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((S^2*(T m ell)^2) f) z=(fixedCoefficient m ell z:ℂ) • f z := by
  have ht (g : QuantumTest) :
      (T m ell g) z=((((1-phiReciprocal z:ℝ)^(m+1)-
        (1-phiReciprocal z)^(ell+1)):ℝ):ℂ) • g z := by
    change ((Q^(m+1)) g) z-((Q^(ell+1)) g) z=_
    rw [geometric_point,geometric_point]
    push_cast
    module
  simp only [Module.End.mul_apply]
  rw [inverse_power_point]
  simp only [pow_two,Module.End.mul_apply]
  rw [ht (T m ell f),ht f]
  unfold fixedCoefficient
  push_cast
  module

private theorem moving_norm (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    ‖embed (((2:ℂ) • (S^3*B m ell)) f)‖ ≤
      24/((m+2:ℝ)*(m+3:ℝ))*‖embed f‖ := by
  have h := real_multiplier_bound (movingCoefficient m ell) (moving_smooth m ell)
    (24/((m+2:ℝ)*(m+3:ℝ))) (by positivity)
    (moving_coefficient_bound m ell hml) f
  have he : ((2:ℂ) • (S^3*B m ell)) f=
      (multiply (movingCoefficient m ell) (fun _ => (moving_smooth m ell).contDiffAt)) f := by
    apply DFunLike.ext
    intro z
    exact moving_point m ell f z
  rw [he]
  exact h
private theorem fixed_norm (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    ‖embed ((S^2*(T m ell)^2) f)‖ ≤
      1/((m+2:ℝ)*(2*m+3:ℝ))*‖embed f‖ := by
  have h := real_multiplier_bound (fixedCoefficient m ell) (fixed_smooth m ell)
    (1/((m+2:ℝ)*(2*m+3:ℝ))) (by positivity)
    (fixed_coefficient_bound m ell hml) f
  have he : (S^2*(T m ell)^2) f=
      (multiply (fixedCoefficient m ell) (fun _ => (fixed_smooth m ell).contDiffAt)) f := by
    apply DFunLike.ext
    intro z
    exact fixed_point m ell f z
  rw [he]
  exact h

private theorem two_square {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]

private theorem native_gradient_generic_price (m ell : ℕ) (hml : m ≤ ell)
    (v h : QuantumTest) :
    (∑ a : ScalarIndex,‖embed (U (D a (((2:ℂ) • (S^3*B m ell) v)-
      (S^2*(T m ell)^2) h)))‖^2) ≤
      (24/((m+2:ℝ)*(m+3:ℝ)))^2/2*‖embed (U v)‖^2+
        (1/((m+2:ℝ)*(2*m+3:ℝ)))^2/2*‖embed (U h)‖^2 := by
  let M : End := (2:ℂ) • (S^3*B m ell)
  let N : End := S^2*(T m ell)^2
  let w : QuantumTest := M v-N h
  have hUS : Commute U S := real_commute _ _ _ _
  have hUB : Commute U (B m ell) :=
    (first_commute hUS.symm m ell).symm
  have hUT : Commute U (T m ell) :=
    (theta_commute hUS.symm m ell).symm
  have hUM : Commute U M :=
    ((hUS.pow_right 3).mul_right hUB).smul_right _
  have hUN : Commute U N :=
    (hUS.pow_right 2).mul_right (hUT.pow_right 2)
  have hUD (a : ScalarIndex) : Commute U (D a) := real_commute _ _ _ _
  have hw : U w=M (U v)-N (U h) := by
    change U (M v-N h)=M (U v)-N (U h)
    rw [map_sub]
    exact congrArg₂ (·-·) (LinearMap.congr_fun hUM.eq v)
      (LinearMap.congr_fun hUN.eq h)
  have hrow (a : ScalarIndex) :
      U (D a w)=D a (U w) := LinearMap.congr_fun (hUD a).eq w
  have hdirection :
      (∑ a : ScalarIndex,‖embed (U (D a w))‖^2) ≤
        (1/4:ℝ)*‖embed (U w)‖^2 := by
    have he := SourceClockPhiRadiusSourceCurrent.original_phi_gradient_energy (embed (U w))
    simp_rw [SourceClockPhiRadiusSourceCurrent.original_phi_direction_core] at he
    simp_rw [←hrow] at he
    have hn := sq_nonneg ‖phiInverseBounded (embed (U w))‖
    nlinarith only [he,hn]
  have hMV := moving_norm m ell hml (U v)
  have hNH := fixed_norm m ell hml (U h)
  have hMV2 := pow_le_pow_left₀ (norm_nonneg _) hMV 2
  have hNH2 := pow_le_pow_left₀ (norm_nonneg _) hNH 2
  have hsplit := two_square (embed (M (U v))) (embed (N (U h)))
  have hsub : ‖embed (U w)‖^2 ≤
      2*(24/((m+2:ℝ)*(m+3:ℝ)))^2*‖embed (U v)‖^2+
      2*(1/((m+2:ℝ)*(2*m+3:ℝ)))^2*‖embed (U h)‖^2 := by
    rw [hw]
    simp only [map_sub]
    dsimp only [M,N] at hMV2 hNH2 hsplit ⊢
    nlinarith only [hsplit,hMV2,hNH2]
  change (∑ a : ScalarIndex,‖embed (U (D a w))‖^2) ≤ _
  nlinarith only [hdirection,hsub]

private theorem actual_phi_coframe_price (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    25*n^2/4*‖embed (U (phiResponseCore m ell F z hz g))‖^2 ≤
      phiPositivePrice m ell F z hz g := by
  let v := phiResponseCore m ell F z hz g
  have hf := SourceClockSourceTail.original_inverse_coframe_floor (U v)
  have hp := actual_phi_positive_slots m ell F z hz g
  have hfactor : 0 ≤ n^2/4 := by positivity
  have hc := mul_le_mul_of_nonneg_left hf hfactor
  have hs : 0 ≤ scalarForm (U v) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs' : 0 ≤ n^2/2*scalarForm (U v) := mul_nonneg (by positivity) hs
  have hv : 0 ≤ 6*n^2*‖embed v‖^2 := by positivity
  change n^2/4*coframeGram (U v)+n^2/2*scalarForm (U v)+
    6*n^2*‖embed v‖^2 ≤ phiPositivePrice m ell F z hz g at hp
  nlinarith only [hp,hc,hs',hv]

/-- The moving native column is absorbed by the actual positive source price.
The weighted fixed h leg remains an explicit source obligation. -/
theorem actual_endpoint_native_gradient_price (m ell : ℕ) (hml : m ≤ ell)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (∑ a : ScalarIndex,‖embed (U (endpointNativeGradient m ell F z hz g a))‖^2) ≤
      1152/(25*n^2*(m+2:ℝ)^2*(m+3:ℝ)^2)*phiPositivePrice m ell F z hz g+
        ‖embed (U (resolventCore F z hz (r (coreEquiv.symm g))))‖^2/
          (2*(m+2:ℝ)^2*(2*m+3:ℝ)^2) := by
  let v := phiResponseCore m ell F z hz g
  let h := resolventCore F z hz (r (coreEquiv.symm g))
  have hsource (a : ScalarIndex) := actual_endpoint_native_gradient m ell F z hz g a
  have hsum :
      (∑ a : ScalarIndex,‖embed (U (endpointNativeGradient m ell F z hz g a))‖^2) ≤
        (24/((m+2:ℝ)*(m+3:ℝ)))^2/2*‖embed (U v)‖^2+
          (1/((m+2:ℝ)*(2*m+3:ℝ)))^2/2*‖embed (U h)‖^2 := by
    calc
      _ = (∑ a : ScalarIndex,‖embed (U (D a (((2:ℂ) • (S^3*B m ell) v)-
        (S^2*(T m ell)^2) h)))‖^2) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hsource a]
      _ ≤ _ := native_gradient_generic_price m ell hml v h
  have hp := actual_phi_coframe_price m ell F z hz g
  change 25*n^2/4*‖embed (U v)‖^2 ≤ phiPositivePrice m ell F z hz g at hp
  have hn : 0 < n := by
    change 0 < sourceTime 0
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hm2 : (m+2:ℝ)≠0 := by positivity
  have hm3 : (m+3:ℝ)≠0 := by positivity
  have hm23 : (2*m+3:ℝ)≠0 := by positivity
  let C : ℝ := 1152/(25*n^2*(m+2:ℝ)^2*(m+3:ℝ)^2)
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hpaid := mul_le_mul_of_nonneg_left hp hC
  have hcoeff : (24/((m+2:ℝ)*(m+3:ℝ)))^2/2=
      C*(25*n^2/4) := by
    dsimp [C]
    field_simp [hn.ne',hm2,hm3]
    ring
  have hfixed : (1/((m+2:ℝ)*(2*m+3:ℝ)))^2/2*‖embed (U h)‖^2=
      ‖embed (U h)‖^2/(2*(m+2:ℝ)^2*(2*m+3:ℝ)^2) := by
    field_simp [hm2,hm23]
  change (∑ a : ScalarIndex,‖embed (U (endpointNativeGradient m ell F z hz g a))‖^2) ≤
    C*phiPositivePrice m ell F z hz g+
      ‖embed (U h)‖^2/(2*(m+2:ℝ)^2*(2*m+3:ℝ)^2)
  calc
    _ ≤ (24/((m+2:ℝ)*(m+3:ℝ)))^2/2*‖embed (U v)‖^2+
      (1/((m+2:ℝ)*(2*m+3:ℝ)))^2/2*‖embed (U h)‖^2 := hsum
    _ = C*(25*n^2/4*‖embed (U v)‖^2)+
      ‖embed (U h)‖^2/(2*(m+2:ℝ)^2*(2*m+3:ℝ)^2) := by rw [hcoeff,hfixed];ring
    _ ≤ _ := add_le_add hpaid le_rfl

end LowEnergy.SourceClockPhiEndpointNativeGradient
