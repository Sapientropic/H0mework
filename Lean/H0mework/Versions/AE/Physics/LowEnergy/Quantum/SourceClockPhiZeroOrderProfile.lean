import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockAbelNativeRadialPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiZeroOrderProfile
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceScalarDoubleCurrent
open SourceScalarVirialBulk SourcePhysicalKineticSquare SourceClockPhiRadiusResponseHessian
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev S : End := phiInverseAction
private abbrev R : End := phiRadiusAction
private abbrev E : End := phiEulerAction
private abbrev Q : End := 1-S
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev B (m ell : ℕ) : End := phiFirstPeak m ell
private abbrev C (m ell : ℕ) : End := phiSecondPeak m ell
private abbrev delta : End := S^3-S
private def profileCore (m ell : ℕ) : Fin 2 → Fin 2 → End :=
  !![(2:ℂ) • (B m ell*S)-T m ell,(-2:ℂ) • (S*(B m ell*S));
    (-2:ℂ) • (S*(B m ell*S)),S^2*(T m ell+(2:ℂ) • (B m ell*S))]
/-- The same literal native e-matrix, including its original right theta. -/
def radialProfile (i j : Fin 2) (m ell : ℕ) : End := profileCore m ell i j*T m ell
/-- The actual affine61 divergence after the entire paired current is combined. -/
def zeroProfile (i j : Fin 2) (m ell : ℕ) : End :=
  S*bracket E (radialProfile i j m ell)+((60:ℂ) • S+S^3)*radialProfile i j m ell

def zeroDerivative (i j : Fin 2) (m ell : ℕ) : End :=
  !![(2:ℂ) • (S*(C m ell*T m ell+(B m ell)^2)),
      (-4:ℂ) • (S*B m ell*T m ell)-(2:ℂ) • (S^2*(C m ell*T m ell+(B m ell)^2));
      (-4:ℂ) • (S*B m ell*T m ell)-(2:ℂ) • (S^2*(C m ell*T m ell+(B m ell)^2)),
      (2:ℂ) • (S*(T m ell)^2)+(8:ℂ) • (S^2*B m ell*T m ell)+
        (2:ℂ) • (S^3*(C m ell*T m ell+(B m ell)^2))] i j

def zeroPolynomial (i j : Fin 2) (m ell : ℕ) : End :=
  -(S^2*(1-S^2)*zeroDerivative i j m ell)+
    ((60:ℂ) • S+S^3)*radialProfile i j m ell

private theorem bracket_product (X Y Z : End) : bracket X (Y*Z)=bracket X Y*Z+Y*bracket X Z := by
  unfold bracket;noncomm_ring
private theorem bracket_sub (X Y Z : End) : bracket X (Y-Z)=bracket X Y-bracket X Z := by
  unfold bracket;noncomm_ring
private theorem bracket_add (X Y Z : End) : bracket X (Y+Z)=bracket X Y+bracket X Z := by
  unfold bracket;noncomm_ring
private theorem bracket_smul (X Y : End) (c : ℂ) : bracket X (c • Y)=c • bracket X Y := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem inverse_radius : S*R=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse : R*S=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem euler_inverse : bracket E S=delta := by
  have hr : bracket E R=R-S := original_phi_euler_radius
  have h1 : S*E*R*S=S*E := by
    calc _=S*E*(R*S) := by noncomm_ring
         _=_ := by rw [radius_inverse,mul_one]
  have h2 : S*R*E*S=E*S := by rw [inverse_radius,one_mul]
  have hi : bracket E S= -(S*bracket E R*S) := by
    unfold bracket
    calc _= -(S*E*R*S-S*R*E*S) := by rw [h1,h2];abel
         _=_ := by noncomm_ring
  rw [hi,hr]
  change -(S*(R-S)*S)=S^3-S
  calc _= -((S*R)*S)+S^3 := by noncomm_ring
       _=_ := by rw [inverse_radius,one_mul];abel
private theorem q_delta : Commute Q delta :=
  (((Commute.one_left S).sub_left (Commute.refl S)).pow_right 3).sub_right
    ((Commute.one_left S).sub_left (Commute.refl S))
private theorem euler_q : bracket E Q= -delta := by
  rw [Q,bracket_sub,euler_inverse]
  simp only [bracket,mul_one,one_mul,sub_self,zero_sub]
private theorem euler_geometric_succ (n : ℕ) :
    bracket E (Q^(n+1))=(-(n+1:ℂ)) • (Q^n*delta) := by
  induction n with
  | zero => simpa only [zero_add,Nat.cast_zero,pow_one,pow_zero,one_mul,one_smul,neg_smul] using euler_q
  | succ n ih =>
    have hm : (Q^n*delta)*Q=Q^(n+1)*delta := by rw [mul_assoc,←q_delta.eq,←mul_assoc,←pow_succ]
    rw [show n+1+1=(n+1)+1 from rfl,pow_succ,bracket_product,ih,euler_q]
    simp only [smul_mul_assoc,mul_neg]
    rw [hm]
    push_cast
    simp only [pow_succ]
    module
private theorem euler_geometric (n : ℕ) : bracket E (Q^n)=(-(n:ℂ)) • (Q^(n-1)*delta) := by
  cases n with
  | zero => simp [bracket]
  | succ n => simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using euler_geometric_succ n
private theorem euler_theta (m ell : ℕ) : bracket E (T m ell)=B m ell*delta := by
  change bracket E (Q^(m+1)-Q^(ell+1))=B m ell*delta
  rw [bracket_sub,euler_geometric_succ,euler_geometric_succ]
  change _=((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m)*delta
  simp only [sub_mul,smul_mul_assoc]
  module
private theorem euler_peak (m ell : ℕ) : bracket E (B m ell)=C m ell*delta := by
  change bracket E ((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m)=C m ell*delta
  rw [bracket_sub,bracket_smul,bracket_smul,euler_geometric,euler_geometric]
  change _=((m*(m+1):ℂ) • Q^(m-1)-(ell*(ell+1):ℂ) • Q^(ell-1))*delta
  simp only [sub_mul,smul_mul_assoc,smul_smul]
  module
private theorem euler_power (n : ℕ) : bracket E (S^n)=(n:ℂ) • (S^n*(S^2-1)) := by
  induction n with
  | zero => simp [bracket]
  | succ n ih =>
    rw [pow_succ,bracket_product,ih,euler_inverse]
    have he : S^n*delta=S^(n+1)*(S^2-1) := by rw [pow_succ];change S^n*(S^3-S)=_;noncomm_ring
    have hn : (S^n*(S^2-1))*S=S^(n+1)*(S^2-1) := by rw [pow_succ];noncomm_ring
    simp only [Nat.cast_succ,add_smul,one_smul,smul_mul_assoc]
    rw [he,hn]
    simp only [pow_succ]
private theorem theta_S (m ell : ℕ) : Commute (T m ell) S :=
  (((Commute.one_left S).sub_left (Commute.refl S)).pow_left (m+1)).sub_left
    (((Commute.one_left S).sub_left (Commute.refl S)).pow_left (ell+1))
private theorem first_S (m ell : ℕ) : Commute (B m ell) S :=
  ((((Commute.one_left S).sub_left (Commute.refl S)).pow_left ell).smul_left _).sub_left
    ((((Commute.one_left S).sub_left (Commute.refl S)).pow_left m).smul_left _)
private theorem second_S (m ell : ℕ) : Commute (C m ell) S :=
  ((((Commute.one_left S).sub_left (Commute.refl S)).pow_left (m-1)).smul_left _).sub_left
    ((((Commute.one_left S).sub_left (Commute.refl S)).pow_left (ell-1)).smul_left _)
private theorem theta_first (m ell : ℕ) : Commute (T m ell) (B m ell) := by
  have hQ : Commute (T m ell) Q := (Commute.one_right _).sub_right (theta_S m ell)
  exact ((hQ.pow_right ell).smul_right _).sub_right ((hQ.pow_right m).smul_right _)

private theorem derivative00 (m ell : ℕ) :
    bracket E (((2:ℂ) • (B m ell*S)-T m ell)*T m ell)=
      delta*((2:ℂ) • (S*(C m ell*T m ell+(B m ell)^2))) := by
  rw [bracket_product,bracket_sub,bracket_smul,bracket_product,euler_peak,euler_inverse,euler_theta]
  unfold delta
  have hs := (first_S m ell).eq
  have ht := (theta_S m ell).eq
  have hb := (theta_first m ell).eq
  have hc := (second_S m ell).eq
  have hsX (X : End) : B m ell*(S*X)=S*(B m ell*X) := by rw [←mul_assoc,hs,mul_assoc]
  have htX (X : End) : T m ell*(S*X)=S*(T m ell*X) := by rw [←mul_assoc,ht,mul_assoc]
  have hbX (X : End) : T m ell*(B m ell*X)=B m ell*(T m ell*X) := by rw [←mul_assoc,hb,mul_assoc]
  have hcX (X : End) : C m ell*(S*X)=S*(C m ell*X) := by rw [←mul_assoc,hc,mul_assoc]
  noncomm_ring [hsX,htX,hbX,hcX,hs,ht,hb,hc]
  module
private theorem derivative01 (m ell : ℕ) :
    bracket E (((-2:ℂ) • (S*(B m ell*S)))*T m ell)=
      delta*((-4:ℂ) • (S*B m ell*T m ell)-(2:ℂ) • (S^2*(C m ell*T m ell+(B m ell)^2))) := by
  rw [bracket_product,bracket_smul,bracket_product,bracket_product,euler_inverse,euler_peak,euler_theta]
  unfold delta
  have hs := (first_S m ell).eq
  have ht := (theta_S m ell).eq
  have hb := (theta_first m ell).eq
  have hc := (second_S m ell).eq
  have hsX (X : End) : B m ell*(S*X)=S*(B m ell*X) := by rw [←mul_assoc,hs,mul_assoc]
  have htX (X : End) : T m ell*(S*X)=S*(T m ell*X) := by rw [←mul_assoc,ht,mul_assoc]
  have hbX (X : End) : T m ell*(B m ell*X)=B m ell*(T m ell*X) := by rw [←mul_assoc,hb,mul_assoc]
  have hcX (X : End) : C m ell*(S*X)=S*(C m ell*X) := by rw [←mul_assoc,hc,mul_assoc]
  noncomm_ring [hsX,htX,hbX,hcX,hs,ht,hb,hc]
  module
private theorem derivative11 (m ell : ℕ) :
    bracket E ((S^2*(T m ell+(2:ℂ) • (B m ell*S)))*T m ell)=
      delta*((2:ℂ) • (S*(T m ell)^2)+(8:ℂ) • (S^2*B m ell*T m ell)+
        (2:ℂ) • (S^3*(C m ell*T m ell+(B m ell)^2))) := by
  rw [bracket_product,bracket_product,euler_power,bracket_add,bracket_smul,bracket_product,
    euler_theta,euler_peak,euler_inverse]
  unfold delta
  have hs := (first_S m ell).eq
  have ht := (theta_S m ell).eq
  have hb := (theta_first m ell).eq
  have hc := (second_S m ell).eq
  have hsX (X : End) : B m ell*(S*X)=S*(B m ell*X) := by rw [←mul_assoc,hs,mul_assoc]
  have htX (X : End) : T m ell*(S*X)=S*(T m ell*X) := by rw [←mul_assoc,ht,mul_assoc]
  have hbX (X : End) : T m ell*(B m ell*X)=B m ell*(T m ell*X) := by rw [←mul_assoc,hb,mul_assoc]
  have hcX (X : End) : C m ell*(S*X)=S*(C m ell*X) := by rw [←mul_assoc,hc,mul_assoc]
  noncomm_ring [hsX,htX,hbX,hcX,hs,ht,hb,hc]
  module

theorem actual_radial_profile_derivative (i j : Fin 2) (m ell : ℕ) :
    bracket E (radialProfile i j m ell)=delta*zeroDerivative i j m ell := by
  fin_cases i <;> fin_cases j
  · exact derivative00 m ell
  · exact derivative01 m ell
  · exact derivative01 m ell
  · exact derivative11 m ell

theorem actual_zero_profile_source (i j : Fin 2) (m ell : ℕ) :
    zeroProfile i j m ell=zeroPolynomial i j m ell := by
  rw [zeroProfile,actual_radial_profile_derivative]
  unfold zeroPolynomial delta
  noncomm_ring

end LowEnergy.SourceClockPhiZeroOrderProfile
