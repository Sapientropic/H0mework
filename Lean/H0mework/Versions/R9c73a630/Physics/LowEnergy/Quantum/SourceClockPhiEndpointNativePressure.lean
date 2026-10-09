import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiWholeCFGreenSource
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiEndpointNativeGradient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiEndpointNativePressure
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare SourceScalarVirialBulk
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusAcceleration SourceClockPhiScalarEndpointAcceleration SourceClockPhiZeroSeedEndpointTail
open SourceClockPhiWholeCFGreenSource SourceClockPhiEndpointNativeGradient
open scoped InnerProductSpace ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U : End := inverseVolumeAction
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev Phi : End := SourceScalarAffineScaleTransport.generator
private abbrev n : ℝ := sourceTime 0
private abbrev W : End := multiply scalarWeight scalarWeight_smooth
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev L (m ell : ℕ) : End := (phiThetaAction m ell)^2
private abbrev M (m ell : ℕ) : End := S*(phiThetaAction m ell)^2
private abbrev Z (A : End) (a : ScalarIndex) : End := Complex.I • bracket (P a) A
attribute [local irreducible] SourceClockYukawaCubicCurrent.resolventCore
  GaussDiagonalHistory.diagonalAction compressionCore defectAction SourceScalarPositiveBulkWard.state

/-- The source scalar radius-square current with its actual causal phase. -/
def pressureTester (z : ℂ) : End := (n/2:ℂ) • (U*Phi)-(2*Complex.I*(z.im:ℂ)) • phiSquare
private theorem pressure_source (z : ℂ) :
    bracket diagonalAction phiSquare-(2*Complex.I*(z.im:ℂ)) • phiSquare=pressureTester z := by
  rw [original_phi_square_current]
  rfl

private theorem pair_add_l (p q v : QuantumTest) : sourcePair (p+q) v=sourcePair p v+sourcePair q v := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r (p q v : QuantumTest) : sourcePair p (q+v)=sourcePair p q+sourcePair p v := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l (p q v : QuantumTest) : sourcePair (p-q) v=sourcePair p v-sourcePair q v := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r (p q v : QuantumTest) : sourcePair p (q-v)=sourcePair p q-sourcePair p v := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l (c : ℂ) (p q : QuantumTest) :
    sourcePair (c • p) q=(starRingEnd ℂ c)*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_smul_r (c : ℂ) (p q : QuantumTest) : sourcePair p (c • q)=c*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_neg_r (p q : QuantumTest) : sourcePair p (-q)= -sourcePair p q := by
  simp only [sourcePair,map_neg,inner_neg_right]
private theorem pair_sum_r {ι : Type*} [Fintype ι] (p : QuantumTest) (q : ι → QuantumTest) :
    sourcePair p (∑ i,q i)=∑ i,sourcePair p (q i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem radius_pair (p q : QuantumTest) : sourcePair p (r q)=sourcePair (r p) q := multiply_pair _ _ _ _
private theorem radius_square_pair (p q : QuantumTest) :
    sourcePair p (phiSquare q)=sourcePair (phiSquare p) q := by
  change sourcePair p ((r^2) q)=sourcePair ((r^2) p) q
  simp only [pow_two,Module.End.mul_apply]
  rw [radius_pair,radius_pair]
private theorem bracket_pair (p q : QuantumTest) :
    sourcePair p (bracket diagonalAction phiSquare q)= -sourcePair (bracket diagonalAction phiSquare p) q := by
  change sourcePair p (diagonalAction (phiSquare q)-phiSquare (diagonalAction q))=
    -sourcePair (diagonalAction (phiSquare p)-phiSquare (diagonalAction p)) q
  rw [pair_sub_r,pair_sub_l,diagonalAction_pair,radius_square_pair,←diagonalAction_pair,radius_square_pair]
  ring
private theorem tester_pair (z : ℂ) (p q : QuantumTest) :
    sourcePair p (pressureTester z q)= -sourcePair (pressureTester z p) q := by
  rw [←pressure_source]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_l,pair_sub_r,
    pair_smul_l,pair_smul_r,bracket_pair,radius_square_pair,map_mul,map_ofNat,
    Complex.conj_I,Complex.conj_ofReal]
  ring
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (phiReciprocal x:ℂ) • ((phiRadius x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse : r*S=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (phiRadius x:ℂ) • ((phiReciprocal x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private abbrev Q : End := 1-S
private abbrev D (a : ScalarIndex) : End := phiDirectionAction (scalarBasis a)
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev B (m ell : ℕ) : End := SourceClockPhiRadiusResponseHessian.phiFirstPeak m ell
private abbrev d (a : ScalarIndex) : End := D a*S^2
private theorem real_commute (c b : SourceCoordinateSlice → ℝ)
    (hc : ∀x:physicalChart,ContDiffAt ℝ ∞ c x.val)
    (hb : ∀x:physicalChart,ContDiffAt ℝ ∞ b x.val) : Commute (multiply c hc) (multiply b hb) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  exact smul_comm (c x:ℂ) (b x:ℂ) (f x)
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
private theorem jet_theta_commute {A : End} (h : Commute S A) (m ell : ℕ) : Commute (T m ell) A :=
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
    ((first_commute ((jet_theta_commute (Commute.refl S) m ell).symm) m ell).symm.mul_right
      ((jet_theta_commute (inverse_D a) m ell).mul_right ((jet_theta_commute (Commute.refl S) m ell).pow_right 2)))
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

private theorem commute_inverse {A : End} (h : Commute A r) : Commute A S := by
  change A*S=S*A
  have he := congrArg (fun B : End => S*B*S) h.eq
  simp only [mul_assoc,radius_inverse,mul_one] at he
  simpa only [←mul_assoc,inverse_radius,one_mul] using he.symm
private theorem theta_commute {A : End} (h : Commute A S) (m ell : ℕ) : Commute A (phiThetaAction m ell) :=
  (((Commute.one_right A).sub_right h).pow_right (m+1)).sub_right
    (((Commute.one_right A).sub_right h).pow_right (ell+1))
private theorem paired_mul {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) (h : Commute A B) : GaussCoframeForm.Paired (A*B) (A*B) := by
  intro p q
  change sourcePair p (A (B q))=sourcePair (A (B p)) q
  rw [hA p (B q),hB (A p) q]
  exact congrArg (fun f => sourcePair f q) (LinearMap.congr_fun h.eq p).symm
private theorem paired_sub {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) : GaussCoframeForm.Paired (A-B) (A-B) := by
  intro p q
  simp only [LinearMap.sub_apply,pair_sub_l,pair_sub_r]
  rw [hA p q,hB p q]
private theorem paired_pow {A : End} (hA : GaussCoframeForm.Paired A A) (j : ℕ) :
    GaussCoframeForm.Paired (A^j) (A^j) := by
  induction j with
  | zero => intro p q;rfl
  | succ j ih => rw [pow_succ];exact paired_mul ih hA ((Commute.refl A).pow_left j)
private theorem theta_pair (m ell : ℕ) : GaussCoframeForm.Paired (phiThetaAction m ell) (phiThetaAction m ell) := by
  have h1 : GaussCoframeForm.Paired (1:End) 1 := by intro p q;rfl
  exact paired_sub (paired_pow (paired_sub h1 (multiply_pair _ _)) (m+1))
    (paired_pow (paired_sub h1 (multiply_pair _ _)) (ell+1))
private theorem L_pair (m ell : ℕ) : GaussCoframeForm.Paired (L m ell) (L m ell) := paired_pow (theta_pair m ell) 2
private theorem M_pair (m ell : ℕ) : GaussCoframeForm.Paired (M m ell) (M m ell) :=
  paired_mul (multiply_pair _ _) (L_pair m ell) ((theta_commute (Commute.refl S) m ell).pow_right 2)
private theorem weight_inverse : W=(-(n:ℂ)) • U := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (scalarWeight x:ℂ) • f x=(-(n:ℂ)) • ((reciprocalVolume x:ℂ) • f x)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1
private theorem inverse_radius_commute : Commute U r := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  exact smul_comm (reciprocalVolume x:ℂ) (phiRadius x:ℂ) (f x)
private theorem weight_L (m ell : ℕ) : Commute W (L m ell) := by
  rw [weight_inverse]
  exact ((theta_commute (commute_inverse inverse_radius_commute) m ell).pow_right 2).smul_left _
private theorem weight_M (m ell : ℕ) : Commute W (M m ell) := by
  rw [weight_inverse]
  exact ((commute_inverse inverse_radius_commute).mul_right
    ((theta_commute (commute_inverse inverse_radius_commute) m ell).pow_right 2)).smul_left _
private theorem scalar_cutoff {A : End} (h : Commute (diagonalAction-scalarKinetic) A) :
    bracket diagonalAction A=bracket scalarKinetic A := by
  have he := h.eq
  unfold bracket
  linear_combination (norm := noncomm_ring) he
private theorem full_L (m ell : ℕ) : bracket diagonalAction (L m ell)=bracket scalarKinetic (L m ell) :=
  scalar_cutoff ((theta_commute (commute_inverse original_phi_radius_non_scalar_commute.2.2.2) m ell).pow_right 2)
private theorem full_M (m ell : ℕ) : bracket diagonalAction (M m ell)=bracket scalarKinetic (M m ell) :=
  scalar_cutoff ((commute_inverse original_phi_radius_non_scalar_commute.2.2.2).mul_right
    ((theta_commute (commute_inverse original_phi_radius_non_scalar_commute.2.2.2) m ell).pow_right 2))
private theorem scalar_form (p q : QuantumTest) : sourcePair p (scalarKinetic q)=
    (1/2:ℂ)*∑ a : ScalarIndex,sourcePair (P a p) (W (P a q)) := by
  simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,pair_smul_r,pair_sum_r]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change sourcePair p (GaussMomentumAdjoint.adjoint (scalarDirection a) (W (P a q)))=_
  exact adjoint_pair _ _ _
private theorem jet_source (A : End) (a : ScalarIndex) (q : QuantumTest) :
    P a (A q)=A (P a q)+(-Complex.I) • Z A a q := by
  simp only [Z,bracket,LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,smul_smul]
  have hi : -Complex.I*Complex.I=1 := by rw [neg_mul,Complex.I_mul_I];ring
  rw [hi,one_smul]
  abel
private theorem weak_scalar_current (A : End) (hA : GaussCoframeForm.Paired A A)
    (hW : Commute W A) (p q : QuantumTest) :
    sourcePair p (bracket scalarKinetic A q)=(-Complex.I/2)*∑ a : ScalarIndex,
      (sourcePair (P a p) (W (Z A a q))+sourcePair (Z A a p) (W (P a q))) := by
  change sourcePair p (scalarKinetic (A q)-A (scalarKinetic q))=_
  rw [pair_sub_r,hA p (scalarKinetic q),scalar_form,scalar_form,←mul_sub,←Finset.sum_sub_distrib]
  have hrow (a : ScalarIndex) :
      sourcePair (P a p) (W (P a (A q)))-sourcePair (P a (A p)) (W (P a q))=
      (-Complex.I)*(sourcePair (P a p) (W (Z A a q))+sourcePair (Z A a p) (W (P a q))) := by
    rw [jet_source A a q,jet_source A a p]
    have hc : sourcePair (A (P a p)) (W (P a q))=sourcePair (P a p) (W (A (P a q))) := by
      rw [←hA (P a p) (W (P a q))]
      exact congrArg (sourcePair (P a p)) (LinearMap.congr_fun hW.eq (P a q)).symm
    simp only [map_add,map_smul,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,hc,
      map_neg,Complex.conj_I]
    ring
  simp_rw [hrow]
  rw [←Finset.mul_sum]
  ring
private theorem native_symmetric_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (p : QuantumTest) :
    let q := resolventCore F z hz (coreEquiv.symm g)
    let h := resolventCore F z hz (r (coreEquiv.symm g))
    sourcePair p (nativeCutoff m ell F z hz g)=(-Complex.I/2)*∑ a : ScalarIndex,
      (sourcePair (P a p) (W (endpointNativeGradient m ell F z hz g a))+
        sourcePair (Z (L m ell) a p) (W (P a q))-
        sourcePair (Z (M m ell) a p) (W (P a h))) := by
  let q : QuantumTest := resolventCore F z hz (coreEquiv.symm g)
  let h : QuantumTest := resolventCore F z hz (r (coreEquiv.symm g))
  dsimp only
  have hL := congrArg (fun A : End => sourcePair p (A q)) (full_L m ell)
  have hM := congrArg (fun A : End => sourcePair p (A h)) (full_M m ell)
  have h1 := weak_scalar_current (L m ell) (L_pair m ell) (weight_L m ell) p q
  have h2 := weak_scalar_current (M m ell) (M_pair m ell) (weight_M m ell) p h
  change sourcePair p (nativeCutoff m ell F z hz g)=_
  calc
    _=sourcePair p (bracket scalarKinetic (L m ell) q)-
        sourcePair p (bracket scalarKinetic (M m ell) h) := by
      unfold nativeCutoff
      change sourcePair p (bracket diagonalAction (L m ell) q-bracket diagonalAction (M m ell) h)=_
      rw [pair_sub_r]
      exact congrArg₂ (·-·) hL hM
    _=(-Complex.I/2)*(∑ a : ScalarIndex,
        (sourcePair (P a p) (W (Z (L m ell) a q))+sourcePair (Z (L m ell) a p) (W (P a q)))-
        ∑ a : ScalarIndex,(sourcePair (P a p) (W (Z (M m ell) a h))+
          sourcePair (Z (M m ell) a p) (W (P a h)))) := by rw [h1,h2,mul_sub]
    _=_ := by
      rw [←Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      have he : endpointNativeGradient m ell F z hz g a=Z (L m ell) a q-Z (M m ell) a h := by
        simp only [endpointNativeGradient,Z,LinearMap.smul_apply,smul_sub,q,h]
      rw [he,map_sub,pair_sub_r]
      ring

private theorem native_Phi (a : ScalarIndex) : bracket (P a) Phi=P a := by
  have h := original_scalar_momentum_phi (scalarDirection a) rfl
  have he := SourceScalarAffineScaleTransport.generator_commutator (P a)
  change Phi*P a-P a*Phi=phiEulerAction*P a-P a*phiEulerAction at he
  unfold bracket
  linear_combination (norm := module) -he-h
private theorem native_square (a : ScalarIndex) :
    bracket (P a) phiSquare=(2*Complex.I) • (r*phiDirectionAction (scalarBasis a)) := by
  have h := (original_phi_radius_native_jet (scalarDirection a)).1
  change bracket (P a) r=Complex.I • phiDirectionAction (scalarBasis a) at h
  have hc : Commute (phiDirectionAction (scalarBasis a)) r := by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
    exact smul_comm (phiDirectionWeight (scalarBasis a) x:ℂ) (phiRadius x:ℂ) (f x)
  change bracket (P a) (r^2)=_
  have he : bracket (P a) (r^2)=bracket (P a) r*r+r*bracket (P a) r := by unfold bracket;noncomm_ring
  rw [he,h,smul_mul_assoc,mul_smul_comm,hc.eq]
  module

/-- Actual native degree, connection and rho jet give the first-order pressure row. -/
theorem original_pressure_native_jet (a : ScalarIndex) (z : ℂ) :
    bracket (P a) (pressureTester z)=(n/2:ℂ) • (U*P a)+
      (4*(z.im:ℂ)) • (r*phiDirectionAction (scalarBasis a)) := by
  have hU : Commute (P a) U := SourceScalarInverseNativeEnergy.original_native_inverse_commute _
  have hprod : bracket (P a) (U*Phi)=U*bracket (P a) Phi := by
    unfold bracket
    linear_combination (norm := noncomm_ring) hU.eq*Phi
  unfold pressureTester
  have he : bracket (P a) ((n/2:ℂ) • (U*Phi)-(2*Complex.I*(z.im:ℂ)) • phiSquare)=
      (n/2:ℂ) • bracket (P a) (U*Phi)-(2*Complex.I*(z.im:ℂ)) • bracket (P a) phiSquare := by
    unfold bracket
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,smul_sub]
    abel
  rw [he,hprod,native_Phi,native_square,smul_smul]
  have hi : -(2*Complex.I*(z.im:ℂ))*(2*Complex.I)=4*(z.im:ℂ) := by
    calc _= -(4*(z.im:ℂ))*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [sub_eq_add_neg,←neg_smul,←neg_mul,hi]

private theorem tester_weight (z : ℂ) : Commute (pressureTester z) W := by
  have hE : Commute phiEulerAction U := by
    have h := SourceScalarInverseBulk.inverse_phi
    change phiEulerAction*U-U*phiEulerAction=0 at h
    exact sub_eq_zero.mp h
  have hPhi : Commute Phi U := hE.add_left ((Commute.one_left U).smul_left _)
  have hrU := inverse_radius_commute.symm
  unfold pressureTester
  rw [weight_inverse]
  exact (((Commute.refl U).mul_left hPhi).smul_left _).sub_left
    (((hrU.pow_left 2).smul_left _)) |>.smul_right _
private def pressureRow (a : ScalarIndex) (z : ℂ) : End :=
  (n/2:ℂ) • (U*P a)+(4*(z.im:ℂ)) • (r*phiDirectionAction (scalarBasis a))
private theorem pressure_pair_move (a : ScalarIndex) (z : ℂ) (q f : QuantumTest) :
    sourcePair (P a (pressureTester z q)) (W f)=
      -sourcePair (P a q) (W (pressureTester z f))+sourcePair (pressureRow a z q) (W f) := by
  have hj := LinearMap.congr_fun (original_pressure_native_jet a z) q
  change P a (pressureTester z q)-pressureTester z (P a q)=pressureRow a z q at hj
  have he : P a (pressureTester z q)=pressureTester z (P a q)+pressureRow a z q := by
    linear_combination (norm := module) hj
  have hm : sourcePair (pressureTester z (P a q)) (W f)=
      -sourcePair (P a q) (pressureTester z (W f)) := by
    have hp := tester_pair z (P a q) (W f)
    linear_combination (norm := ring) hp
  rw [he,pair_add_l,hm]
  have hw := LinearMap.congr_fun (tester_weight z).eq f
  change pressureTester z (W f)=W (pressureTester z f) at hw
  rw [hw]

private def leftJet (m ell : ℕ) (a : ScalarIndex) : End := (2:ℂ) • (T m ell*B m ell*d a)
private def rightJet (m ell : ℕ) (a : ScalarIndex) : End :=
  d a*(T m ell)^2+(2:ℂ) • (S*T m ell*B m ell*d a)
private theorem leftJet_return (m ell : ℕ) (a : ScalarIndex) : Z (L m ell) a=leftJet m ell a := by
  change Complex.I • bracket (P a) ((T m ell)^2)=_
  rw [theta_square_native,smul_smul]
  have hi : Complex.I*(-2*Complex.I)=2 := by
    calc _= -2*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi]
  rfl
private theorem rightJet_return (m ell : ℕ) (a : ScalarIndex) : Z (M m ell) a=rightJet m ell a := by
  change Complex.I • bracket (P a) (S*(T m ell)^2)=_
  rw [inverse_theta_square_native,smul_smul]
  have hi : Complex.I*(-Complex.I)=1 := by rw [mul_neg,Complex.I_mul_I];ring
  rw [hi,one_smul]
  rfl

private def gradientSource (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (a : ScalarIndex) : QuantumTest :=
  phiDirectionAction (scalarBasis a)
    (((2:ℂ) • (S^3*SourceClockPhiRadiusResponseHessian.phiFirstPeak m ell))
      (phiResponseCore m ell F z hz g)-
      (S^2*(phiThetaAction m ell)^2) (resolventCore F z hz (r (coreEquiv.symm g))))
private theorem gradient_return (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (a : ScalarIndex) :
    endpointNativeGradient m ell F z hz g a=gradientSource m ell F z hz g a :=
  actual_endpoint_native_gradient m ell F z hz g a

/-- All seventy native rows retain their actual K, source transpose and density. -/
def nativePressure (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  let q := resolventCore F z hz (coreEquiv.symm g)
  let h := resolventCore F z hz (r (coreEquiv.symm g))
  (1/2:ℝ)*∑ a : ScalarIndex,
    (-sourcePair (P a q) (W (pressureTester z (gradientSource m ell F z hz g a)))+
      sourcePair (pressureRow a z q) (W (gradientSource m ell F z hz g a))+
      sourcePair (leftJet m ell a (pressureTester z q)) (W (P a q))-
      sourcePair (rightJet m ell a (pressureTester z q)) (W (P a h))).im
private theorem actual_native_pressure (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    (sourcePair (pressureTester z (resolventCore F z hz (coreEquiv.symm g)))
      (nativeCutoff m ell F z hz g)).re=nativePressure m ell F z hz g := by
  have h := native_symmetric_source m ell F z hz g
    (pressureTester z (resolventCore F z hz (coreEquiv.symm g)))
  dsimp only at h
  simp_rw [pressure_pair_move,gradient_return,leftJet_return,rightJet_return] at h
  have hr := congrArg Complex.re h
  unfold nativePressure
  dsimp only
  norm_num only [Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.normSq_apply,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,
    map_sum] at hr
  have him (f : ScalarIndex → ℂ) : (∑ a,f a).im=∑ a,(f a).im := map_sum Complex.imAddGroupHom _ _
  simpa only [zero_mul,zero_sub,neg_mul,neg_neg,him] using hr

private def localPressure : End :=
  (n:ℂ) • (U*(centeredAction-vacuumLinearAction))+stableSpatialAcceleration+
    ((n:ℂ)^2/4) • (U*U*Phi)
private def fieldPressure (q p : QuantumTest) : ℝ :=
  n^2/2*(∑ a : ScalarIndex,(sourcePair (P a q) ((U*U) (P a p))).re)+
    (sourcePair q (localPressure p)).re
private theorem scalar_field_source (q p : QuantumTest) :
    (sourcePair q ((scalarAcceleration+stableSpatialAcceleration+((n:ℂ)^2/4) • (U*U*Phi)) p)).re=
      fieldPressure q p := by
  have hU (f k : QuantumTest) : sourcePair f (U k)=sourcePair (U f) k := multiply_pair _ _ _ _
  have hs : sourcePair q (U (scalarKinetic p))=
      (-(n:ℂ)/2)*∑ a : ScalarIndex,sourcePair (P a q) ((U*U) (P a p)) := by
    rw [hU,scalar_form]
    have hrow (a : ScalarIndex) : sourcePair (P a (U q)) (W (P a p))=
        -(n:ℂ)*sourcePair (P a q) ((U*U) (P a p)) := by
      have hc := LinearMap.congr_fun
        (SourceScalarInverseNativeEnergy.original_native_inverse_commute (scalarDirection a)).eq q
      change P a (U q)=U (P a q) at hc
      rw [hc,weight_inverse,LinearMap.smul_apply,pair_smul_r,←hU]
      rfl
    simp_rw [hrow]
    rw [←Finset.mul_sum]
    ring
  have he : sourcePair q ((scalarAcceleration+stableSpatialAcceleration+
      ((n:ℂ)^2/4) • (U*U*Phi)) p)=
      -(n:ℂ)*sourcePair q (U (scalarKinetic p))+sourcePair q (localPressure p) := by
    simp only [scalarAcceleration,localPressure,LinearMap.add_apply,LinearMap.sub_apply,
      LinearMap.neg_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sub,map_add,map_neg,
      pair_sub_r,pair_add_r,pair_smul_r,pair_neg_r]
    ring
  have hc : sourcePair q ((scalarAcceleration+stableSpatialAcceleration+
      ((n:ℂ)^2/4) • (U*U*Phi)) p)=
      ((n:ℂ)^2/2)*(∑ a : ScalarIndex,sourcePair (P a q) ((U*U) (P a p)))+
        sourcePair q (localPressure p) := by
    rw [he,hs]
    ring
  have hn : ((n:ℂ)^2/2)=((n^2/2:ℝ):ℂ) := by push_cast;ring
  rw [hn] at hc
  have h := congrArg Complex.re hc
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at h
  have hsum : (∑ a : ScalarIndex,sourcePair (P a q) ((U*U) (P a p))).re=
      ∑ a : ScalarIndex,(sourcePair (P a q) ((U*U) (P a p))).re :=
    map_sum Complex.reAddGroupHom _ _
  rw [hsum] at h
  exact h

/-- The full geometric, native and coherent remainder in first-order weak form. -/
def firstOrderRemainder (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) : ℝ :=
  let q := resolventCore F z hz (coreEquiv.symm g)
  let p := endpointState m ell F z hz g
  let v := phiResponseCore m ell F z hz g
  let dc := SourceClockPhiRadiusResponseHessian.phiCoherentDefect m ell F z hz g
  let tester := v+(4*α:ℂ) • SourceClockAcceleration.clockCurrent v+(Complex.I*(α:ℂ)*(n:ℂ)) • U v
  2*α*(fieldPressure q p-
    n^2/16*(sourcePair (((1:End)-S^2) q) (endpointWord p)).im+nativePressure m ell F z hz g+
    (sourcePair (pressureTester z q) (S (phiThetaAction m ell dc))).re+
    (sourcePair (defectAction F q) (pressureTester z p)).re)-
    (sourcePair tester dc).im

/-- The frozen complete Green consumer now uses only first-order native legs. -/
theorem actual_whole_native_pressure (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) :
    wholeRemainder m ell F z hz g α=firstOrderRemainder m ell F z hz g α := by
  let q : QuantumTest := resolventCore F z hz (coreEquiv.symm g)
  let p : QuantumTest := endpointState m ell F z hz g
  let dc : QuantumTest := SourceClockPhiRadiusResponseHessian.phiCoherentDefect m ell F z hz g
  have hN := actual_native_pressure m ell F z hz g
  have hF := scalar_field_source q p
  have hA := congrArg Complex.re (pair_add_r (pressureTester z q)
    (nativeCutoff m ell F z hz g) (S (phiThetaAction m ell dc)))
  simp only [Complex.add_re] at hA
  let v : QuantumTest := phiResponseCore m ell F z hz g
  let A : End := scalarAcceleration+stableSpatialAcceleration+((n:ℂ)^2/4) • (U*U*Phi)
  let correction : ℝ := n^2/16*(sourcePair (((1:End)-S^2) q) (endpointWord p)).im
  let defectPair : ℝ := (sourcePair (defectAction F q) (pressureTester z p)).re
  let coherentPair : ℂ := sourcePair
    (v+(4*α:ℂ) • SourceClockAcceleration.clockCurrent v+(Complex.I*(α:ℂ)*(n:ℂ)) • U v) dc
  change (sourcePair (pressureTester z q) (nativeCutoff m ell F z hz g)).re=
    nativePressure m ell F z hz g at hN
  change (sourcePair q (A p)).re=fieldPressure q p at hF
  unfold wholeRemainder firstOrderRemainder
  dsimp only
  simp_rw [pressure_source]
  change 2*α*((sourcePair q (A p)).re-correction+
      (sourcePair (pressureTester z q) (nativeCutoff m ell F z hz g+S (phiThetaAction m ell dc))).re+
      defectPair)-coherentPair.im=
    2*α*(fieldPressure q p-correction+nativePressure m ell F z hz g+
      (sourcePair (pressureTester z q) (S (phiThetaAction m ell dc))).re+defectPair)-coherentPair.im
  linear_combination (norm := ring) (2*α)*hA+(2*α)*hN+(2*α)*hF

end LowEnergy.SourceClockPhiEndpointNativePressure
