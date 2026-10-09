import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiScalarEndpointAcceleration
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiZeroSeedEndpointTail
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseHessian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiWholeCFGreenSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open SourceScalarVirialBulk SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockYukawaCubicCurrent SourceClockPhiRadiusAcceleration
open SourceClockPhiScalarEndpointAcceleration SourceClockPhiZeroSeedEndpointTail
open SourceClockPhiRadiusResponseNativeBudget SourceScalarPositiveBulkWard
open SourceMixedNativeReturn SourceLocalizedInverseFormPayment FullYSourceResolventGraphSplice
open SourceResolventBandLimit MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U : End := inverseVolumeAction
private abbrev r : End := phiRadiusAction
private abbrev S : End := phiInverseAction
private abbrev T : End := phiSquare
private abbrev B : End := bracket diagonalAction T
private abbrev Bd (F : Index) : End := bracket (defectAction F) T
private abbrev Kc (F : Index) : End := bracket (compressionCore F) T
private abbrev K (z : ℂ) : End := B-(2*Complex.I*(z.im:ℂ)) • T
private abbrev a (m ell : ℕ) : End := S*phiThetaAction m ell
private abbrev Phi : End := SourceScalarAffineScaleTransport.generator
private abbrev n : ℝ := sourceTime 0
attribute [local irreducible] SourceClockYukawaCubicCurrent.resolventCore
  GaussDiagonalHistory.diagonalAction compressionCore defectAction state

private theorem pair_add_l (p q v : QuantumTest) :
    sourcePair (p+q) v=sourcePair p v+sourcePair q v := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r (p q v : QuantumTest) :
    sourcePair p (q+v)=sourcePair p q+sourcePair p v := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l (p q v : QuantumTest) :
    sourcePair (p-q) v=sourcePair p v-sourcePair q v := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r (p q v : QuantumTest) :
    sourcePair p (q-v)=sourcePair p q-sourcePair p v := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l (c : ℂ) (p q : QuantumTest) :
    sourcePair (c • p) q=(starRingEnd ℂ c)*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_smul_r (c : ℂ) (p q : QuantumTest) :
    sourcePair p (c • q)=c*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_neg_l (p q : QuantumTest) : sourcePair (-p) q= -sourcePair p q := by
  simp only [sourcePair,map_neg,inner_neg_left]
private theorem pair_neg_r (p q : QuantumTest) : sourcePair p (-q)= -sourcePair p q := by
  simp only [sourcePair,map_neg,inner_neg_right]

private theorem compression_pair (F : Index) : GaussCoframeForm.Paired (compressionCore F) (compressionCore F) := by
  intro p q
  have he (f : QuantumTest) : embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [sourcePair,he]
  exact (GaussGradedCompression.compression_pair F _ _).symm
private theorem defect_pair (F : Index) : GaussCoframeForm.Paired (defectAction F) (defectAction F) := by
  intro p q
  unfold defectAction
  simp only [LinearMap.sub_apply,pair_sub_l,pair_sub_r,diagonalAction_pair]
  rw [compression_pair F p q]
private theorem radius_square_pair : GaussCoframeForm.Paired T T := by
  intro p q
  have hr (f k : QuantumTest) : sourcePair f (r k)=sourcePair (r f) k := multiply_pair _ _ _ _
  change sourcePair p ((r^2) q)=sourcePair ((r^2) p) q
  simp only [pow_two,Module.End.mul_apply]
  rw [hr,hr]
private theorem bracket_pair {X Y : End} (hX : GaussCoframeForm.Paired X X)
    (hY : GaussCoframeForm.Paired Y Y) (p q : QuantumTest) :
    sourcePair p (bracket X Y q)= -sourcePair (bracket X Y p) q := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_l,pair_sub_r]
  rw [hX,hY,←hX,hY]
  ring
private theorem B_pair (p q : QuantumTest) : sourcePair p (B q)= -sourcePair (B p) q :=
  bracket_pair diagonalAction_pair radius_square_pair p q
private theorem Bd_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (Bd F q)= -sourcePair (Bd F p) q := bracket_pair (defect_pair F) radius_square_pair p q
private theorem Kc_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (Kc F q)= -sourcePair (Kc F p) q := bracket_pair (compression_pair F) radius_square_pair p q
private theorem current_join (F : Index) : Kc F+Bd F=B := by
  unfold Kc Bd B defectAction bracket
  noncomm_ring
private theorem three_defects (F : Index) :
    accelerationDefect F=bracket (compressionCore F) (Bd F)+bracket (defectAction F) B := by
  unfold accelerationDefect Bd B defectAction bracket
  noncomm_ring

private theorem resolvent_equation (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    compressionCore F (resolventCore F z hz f)=f+z • resolventCore F z hz f := by
  have he (k : QuantumTest) : embed (compressionCore F k)=GaussGradedCompression.compression F (embed k) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hr (k : QuantumTest) : embed (resolventCore F z hz k)=finiteResolvent F z (embed k) := by
    unfold resolventCore state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
    (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change (GaussGradedCompression.compression F-z • 1) (finiteResolvent F z (embed f))=embed f at h
  apply embed_injective
  simp only [he,hr,map_add,map_smul]
  simp only [sub_apply,smul_apply,one_apply_eq_self] at h
  linear_combination (norm := module) h

private theorem first_green {X : End} (hX : GaussCoframeForm.Paired X X)
    (Y : End) (p q : QuantumTest) : sourcePair p (bracket X Y q)=
      sourcePair (X p) (Y q)-sourcePair p (Y (X q)) := by
  change sourcePair p (X (Y q)-Y (X q))=_
  rw [pair_sub_r,hX p (Y q)]
private theorem frequency_difference (z : ℂ) : z-starRingEnd ℂ z=2*Complex.I*(z.im:ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

private theorem green_complex (F : Index) (q p g f : QuantumTest) (z : ℂ)
    (hq : compressionCore F q=g+z • q) (hp : compressionCore F p=f+z • p) :
    sourcePair q (bracket (compressionCore F) (Kc F) p)=
      sourcePair g (Kc F p)-sourcePair q (Kc F f)-
      (z-starRingEnd ℂ z)*sourcePair g (T p)+
      (z-starRingEnd ℂ z)*sourcePair q (T f)+
      (z-starRingEnd ℂ z)^2*sourcePair q (T p) := by
  have h1 := first_green (compression_pair F) (Kc F) q p
  have h2 := first_green (compression_pair F) T q p
  change sourcePair q (Kc F p)=
    sourcePair (compressionCore F q) (T p)-sourcePair q (T (compressionCore F p)) at h2
  rw [hq,hp] at h1 h2
  simp only [map_add,map_smul,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r] at h1 h2
  linear_combination (norm := ring) h1-(z-starRingEnd ℂ z)*h2
private theorem green_real (F : Index) (q p g f : QuantumTest) (z : ℂ)
    (hq : compressionCore F q=g+z • q) (hp : compressionCore F p=f+z • p) :
    (sourcePair q (bracket (compressionCore F) (Kc F) p)).re=
      -4*z.im^2*(sourcePair q (T p)).re+
      (sourcePair g (Kc F p)).re+2*z.im*(sourcePair g (T p)).im-
      (sourcePair q (Kc F f)).re-2*z.im*(sourcePair q (T f)).im := by
  have h := congrArg Complex.re (green_complex F q p g f z hq hp)
  rw [frequency_difference z] at h
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,pow_two] at h
  linear_combination (norm := ring) h
private theorem defect_descent (F : Index) (q p g f : QuantumTest) (z : ℂ)
    (hq : compressionCore F q=g+z • q) (hp : compressionCore F p=f+z • p) :
    sourcePair q (accelerationDefect F p)=
      sourcePair g (Bd F p)-sourcePair q (Bd F f)-
      (z-starRingEnd ℂ z)*sourcePair q (Bd F p)+
      sourcePair (defectAction F q) (B p)+sourcePair (B q) (defectAction F p) := by
  rw [three_defects]
  change sourcePair q (bracket (compressionCore F) (Bd F) p+bracket (defectAction F) B p)=_
  rw [pair_add_r,first_green (compression_pair F) (Bd F) q p,first_green (defect_pair F) B q p,
    B_pair q (defectAction F p),hq,hp]
  simp only [map_add,map_smul,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r]
  ring

private theorem joined_green (F : Index) (q p g f : QuantumTest) (z : ℂ)
    (hq : compressionCore F q=g+z • q) (hp : compressionCore F p=f+z • p) :
    (sourcePair q (bracket (compressionCore F) (Kc F) p)).re+
      (sourcePair q (accelerationDefect F p)).re=
    -4*z.im^2*(sourcePair q (T p)).re+
      (sourcePair g (B p)).re+2*z.im*(sourcePair g (T p)).im+
      (sourcePair (K z q) f).re+(sourcePair (Bd F q) ((2*Complex.I*(z.im:ℂ)) • p)).re+
      (sourcePair (defectAction F q) (B p)).re+(sourcePair (B q) (defectAction F p)).re := by
  have hG := green_real F q p g f z hq hp
  have hD := congrArg Complex.re (defect_descent F q p g f z hq hp)
  have hjoin := LinearMap.congr_fun (current_join F) p
  have hjoinf := LinearMap.congr_fun (current_join F) q
  change Kc F p+Bd F p=B p at hjoin
  change Kc F q+Bd F q=B q at hjoinf
  have hfix := congrArg (fun t => (sourcePair g t).re) hjoin
  have hforce := congrArg (fun t => (sourcePair t f).re) hjoinf
  rw [Kc_pair F q f] at hG
  rw [Bd_pair F q f,Bd_pair F q p,frequency_difference z] at hD
  rw [radius_square_pair q f] at hG
  simp only [Complex.neg_re] at hG
  simp only [pair_add_r,pair_add_l,Complex.add_re] at hfix hforce
  simp only [K,LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_l,pair_smul_l,pair_smul_r,
    Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
    map_mul,map_ofNat,Complex.conj_I,Complex.conj_ofReal,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat] at hD ⊢
  linear_combination (norm := ring) hG+hD+hfix+hforce

private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (phiReciprocal x:ℂ) • ((phiRadius x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem inverse_theta (m ell : ℕ) : Commute S (phiThetaAction m ell) :=
  (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (m+1)).sub_right
    (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (ell+1))
private theorem radius_theta (m ell : ℕ) : Commute r (phiThetaAction m ell) := by
  have hrS : Commute r S := by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
    exact smul_comm (phiRadius x:ℂ) (phiReciprocal x:ℂ) (f x)
  exact (((Commute.one_right r).sub_right hrS).pow_right (m+1)).sub_right
    (((Commute.one_right r).sub_right hrS).pow_right (ell+1))
private theorem paired_sub {X Y : End} (hX : GaussCoframeForm.Paired X X)
    (hY : GaussCoframeForm.Paired Y Y) : GaussCoframeForm.Paired (X-Y) (X-Y) := by
  intro f k
  simp only [LinearMap.sub_apply,pair_sub_l,pair_sub_r]
  rw [hX f k,hY f k]
private theorem paired_pow {X : End} (hX : GaussCoframeForm.Paired X X) (j : ℕ) :
    GaussCoframeForm.Paired (X^j) (X^j) := by
  induction j with
  | zero => intro f k;rfl
  | succ j ih =>
    intro f k
    simp only [pow_succ,Module.End.mul_apply]
    rw [ih,hX]
    exact congrArg (fun t => sourcePair t k)
      (LinearMap.congr_fun ((Commute.refl X).pow_left j).eq f).symm
private theorem theta_pair (m ell : ℕ) : GaussCoframeForm.Paired (phiThetaAction m ell) (phiThetaAction m ell) := by
  have h1 : GaussCoframeForm.Paired (1:End) 1 := by intro f k;rfl
  exact paired_sub (paired_pow (paired_sub h1 (multiply_pair _ _)) (m+1))
    (paired_pow (paired_sub h1 (multiply_pair _ _)) (ell+1))
private theorem a_pair (m ell : ℕ) (f k : QuantumTest) :
    sourcePair f (a m ell k)=sourcePair (a m ell f) k := by
  change sourcePair f (S (phiThetaAction m ell k))=sourcePair (S (phiThetaAction m ell f)) k
  have hS (u v : QuantumTest) : sourcePair u (S v)=sourcePair (S u) v := multiply_pair _ _ _ _
  rw [hS,theta_pair m ell]
  exact congrArg (fun t => sourcePair t k) (LinearMap.congr_fun (inverse_theta m ell).eq f).symm

/-- The complete native cutoff current before any split of its scalar, coframe or density rows. -/
def nativeCutoff (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  bracket diagonalAction ((phiThetaAction m ell)^2) (resolventCore F z hz (coreEquiv.symm g))-
    bracket diagonalAction (S*(phiThetaAction m ell)^2) (resolventCore F z hz (r (coreEquiv.symm g)))
private def cutDefect (m ell : ℕ) (F : Index) (q h : QuantumTest) : QuantumTest :=
  bracket (defectAction F) ((phiThetaAction m ell)^2) q-
    bracket (defectAction F) (S*(phiThetaAction m ell)^2) h
private def coherent (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  SourceClockPhiRadiusResponseHessian.phiCoherentDefect m ell F z hz g
private def tester (α : ℝ) (v : QuantumTest) : QuantumTest :=
  v+(4*α:ℂ) • SourceClockAcceleration.clockCurrent v+(Complex.I*(α:ℂ)*(n:ℂ)) • U v

private theorem endpoint_expansion (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    endpointState m ell F z hz g=
      ((phiThetaAction m ell)^2) (resolventCore F z hz (coreEquiv.symm g))-
      (S*(phiThetaAction m ell)^2) (resolventCore F z hz (r (coreEquiv.symm g))) := by
  have hSr : S*(phiThetaAction m ell)^2*r=(phiThetaAction m ell)^2 := by
    rw [mul_assoc,←((radius_theta m ell).pow_right 2).eq,←mul_assoc,inverse_radius,one_mul]
  have he := LinearMap.congr_fun hSr (resolventCore F z hz (coreEquiv.symm g))
  simp only [Module.End.mul_apply] at he
  unfold endpointState phiResponseCore bracket
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,pow_two] at he ⊢
  rw [he]
private theorem defect_endpoint (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    defectAction F (endpointState m ell F z hz g)=
      a m ell (coherent m ell F z hz g)+cutDefect m ell F
        (resolventCore F z hz (coreEquiv.symm g)) (resolventCore F z hz (r (coreEquiv.symm g))) := by
  rw [endpoint_expansion]
  have hSr : S*(phiThetaAction m ell)^2*r=(phiThetaAction m ell)^2 := by
    rw [mul_assoc,←((radius_theta m ell).pow_right 2).eq,←mul_assoc,inverse_radius,one_mul]
  have he := LinearMap.congr_fun hSr (defectAction F (resolventCore F z hz (coreEquiv.symm g)))
  unfold a coherent SourceClockPhiRadiusResponseHessian.phiCoherentDefect cutDefect
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pow_two,map_sub] at he ⊢
  linear_combination (norm := module) -he
private theorem cutoff_source_algebra (C L M : End) (q h g k : QuantumTest) (z : ℂ)
    (hq : C q=g+z • q) (hh : C h=k+z • h) (hg : L g=M k) :
    C (L q-M h)-z • (L q-M h)=bracket C L q-bracket C M h := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub,hq,hh,map_add,map_smul,hg]
  module
private theorem endpoint_forcing (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    compressionCore F (endpointState m ell F z hz g)-z • endpointState m ell F z hz g=
      nativeCutoff m ell F z hz g-cutDefect m ell F
        (resolventCore F z hz (coreEquiv.symm g)) (resolventCore F z hz (r (coreEquiv.symm g))) := by
  let L : End := (phiThetaAction m ell)^2
  let M : End := S*(phiThetaAction m ell)^2
  have hSr : M*r=L := by
    dsimp only [M,L]
    rw [mul_assoc,←((radius_theta m ell).pow_right 2).eq,←mul_assoc,inverse_radius,one_mul]
  have hg : L (coreEquiv.symm g)=M (r (coreEquiv.symm g)) :=
    (LinearMap.congr_fun hSr (coreEquiv.symm g)).symm
  have hC (A : End) : bracket diagonalAction A-bracket (defectAction F) A=bracket (compressionCore F) A := by
    unfold defectAction bracket
    noncomm_ring
  have he := cutoff_source_algebra (compressionCore F) L M _ _ _ _ z
    (resolvent_equation F z hz (coreEquiv.symm g))
    (resolvent_equation F z hz (r (coreEquiv.symm g))) hg
  rw [endpoint_expansion]
  have hL := LinearMap.congr_fun (hC L) (resolventCore F z hz (coreEquiv.symm g))
  have hM := LinearMap.congr_fun (hC M) (resolventCore F z hz (r (coreEquiv.symm g)))
  change bracket diagonalAction L (resolventCore F z hz (coreEquiv.symm g))-
    bracket (defectAction F) L (resolventCore F z hz (coreEquiv.symm g))=
    bracket (compressionCore F) L (resolventCore F z hz (coreEquiv.symm g)) at hL
  change bracket diagonalAction M (resolventCore F z hz (r (coreEquiv.symm g)))-
    bracket (defectAction F) M (resolventCore F z hz (r (coreEquiv.symm g)))=
    bracket (compressionCore F) M (resolventCore F z hz (r (coreEquiv.symm g))) at hM
  unfold nativeCutoff cutDefect
  dsimp only [L,M] at he hL hM
  linear_combination (norm := module) he-hL+hM

private theorem native_cost_algebra (F : Index) (z : ℂ) (q p u c w f : QuantumTest)
    (hd : defectAction F p=u+c) (hf : f=w-c) :
    (sourcePair (K z q) f).re+(sourcePair (Bd F q) ((2*Complex.I*(z.im:ℂ)) • p)).re+
      (sourcePair (defectAction F q) (B p)).re+(sourcePair (B q) (defectAction F p)).re=
    (sourcePair (K z q) (w+u)).re+(sourcePair (defectAction F q) (K z p)).re := by
  have hBd : sourcePair (Bd F q) p=
      sourcePair (T q) (defectAction F p)-sourcePair (defectAction F q) (T p) := by
    change sourcePair (defectAction F (T q)-T (defectAction F q)) p=_
    rw [pair_sub_l,←defect_pair F (T q) p,←radius_square_pair (defectAction F q) p]
  rw [hf,pair_smul_r,hBd,hd]
  simp only [K,LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_l,pair_sub_r,
    pair_add_r,pair_smul_l,pair_smul_r,map_mul,map_ofNat,Complex.conj_I,Complex.conj_ofReal,
    Complex.add_re,Complex.sub_re,Complex.add_im,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,
    Complex.re_ofNat,Complex.im_ofNat]
  ring
private theorem native_join (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) :
    let q := resolventCore F z hz (coreEquiv.symm g)
    let p := endpointState m ell F z hz g
    let dc := coherent m ell F z hz g
    let fp := compressionCore F p-z • p
    2*α*((sourcePair (K z q) fp).re+
      (sourcePair (Bd F q) ((2*Complex.I*(z.im:ℂ)) • p)).re+
      (sourcePair (defectAction F q) (B p)).re+(sourcePair (B q) (defectAction F p)).re)-
      (sourcePair (tester α (phiResponseCore m ell F z hz g)) dc).im=
    2*α*((sourcePair (K z q) (nativeCutoff m ell F z hz g+a m ell dc)).re+
      (sourcePair (defectAction F q) (K z p)).re)-
      (sourcePair (tester α (phiResponseCore m ell F z hz g)) dc).im := by
  dsimp only
  have he := native_cost_algebra F z (resolventCore F z hz (coreEquiv.symm g))
    (endpointState m ell F z hz g) (a m ell (coherent m ell F z hz g))
    (cutDefect m ell F (resolventCore F z hz (coreEquiv.symm g))
      (resolventCore F z hz (r (coreEquiv.symm g))))
    (nativeCutoff m ell F z hz g)
    (compressionCore F (endpointState m ell F z hz g)-z • endpointState m ell F z hz g)
    (defect_endpoint m ell F z hz g) (endpoint_forcing m ell F z hz g)
  linear_combination (norm := ring) (2*α)*he

private theorem radius_metric (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    let q := resolventCore F z hz (coreEquiv.symm g)
    let h := resolventCore F z hz (r (coreEquiv.symm g))
    let v := phiResponseCore m ell F z hz g
    (sourcePair q (T (endpointState m ell F z hz g))).re=
      ‖embed v‖^2+(sourcePair (phiThetaAction m ell h) v).re := by
  dsimp only
  have hrr : (r^2)*S=r := by
    have hrS : r*S=1 := by
      apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
      change (phiRadius x:ℂ) • ((phiReciprocal x:ℂ) • f x)=f x
      rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
    rw [pow_two,mul_assoc,hrS,mul_one]
  have he := LinearMap.congr_fun hrr (phiThetaAction m ell (phiResponseCore m ell F z hz g))
  change T (endpointState m ell F z hz g)=r (phiThetaAction m ell (phiResponseCore m ell F z hz g)) at he
  have hr (u v : QuantumTest) : sourcePair u (r v)=sourcePair (r u) v := multiply_pair _ _ _ _
  rw [he,hr,theta_pair m ell]
  have hcomm := LinearMap.congr_fun (radius_theta m ell).eq (resolventCore F z hz (coreEquiv.symm g))
  change r (phiThetaAction m ell (resolventCore F z hz (coreEquiv.symm g)))=
    phiThetaAction m ell (r (resolventCore F z hz (coreEquiv.symm g))) at hcomm
  have hv : phiThetaAction m ell (r (resolventCore F z hz (coreEquiv.symm g)))=
      phiResponseCore m ell F z hz g+
        phiThetaAction m ell (resolventCore F z hz (r (coreEquiv.symm g))) := by
    simp only [phiResponseCore,bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
    abel
  rw [hv,pair_add_l,Complex.add_re]
  congr 1
  simpa only [sourcePair] using! inner_self_eq_norm_sq (𝕜 := ℂ)
    (embed (phiResponseCore m ell F z hz g))

/-- The literal scalar endpoint and the original coherent tester, prior to clipping. -/
def testedEndpoint (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) : ℝ :=
  let q := resolventCore F z hz (coreEquiv.symm g)
  2*α*(n^2/8*(sourcePair (sourceLq q) (endpointWord (endpointState m ell F z hz g))).im)-
    (sourcePair (tester α (phiResponseCore m ell F z hz g)) (coherent m ell F z hz g)).im

/-- All native cutoff forcing and both first-defect legs remain in a single real word. -/
def wholeRemainder (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) : ℝ :=
  let q := resolventCore F z hz (coreEquiv.symm g)
  let p := endpointState m ell F z hz g
  let dc := coherent m ell F z hz g
  2*α*((sourcePair q ((scalarAcceleration+stableSpatialAcceleration+
        ((n:ℂ)^2/4) • (U*U*Phi)) p)).re-
      n^2/16*(sourcePair (((1:End)-S^2) q) (endpointWord p)).im+
      (sourcePair (K z q) (nativeCutoff m ell F z hz g+a m ell dc)).re+
      (sourcePair (defectAction F q) (K z p)).re)-
    (sourcePair (tester α (phiResponseCore m ell F z hz g)) dc).im

/-- Same-CF Green and all three double defects combine before any estimate. -/
theorem actual_phi_whole_green_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) :
    testedEndpoint m ell F z hz g α=
      -8*α*z.im^2*‖embed (phiResponseCore m ell F z hz g)‖^2-
      8*α*z.im^2*(sourcePair
        (phiThetaAction m ell (resolventCore F z hz (r (coreEquiv.symm g))))
        (phiResponseCore m ell F z hz g)).re+
      2*α*((sourcePair (coreEquiv.symm g) (B (endpointState m ell F z hz g))).re+
        2*z.im*(sourcePair (coreEquiv.symm g) (T (endpointState m ell F z hz g))).im)+
      wholeRemainder m ell F z hz g α := by
  let q := resolventCore F z hz (coreEquiv.symm g)
  let p := endpointState m ell F z hz g
  let fp := compressionCore F p-z • p
  have hp : compressionCore F p=fp+z • p := by dsimp only [fp];module
  have hG := joined_green F q p (coreEquiv.symm g) fp z (resolvent_equation F z hz _) hp
  have hN := native_join m ell F z hz g α
  have hM := radius_metric m ell F z hz g
  have hE := actual_phi_endpoint_compression m ell F z hz g
  have he : (S*(phiThetaAction m ell)^2)
      (r q-resolventCore F z hz (r (coreEquiv.symm g)))=p := by
    simp only [p,endpointState,phiResponseCore,bracket,LinearMap.sub_apply,Module.End.mul_apply,pow_two,map_sub]
    rfl
  dsimp only at hE hN hM
  rw [he] at hE
  change n^2/8*(sourcePair (sourceLq q) (endpointWord p)).im=
    (sourcePair q ((scalarAcceleration+stableSpatialAcceleration+accelerationDefect F+
      bracket (compressionCore F) (Kc F)+((n:ℂ)^2/4) • (U*U*Phi)) p)).re-
    n^2/16*(sourcePair (((1:End)-S^2) q) (endpointWord p)).im at hE
  simp only [LinearMap.add_apply,pair_add_r,Complex.add_re] at hE
  have hfield : (sourcePair q ((scalarAcceleration+stableSpatialAcceleration+((n:ℂ)^2/4) • (U*U*Phi)) p)).re=
      (sourcePair q (scalarAcceleration p)).re+(sourcePair q (stableSpatialAcceleration p)).re+
      (sourcePair q ((((n:ℂ)^2/4) • (U*U*Phi)) p)).re := by
    simp only [LinearMap.add_apply,pair_add_r,Complex.add_re]
  unfold testedEndpoint wholeRemainder
  dsimp only
  linear_combination (norm := ring) (2*α)*hE+(2*α)*hG+hN-(8*α*z.im^2)*hM-(2*α)*hfield

private def greenError (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) : ℝ :=
  4*α*z.im^2*‖embed (phiThetaAction m ell (resolventCore F z hz (r (coreEquiv.symm g))))‖^2+
    2*α*(‖embed (B (coreEquiv.symm g))‖+2*|z.im| *‖embed (T (coreEquiv.symm g))‖)*
      ‖embed (endpointState m ell F z hz g)‖
private theorem green_point_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) (hα : 0 ≤ α) :
    testedEndpoint m ell F z hz g α+4*α*z.im^2*‖embed (phiResponseCore m ell F z hz g)‖^2≤
      wholeRemainder m ell F z hz g α+greenError m ell F z hz g α := by
  let v := phiResponseCore m ell F z hz g
  let t := phiThetaAction m ell (resolventCore F z hz (r (coreEquiv.symm g)))
  let p := endpointState m ell F z hz g
  have hcross : -(sourcePair t v).re≤‖embed t‖*‖embed v‖ :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
  have hdiag : -8*α*z.im^2*‖embed v‖^2-8*α*z.im^2*(sourcePair t v).re+
      4*α*z.im^2*‖embed v‖^2≤4*α*z.im^2*‖embed t‖^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 4*α*z.im^2 by positivity)
      (sq_nonneg (‖embed t‖-‖embed v‖)),
      mul_le_mul_of_nonneg_left hcross (show 0 ≤ 8*α*z.im^2 by positivity)]
  have hb : (sourcePair (coreEquiv.symm g) (B p)).re≤
      ‖embed (B (coreEquiv.symm g))‖*‖embed p‖ := by
    rw [B_pair,Complex.neg_re]
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
  have ht : |(sourcePair (coreEquiv.symm g) (T p)).im|≤
      ‖embed (T (coreEquiv.symm g))‖*‖embed p‖ := by
    rw [radius_square_pair]
    exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have hti : 2*z.im*(sourcePair (coreEquiv.symm g) (T p)).im≤
      2*|z.im| *‖embed (T (coreEquiv.symm g))‖*‖embed p‖ := by
    have h := le_abs_self (z.im*(sourcePair (coreEquiv.symm g) (T p)).im)
    rw [abs_mul] at h
    have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg z.im)
    nlinarith
  have hfix := mul_le_mul_of_nonneg_left (add_le_add hb hti) (show 0 ≤ 2*α by positivity)
  rw [actual_phi_whole_green_source]
  dsimp only [greenError]
  dsimp only [v,t,p] at hdiag hfix
  linarith only [hdiag,hfix]

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem frequency_im (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (actualFrequency advanced μ w).im^2=μ^2 ∧ |(actualFrequency advanced μ w).im|=μ := by
  cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_sq,abs_neg,abs_of_pos hμ,and_self]
private theorem finite_star (F : Index) (z : ℂ) :
    finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (F : Index) :
    Continuous (fun w : ℝ => finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have h : (fun w : ℝ => finiteResolvent F (actualFrequency true μ w))=
        fun w : ℝ => (finiteResolvent F (line μ w)).adjoint := by
      funext w;exact finite_star F _
    exact h ▸ (ContinuousLinearMap.adjoint.continuous.comp
      (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F))
private theorem read_core (F : Index) (f : QuantumTest) (A : End) (z : ℂ) (hz : z.im≠0) :
    sourceRead F (coreEquiv f) A (finiteResolvent F z (embed f))=embed (A (resolventCore F z hz f)) := by
  have h := source_read_resolvent F (coreEquiv f) A z hz
  have he : ((coreEquiv f : Core) : H)=embed f := rfl
  rw [he] at h
  simpa only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,state] using h
private theorem theta_continuous (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (advanced : Bool) :
    Continuous (fun w : ℝ => embed (phiThetaAction m ell
      (resolventCore F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w)
        (r (coreEquiv.symm g))))) := by
  simp_rw [←read_core]
  exact (sourceRead F (coreEquiv (r (coreEquiv.symm g))) (phiThetaAction m ell)).continuous.comp
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)
private theorem endpoint_continuous (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (advanced : Bool) :
    Continuous (fun w : ℝ => embed (endpointState m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)) := by
  simp_rw [endpoint_expansion,map_sub,←read_core]
  exact ((sourceRead F (coreEquiv (coreEquiv.symm g)) ((phiThetaAction m ell)^2)).continuous.comp
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).sub
    ((sourceRead F (coreEquiv (r (coreEquiv.symm g))) (S*(phiThetaAction m ell)^2)).continuous.comp
      ((frequency_continuous advanced μ hμ F).clm_apply continuous_const))
private theorem error_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (α : ℝ) (advanced : Bool) :
    Measurable (fun w : ℝ => ENNReal.ofReal (greenError m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g α)) := by
  simp_rw [greenError,(frequency_im advanced μ hμ _).1,(frequency_im advanced μ hμ _).2]
  exact (((continuous_const.mul ((theta_continuous m ell F μ hμ g advanced).norm.pow 2)).add
    (continuous_const.mul (endpoint_continuous m ell F μ hμ g advanced).norm)).measurable).ennreal_ofReal
private theorem error_common_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (α : ℝ) (hα : 0 < α) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (greenError m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g α))≤ENNReal.ofReal ε := by
  intro ε hε
  let C1 : ℝ := 4*α*μ^2
  let C2 : ℝ := 2*α*(‖embed (B (coreEquiv.symm g))‖+2*μ*‖embed (T (coreEquiv.symm g))‖)
  have hC1 : 0 ≤ C1 := by dsimp only [C1];positivity
  have hC2 : 0 ≤ C2 := by dsimp only [C2];positivity
  let δ : ℝ := ε/(C1+C2+1)
  have hδ : 0 < δ := by dsimp only [δ];positivity
  obtain ⟨N1,h1⟩ := actual_phi_theta_common_tail μ hμ (phiRadiusSource g) δ hδ
  obtain ⟨N2,h2⟩ := actual_endpoint_absolute_common_tail μ hμ g δ hδ
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m (le_trans (le_max_left _ _) hm) ell hml,
    h2 m (le_trans (le_max_right _ _) hm) ell hml] with F hF1 hF2
  intro advanced
  let X : ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖embed (phiThetaAction m ell
    (resolventCore F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w)
      (r (coreEquiv.symm g))))‖^2)
  let Y : ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖embed (endpointState m ell F
    (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)‖)
  have hmX : Measurable X := ((theta_continuous m ell F μ hμ g advanced).norm.pow 2).measurable.ennreal_ofReal
  have hX : (∫⁻ w,X w)≤ENNReal.ofReal δ := by
    simpa only [X,resolventCore,LinearMap.coe_mk,AddHom.coe_mk,phiRadiusSource] using hF1 advanced
  have hY : (∫⁻ w,Y w)≤ENNReal.ofReal δ := hF2 advanced
  have he (w : ℝ) : ENNReal.ofReal (greenError m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g α)=ENNReal.ofReal C1*X w+ENNReal.ofReal C2*Y w := by
    simp only [greenError,(frequency_im advanced μ hμ w).1,(frequency_im advanced μ hμ w).2]
    change ENNReal.ofReal (C1*_+C2*_)=_
    rw [ENNReal.ofReal_add (mul_nonneg hC1 (sq_nonneg _)) (mul_nonneg hC2 (norm_nonneg _)),
      ENNReal.ofReal_mul hC1,ENNReal.ofReal_mul hC2]
  calc
    _=ENNReal.ofReal C1*(∫⁻ w,X w)+ENNReal.ofReal C2*(∫⁻ w,Y w) := by
      simp_rw [he]
      have hmCX : Measurable (fun w => ENNReal.ofReal C1*X w) := measurable_const.mul hmX
      rw [lintegral_add_left hmCX,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _≤ENNReal.ofReal C1*ENNReal.ofReal δ+ENNReal.ofReal C2*ENNReal.ofReal δ := by
      gcongr
    _≤ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC1,←ENNReal.ofReal_mul hC2,
        ←ENNReal.ofReal_add (mul_nonneg hC1 hδ.le) (mul_nonneg hC2 hδ.le)]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [δ]
      rw [←add_mul,←mul_div_assoc]
      apply (div_le_iff₀ (show 0 < C1+C2+1 by positivity)).mpr
      nlinarith

/-- The fixed Green endpoints and reflected radius source are paid at one common cutoff.
The full native/coherent word is retained inside one positive part. -/
theorem actual_phi_whole_green_payment (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain)
    (α : ℝ) (hα : 0 < α) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal
          (testedEndpoint m ell F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g α+
            4*α*μ^2*‖embed (phiResponseCore m ell F (actualFrequency advanced μ w)
              (frequency_nonreal advanced μ hμ w) g)‖^2))≤ENNReal.ofReal ε+
        ∫⁻ w : ℝ,ENNReal.ofReal (wholeRemainder m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g α) := by
  intro ε hε
  obtain ⟨N,hN⟩ := error_common_tail μ hμ g α hα ε hε
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  let R : ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (wholeRemainder m ell F
    (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g α)
  let X : ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (greenError m ell F
    (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g α)
  have hmX : Measurable X := error_measurable m ell F μ hμ g α advanced
  calc
    _≤∫⁻ w,X w+R w := by
      apply lintegral_mono
      intro w
      dsimp only [X,R]
      have hp := green_point_price m ell F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g α hα.le
      rw [(frequency_im advanced μ hμ w).1] at hp
      exact (ENNReal.ofReal_le_ofReal hp).trans (by
        rw [add_comm]
        exact ENNReal.ofReal_add_le)
    _=(∫⁻ w,X w)+∫⁻ w,R w := lintegral_add_left hmX _
    _≤ENNReal.ofReal ε+∫⁻ w,R w := add_le_add (hF advanced) le_rfl

end LowEnergy.SourceClockPhiWholeCFGreenSource
