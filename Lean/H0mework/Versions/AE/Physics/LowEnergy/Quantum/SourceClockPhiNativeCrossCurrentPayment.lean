import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiNativeSignedCurrent
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiZeroSeedEndpointTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiNativeCrossCurrentPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussFockWeights GaussDensityCore SourceRelativePowerTail
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockPhiRadiusResponseHessian
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourcePhysicalKineticSquare SourceScalarPairedTransport
open SourceClockYukawaCubicCurrent SourceClockPhiRadiusResponsePositiveSource SourceClockPhiRadiusClockSturm
open SourceInverseJetEnergy FullYSourceResolventGraphSplice SourceLocalizedInverseFormPayment SourceResolventBandLimit
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev E : End := phiEulerAction
private abbrev Phi : End := SourceScalarAffineScaleTransport.generator
private abbrev U : End := inverseVolumeAction
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev M (m ell : ℕ) : End := U*(T m ell)^2
private abbrev n : ℝ := sourceTime 0
attribute [local irreducible] resolventCore compressionCore defectAction diagonalAction
  SourceScalarPositiveBulkWard.state GaussAdjointHistory.coreStep sourcePair embed

private def weightedGenerator := SourceClockPhiNativeSignedCurrent.weightedGenerator
private abbrev fieldCurrent := SourceClockPhiNativeSignedCurrent.fieldCurrent
private abbrev signedCurrent := SourceClockPhiNativeSignedCurrent.signedCurrent
private theorem pair_add_l (f g h:QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r (f g h:QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l (f g h:QuantumTest) : sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r (f g h:QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l (c:ℂ) (f g:QuantumTest) : sourcePair (c • f) g=(starRingEnd ℂ c)*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_smul_r (c:ℂ) (f g:QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem phi_pair (f g:QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g := by
  have h:=SourceClockPhiRadiusClockSturm.phi_profile_paired_derivative (1:End) f g
  have hz:bracket E (1:End)=0 := by simp [bracket]
  rw [hz] at h
  simp only [Module.End.one_apply,zero_add,LinearMap.smul_apply] at h
  change sourcePair f (E g)= -sourcePair (E f) g-sourcePair f ((61:ℂ) • g) at h
  simp only [Phi,SourceScalarAffineScaleTransport.generator,LinearMap.add_apply,
    LinearMap.smul_apply,Module.End.one_apply,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r] at h ⊢
  norm_num only [map_div₀,map_ofNat,map_one]
  linear_combination (norm:=ring) h
private theorem real_commute (a b:SourceCoordinateSlice → ℝ)
    (ha:∀z:physicalChart,ContDiffAt ℝ ∞ a z.val) (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val) :
    Commute (multiply a ha) (multiply b hb) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (a z:ℂ) (b z:ℂ) (f z)
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse : r*S=(1:End) := (real_commute _ _ _ _).eq.symm.trans inverse_radius
private theorem commute_inverse {A:End} (ha:Commute A r) : Commute A S := by
  change A*S=S*A
  have h:=congrArg (fun B:End=>S*B*S) ha.eq
  simp only [mul_assoc,radius_inverse,mul_one] at h
  simpa only [←mul_assoc,inverse_radius,one_mul] using h.symm
private theorem theta_commute {A:End} (ha:Commute A S) (m ell:ℕ) : Commute A (T m ell) :=
  (((Commute.one_right A).sub_right ha).pow_right (m+1)).sub_right
    (((Commute.one_right A).sub_right ha).pow_right (ell+1))
private theorem pair_product {A B:End} (ha:GaussCoframeForm.Paired A A)
    (hb:GaussCoframeForm.Paired B B) (hc:Commute A B) : GaussCoframeForm.Paired (A*B) (A*B) := by
  intro f g
  change sourcePair f (A (B g))=sourcePair (A (B f)) g
  rw [ha,hb]
  exact congrArg (fun p=>sourcePair p g) (LinearMap.congr_fun hc.eq f).symm
private theorem pair_power {A:End} (ha:GaussCoframeForm.Paired A A) (k:ℕ) : GaussCoframeForm.Paired (A^k) (A^k) := by
  induction k with
  | zero => intro f g;rfl
  | succ k ih => rw [pow_succ];exact pair_product ih ha ((Commute.refl A).pow_left k)
private theorem pair_sub {A B:End} (ha:GaussCoframeForm.Paired A A)
    (hb:GaussCoframeForm.Paired B B) : GaussCoframeForm.Paired (A-B) (A-B) := by
  intro f g
  simp only [LinearMap.sub_apply,pair_sub_l,pair_sub_r]
  rw [ha f g,hb f g]
private theorem theta_pair (m ell:ℕ) : GaussCoframeForm.Paired (T m ell) (T m ell) := by
  have h1:GaussCoframeForm.Paired (1:End) 1 := by intro f g;rfl
  exact pair_sub (pair_power (pair_sub h1 (multiply_pair _ _)) (m+1))
    (pair_power (pair_sub h1 (multiply_pair _ _)) (ell+1))
private theorem weight_pair (m ell:ℕ) : GaussCoframeForm.Paired (M m ell) (M m ell) :=
  pair_product (multiply_pair _ _) (pair_power (theta_pair m ell) 2)
    ((theta_commute (real_commute _ _ _ _) m ell).pow_right 2)
private theorem generator_pair (m ell:ℕ) (f g:QuantumTest) :
    sourcePair f (weightedGenerator m ell g)= -sourcePair (weightedGenerator m ell f) g := by
  have h1:sourcePair f (M m ell (Phi g))= -sourcePair (Phi (M m ell f)) g := by
    rw [weight_pair,phi_pair]
  have h2:sourcePair f (Phi (M m ell g))= -sourcePair (M m ell (Phi f)) g := by
    rw [phi_pair,weight_pair]
  unfold weightedGenerator SourceClockPhiNativeSignedCurrent.weightedGenerator
  simp only [LinearMap.smul_apply,LinearMap.add_apply,pair_smul_l,pair_smul_r,pair_add_l,pair_add_r]
  change (1/2:ℂ)*(sourcePair f (M m ell (Phi g))+sourcePair f (Phi (M m ell g)))=
    -(starRingEnd ℂ (1/2:ℂ)*(sourcePair (M m ell (Phi f)) g+sourcePair (Phi (M m ell f)) g))
  rw [h1,h2]
  norm_num only [map_div₀,map_one,map_ofNat]
  ring
private theorem compression_pair (F:Index) : GaussCoframeForm.Paired (compressionCore F) (compressionCore F) := by
  intro f g
  have he (u:QuantumTest):embed (compressionCore F u)=GaussGradedCompression.compression F (embed u) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [sourcePair,he]
  exact (GaussGradedCompression.compression_pair F _ _).symm
private theorem resolvent_source (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    compressionCore F (resolventCore F z hz (coreEquiv.symm g))=
      coreEquiv.symm g+z • resolventCore F z hz (coreEquiv.symm g) := by
  have he (u:QuantumTest):embed (compressionCore F u)=GaussGradedCompression.compression F (embed u) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hr (u:QuantumTest):embed (resolventCore F z hz u)=finiteResolvent F z (embed u) := by
    unfold resolventCore SourceScalarPositiveBulkWard.state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have h:=congrArg (fun A:H →L[ℂ] H=>A (g:H))
    (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
  apply embed_injective
  simp only [he,hr,map_add,map_smul]
  have hg:embed (coreEquiv.symm g)=(g:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply g)
  rw [hg]
  change (GaussGradedCompression.compression F-z • 1) (finiteResolvent F z (g:H))=(g:H) at h
  simp only [sub_apply,smul_apply,one_apply_eq_self] at h
  linear_combination (norm:=module) h

private theorem paired_resolvent_current (A C:End)
    (hA:∀f g:QuantumTest,sourcePair f (A g)= -sourcePair (A f) g)
    (hC:GaussCoframeForm.Paired C C) (q f:QuantumTest) (z:ℂ)
    (hq:C q=f+z • q) :
    (sourcePair q (bracket A C q)).re=
      -2*(sourcePair (A q) f).re+2*z.im*(sourcePair (A q) q).im := by
  change (sourcePair q (A (C q)-C (A q))).re=_
  rw [pair_sub_r,hA q (C q),hC q (A q),hq,pair_add_r,pair_smul_r,pair_add_l,pair_smul_l]
  rw [hA q q,←pair_conjugate (A q) f]
  simp only [Complex.sub_re,Complex.neg_re,Complex.add_re,Complex.mul_re,Complex.conj_re,
    Complex.conj_im,Complex.neg_im]
  ring
private theorem generator_source_pair (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    let q:=resolventCore F z hz (coreEquiv.symm g)
    (sourcePair q (bracket (weightedGenerator m ell) (compressionCore F) q)).re=
      -2*(sourcePair (weightedGenerator m ell q) (coreEquiv.symm g)).re+
        2*z.im*(sourcePair (weightedGenerator m ell q) q).im :=
  paired_resolvent_current _ _ (generator_pair m ell) (compression_pair F) _ _ z
    (resolvent_source F z hz g)

private abbrev W (m ell:ℕ) : End := U*S*T m ell
private theorem W_pair (m ell:ℕ) : GaussCoframeForm.Paired (W m ell) (W m ell) := by
  have hUS:Commute U S:=real_commute _ _ _ _
  have hU:Commute U (T m ell):=theta_commute hUS m ell
  have hS:Commute S (T m ell):=theta_commute (Commute.refl S) m ell
  exact pair_product (pair_product (multiply_pair _ _) (multiply_pair _ _) hUS)
    (theta_pair m ell) (hU.mul_left hS)
private theorem W_radius (m ell:ℕ) : W m ell*r*T m ell=M m ell := by
  have hS:Commute S r:=inverse_radius.trans radius_inverse.symm
  have hT:=theta_commute hS.symm m ell
  change U*S*T m ell*r*T m ell=U*(T m ell)^2
  calc _=U*(S*(T m ell*r))*T m ell := by simp only [mul_assoc]
       _=U*(S*(r*T m ell))*T m ell := by rw [←hT.eq]
       _=U*(S*r)*((T m ell)^2) := by simp only [mul_assoc,pow_two]
       _=_ := by rw [inverse_radius,mul_one]
private theorem generator_phase (m ell:ℕ) (q h:QuantumTest) :
    (sourcePair (weightedGenerator m ell q) q).im=
      (sourcePair (W m ell (Phi q)) (T m ell (r q-h))).im+
      (sourcePair (W m ell (Phi q)) (T m ell h)).im := by
  let c:=sourcePair (Phi q) (M m ell q)
  have hm:sourcePair (M m ell (Phi q)) q=c := (weight_pair m ell (Phi q) q).symm
  have hp:sourcePair (Phi (M m ell q)) q= -(starRingEnd ℂ c) := by
    calc _= -sourcePair (M m ell q) (Phi q) := by
           linear_combination (norm:=ring) phi_pair (M m ell q) q
         _=_ := congrArg Neg.neg (pair_conjugate (Phi q) (M m ell q)).symm
  have he:sourcePair (weightedGenerator m ell q) q=(1/2:ℂ)*(c-starRingEnd ℂ c) := by
    unfold weightedGenerator SourceClockPhiNativeSignedCurrent.weightedGenerator
    simp only [LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,pair_smul_l,pair_add_l]
    change (starRingEnd ℂ (1/2:ℂ))*(sourcePair (M m ell (Phi q)) q+sourcePair (Phi (M m ell q)) q)=_
    rw [hm,hp]
    norm_num only [map_div₀,map_one,map_ofNat]
    ring
  have hi:(sourcePair (weightedGenerator m ell q) q).im=c.im := by
    rw [he]
    simp only [Complex.mul_im,Complex.sub_im,Complex.conj_im,Complex.one_re,Complex.one_im,
      Complex.div_re,Complex.div_im,Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat]
    ring
  have hc:c=sourcePair (W m ell (Phi q)) (r (T m ell q)) := by
    rw [←W_pair]
    exact congrArg (sourcePair (Phi q)) (LinearMap.congr_fun (W_radius m ell) q).symm
  rw [hi,hc]
  have hT:Commute r (T m ell):=theta_commute (real_commute _ _ _ _) m ell
  have ht:=LinearMap.congr_fun hT.eq q
  change r (T m ell q)=T m ell (r q) at ht
  rw [ht]
  simp only [map_sub,pair_sub_r,Complex.sub_im]
  ring

private theorem generic_signed_return (m ell:ℕ) (F:Index) (z:ℂ) (q h u:QuantumTest)
    (hq:compressionCore F q=u+z • q):
    (sourcePair q ((SourceClockPhiNativeSignedCurrent.fieldCurrent m ell-
      bracket (SourceClockPhiNativeSignedCurrent.weightedGenerator m ell) (defectAction F)) q)).re-
      2*z.im*(sourcePair (W m ell (Phi q)) (T m ell (r q-h))).im=
    -2*(sourcePair (weightedGenerator m ell q) u).re+
      2*z.im*(sourcePair (W m ell (Phi q)) (T m ell h)).im := by
  have hc:SourceClockPhiNativeSignedCurrent.fieldCurrent m ell-
      bracket (SourceClockPhiNativeSignedCurrent.weightedGenerator m ell) (defectAction F)=
      bracket (weightedGenerator m ell) (compressionCore F) := by
    unfold weightedGenerator
    rw [←SourceClockPhiNativeSignedCurrent.original_weighted_phi_field_source]
    unfold bracket defectAction
    noncomm_ring
  have hs:=paired_resolvent_current _ _ (generator_pair m ell) (compression_pair F) q u z hq
  have hp:=generator_phase m ell q h
  rw [hc]
  linear_combination (norm:=ring) hs+(2*z.im)*hp
private theorem signed_current_return (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain):
    let q:=resolventCore F z hz (coreEquiv.symm g)
    let h:=resolventCore F z hz (r (coreEquiv.symm g))
    signedCurrent m ell F z hz g=
      -2*(sourcePair (weightedGenerator m ell q) (coreEquiv.symm g)).re+
        2*z.im*(sourcePair (W m ell (Phi q)) (T m ell h)).im := by
  let q:QuantumTest:=resolventCore F z hz (coreEquiv.symm g)
  let h:QuantumTest:=resolventCore F z hz (r (coreEquiv.symm g))
  have hs:=generic_signed_return m ell F z q h (coreEquiv.symm g) (resolvent_source F z hz g)
  have hv:T m ell (r q-h)=phiResponseCore m ell F z hz g := by
    unfold phiResponseCore bracket
    rfl
  have hp:=congrArg (fun v:QuantumTest=>(sourcePair (W m ell (Phi q)) v).im) hv
  let f:ℝ:=(sourcePair q ((SourceClockPhiNativeSignedCurrent.fieldCurrent m ell-
    bracket (SourceClockPhiNativeSignedCurrent.weightedGenerator m ell) (defectAction F)) q)).re
  calc
    _=f-2*z.im*(sourcePair (W m ell (Phi q)) (phiResponseCore m ell F z hz g)).im:=rfl
    _=f-2*z.im*(sourcePair (W m ell (Phi q)) (T m ell (r q-h))).im:=
      congrArg (fun x:ℝ=>f-2*z.im*x) hp.symm
    _=_:=hs

private def K0 : End := (n/2:ℂ) • (U*Phi)
private def C (m ell:ℕ) : End := S*(T m ell)^2
/-- The original mixed K0/window row, with its actual one-sided ordering. -/
def crossOperator (m ell:ℕ) : End := K0*C m ell
private def crossAdjoint (m ell:ℕ) : End := -(C m ell*K0)
private theorem pair_neg_l (f g:QuantumTest):sourcePair (-f) g= -sourcePair f g := by
  simp only [sourcePair,map_neg,inner_neg_left]
private theorem euler_U : Commute E U := sub_eq_zero.mp SourceScalarInverseBulk.inverse_phi
private theorem phi_U : Commute Phi U := by
  change (E+(61/2:ℂ) • 1)*U=U*(E+(61/2:ℂ) • 1)
  noncomm_ring [euler_U.eq]
private theorem K0_pair (f g:QuantumTest):sourcePair f (K0 g)= -sourcePair (K0 f) g := by
  have h:sourcePair f (U (Phi g))= -sourcePair (U (Phi f)) g := by
    have hu (p q:QuantumTest):sourcePair p (U q)=sourcePair (U p) q:=multiply_pair _ _ _ _
    rw [hu,phi_pair]
    exact congrArg (fun p=> -sourcePair p g) (LinearMap.congr_fun phi_U.eq f)
  simp only [K0,LinearMap.smul_apply,Module.End.mul_apply,pair_smul_r,pair_smul_l]
  rw [h]
  norm_num only [map_div₀,Complex.conj_ofReal,map_ofNat]
  ring
private theorem C_pair (m ell:ℕ):GaussCoframeForm.Paired (C m ell) (C m ell) :=
  pair_product (multiply_pair _ _) (pair_power (theta_pair m ell) 2)
    ((theta_commute (Commute.refl S) m ell).pow_right 2)
private theorem cross_pair (m ell:ℕ) (f g:QuantumTest):
    sourcePair f (crossOperator m ell g)=sourcePair (crossAdjoint m ell f) g := by
  change sourcePair f (K0 (C m ell g))=sourcePair (-(C m ell (K0 f))) g
  rw [K0_pair,C_pair,pair_neg_l]
private def fixedCross (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g k:diagonal.domain):ℂ :=
  sourcePair (resolventCore F z hz (coreEquiv.symm g)) (crossOperator m ell (coreEquiv.symm k))-
    sourcePair (crossAdjoint m ell (coreEquiv.symm g)) (resolventCore F z hz (coreEquiv.symm k))
/-- Both actual resolvent seeds enter the complete same-CF mixed commutator. -/
def crossCurrent (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain):ℝ :=
  (sourcePair (resolventCore F z hz (coreEquiv.symm g))
    (bracket (crossOperator m ell) (compressionCore F)
      (resolventCore F z hz (r (coreEquiv.symm g))))).re
private theorem mixed_resolvent_current (B C:End) (hC:GaussCoframeForm.Paired C C)
    (q h g k:QuantumTest) (z:ℂ) (hq:C q=g+z • q) (hh:C h=k+z • h):
    sourcePair q (bracket B C h)=sourcePair q (B k)-sourcePair g (B h)+
      (z-starRingEnd ℂ z)*sourcePair q (B h) := by
  change sourcePair q (B (C h)-C (B h))=_
  rw [pair_sub_r,hC q (B h),hq,hh]
  simp only [map_add,map_smul,pair_add_r,pair_smul_r,pair_add_l,pair_smul_l]
  ring
private theorem cross_source (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g k:diagonal.domain):
    sourcePair (resolventCore F z hz (coreEquiv.symm g))
      (bracket (crossOperator m ell) (compressionCore F)
        (resolventCore F z hz (coreEquiv.symm k)))=
    fixedCross m ell F z hz g k+(z-starRingEnd ℂ z)*
      sourcePair (resolventCore F z hz (coreEquiv.symm g))
        (crossOperator m ell (resolventCore F z hz (coreEquiv.symm k))) := by
  rw [mixed_resolvent_current _ _ (compression_pair F) _ _ _ _ z
    (resolvent_source F z hz g) (resolvent_source F z hz k)]
  unfold fixedCross
  rw [cross_pair m ell (coreEquiv.symm g) (resolventCore F z hz (coreEquiv.symm k))]

private theorem cross_phase_pair (m ell:ℕ) (q h:QuantumTest):
    sourcePair q (crossOperator m ell h)= -(n/2:ℂ)*sourcePair (W m ell (Phi q)) (T m ell h) := by
  have hs (f k:QuantumTest):sourcePair f (S k)=sourcePair (S f) k:=multiply_pair _ _ _ _
  have huS:Commute U S:=real_commute _ _ _ _
  have huT:Commute U (T m ell):=theta_commute huS m ell
  have hTS:Commute (T m ell) S:=(theta_commute (Commute.refl S) m ell).symm
  have he:T m ell*S*U=U*S*T m ell := by
    rw [hTS.eq,mul_assoc,huT.symm.eq,←mul_assoc,huS.symm.eq,mul_assoc]
  have hp:sourcePair (U (Phi q)) (C m ell h)=sourcePair (W m ell (Phi q)) (T m ell h) := by
    change sourcePair (U (Phi q)) (S (T m ell (T m ell h)))=_
    rw [hs,theta_pair]
    exact congrArg (fun f=>sourcePair f (T m ell h)) (LinearMap.congr_fun he (Phi q))
  unfold crossOperator
  change sourcePair q (K0 (C m ell h))=_
  rw [K0_pair]
  simp only [K0,LinearMap.smul_apply,Module.End.mul_apply,pair_smul_l]
  change -(starRingEnd ℂ (n/2:ℂ)*sourcePair (U (Phi q)) (C m ell h))=
    -(n/2:ℂ)*sourcePair (W m ell (Phi q)) (T m ell h)
  rw [hp]
  norm_num only [map_div₀,map_ofNat,Complex.conj_ofReal]
  ring
private theorem cross_current_return (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain):
    crossCurrent m ell F z hz g=(fixedCross m ell F z hz g (phiRadiusSource g)).re+
      n*z.im*(sourcePair (W m ell (Phi (resolventCore F z hz (coreEquiv.symm g))))
        (T m ell (resolventCore F z hz (r (coreEquiv.symm g))))).im := by
  have hk:coreEquiv.symm (phiRadiusSource g)=r (coreEquiv.symm g) := by
    unfold phiRadiusSource;rw [coreEquiv.symm_apply_apply]
  have hc:=cross_source m ell F z hz g (phiRadiusSource g)
  rw [hk,cross_phase_pair] at hc
  have hr:=congrArg Complex.re hc
  change crossCurrent m ell F z hz g=_ at hr
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.conj_re,Complex.conj_im,Complex.neg_re,Complex.neg_im,
    Complex.div_re,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat] at hr
  linear_combination (norm:=ring) hr

/-- This is the same original diagonal/mixed current combination, before any clipping. -/
def jointCurrent (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain):ℝ :=
  n/2*signedCurrent m ell F z hz g-crossCurrent m ell F z hz g
private theorem weighted_K_source (m ell:ℕ):
    (n:ℂ) • weightedGenerator m ell=K0*(T m ell)^2+(T m ell)^2*K0 := by
  have hu:Commute U (T m ell):=theta_commute (real_commute _ _ _ _) m ell
  unfold weightedGenerator SourceClockPhiNativeSignedCurrent.weightedGenerator K0
  change (n:ℂ) • ((1/2:ℂ) • (U*(T m ell)^2*Phi+Phi*(U*(T m ell)^2)))=_
  simp only [smul_smul,smul_mul_assoc,mul_smul_comm]
  have h0:Phi*(U*(T m ell)^2)=U*Phi*(T m ell)^2 := by
    rw [←mul_assoc,phi_U.eq,mul_assoc]
  have h1:(T m ell)^2*(U*Phi)=U*(T m ell)^2*Phi := by
    rw [←mul_assoc,(hu.pow_right 2).symm.eq]
  rw [h0,h1]
  module
private theorem cross_radius (m ell:ℕ):crossOperator m ell*r=K0*(T m ell)^2 := by
  have ht:Commute r (T m ell):=theta_commute (real_commute _ _ _ _) m ell
  unfold crossOperator C
  rw [mul_assoc,mul_assoc,←(ht.pow_right 2).eq,←mul_assoc S,inverse_radius,one_mul]
private theorem endpoint_source (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain):
    SourceClockPhiZeroSeedEndpointTail.endpointState m ell F z hz g=
      ((T m ell)^2) (resolventCore F z hz (coreEquiv.symm g))-
        C m ell (resolventCore F z hz (r (coreEquiv.symm g))) := by
  have hs(f:QuantumTest):S (T m ell f)=T m ell (S f):=
    LinearMap.congr_fun (theta_commute (Commute.refl S) m ell).eq f
  have hr(f:QuantumTest):S (r f)=f:=LinearMap.congr_fun inverse_radius f
  unfold SourceClockPhiZeroSeedEndpointTail.endpointState phiResponseCore bracket C
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,hs,hr,pow_two]
attribute [local irreducible] K0 C weightedGenerator
private theorem fixed_joint_pair (m ell:ℕ) (q h u:QuantumTest):
    -n*(sourcePair (weightedGenerator m ell q) u).re-
      (sourcePair q (crossOperator m ell (r u))-sourcePair (crossAdjoint m ell u) h).re=
    -(sourcePair u (K0 (((T m ell)^2) q-C m ell h))).re := by
  have hA:=congrArg Complex.re (generator_pair m ell q u)
  have hNc:=congrArg (sourcePair q) (LinearMap.congr_fun (weighted_K_source m ell) u)
  change sourcePair q ((n:ℂ) • weightedGenerator m ell u)=
    sourcePair q (K0 (((T m ell)^2) u)+((T m ell)^2) (K0 u)) at hNc
  simp only [pair_smul_r,pair_add_r] at hNc
  have hN:=congrArg Complex.re hNc
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hN
  simp only [Complex.neg_re] at hA
  have ha:=pair_power (theta_pair m ell) 2 q (K0 u)
  have hconj:=congrArg Complex.re (pair_conjugate (K0 u) (((T m ell)^2) q))
  simp only [Complex.conj_re] at hconj
  have hC:=C_pair m ell (K0 u) h
  have hK:=K0_pair u (((T m ell)^2) q-C m ell h)
  simp only [map_sub,pair_sub_r] at hK
  have hKre:=congrArg Complex.re hK
  simp only [Complex.neg_re,Complex.sub_re] at hKre
  have hR:crossOperator m ell (r u)=K0 (((T m ell)^2) u):=
    LinearMap.congr_fun (cross_radius m ell) u
  have hD:sourcePair (crossAdjoint m ell u) h= -sourcePair (K0 u) (C m ell h) := by
    change sourcePair (-(C m ell (K0 u))) h=_
    rw [pair_neg_l,←hC]
  rw [hR,hD]
  simp only [Complex.sub_re,Complex.neg_re]
  have har:=congrArg Complex.re ha
  simp only [map_sub,pair_sub_r,Complex.sub_re]
  linear_combination (norm:=ring) hN-(n:ℝ)*hA+har-hconj+hKre
attribute [local irreducible] fixedCross crossCurrent SourceClockPhiNativeSignedCurrent.signedCurrent
private theorem joint_endpoint_source (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain):
    jointCurrent m ell F z hz g= -(sourcePair (coreEquiv.symm g)
      (K0 (SourceClockPhiZeroSeedEndpointTail.endpointState m ell F z hz g))).re := by
  let q:QuantumTest:=resolventCore F z hz (coreEquiv.symm g)
  let h:QuantumTest:=resolventCore F z hz (r (coreEquiv.symm g))
  let u:QuantumTest:=coreEquiv.symm g
  have hk:coreEquiv.symm (phiRadiusSource g)=r u := by unfold phiRadiusSource;rw [coreEquiv.symm_apply_apply]
  have hf:=fixed_joint_pair m ell q h u
  unfold jointCurrent
  rw [signed_current_return,cross_current_return,endpoint_source]
  have hB:crossOperator m ell (coreEquiv.symm (phiRadiusSource g))=crossOperator m ell (r u):=
    congrArg (crossOperator m ell) hk
  have hR:resolventCore F z hz (coreEquiv.symm (phiRadiusSource g))=h:=
    congrArg (resolventCore F z hz) hk
  have hFixed:fixedCross m ell F z hz g (phiRadiusSource g)=
      sourcePair q (crossOperator m ell (r u))-sourcePair (crossAdjoint m ell u) h:=by
    unfold fixedCross
    exact congrArg₂ (fun x y:QuantumTest=>sourcePair q x-sourcePair (crossAdjoint m ell u) y) hB hR
  have hFixedRe:=congrArg Complex.re hFixed
  change n/2*(-2*(sourcePair (weightedGenerator m ell q) u).re+
      2*z.im*(sourcePair (W m ell (Phi q)) (T m ell h)).im)-
    ((fixedCross m ell F z hz g (phiRadiusSource g)).re+
      n*z.im*(sourcePair (W m ell (Phi q)) (T m ell h)).im)=_
  linear_combination (norm:=ring) hf-hFixedRe
private theorem frequency_nonreal (advanced:Bool) (μ:ℝ) (hμ:0<μ) (t:ℝ):
    (actualFrequency advanced μ t).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'

/-- The complete diagonal-minus-mixed source current has an absolute common tail, with no first-jet debit. -/
theorem actual_joint_phi_current_common_tail (μ:ℝ) (hμ:0<μ) (g:diagonal.domain):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻ t:ℝ,ENNReal.ofReal |jointCurrent m ell F (actualFrequency advanced μ t)
          (frequency_nonreal advanced μ hμ t) g|)≤ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=SourceClockPhiZeroSeedEndpointTail.actual_phi_acceleration_fixed_endpoint_tail μ hμ g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  refine (lintegral_mono (fun t=>?_)).trans (hF advanced)
  rw [joint_endpoint_source,abs_neg]
  apply ENNReal.ofReal_le_ofReal
  change |(sourcePair (coreEquiv.symm g)
    (K0 (SourceClockPhiZeroSeedEndpointTail.endpointState m ell F (actualFrequency advanced μ t) _ g))).re|≤
    ‖sourcePair (coreEquiv.symm g) ((bracket diagonalAction SourceClockPhiRadiusAcceleration.phiSquare)
      (SourceClockPhiZeroSeedEndpointTail.endpointState m ell F (actualFrequency advanced μ t) _ g))‖
  have he:bracket diagonalAction SourceClockPhiRadiusAcceleration.phiSquare=K0:=
    by unfold K0;exact SourceClockPhiRadiusAcceleration.original_phi_square_current
  rw [he]
  exact Complex.abs_re_le_norm _
private def fieldOperator : End := SourceClockPhiRadiusAcceleration.scalarAcceleration+
  SourceClockPhiRadiusAcceleration.stableSpatialAcceleration+((n:ℂ)^2/4) • (U*U*Phi)
/-- The original coframe current is retained after the whole mixed field/current sector is paid. -/
def coframeResidual : End := ((n:ℂ)^2/4) • (U*U*Phi)-
  (n/2:ℂ) • (bracket U diagonalAction*Phi)
/-- The h-cross sector of the actual field/native/full-defect pressure, with its source ordering. -/
def mixedFieldCurrent (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain):ℝ :=
  let q:=resolventCore F z hz (coreEquiv.symm g)
  let h:=resolventCore F z hz (r (coreEquiv.symm g));
  -(sourcePair q (fieldOperator (C m ell h))).re -
    (sourcePair (K0 q) (bracket diagonalAction (C m ell) h)).re -
    (sourcePair (K0 q) (C m ell (defectAction F h))).re -
    (sourcePair (defectAction F q) (K0 (C m ell h) )).re

private theorem defect_pair (F:Index):GaussCoframeForm.Paired (defectAction F) (defectAction F) := by
  intro p q
  unfold defectAction
  simp only [LinearMap.sub_apply,pair_sub_l,pair_sub_r,diagonalAction_pair]
  rw [compression_pair F p q]
private theorem field_operator_source : fieldOperator-bracket K0 diagonalAction=coframeResidual := by
  have h:=SourceScalarVirialBulk.original_scalar_gauge_current
  rw [SourceInverseHamiltonianForceReduction.original_hamiltonian_gauge_source] at h
  have he:=SourceScalarAffineScaleTransport.generator_commutator diagonalAction
  change Phi*diagonalAction-diagonalAction*Phi=E*diagonalAction-diagonalAction*E at he
  have hb:bracket Phi diagonalAction=(-2:ℂ) • scalarKinetic+(2:ℂ) • centeredAction-
      (2:ℂ) • vacuumLinearAction+(2:ℂ) • scalarSpatialAction := by
    unfold bracket
    change (E*diagonalAction-diagonalAction*E)-_=_ at h
    linear_combination (norm:=module) h+he
  unfold bracket at hb
  unfold fieldOperator coframeResidual K0 SourceClockPhiRadiusAcceleration.scalarAcceleration
    SourceClockPhiRadiusAcceleration.stableSpatialAcceleration bracket
  linear_combination (norm:=(noncomm_ring;module)) -(n/2:ℂ) • (U*hb)
private theorem mixed_operator_source (m ell:ℕ) (F:Index):
    -fieldOperator*C m ell+K0*bracket diagonalAction (C m ell)+
      K0*C m ell*defectAction F-defectAction F*K0*C m ell=
    -bracket (K0*C m ell) (compressionCore F)-coframeResidual*C m ell := by
  have hc:compressionCore F=diagonalAction-defectAction F := by
    unfold defectAction
    abel
  rw [hc,←field_operator_source]
  unfold bracket
  noncomm_ring
attribute [local irreducible] fieldOperator
/-- This is the exact original h-field/native sector and both of its same-F defect terms. -/
theorem actual_mixed_phi_field_source (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain):
    mixedFieldCurrent m ell F z hz g= -crossCurrent m ell F z hz g-
      (sourcePair (resolventCore F z hz (coreEquiv.symm g))
        (coframeResidual (C m ell (resolventCore F z hz (r (coreEquiv.symm g)))))).re := by
  let q:QuantumTest:=resolventCore F z hz (coreEquiv.symm g)
  let h:QuantumTest:=resolventCore F z hz (r (coreEquiv.symm g))
  have hop:=congrArg (fun A:End=>sourcePair q (A h)) (mixed_operator_source m ell F)
  have hk1:=K0_pair q (bracket diagonalAction (C m ell) h)
  have hk2:=K0_pair q (C m ell (defectAction F h))
  have hd:=defect_pair F q (K0 (C m ell h))
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,
    Module.End.mul_apply,pair_sub_r,pair_add_r] at hop
  have hn(f:QuantumTest):sourcePair q (-f)= -sourcePair q f := by
    simp only [sourcePair,map_neg,inner_neg_right]
  simp only [hn] at hop
  have hp:=congrArg Complex.re hop
  have h1:=congrArg Complex.re hk1
  have h2:=congrArg Complex.re hk2
  have h3:=congrArg Complex.re hd
  simp only [Complex.add_re,Complex.sub_re,Complex.neg_re] at hp h1 h2
  rw [h1,h2,h3] at hp
  unfold mixedFieldCurrent crossCurrent
  change -(sourcePair q (fieldOperator (C m ell h))).re-
    (sourcePair (K0 q) (bracket diagonalAction (C m ell) h)).re-
    (sourcePair (K0 q) (C m ell (defectAction F h))).re-
    (sourcePair (defectAction F q) (K0 (C m ell h))).re=
    -(sourcePair q (bracket (crossOperator m ell) (compressionCore F) h)).re-
    (sourcePair q (coframeResidual (C m ell h))).re
  unfold crossOperator
  simpa only [sub_eq_add_neg,add_assoc] using hp

end LowEnergy.SourceClockPhiNativeCrossCurrentPayment
