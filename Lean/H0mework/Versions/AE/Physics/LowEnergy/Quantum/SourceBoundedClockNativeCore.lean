import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceBoundedClockAbel
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiEndpointNativePressure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 180000
noncomputable section
namespace LowEnergy.BoundedClockNativeCore
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory GaussFockPair
open GaussNativeEnergy SourceScalarPairedTransport
open SourceJointResidualEnergy SourceInverseNoetherChannelGap
open SourceRetardedIncrement
open SourceBoundedClockAbel SourceClockPhiRadiusSourceCurrent
open SourceClockRadiusAffineCutoff GaussNativeForm SourceScalarDoubleCurrent
open SourceClockPhiWholeCFGreenSource SourceScalarPositiveBulkWard
open FullYSourceResolventGraphSplice
open GaussLiveMomentum SourcePhysicalKineticSquare
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev C (F : Index) : End := compressionCore F
private abbrev n : ℝ := sourceTime 0
private abbrev H0 : End := diagonalAction
private abbrev Hn : End := scalarKinetic
private abbrev U : End := SourcePhysicalKineticSquare.inverseVolumeAction
private abbrev W : End := multiply scalarWeight scalarWeight_smooth
private abbrev S : End := phiInverseAction
private abbrev rho : End := phiRadiusAction
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev theta (m ell : ℕ) : End := phiThetaAction m ell

private theorem inverse_radius : S*rho=(1:End) := by
  apply LinearMap.ext; intro f; apply DFunLike.ext; intro x
  change (phiReciprocal x:ℂ) • ((phiRadius x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse : rho*S=(1:End) := by
  apply LinearMap.ext; intro f; apply DFunLike.ext; intro x
  change (phiRadius x:ℂ) • ((phiReciprocal x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem commute_inverse {A : End} (h : Commute A rho) : Commute A S := by
  change A*S=S*A
  have he := congrArg (fun B : End => S*B*S) h.eq
  simp only [mul_assoc,radius_inverse,mul_one] at he
  simpa only [←mul_assoc,inverse_radius,one_mul] using he.symm
private theorem theta_commute {A : End} (h : Commute A S) (m ell : ℕ) :
    Commute A (theta m ell) :=
  (((Commute.one_right A).sub_right h).pow_right (m+1)).sub_right
    (((Commute.one_right A).sub_right h).pow_right (ell+1))

private theorem channel_add (F : Index) (i : Channel F) (x y : H) :
    channel F i (x+y)=channel F i x+channel F i y := by
  cases i with
  | none => simp [channel, SourceRetardedIncrement.escapeProjection, map_add]
  | some j => simp [channel, map_add, add_smul]
private theorem channel_smul (F : Index) (i : Channel F) (c : ℂ) (x : H) :
    channel F i (c • x)=c • channel F i x := by
  cases i with
  | none => simp [channel, SourceRetardedIncrement.escapeProjection, map_smul]
  | some j => simp [channel, map_smul, smul_smul]

private theorem channelTest_embed (F : Index) (i : Channel F) (g : diagonal.domain) :
    embed (channelTest F g i)=channel F i (g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private def channelCore (F : Index) (i : Channel F) : End where
  toFun f := channelTest F (coreEquiv f) i
  map_add' f g := by
    apply embed_injective
    simp only [map_add, channelTest_embed]
    simpa only [Submodule.coe_add] using channel_add F i (coreEquiv f : H) (coreEquiv g : H)
  map_smul' c f := by
    apply embed_injective
    simp only [map_smul, channelTest_embed]
    simpa only [Submodule.coe_smul, RingHom.id_apply] using
      channel_smul F i c (coreEquiv f : H)

private theorem channelCore_embed (F : Index) (i : Channel F) (f : QuantumTest) :
    embed (channelCore F i f)=channel F i (embed f) := by
  change embed (channelTest F (coreEquiv f) i)=channel F i (embed f)
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem channel_resolution (F : Index) (g : H) :
    ∑ i : Channel F, channel F i g=g := by
  rw [Fintype.sum_option]
  simp only [channel]
  have hs := congrArg (supportSpan F).subtypeL
    ((sourceBasis F).sum_repr ((supportSpan F).orthogonalProjectionOnto g))
  simp only [map_sum,map_smul] at hs
  change (∑ i,(sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto g) i •
    ((sourceBasis F) i : H))=((supportSpan F).orthogonalProjectionOnto g : H) at hs
  rw [hs]
  change (g-(supportSpan F).starProjection g)+(supportSpan F).starProjection g=g
  abel

private theorem channelCore_resolution (F : Index) (f : QuantumTest) :
    (∑ i : Channel F, channelCore F i) f=f := by
  apply embed_injective
  simp only [LinearMap.sum_apply,map_sum,channelCore_embed]
  exact channel_resolution F (embed f)

private def clockCoreSquare : End := clockCore*clockCore
private theorem clockCoreSquare_embed (f : QuantumTest) :
    embed (clockCoreSquare f)=clockObservable (embed f) := by
  exact (actual_bounded_clock_abel_source (1:ℝ) (by norm_num) ∅).1 f |>.symm

private def channelPole (μ : ℝ) (F : Index) (j : Channel F) : ℂ :=
  (channelValue F j : ℂ)-Complex.I*(4*μ:ℂ)
private theorem channelPole_nonreal (μ : ℝ) (hμ : 0<μ) (F : Index) (j : Channel F) :
    (channelPole μ F j).im≠0 := by
  simp only [channelPole,Complex.sub_im,Complex.ofReal_im,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_sub]
  exact neg_ne_zero.mpr (by simpa using
    (mul_ne_zero (show (4:ℝ)≠0 by norm_num) hμ.ne'))
private def abelCoefficient (μ : ℝ) (F : Index) (i j : Channel F) : ℂ :=
  Complex.I*(4*μ:ℂ)*((channelValue F i:ℂ)-channelPole μ F j)⁻¹

private theorem abelCoefficient_closed (μ : ℝ) (F : Index) (i j : Channel F) :
    abelCoefficient μ F i j=(4*μ:ℂ)*
      ((4*μ:ℂ)-Complex.I*((channelValue F i-channelValue F j:ℝ):ℂ))⁻¹ := by
  have hd : ((channelValue F i:ℂ)-channelPole μ F j)=
      Complex.I*((4*μ:ℂ)-Complex.I*((channelValue F i-channelValue F j:ℝ):ℂ)) := by
    dsimp [channelPole]
    simp only [mul_sub,←mul_assoc,Complex.I_mul_I,neg_mul]
    push_cast
    ring
  rw [abelCoefficient,hd,mul_inv_rev]
  have hi : Complex.I*Complex.I⁻¹=(1:ℂ) := mul_inv_cancel₀ Complex.I_ne_zero
  calc
    _=(4*μ:ℂ)*((4*μ:ℂ)-Complex.I*((channelValue F i-channelValue F j:ℝ):ℂ))⁻¹*
        (Complex.I*Complex.I⁻¹) := by ring
    _=_ := by rw [hi,mul_one]

def abelCore (μ : ℝ) (F : Index) : End :=
  ∑ i : Channel F, ∑ j : Channel F,
    abelCoefficient μ F i j • (channelCore F i*clockCoreSquare*channelCore F j)

def currentCore (μ : ℝ) (F : Index) : End := C F*abelCore μ F-abelCore μ F*C F

def nativeMetricCore (i j : Fin 2) (m ell : ℕ) : End :=
  (!![rho*(theta m ell)^2,-(theta m ell)^2;
      -(theta m ell)^2,S*(theta m ell)^2] : Matrix (Fin 2) (Fin 2) End) i j

def nativeColumnCore (a : ScalarIndex) (i j : Fin 2) (m ell : ℕ) : End :=
  Complex.I • bracket (P a) (nativeMetricCore i j m ell)

private theorem nonNative_commute_metric (i j : Fin 2) (m ell : ℕ) :
    Commute (H0-Hn) (nativeMetricCore i j m ell) := by
  have hr : Commute (H0-Hn) rho := original_phi_radius_non_scalar_commute.2.2.2
  have hs : Commute (H0-Hn) S := commute_inverse hr
  have ht : Commute (H0-Hn) (theta m ell) := theta_commute hs m ell
  fin_cases i <;> fin_cases j <;>
    first
    | simpa [nativeMetricCore] using hr.mul_right (ht.pow_right 2)
    | simpa [nativeMetricCore] using (ht.pow_right 2).neg_right
    | simpa [nativeMetricCore] using hs.mul_right (ht.pow_right 2)

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (C F f)=GaussGradedCompression.compression F (embed f) := by
  unfold C compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem resolventCore_embed (F : Index) (z : ℂ) (hz : z.im≠0)
    (f : QuantumTest) :
    embed (SourceClockYukawaCubicCurrent.resolventCore F z hz f)=
      finiteResolvent F z (embed f) := by
  change embed (state F z hz (coreEquiv f))=_
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem channelCore_eigen (F : Index) (j : Channel F) (f : QuantumTest) :
    C F (channelCore F j f)=(channelValue F j:ℂ) • channelCore F j f := by
  exact actual_channel_eigen F (coreEquiv f) j

private theorem abelObservable_channel (μ : ℝ) (hμ : 0<μ) (F : Index)
    (j : Channel F) (f : QuantumTest) :
    abelObservable μ F (embed (channelCore F j f))=
      (Complex.I*(4*μ:ℂ)) • finiteResolvent F (channelPole μ F j)
        (clockObservable (embed (channelCore F j f))) := by
  let A := abelObservable μ F
  let CF := GaussGradedCompression.compression F
  let x := embed (channelCore F j f)
  let y := A x
  let b := clockObservable x
  let z := channelPole μ F j
  let k : ℂ := (4*μ:ℂ)
  have he : CF x=(channelValue F j:ℂ) • x := by
    simpa only [x,compression_embed,map_smul] using
      congrArg embed (channelCore_eigen F j f)
  have hs := congrArg (fun T : H →L[ℂ] H => T x)
    (actual_bounded_clock_abel_source μ hμ F).2.2.2.1
  have hs' : CF y-z • y=(Complex.I*k) • b := by
    change Complex.I • (CF y-A (CF x))=k • (y-b) at hs
    rw [he,map_smul] at hs
    have hs2 := congrArg (fun v : H => (-Complex.I) • v) hs
    simp only [smul_smul] at hs2
    have hi : (-Complex.I)*Complex.I=(1:ℂ) := by simp [Complex.I_mul_I]
    rw [hi,one_smul] at hs2
    dsimp [y,b,z,k,channelPole]
    linear_combination (norm := module) hs2
  have hr := congrArg (fun T : H →L[ℂ] H => T y)
    (FullYSourceResolventGraphSplice.resolvent_left CF
      (GaussGradedCompression.compression_selfAdjoint F) z
      (channelPole_nonreal μ hμ F j))
  have hsolve : y=(Complex.I*k) • finiteResolvent F z b := by
    simp only [mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self] at hr
    change finiteResolvent F z (CF y-z • y)=y at hr
    rw [hs',map_smul] at hr
    exact hr.symm
  exact hsolve

private theorem resolventCore_channels (F : Index) (z : ℂ) (hz : z.im≠0)
    (f : QuantumTest) :
    SourceClockYukawaCubicCurrent.resolventCore F z hz f=
      ∑ i : Channel F, ((channelValue F i:ℂ)-z)⁻¹ • channelCore F i f := by
  exact actual_state_channels F z hz (coreEquiv f)

private theorem abelObservable_channel_core (μ : ℝ) (hμ : 0<μ)
    (F : Index) (j : Channel F) (f : QuantumTest) :
    abelObservable μ F (embed (channelCore F j f))=
      embed ((∑ i : Channel F,
        abelCoefficient μ F i j •
          (channelCore F i*clockCoreSquare*channelCore F j)) f) := by
  have h := abelObservable_channel μ hμ F j f
  rw [←clockCoreSquare_embed (channelCore F j f)] at h
  rw [←resolventCore_embed F (channelPole μ F j)
    (channelPole_nonreal μ hμ F j) (clockCoreSquare (channelCore F j f))] at h
  rw [resolventCore_channels F (channelPole μ F j)
    (channelPole_nonreal μ hμ F j) (clockCoreSquare (channelCore F j f))] at h
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    map_sum,map_smul,Finset.smul_sum,smul_smul,abelCoefficient] using h

theorem abelCore_embed (μ : ℝ) (hμ : 0<μ) (F : Index) (f : QuantumTest) :
    embed (abelCore μ F f)=abelObservable μ F (embed f) := by
  have hres := channelCore_resolution F f
  have hread := congrArg (fun g : QuantumTest => abelObservable μ F (embed g)) hres
  simp only [LinearMap.sum_apply,map_sum] at hread
  simp only [abelCore,LinearMap.sum_apply,map_sum]
  rw [←hread]
  simp only [abelObservable_channel_core μ hμ F,map_sum,LinearMap.sum_apply]
  rw [Finset.sum_comm]

theorem currentCore_embed (μ : ℝ) (hμ : 0<μ) (F : Index) (f : QuantumTest) :
    embed (currentCore μ F f)=abelCurrent μ F (embed f) := by
  change embed (C F (abelCore μ F f)-abelCore μ F (C F f))=
    GaussGradedCompression.compression F (abelObservable μ F (embed f))-
      abelObservable μ F (GaussGradedCompression.compression F (embed f))
  rw [map_sub,compression_embed,abelCore_embed μ hμ F,
    abelCore_embed μ hμ F,compression_embed]

theorem currentCore_source (μ : ℝ) (hμ : 0<μ) (F : Index) :
    Complex.I • currentCore μ F=
      (4*μ:ℂ) • (abelCore μ F-clockCoreSquare) := by
  apply LinearMap.ext; intro f; apply embed_injective
  have h := congrArg (fun T : H →L[ℂ] H => T (embed f))
    (actual_bounded_clock_abel_source μ hμ F).2.2.2.1
  simpa only [LinearMap.smul_apply,LinearMap.sub_apply,smul_apply,sub_apply,
    map_smul,map_sub,currentCore_embed μ hμ F,abelCore_embed μ hμ F,
    clockCoreSquare_embed] using h

private theorem metric_scalar_cutoff (i j : Fin 2) (m ell : ℕ) :
    bracket H0 (nativeMetricCore i j m ell)=
      bracket Hn (nativeMetricCore i j m ell) := by
  have h := (nonNative_commute_metric i j m ell).eq
  unfold bracket
  linear_combination (norm := noncomm_ring) h

private theorem pair_sub_right (p q r : QuantumTest) :
    sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_add_left (p q r : QuantumTest) :
    sourcePair (p+q) r=sourcePair p r+sourcePair q r := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_right (p q r : QuantumTest) :
    sourcePair p (q+r)=sourcePair p q+sourcePair p r := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_smul_right (c : ℂ) (p q : QuantumTest) :
    sourcePair p (c • q)=c*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_smul_left (c : ℂ) (p q : QuantumTest) :
    sourcePair (c • p) q=starRingEnd ℂ c*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_sum_right (p : QuantumTest) (q : ScalarIndex → QuantumTest) :
    sourcePair p (∑ a : ScalarIndex,q a)=∑ a,sourcePair p (q a) := by
  simp only [sourcePair,map_sum,inner_sum]

private theorem paired_mul {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) (h : Commute A B) :
    GaussCoframeForm.Paired (A*B) (A*B) := by
  intro p q
  change sourcePair p (A (B q))=sourcePair (A (B p)) q
  rw [hA p (B q),hB (A p) q]
  exact congrArg (fun f => sourcePair f q) (LinearMap.congr_fun h.eq p).symm
private theorem paired_sub {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) : GaussCoframeForm.Paired (A-B) (A-B) := by
  intro p q
  change sourcePair p (A q-B q)=sourcePair (A p-B p) q
  simpa only [sourcePair,map_sub,inner_sub_left,inner_sub_right] using
    congrArg₂ (·-·) (hA p q) (hB p q)
private theorem paired_neg {A : End} (hA : GaussCoframeForm.Paired A A) :
    GaussCoframeForm.Paired (-A) (-A) := by
  intro p q
  change sourcePair p (-(A q))=sourcePair (-(A p)) q
  simpa only [sourcePair,map_neg,inner_neg_left,inner_neg_right] using
    congrArg Neg.neg (hA p q)
private theorem paired_pow {A : End} (hA : GaussCoframeForm.Paired A A) (k : ℕ) :
    GaussCoframeForm.Paired (A^k) (A^k) := by
  induction k with
  | zero => intro p q; rfl
  | succ k ih => rw [pow_succ]; exact paired_mul ih hA ((Commute.refl A).pow_left k)
private theorem theta_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (theta m ell) (theta m ell) := by
  have h1 : GaussCoframeForm.Paired (1:End) 1 := by intro p q; rfl
  exact paired_sub
    (paired_pow (paired_sub h1 (multiply_pair _ _)) (m+1))
    (paired_pow (paired_sub h1 (multiply_pair _ _)) (ell+1))
private theorem metric_pair (i j : Fin 2) (m ell : ℕ) :
    GaussCoframeForm.Paired (nativeMetricCore i j m ell)
      (nativeMetricCore i j m ell) := by
  have ht := paired_pow (theta_pair m ell) 2
  have hs : GaussCoframeForm.Paired S S := multiply_pair _ _
  have hr : GaussCoframeForm.Paired rho rho := multiply_pair _ _
  have hsr : Commute S rho := by
    change S*rho=rho*S
    rw [inverse_radius,radius_inverse]
  have hst := theta_commute (Commute.refl S) m ell
  have hrt := theta_commute hsr.symm m ell
  fin_cases i <;> fin_cases j <;>
    first
    | simpa [nativeMetricCore] using paired_mul hr ht (hrt.pow_right 2)
    | simpa [nativeMetricCore] using paired_neg ht
    | simpa [nativeMetricCore] using paired_mul hs ht (hst.pow_right 2)

private theorem weight_inverse : W=(-(n:ℂ)) • U := by
  apply LinearMap.ext; intro f; apply DFunLike.ext; intro x
  change (scalarWeight x:ℂ) • f x=(-(n:ℂ)) • ((reciprocalVolume x:ℂ) • f x)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1
private theorem weight_metric (i j : Fin 2) (m ell : ℕ) :
    Commute W (nativeMetricCore i j m ell) := by
  have hur : Commute U rho := by
    apply LinearMap.ext; intro f; apply DFunLike.ext; intro x
    exact smul_comm (reciprocalVolume x:ℂ) (phiRadius x:ℂ) (f x)
  have hus := commute_inverse hur
  have hut := theta_commute hus m ell
  rw [weight_inverse]
  fin_cases i <;> fin_cases j <;>
    first
    | simpa [nativeMetricCore] using (hur.mul_right (hut.pow_right 2)).smul_left (-(n:ℂ))
    | simpa [nativeMetricCore] using ((hut.pow_right 2).neg_right).smul_left (-(n:ℂ))
    | simpa [nativeMetricCore] using (hus.mul_right (hut.pow_right 2)).smul_left (-(n:ℂ))

private theorem scalar_form (p q : QuantumTest) :
    sourcePair p (Hn q)=(1/2:ℂ)*∑ a : ScalarIndex,
      sourcePair (P a p) (W (P a q)) := by
  simp only [Hn,scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,
    pair_smul_right,pair_sum_right]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change sourcePair p (GaussMomentumAdjoint.adjoint (scalarDirection a) (W (P a q)))=_
  exact adjoint_pair _ _ _

private theorem jet_source (A : End) (a : ScalarIndex) (q : QuantumTest) :
    P a (A q)=A (P a q)+(-Complex.I) •
      (Complex.I • bracket (P a) A) q := by
  simp only [bracket,LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,smul_smul]
  have hi : -Complex.I*Complex.I=1 := by rw [neg_mul,Complex.I_mul_I]; ring
  rw [hi,one_smul]
  abel

private theorem weak_scalar_current (A : End) (hA : GaussCoframeForm.Paired A A)
    (hW : Commute W A) (p q : QuantumTest) :
    sourcePair p (bracket Hn A q)=(-Complex.I/2)*∑ a : ScalarIndex,
      (sourcePair (P a p) (W ((Complex.I • bracket (P a) A) q))+
        sourcePair ((Complex.I • bracket (P a) A) p) (W (P a q))) := by
  change sourcePair p (Hn (A q)-A (Hn q))=_
  rw [pair_sub_right,hA p (Hn q),scalar_form,scalar_form,←mul_sub,
    ←Finset.sum_sub_distrib]
  have hrow (a : ScalarIndex) :
      sourcePair (P a p) (W (P a (A q)))-sourcePair (P a (A p)) (W (P a q))=
        (-Complex.I)*(sourcePair (P a p) (W ((Complex.I • bracket (P a) A) q))+
          sourcePair ((Complex.I • bracket (P a) A) p) (W (P a q))) := by
    rw [jet_source A a q,jet_source A a p]
    have hc : sourcePair (A (P a p)) (W (P a q))=
        sourcePair (P a p) (W (A (P a q))) := by
      rw [←hA (P a p) (W (P a q))]
      exact congrArg (sourcePair (P a p))
        (LinearMap.congr_fun hW.eq (P a q)).symm
    simp only [map_add,map_smul,pair_add_left,pair_add_right,
      pair_smul_left,pair_smul_right,hc,map_neg,Complex.conj_I]
    ring
  simp_rw [hrow]
  rw [←Finset.mul_sum]
  ring

/-- The complete finite/escape-channel native commutator return, with both
coframe legs and every two-seed matrix cross term retained. -/
theorem whole_native_row (μ : ℝ) (F : Index) (m ell : ℕ)
    (X : Fin 2 → QuantumTest) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      sourcePair (currentCore μ F (X i))
        (bracket H0 (nativeMetricCore i j m ell) (X j)))=
    (-Complex.I/2)*∑ i : Fin 2, ∑ j : Fin 2, ∑ a : ScalarIndex,
      (sourcePair (P a (currentCore μ F (X i)))
        (W (nativeColumnCore a i j m ell (X j)))+
       sourcePair (nativeColumnCore a i j m ell (currentCore μ F (X i)))
        (W (P a (X j)))) := by
  calc
    _=∑ i : Fin 2, ∑ j : Fin 2,
        sourcePair (currentCore μ F (X i))
          (bracket Hn (nativeMetricCore i j m ell) (X j)) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [metric_scalar_cutoff i j m ell]
    _=∑ i : Fin 2, ∑ j : Fin 2, (-Complex.I/2)*∑ a : ScalarIndex,
        (sourcePair (P a (currentCore μ F (X i)))
          (W (nativeColumnCore a i j m ell (X j)))+
         sourcePair (nativeColumnCore a i j m ell (currentCore μ F (X i)))
          (W (P a (X j)))) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      exact weak_scalar_current (nativeMetricCore i j m ell)
        (metric_pair i j m ell) (weight_metric i j m ell)
        (currentCore μ F (X i)) (X j)
    _=_ := by simp only [Finset.mul_sum]

private abbrev L (a : ScalarIndex) : End := U*P a
private theorem weight_pair_move (p q : QuantumTest) :
    sourcePair p (W q)=(-(n:ℂ))*sourcePair (U p) q := by
  rw [weight_inverse,LinearMap.smul_apply,pair_smul_right]
  have hu : sourcePair p (U q)=sourcePair (U p) q := multiply_pair _ _ _ _
  exact congrArg ((-(n:ℂ))*·) hu
private theorem weight_pair_right (p q : QuantumTest) :
    sourcePair p (W q)=(-(n:ℂ))*sourcePair p (U q) := by
  rw [weight_inverse,LinearMap.smul_apply,pair_smul_right]

theorem whole_native_U_row (μ : ℝ) (F : Index) (m ell : ℕ)
    (X : Fin 2 → QuantumTest) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      sourcePair (currentCore μ F (X i))
        (bracket H0 (nativeMetricCore i j m ell) (X j)))=
    (Complex.I*(n:ℂ)/2)*∑ i : Fin 2, ∑ j : Fin 2, ∑ a : ScalarIndex,
      (sourcePair (L a (currentCore μ F (X i)))
        (nativeColumnCore a i j m ell (X j))+
       sourcePair (nativeColumnCore a i j m ell (currentCore μ F (X i)))
        (L a (X j))) := by
  rw [whole_native_row]
  have hrow (i j : Fin 2) (a : ScalarIndex) :
      sourcePair (P a (currentCore μ F (X i)))
          (W (nativeColumnCore a i j m ell (X j)))+
        sourcePair (nativeColumnCore a i j m ell (currentCore μ F (X i)))
          (W (P a (X j)))=
      (-(n:ℂ))*
        (sourcePair (L a (currentCore μ F (X i)))
          (nativeColumnCore a i j m ell (X j))+
         sourcePair (nativeColumnCore a i j m ell (currentCore μ F (X i)))
          (L a (X j))) := by
    rw [weight_pair_move,weight_pair_right]
    simp only [L,Module.End.mul_apply]
    ring
  simp_rw [hrow]
  simp only [←Finset.mul_sum]
  ring

def nativePiCore (μ : ℝ) (F : Index) (m ell : ℕ)
    (X : Fin 2 → QuantumTest) : ℝ :=
  (∑ i : Fin 2, ∑ j : Fin 2,
    sourcePair (currentCore μ F (X i))
      (bracket H0 (nativeMetricCore i j m ell) (X j))).im

theorem nativePiCore_source (μ : ℝ) (F : Index) (m ell : ℕ)
    (X : Fin 2 → QuantumTest) :
    nativePiCore μ F m ell X=
      ((-Complex.I/2)*∑ i : Fin 2, ∑ j : Fin 2, ∑ a : ScalarIndex,
        (sourcePair (P a (currentCore μ F (X i)))
          (W (nativeColumnCore a i j m ell (X j)))+
         sourcePair (nativeColumnCore a i j m ell (currentCore μ F (X i)))
          (W (P a (X j))))).im := by
  exact congrArg Complex.im (whole_native_row μ F m ell X)

end LowEnergy.BoundedClockNativeCore
