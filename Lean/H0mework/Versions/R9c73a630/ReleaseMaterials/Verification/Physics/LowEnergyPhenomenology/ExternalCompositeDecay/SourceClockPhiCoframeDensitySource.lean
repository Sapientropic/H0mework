import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedScalarNoetherPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentJointBudgetNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussCoframeForm GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceCoframeCovariantAction SourceCoframeCovariantSquare SourceClockReflectedForm
open SourceDilationAlgebra SourceDilationKinetic SourceDilationMultiplier SourceScalarDoubleCurrent
open SourceKineticTranspose SourceNativeCoframeCompatibility SourceScalarInverseBulk
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource
open SourceClockPhiOriginalGaussianH0CoframeRecognition NativePointReturn
open scoped InnerProductSpace ContDiff
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := inverseVolumeAction
private abbrev Hc : End := covariantKinetic
private abbrev Dc : End := dilation
private abbrev D : End := combinedGenerator
private abbrev M : End := matchedTester
private abbrev c : ℂ := 3*Complex.I*(n:ℂ)/4
attribute [local irreducible] sourcePair embed diagonalAction covariantKinetic dilation combinedGenerator matchedTester
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only[sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only[sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only[sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(a:ℂ)(f g:QuantumTest):sourcePair (a • f) g=star a*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(a:ℂ)(f g:QuantumTest):sourcePair f (a • g)=a*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_right]
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by simpa only[sourcePair] using! inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem U_pair(f g:QuantumTest):sourcePair f (U g)=sourcePair (U f) g:=multiply_pair _ _ _ _
private theorem spin_real(a:Fin 7)(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):
    Commute (GaussCoframeSpin.current a) (multiply b hb):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)) (b z:ℂ) (f z)
private theorem spin_dilation:
    Dc*spinRemainder-spinRemainder*Dc=(2*Complex.I) • spinRemainder:=by
  have hS(a:Fin 7):Dc*GaussCoframeSpin.current a-GaussCoframeSpin.current a*Dc=
      (0:ℂ) • GaussCoframeSpin.current a:=by simpa only[zero_smul] using spin_current a
  unfold spinRemainder
  apply homogeneous_sum
  intro a
  have h1:=homogeneous_mul _ _ _ _ _ inverse_volume_commutator (hS a)
  have h2:=homogeneous_mul _ _ _ _ _ (hS a) h1
  have h:=homogeneous_smul _ _ _ (residualWeight a:ℂ) h2
  simpa only[zero_add,add_zero,mul_assoc] using! h
private theorem coframe_dilation: Dc*Hc-Hc*Dc=(2*Complex.I) • Hc:=by
  have hk:kineticAction=scalarKinetic+gaugeKinetic+Hc+spinRemainder+numberShift:=by
    unfold kineticAction
    rw [original_coframe_covariant]
    abel
  have h:=kinetic_scale_current
  rw [hk] at h
  have hs:=scalar_kinetic_current
  have hg:=gauge_kinetic_current
  have hr:=spin_dilation
  have hn:=number_shift_current
  simp only [mul_add,add_mul,smul_add] at h
  linear_combination (norm:=module) h-hs-hg-hr-hn
private theorem number_real(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):
    Commute number (multiply b hb):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change number (multiply b hb f) z word=(b z:ℂ)*number f z word
  rw [number_apply,number_apply]
  change (word.card:ℂ)*((b z:ℂ)*f z word)=(b z:ℂ)*((word.card:ℂ)*f z word)
  ring
private theorem real_U(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):Commute (multiply b hb) U:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (b z:ℂ) (reciprocalVolume z:ℂ) (f z)
private theorem spin_U:Commute spinRemainder U:=by
  have hS(a:Fin 7)(q:QuantumTest):GaussCoframeSpin.current a (U q)=U (GaussCoframeSpin.current a q):=
    LinearMap.congr_fun (spin_real a reciprocalVolume reciprocal_volume_smooth).eq q
  have hR(q:QuantumTest):multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth (U q)=
      U (multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth q):=
    LinearMap.congr_fun (real_U _ _).eq q
  apply LinearMap.ext
  intro f
  change spinRemainder (U f)=U (spinRemainder f)
  simp only [spinRemainder,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    map_sum,map_smul,hS,hR]
private theorem number_shift_U:Commute numberShift U:=by
  let L:End:=multiply numberCoefficient numberCoefficient_smooth
  have hN(q:QuantumTest):number (U q)=U (number q):=
    LinearMap.congr_fun (number_real reciprocalVolume reciprocal_volume_smooth).eq q
  have hR(q:QuantumTest):L (U q)=U (L q):=LinearMap.congr_fun (real_U _ _).eq q
  apply LinearMap.ext
  intro f
  change (1/2:ℂ) • (number (L (U f))+L (number (U f)))=
    U ((1/2:ℂ) • (number (L f)+L (number f)))
  simp only [map_smul,map_add,hN,hR]
private theorem coframe_inverse: Hc*U-U*Hc=c • (U*Dc*U):=by
  have h:=original_coframe_inverse_current
  rw [original_coframe_covariant] at h
  simp only [add_mul,mul_add,spin_U.eq,number_shift_U.eq,(real_U _ _).eq] at h
  linear_combination (norm:=module) h
private theorem dilation_inverse: Dc*U-U*Dc=(2*Complex.I) • U:=by
  have h:=congrArg (fun X:End=>(-2*Complex.I/3) • X) inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc))=
    (-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=(1:ℂ):=by
    calc _= -(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  have hj:(-2*Complex.I/3)*(-3:ℂ)=2*Complex.I:=by ring
  simpa only[hi,hj,one_smul] using h

/-- The original weighted dilation and full covariant coframe form have one ordered Sylvester debit. -/
theorem actual_coframe_dilation_sylvester:
    (U*Dc)*Hc-Hc*(Dc*U)=(-c) • (U*Dc*Dc*U):=by
  have hd:=coframe_dilation
  have hu:=coframe_inverse
  have hv:=dilation_inverse
  linear_combination (norm:=(noncomm_ring;module))
    U*hd-hu*Dc-Hc*hv-(2*Complex.I) • hu+c • (U*Dc*hv)
private theorem coframe_dilation_pair(w:QuantumTest):
    (sourcePair (Dc (U w)) (Hc w)).im= -(3*n/8)*‖embed (Dc (U w))‖^2:=by
  have h:=congrArg (sourcePair w) (LinearMap.congr_fun actual_coframe_dilation_sylvester w)
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,pair_sub_r,pair_smul_r] at h
  change sourcePair w (U (Dc (Hc w)))-sourcePair w (Hc (Dc (U w)))=
    -c*sourcePair w (U (Dc (Dc (U w)))) at h
  rw [U_pair w (Dc (Hc w)),dilation_pair (U w) (Hc w),
    actual_covariant_kinetic_pair w (Dc (U w)),U_pair w (Dc (Dc (U w))),
    dilation_pair (U w) (Dc (U w))] at h
  rw [←pair_conjugate (Dc (U w)) (Hc w)] at h
  have hi:=congrArg Complex.im h
  simp only [Complex.sub_im,Complex.conj_im,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    c,Complex.div_re,Complex.div_im,Complex.normSq_ofNat,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,
    sub_zero,add_zero,zero_add,pair_norm] at hi
  nlinarith only[hi]
private theorem UD_pair(f g:QuantumTest):sourcePair f ((U*D) g)= -sourcePair ((U*D) f) g:=by
  have h:=ClockPhiMatchedNoiseCore.noiseGenerator_pair 0 1 f g
  simpa only[ClockPhiMatchedNoiseCore.noiseGenerator,Complex.ofReal_zero,Complex.ofReal_one,
    zero_smul,one_smul,zero_add] using h
private theorem coframe_combined_pair(w:QuantumTest):
    (sourcePair (U (D w)) (Hc w)).re=(3*n/8)*(sourcePair (U (D w)) (Dc (U w))).im:=by
  have hD:=original_covariant_kinetic_combined.eq
  have hi:(U*D)*Hc-Hc*(U*D)=(-c) • (U*Dc*U*D):=by
    linear_combination (norm:=(noncomm_ring;module)) U*hD-coframe_inverse*D
  have h:=congrArg (sourcePair w) (LinearMap.congr_fun hi w)
  have hb:sourcePair w ((U*D) (Hc w))= -sourcePair (U (D w)) (Hc w):=UD_pair _ _
  change sourcePair w ((U*D) (Hc w)-Hc (U (D w)))=
    sourcePair w ((-c) • U (Dc (U (D w)))) at h
  rw [pair_sub_r,hb,actual_covariant_kinetic_pair w (U (D w)),pair_smul_r,
    U_pair w (Dc (U (D w))),dilation_pair (U w) (U (D w))] at h
  rw [←pair_conjugate (U (D w)) (Hc w),←pair_conjugate (U (D w)) (Dc (U w))] at h
  have hr:=congrArg Complex.re h
  simp only [Complex.sub_re,Complex.neg_re,Complex.conj_re,Complex.conj_im,
    c,Complex.mul_re,Complex.mul_im,Complex.neg_im,Complex.div_re,Complex.div_im,
    Complex.normSq_ofNat,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,sub_zero,add_zero,zero_add] at hr
  nlinarith only[hr]

theorem actual_coframe_matched_pair (w:QuantumTest):
    -6*(sourcePair (M w) (Hc w)).re=
      -12*(sourcePair w (U (Hc w))).re+(27*n/4)*‖embed (Dc (U w))‖^2-
      (9*n/4)*(sourcePair (U (D w)) (Dc (U w))).im:=by
  have hD:=coframe_combined_pair w
  have hC:=coframe_dilation_pair w
  have hm:M w=U (D w)+(3*Complex.I:ℂ) • Dc (U w)+(2:ℂ) • U w:=by
    unfold M matchedTester matchedColumn
    rfl
  rw [hm,pair_add_l,pair_add_l,pair_smul_l,pair_smul_l,←U_pair w (Hc w)]
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.star_def,map_mul,map_ofNat,
    Complex.conj_I,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.re_ofNat,
    Complex.im_ofNat,mul_zero,zero_mul,sub_zero,add_zero,neg_zero]
  nlinarith only[hD,hC]
end LowEnergy.FirstCurrentJointBudgetNext
