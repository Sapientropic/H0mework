import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarEssentialBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusNormalizedFluxBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaQ8RadiusBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiNormalizedScalarBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussFockWeights GaussDensityCore GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard SourcePhysicalKineticSquare
open SourceMixedNativeReturn
open SourceGammaNativeBudget
open SourceScalarEssentialBudget SourceScalarShiftedBulk SourceScalarInverseNativeEnergy SourceScalarVirialBulk
open SourceClockPhiRadiusNormalizedFluxBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockYukawaQ8RadiusBudget SourceClockYukawaRadialGammaNativeBudget SourceFourPoleEnergyClosed
open FullYSourceResolventGraphSplice MeasureTheory Filter
open SaturationMonoid.PhysicsCore StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
open scoped ContDiff InnerProductSpace Topology ENNReal
abbrev End := QuantumTest  →ₗ[ℂ] QuantumTest
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev B : End := scalarBulkComplete
private abbrev n : ℝ := sourceTime 0
attribute [local irreducible] resolventCore compressionCore defectAction diagonalAction sourcePair embed sourceRead finiteResolvent

def sourceMu : ℝ := (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).renormalizationScale
private theorem mu_pos : 0<sourceMu := by unfold sourceMu sourceGeneratedUnifiedCouplings;positivity
private theorem lapse_pos : 0<n := by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem mu_gap : 0<sourceMu-2*n := by
  have hn:=SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hs:=SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_sq
  have hlt:SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse<1 := by nlinarith
  change 0<sourceMu-2*sourceTime 0
  rw [source_time_generated]
  change 0<(1+(2*Real.pi)^2)-2*SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse
  nlinarith [Real.pi_gt_three]
private theorem pair_add_l (f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r (f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l (f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r (f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l (c:ℂ) (f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r (c:ℂ) (f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem self_pair (f:QuantumTest):sourcePair f f=((‖embed f‖^2:ℝ):ℂ) := by
  simpa only [sourcePair,Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (embed f)
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
private theorem theta_commute (m ell:ℕ) : Commute S (T m ell) :=
  (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (m+1)).sub_right
    (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (ell+1))
private theorem frequency_nonreal (advanced:Bool)(μ t:ℝ)(hμ:0<μ):
    (actualFrequency advanced μ t).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem source_step (F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    compressionCore F (resolventCore F z hz f)=f+z • resolventCore F z hz f := by
  have he (u:QuantumTest):embed (compressionCore F u)=GaussGradedCompression.compression F (embed u) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hr (u:QuantumTest):embed (resolventCore F z hz u)=finiteResolvent F z (embed u) := by
    unfold resolventCore SourceScalarPositiveBulkWard.state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have h:=congrArg (fun A:H  →L[ℂ] H=>A (embed f))
    (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
  apply embed_injective
  simp only [he,hr,map_add,map_smul]
  have hf:FullYSourceResolventGraphSplice.resolvent (GaussGradedCompression.compression F) z=
      finiteResolvent F z := by unfold finiteResolvent;rfl
  rw [hf] at h
  change (GaussGradedCompression.compression F-z • 1) (finiteResolvent F z (embed f))=embed f at h
  simp only [sub_apply,smul_apply,one_apply_eq_self] at h
  linear_combination (norm:=module) h

def normalizedState (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest :=
  T m ell (resolventCore F z hz (coreEquiv.symm g))-
    (S*T m ell) (resolventCore F z hz (r (coreEquiv.symm g)))
def normalizedForcing (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest :=
  let q:=resolventCore F z hz (coreEquiv.symm g)
  let h:=resolventCore F z hz (r (coreEquiv.symm g))
  bracket diagonalAction (T m ell) q-bracket diagonalAction (S*T m ell) h+
    T m ell (defectAction F q)-(S*T m ell) (defectAction F h)
def signedRemainder (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ :=
  (sourcePair (normalizedForcing m ell F z hz g) (B (normalizedState m ell F z hz g))).im-
    (sourcePair (normalizedState m ell F z hz g)
      (geometricScalarCurrent (normalizedState m ell F z hz g))).im/2
private theorem normalized_return (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    normalizedState m ell F z hz g=S (phiResponseCore m ell F z hz g) := by
  have hc (f:QuantumTest):S (T m ell f)=T m ell (S f) :=
    LinearMap.congr_fun (theta_commute m ell).eq f
  have hi (f:QuantumTest):S (r f)=f := LinearMap.congr_fun inverse_radius f
  change T m ell (resolventCore F z hz (coreEquiv.symm g))-
    S (T m ell (resolventCore F z hz (r (coreEquiv.symm g))))=
    S (T m ell (r (resolventCore F z hz (coreEquiv.symm g))-
      resolventCore F z hz (r (coreEquiv.symm g))))
  simp only [map_sub,hc,hi]
private theorem full_source (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    diagonalAction (normalizedState m ell F z hz g)=normalizedForcing m ell F z hz g+
      z • normalizedState m ell F z hz g := by
  let q:=resolventCore F z hz (coreEquiv.symm g)
  let h:=resolventCore F z hz (r (coreEquiv.symm g))
  have hq:diagonalAction q=coreEquiv.symm g+z • q+defectAction F q := by
    have hx:=source_step F z hz (coreEquiv.symm g)
    change compressionCore F q=coreEquiv.symm g+z • q at hx
    rw [←hx]
    simp only [defectAction,LinearMap.sub_apply]
    module
  have hh:diagonalAction h=r (coreEquiv.symm g)+z • h+defectAction F h := by
    have hx:=source_step F z hz (r (coreEquiv.symm g))
    change compressionCore F h=r (coreEquiv.symm g)+z • h at hx
    rw [←hx]
    simp only [defectAction,LinearMap.sub_apply]
    module
  have htr:(S*T m ell)*r=T m ell := by
    rw [(theta_commute m ell).eq, mul_assoc,inverse_radius,mul_one]
  have ht:=LinearMap.congr_fun htr (coreEquiv.symm g)
  unfold normalizedForcing normalizedState bracket
  change diagonalAction (T m ell q-(S*T m ell) h)=
    ((diagonalAction*(T m ell)-(T m ell)*diagonalAction) q-
      (diagonalAction*(S*T m ell)-(S*T m ell)*diagonalAction) h+
      T m ell (defectAction F q)-(S*T m ell) (defectAction F h))+z • (T m ell q-(S*T m ell) h)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,hq,hh,map_add,map_smul] at ht ⊢
  linear_combination (norm:=module) -ht
private theorem scalar_self (f:QuantumTest):sourcePair f (B f)=((scalarEnergy f:ℝ):ℂ) := by
  have hr:=original_scalar_energy f
  have hp:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (B f))
  rw [←original_scalar_pair] at hp
  simp only [Complex.conj_im] at hp
  apply Complex.ext
  · exact hr
  · simp only [Complex.ofReal_im];linarith only [hp]
private theorem scalar_ward (w f:QuantumTest)(z:ℂ)(he:diagonalAction w=f+z • w):
    z.im*scalarEnergy w=(sourcePair f (B w)).im-
      (sourcePair w ((diagonalAction*B-B*diagonalAction) w)).im/2 := by
  have hp:sourcePair w ((diagonalAction*B-B*diagonalAction) w)=
      sourcePair (diagonalAction w) (B w)-sourcePair (B w) (diagonalAction w) := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r,diagonalAction_pair,original_scalar_pair]
  have hbself:sourcePair (B w) w=((scalarEnergy w:ℝ):ℂ) :=
    (original_scalar_pair w w).symm.trans (scalar_self w)
  rw [he,pair_add_l,pair_smul_l,pair_add_r,pair_smul_r,scalar_self,hbself] at hp
  have hc:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (B w))
  simp only [Complex.conj_im] at hc
  have hi:=congrArg Complex.im hp
  simp only [Complex.sub_im,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,mul_zero,zero_add] at hi
  linarith only [hi,hc]

/-- The actual normalized two-seed source absorbs only the closed scalar oscillator; geometry and the full defect stay signed. -/
theorem actual_normalized_scalar_source (m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)
    (g:diagonal.domain)(advanced:Bool)(t:ℝ):
    let z:=actualFrequency advanced μ t
    let hz:=frequency_nonreal advanced μ t hμ
    (μ-2*n)*scalarEnergy (normalizedState m ell F z hz g)  ≤
      (if advanced then (-1:ℝ) else 1)*signedRemainder m ell F z hz g+
        n^2*‖vacuum‖^2*‖embed (normalizedState m ell F z hz g)‖^2 := by
  dsimp only
  let z:=actualFrequency advanced μ t
  let hz:=frequency_nonreal advanced μ t hμ
  let w:=normalizedState m ell F z hz g
  have hs:=scalar_ward w (normalizedForcing m ell F z hz g) z (full_source m ell F z hz g)
  rw [original_scalar_current_geometric] at hs
  simp only [LinearMap.add_apply,pair_add_r,Complex.add_im] at hs
  have hb:=original_scalar_oscillator_bound w
  change |(sourcePair w (scalarCurrentComplete w)).im/2|  ≤  2*n*scalarEnergy w+
    n^2*‖vacuum‖^2*‖embed w‖^2 at hb
  change (μ-2*n)*scalarEnergy w  ≤  (if advanced then (-1:ℝ) else 1)*
    ((sourcePair (normalizedForcing m ell F z hz g) (B w)).im-
      (sourcePair w (geometricScalarCurrent w)).im/2)+n^2*‖vacuum‖^2*‖embed w‖^2
  cases advanced
  · have hzi:z.im=μ := line_im μ t
    rw [hzi] at hs
    simp only [Bool.false_eq_true,ite_false,one_mul]
    have hlo:=neg_le_abs ((sourcePair w (scalarCurrentComplete w)).im/2)
    linarith only [hs,hb,hlo]
  · have hzi:z.im= -μ := by simp only [z,actualFrequency,ite_true,Complex.star_def,Complex.conj_im,line_im]
    rw [hzi] at hs
    simp only [ite_true,neg_one_mul]
    have hhi:=le_abs_self ((sourcePair w (scalarCurrentComplete w)).im/2)
    linarith only [hs,hb,hhi]

private theorem phi_square (x:SourceCoordinateSlice) : (phiRadius x)^2=1+‖scalarField x‖^2/4 := by
  change (Real.sqrt (1+‖scalarField x‖^2/4))^2=1+‖scalarField x‖^2/4
  exact Real.sq_sqrt (by positivity)
private theorem radius_completion : r*r=
    ((1+‖vacuum‖^2/8:ℝ):ℂ) • (1:End)+(1/2:ℂ) •
      (∑ a:ScalarIndex,shiftedColumn a*shiftedColumn a)-(1/4:ℂ) •
      (∑ a:ScalarIndex,scalarColumn a*scalarColumn a) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  have hs:(∑ a:ScalarIndex,(shiftedCoordinate a x)^2)=‖scalarField x-(1/2:ℝ) • vacuum‖^2 :=
    scalarBasis.sum_sq_inner_left _
  have hq:(∑ a:ScalarIndex,(inner ℝ (x.2.1:Scalar) (scalarBasis a))^2)=‖(x.2.1:Scalar)‖^2 :=
    scalarBasis.sum_sq_inner_left _
  have hshift:scalarField x-(1/2:ℝ) • vacuum=(x.2.1:Scalar)+(1/2:ℝ) • vacuum := by
    unfold scalarField;module
  have hr:(phiRadius x)^2=1+‖vacuum‖^2/8+
      (1/2:ℝ)*(∑ a:ScalarIndex,(shiftedCoordinate a x)^2)-
      (1/4:ℝ)*(∑ a:ScalarIndex,(inner ℝ (x.2.1:Scalar) (scalarBasis a))^2) := by
    rw [phi_square,hs,hq,hshift]
    unfold scalarField
    rw [norm_add_sq_real,norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs]
    norm_num
    rw [real_inner_comm vacuum (x.2.1:Scalar)]
    ring
  change (phiRadius x:ℂ) • ((phiRadius x:ℂ) • f x)=_
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    LinearMap.sum_apply,Module.End.mul_apply]
  change (phiRadius x:ℂ) • ((phiRadius x:ℂ) • f x)=
    ((1+‖vacuum‖^2/8:ℝ):ℂ) • f x+(1/2:ℂ) •
      ((∑ a:ScalarIndex,shiftedColumn a (shiftedColumn a f)) x)-
      (1/4:ℂ) • ((∑ a:ScalarIndex,scalarColumn a (scalarColumn a f)) x)
  rw [sum_apply,sum_apply]
  change (phiRadius x:ℂ) • ((phiRadius x:ℂ) • f x)=
    ((1+‖vacuum‖^2/8:ℝ):ℂ) • f x+(1/2:ℂ) •
      (∑ a:ScalarIndex,(shiftedCoordinate a x:ℂ) • ((shiftedCoordinate a x:ℂ) • f x))-
      (1/4:ℂ) • (∑ a:ScalarIndex,(inner ℝ (x.2.1:Scalar) (scalarBasis a):ℂ) •
        ((inner ℝ (x.2.1:Scalar) (scalarBasis a):ℂ) • f x))
  simp only [smul_smul,←pow_two,←Finset.sum_smul,←Complex.ofReal_pow,←Complex.ofReal_sum,
    ←Complex.ofReal_ofNat,←Complex.ofReal_one,←Complex.ofReal_div,←Complex.ofReal_mul]
  rw [←add_smul,←sub_smul,←Complex.ofReal_add,←Complex.ofReal_sub,hr]
private theorem radius_norm (f:QuantumTest) :
    ‖embed (r f)‖^2  ≤  (1+‖vacuum‖^2/8)*‖embed f‖^2+scalarEnergy f/(16*n) := by
  have hp:=congrArg (fun A:End=>sourcePair f (A f)) radius_completion
  have hr:sourcePair f ((r*r) f)=sourcePair (r f) (r f) := multiply_pair _ _ _ _
  have hs (a:ScalarIndex):sourcePair f ((shiftedColumn a*shiftedColumn a) f)=
      sourcePair (shiftedColumn a f) (shiftedColumn a f) := multiply_pair _ _ _ _
  have hq (a:ScalarIndex):sourcePair f ((scalarColumn a*scalarColumn a) f)=
      sourcePair (scalarColumn a f) (scalarColumn a f) := by
    unfold scalarColumn SourceClosedCostNativeProbe.coordinateAction
    exact multiply_pair _ _ _ _
  rw [hr] at hp
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    Module.End.one_apply,pair_add_r,pair_sub_r,pair_smul_r] at hp
  have hsum (k:ScalarIndex → QuantumTest):sourcePair f (∑a,k a)=∑a,sourcePair f (k a) := by
    simp only [sourcePair,map_sum,inner_sum]
  rw [hsum,hsum] at hp
  simp_rw [hs,hq,self_pair] at hp
  have hre:=congrArg Complex.re hp
  norm_num only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.div_re,Complex.div_im,Complex.normSq_apply,Complex.re_ofNat,Complex.im_ofNat,
    Complex.one_re,Complex.one_im,Complex.re_sum,Complex.im_sum,
    mul_zero,zero_mul,sub_zero,add_zero] at hre
  change ‖embed (r f)‖^2=(1+‖vacuum‖^2/8)*‖embed f‖^2+
    (1/2:ℝ)*shiftedMoment f-(1/4:ℝ)*scalarMoment f at hre
  have hN:0 ≤ inverseNativeEnergy f := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hQ:0 ≤ scalarMoment f := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have he:8*n*shiftedMoment f ≤ scalarEnergy f := by
    unfold scalarEnergy
    nlinarith only [mul_nonneg lapse_pos.le hN]
  have hd:0<16*n := by have hn:=lapse_pos;positivity
  have hE:(1/2:ℝ)*shiftedMoment f ≤ scalarEnergy f/(16*n) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith only [he]
  linarith only [hre,hQ,hE]
private theorem normalized_radius (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    r (normalizedState m ell F z hz g)=phiResponseCore m ell F z hz g := by
  rw [normalized_return]
  exact LinearMap.congr_fun radius_inverse _

def scalarPrice (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(advanced:Bool):ℝ :=
  (if advanced then (-1:ℝ) else 1)*signedRemainder m ell F z hz g

def scalarBudget (m ell:ℕ)(F:Index)(g:diagonal.domain)(advanced:Bool):ENNReal :=
  ∫⁻ t:ℝ,ENNReal.ofReal (scalarPrice m ell F (actualFrequency advanced sourceMu t)
    (frequency_nonreal advanced sourceMu t mu_pos) g advanced)
private def scalarFactor : ℝ := sourceMu/(16*n*(sourceMu-2*n))
private def normFactor : ℝ := sourceMu*((1+‖vacuum‖^2/8)+n^2*‖vacuum‖^2/(16*n*(sourceMu-2*n)))
private theorem factor_nonnegative : 0 ≤ scalarFactor := by unfold scalarFactor;have hn:=lapse_pos;have hg:=mu_gap;have hm:=mu_pos;positivity
private theorem norm_factor_nonnegative : 0 ≤ normFactor := by unfold normFactor;have hn:=lapse_pos;have hg:=mu_gap;have hm:=mu_pos;positivity
private theorem response_price (m ell:ℕ)(F:Index)(g:diagonal.domain)(advanced:Bool)(t:ℝ):
    let z:=actualFrequency advanced sourceMu t
    let hz:=frequency_nonreal advanced sourceMu t mu_pos
    sourceMu*‖embed (phiResponseCore m ell F z hz g)‖^2  ≤
      scalarFactor*scalarPrice m ell F z hz g advanced+
        normFactor*‖embed (normalizedState m ell F z hz g)‖^2 := by
  dsimp only
  let z:=actualFrequency advanced sourceMu t
  let hz:=frequency_nonreal advanced sourceMu t mu_pos
  let w:=normalizedState m ell F z hz g
  have h1:=actual_normalized_scalar_source m ell F sourceMu mu_pos g advanced t
  change (sourceMu-2*n)*scalarEnergy w ≤ scalarPrice m ell F z hz g advanced+n^2*‖vacuum‖^2*‖embed w‖^2 at h1
  have h2:=radius_norm w
  rw [normalized_radius] at h2
  have hE:scalarEnergy w ≤ (scalarPrice m ell F z hz g advanced+n^2*‖vacuum‖^2*‖embed w‖^2)/(sourceMu-2*n) :=
    (le_div_iff₀ mu_gap).mpr (by simpa only [mul_comm] using h1)
  have h3:=mul_le_mul_of_nonneg_left (add_le_add
    (le_refl ((1+‖vacuum‖^2/8)*‖embed w‖^2))
    (div_le_div_of_nonneg_right hE (by have hn:=lapse_pos;positivity : 0 ≤ 16*n))) mu_pos.le
  have h4:sourceMu*‖embed (phiResponseCore m ell F z hz g)‖^2 ≤
      sourceMu*((1+‖vacuum‖^2/8)*‖embed w‖^2+
        ((scalarPrice m ell F z hz g advanced+n^2*‖vacuum‖^2*‖embed w‖^2)/(sourceMu-2*n))/(16*n)) :=
    (mul_le_mul_of_nonneg_left h2 mu_pos.le).trans h3
  exact h4.trans_eq (by
    change _=scalarFactor*scalarPrice m ell F z hz g advanced+normFactor*‖embed w‖^2
    unfold scalarFactor normFactor
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring)

private theorem finite_star (F:Index)(z:ℂ):finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced:Bool)(F:Index):
    Continuous (fun t:ℝ=>finiteResolvent F (actualFrequency advanced sourceMu t)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous sourceMu mu_pos F
  · have he:(fun t:ℝ=>finiteResolvent F (actualFrequency true sourceMu t))=
        (fun t:ℝ=>(finiteResolvent F (line sourceMu t)).adjoint) := by
      funext t;exact finite_star F _
    exact he ▸ (ContinuousLinearMap.adjoint.continuous.comp
      (SourceRetardedBandCurrent.finite_frequency_continuous sourceMu mu_pos F))
private theorem normalized_read (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    embed (normalizedState m ell F z hz g)=
      sourceRead F g (T m ell) (finiteResolvent F z (g:H))-
      sourceRead F (phiRadiusSource g) (S*T m ell) (finiteResolvent F z (phiRadiusSource g:H)) := by
  have hh:r (coreEquiv.symm g)=coreEquiv.symm (phiRadiusSource g) :=
    (coreEquiv.symm_apply_apply _).symm
  have hread (A:End)(k:diagonal.domain):
      sourceRead F k A (finiteResolvent F z (k:H))=
        embed (A (resolventCore F z hz (coreEquiv.symm k))) := by
    simpa only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply,
      SourceScalarPositiveBulkWard.state] using! source_read_resolvent F k A z hz
  have hg:=hread (T m ell) g
  have hk:=hread (S*T m ell) (phiRadiusSource g)
  unfold normalizedState
  rw [hh,map_sub]
  exact congrArg₂ (fun a b:H=>a-b) hg.symm hk.symm
private theorem normalized_measurable (m ell:ℕ)(F:Index)(g:diagonal.domain)(advanced:Bool):
    Measurable (fun t:ℝ=>ENNReal.ofReal (‖embed (normalizedState m ell F
      (actualFrequency advanced sourceMu t) (frequency_nonreal advanced sourceMu t mu_pos) g)‖^2)) := by
  simp_rw [normalized_read]
  have hg:Continuous (fun t:ℝ=>finiteResolvent F (actualFrequency advanced sourceMu t) (g:H)) :=
    (frequency_continuous advanced F).clm_apply continuous_const
  have hh:Continuous (fun t:ℝ=>finiteResolvent F (actualFrequency advanced sourceMu t) (phiRadiusSource g:H)) :=
    (frequency_continuous advanced F).clm_apply continuous_const
  exact ((((sourceRead F g (T m ell)).continuous.comp hg).sub
    ((sourceRead F (phiRadiusSource g) (S*T m ell)).continuous.comp hh)).norm.pow 2).measurable.ennreal_ofReal
private def responseIntegral (m ell:ℕ)(F:Index)(g:diagonal.domain)(advanced:Bool):ENNReal :=
  ∫⁻ t:ℝ,ENNReal.ofReal (sourceMu*‖embed (phiResponseCore m ell F (actualFrequency advanced sourceMu t)
    (frequency_nonreal advanced sourceMu t mu_pos) g)‖^2)
private theorem integrated_price (m ell:ℕ)(F:Index)(g:diagonal.domain)(advanced:Bool):
    responseIntegral m ell F g advanced ≤ ENNReal.ofReal scalarFactor*scalarBudget m ell F g advanced+
      ENNReal.ofReal normFactor*(∫⁻ t:ℝ,ENNReal.ofReal (‖embed (normalizedState m ell F
        (actualFrequency advanced sourceMu t) (frequency_nonreal advanced sourceMu t mu_pos) g)‖^2)) := by
  unfold responseIntegral scalarBudget
  calc
    _ ≤ ∫⁻t:ℝ,ENNReal.ofReal scalarFactor*ENNReal.ofReal (scalarPrice m ell F
        (actualFrequency advanced sourceMu t) (frequency_nonreal advanced sourceMu t mu_pos) g advanced)+
      ENNReal.ofReal normFactor*ENNReal.ofReal (‖embed (normalizedState m ell F
        (actualFrequency advanced sourceMu t) (frequency_nonreal advanced sourceMu t mu_pos) g)‖^2) := by
      apply lintegral_mono;intro t
      exact (ENNReal.ofReal_le_ofReal (response_price m ell F g advanced t)).trans
        (ENNReal.ofReal_add_le.trans (add_le_add
          (le_of_eq (ENNReal.ofReal_mul factor_nonnegative))
          (le_of_eq (ENNReal.ofReal_mul norm_factor_nonnegative))))
    _=_ := by
      rw [lintegral_add_right _ ((normalized_measurable m ell F g advanced).const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
private theorem normalized_common_payment (g:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      responseIntegral m ell F g advanced ≤ ENNReal.ofReal ε+
        ENNReal.ofReal scalarFactor*scalarBudget m ell F g advanced := by
  intro ε hε
  let δ:=ε/(normFactor+1)
  have hd:0<δ := by dsimp [δ];have hn:=norm_factor_nonnegative;positivity
  obtain ⟨N,hN⟩:=actual_normalized_response_common_tail sourceMu mu_pos g δ hd
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have ht:=hF advanced
  change (∫⁻t:ℝ,ENNReal.ofReal (‖embed (S (phiResponseCore m ell F
    (actualFrequency advanced sourceMu t) _ g))‖^2)) ≤ ENNReal.ofReal δ at ht
  simp_rw [←normalized_return] at ht
  have hb:=(integrated_price m ell F g advanced).trans
    (add_le_add le_rfl (mul_le_mul le_rfl ht zero_le zero_le))
  have ha:normFactor*δ ≤ ε := by
    dsimp only [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by have hn:=norm_factor_nonnegative;positivity : 0<normFactor+1)).mpr
    nlinarith only [hε]
  rw [←ENNReal.ofReal_mul norm_factor_nonnegative] at hb
  exact hb.trans ((add_le_add le_rfl (ENNReal.ofReal_le_ofReal ha)).trans_eq (add_comm _ _))

/-- The original source frequency consumes the normalized scalar oscillator and its two fixed-input norm tails, leaving one clipped geometric/full-defect word. -/
theorem actual_original_normalized_scalar_Gamma_budget (g k:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠF in (sourceFilter:Filter Index),∀sharp:Bool,
      ENNReal.ofReal (closedJointCost sharp m ell F sourceMu (g:H) (k:H)) ≤ ENNReal.ofReal ε+
        ENNReal.ofReal (24*sourceMuFactor sourceMu k*radiusPrice*
          (sourceMu/(16*n*(sourceMu-2*n))))*scalarBudget m ell F g false := by
  intro ε hε
  let C:=6*sourceMuFactor sourceMu k*radiusPrice
  have hC:0 ≤ C := by dsimp [C];unfold sourceMuFactor radiusPrice;have hm:=mu_pos;positivity
  let δ:=ε/(10*(C+1))
  have hd:0<δ := by dsimp [δ];positivity
  obtain ⟨N1,h1⟩:=actual_original_Q8_radius_response_budget sourceMu mu_pos g k (ε/2) (by positivity)
  obtain ⟨N2,h2⟩:=actual_original_radius_homogeneous_budget sourceMu mu_pos g δ hd
  obtain ⟨N3,h3⟩:=normalized_common_payment g δ hd
  refine ⟨max N1 (max N2 N3),fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml,h3 m (by omega) ell hml] with F hg hr hp
  intro sharp
  have hp0:=hp false
  change phiResponseBudget m ell F sourceMu mu_pos g ≤ ENNReal.ofReal δ+
    ENNReal.ofReal scalarFactor*scalarBudget m ell F g false at hp0
  have hx:=hr.trans (add_le_add le_rfl (mul_le_mul le_rfl hp0 zero_le zero_le))
  have heδ:ENNReal.ofReal δ+4*ENNReal.ofReal δ=ENNReal.ofReal (5*δ) := by
    rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num,
      ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),←ENNReal.ofReal_add hd.le (by positivity)]
    congr 1;ring
  rw [mul_add,←add_assoc,heδ] at hx
  have hb:=(hg sharp).trans (add_le_add le_rfl (mul_le_mul le_rfl hx zero_le zero_le))
  have halloc:ε/2+C*(5*δ) ≤ ε := by
    have hs:C*(5*δ) ≤ ε/2 := by
      dsimp only [δ]
      rw [←mul_div_assoc,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<10*(C+1))).mpr
      nlinarith only [hε]
    linarith only [hs]
  have hcoef:ENNReal.ofReal C*4*ENNReal.ofReal scalarFactor=
      ENNReal.ofReal (24*sourceMuFactor sourceMu k*radiusPrice*(sourceMu/(16*n*(sourceMu-2*n)))) := by
    rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num,
      ←ENNReal.ofReal_mul hC,←ENNReal.ofReal_mul (mul_nonneg hC (by norm_num))]
    congr 1;unfold scalarFactor;dsimp only [C];ring
  change _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal (5*δ)+
    4*(ENNReal.ofReal scalarFactor*scalarBudget m ell F g false)) at hb
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal (5*δ)+
      4*(ENNReal.ofReal scalarFactor*scalarBudget m ell F g false)) := hb
    _=ENNReal.ofReal (ε/2+C*(5*δ))+
      ENNReal.ofReal (24*sourceMuFactor sourceMu k*radiusPrice*(sourceMu/(16*n*(sourceMu-2*n))))*
        scalarBudget m ell F g false := by
      rw [mul_add,←mul_assoc,←mul_assoc,hcoef,←ENNReal.ofReal_mul hC,←add_assoc,
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal halloc) le_rfl

end LowEnergy.SourceClockPhiNormalizedScalarBudget
