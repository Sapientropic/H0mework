import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiJointScaleNoether
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusNormalizedFluxBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockSourceTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiNativeMatchedSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarVirialBulk SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNormalizedScalarBudget
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiRadiusNormalizedFluxBudget
open SourceClockAcceleration
open SourceClockReflectedForm SourceClockSourceTail SourceCoframeBlockHardy GaussCoframeForm
open SourceClockPhiJointScaleNoether
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourcePhysicalHamiltonianSquare SourceScalarInverseNativeEnergy
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceLocalizedInverseFormPayment
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest
private abbrev a:End:=inverseRootAction
private abbrev U:End:=inverseVolumeAction
private abbrev S:End:=phiInverseAction
private abbrev r:End:=phiRadiusAction
private abbrev T (m ell:ℕ):End:=phiThetaAction m ell
private abbrev D:End:=combinedGenerator
private abbrev A:End:=combinedConjugate
private abbrev H0:End:=diagonalAction
private abbrev Phi:End:=SourceScalarAffineScaleTransport.generator
private abbrev Gauge:End:=SourceGaugeScaleTransport.generator
private abbrev Dc:End:=SourceCoframeVolumeCurrent.dilation
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction compressionCore defectAction resolventCore finiteResolvent

private theorem pair_sum_r {ι:Type*}[Fintype ι](f:QuantumTest)(v:ι → QuantumTest):
    sourcePair f (∑i,v i)=∑i,sourcePair f (v i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem lapse_pos : 0<n := by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem pair_add_l (f g h:QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]

private theorem pair_add_r (f g h:QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]

private theorem pair_sub_l (f g h:QuantumTest) : sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]

private theorem pair_sub_r (f g h:QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]

private theorem pair_smul_l (c:ℂ)(f g:QuantumTest) : sourcePair (c • f) g=(starRingEnd ℂ c)*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left]

private theorem pair_smul_r (c:ℂ)(f g:QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]

private theorem self_pair (f:QuantumTest) : sourcePair f f=(‖embed f‖^2:ℂ) := by
  simpa only [sourcePair,Complex.ofReal_pow] using!
    inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (embed f)

private theorem flow_pair_generator (flow:ℝ → End)(G:End)
    (hzero:∀f,flow 0 f=f)
    (hpair:∀t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv:∀f,HasDerivAt (fun t:ℝ=>embed (flow t f)) (embed (G f)) 0)
    (f g:QuantumTest) : sourcePair f (G g)= -sourcePair (G f) g := by
  unfold sourcePair at hpair ⊢
  have h:=(hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he:(fun t:ℝ=>inner ℂ (embed (flow t f)) (embed (flow t g)))=fun _=>inner ℂ (embed f) (embed g) :=
    funext (fun t=>hpair t f g)
  rw [he] at h
  have heq:=h.unique (hasDerivAt_const (0:ℝ) (inner ℂ (embed f) (embed g)))
  exact eq_neg_of_add_eq_zero_left heq

private theorem phi_pair (f g:QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g :=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow Phi
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g

private theorem gauge_pair (f g:QuantumTest) : sourcePair f (Gauge g)= -sourcePair (Gauge f) g :=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow Gauge
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g

private theorem combined_pair (f g:QuantumTest) :
    sourcePair f (combinedGenerator g)= -sourcePair (combinedGenerator f) g := by
  simp only [combinedGenerator,LinearMap.sub_apply,pair_sub_l,pair_sub_r,phi_pair,gauge_pair]
  ring

private theorem weight_pair (f g:QuantumTest) : sourcePair f (U g)=sourcePair (U f) g :=
  multiply_pair _ _ f g

private theorem real_commute (c d:SourceCoordinateSlice → ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)

private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'

private theorem radius_inverse : r*S=(1:End):=(real_commute _ _ _ _).eq.symm.trans inverse_radius

private theorem theta_commute {A:End}(hA:Commute A S)(m ell:ℕ):Commute A (T m ell):=
  (((Commute.one_right A).sub_right hA).pow_right (m+1)).sub_right
    (((Commute.one_right A).sub_right hA).pow_right (ell+1))

private theorem phi_inverse_core(f:QuantumTest):phiInverseBounded (embed f)=embed (S f):=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f

private theorem phi_inverse_norm:‖phiInverseBounded‖ ≤ 1:=GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

private theorem normalized_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    normalizedState m ell F z hz g=S (phiResponseCore m ell F z hz g) := by
  have hc(f:QuantumTest):S (T m ell f)=T m ell (S f):=
    LinearMap.congr_fun (theta_commute (Commute.refl S) m ell).eq f
  have hi(f:QuantumTest):S (r f)=f:=LinearMap.congr_fun inverse_radius f
  change T m ell (resolventCore F z hz (coreEquiv.symm g))-
    S (T m ell (resolventCore F z hz (r (coreEquiv.symm g))))=
    S (T m ell (r (resolventCore F z hz (coreEquiv.symm g))-
      resolventCore F z hz (r (coreEquiv.symm g))))
  simp only [map_sub,hc,hi]

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
    rw [(theta_commute (Commute.refl S) m ell).eq, mul_assoc,inverse_radius,mul_one]
  have ht:=LinearMap.congr_fun htr (coreEquiv.symm g)
  unfold normalizedForcing normalizedState bracket
  change diagonalAction (T m ell q-(S*T m ell) h)=
    ((diagonalAction*(T m ell)-(T m ell)*diagonalAction) q-
      (diagonalAction*(S*T m ell)-(S*T m ell)*diagonalAction) h+
      T m ell (defectAction F q)-(S*T m ell) (defectAction F h))+z • (T m ell q-(S*T m ell) h)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,hq,hh,map_add,map_smul] at ht ⊢
  linear_combination (norm:=module) -ht

private theorem weight_combined : Commute U D := by
  have hp:=SourceScalarAffineScaleTransport.generator_commutator U
  have hg:=SourceGaugeScaleTransport.generator_commutator U
  rw [SourceScalarInverseBulk.inverse_phi] at hp
  rw [SourceScalarInverseBulk.inverse_gauge] at hg
  change U*(Phi-Gauge)=(Phi-Gauge)*U
  linear_combination (norm:=noncomm_ring) -hp+hg
private theorem weighted_pair (f g:QuantumTest):sourcePair f (U (D g))= -sourcePair (U (D f)) g := by
  rw [weight_pair,combined_pair]
  have hc:=LinearMap.congr_fun weight_combined.eq f
  change U (D f)=D (U f) at hc
  rw [←hc]
private theorem pair_star(f g:QuantumTest):starRingEnd ℂ (sourcePair f g)=sourcePair g f := by
  unfold sourcePair
  exact inner_conj_symm _ _
private theorem pair_sym_re(f g:QuantumTest):(sourcePair f g).re=(sourcePair g f).re := by
  rw [←pair_star,Complex.conj_re]
private theorem weighted_self_real(f:QuantumTest):(sourcePair (U (D f)) f).re=0 := by
  have h:=congrArg Complex.re (weighted_pair f f)
  rw [Complex.neg_re,pair_sym_re f (U (D f))] at h
  linarith
private theorem number_nonnegative (f : QuantumTest) : 0 ≤ (sourcePair f (number f)).re := by
  rw [sourcePair_integral]
  change 0 ≤ RCLike.re (∫ z,densityPair f (number f) z ∂GaussHistoryHilbert.configurationMeasure)
  rw [←integral_re (densityPair_integrable f (number f))]
  apply integral_nonneg
  intro z
  change 0 ≤ (densityPair f (number f) z).re
  by_cases hz : z∈physicalChart
  · rw [densityPair_sum]
    simp only [Complex.re_sum,GaussCoframeForm.number_apply]
    apply Finset.sum_nonneg
    intro word _
    have hd := (GaussDensityCore.density_pos word.card ⟨z,hz⟩).le
    have he : (GaussDensityCore.complexDensity word.card z*star (f z word)*
        ((word.card:ℂ)*f z word)).re=
        GaussDensityCore.density word.card z*(word.card:ℝ)*‖f z word‖^2 := by
      rw [GaussDensityCore.complexDensity]
      have hh : (star (f z word))*(f z word)=((‖f z word‖^2:ℝ):ℂ) := by
        simpa only [RCLike.inner_apply,mul_comm,starRingEnd_apply,Complex.ofReal_pow] using!
          inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (f z word)
      calc
        _=(((GaussDensityCore.density word.card z:ℂ)*(word.card:ℂ))*
            (star (f z word)*f z word)).re := by congr 1;ring
        _=_ := by
          rw [hh]
          norm_cast
          rw [←Complex.ofReal_mul,Complex.ofReal_re]
    rw [he]
    positivity
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem dilation_gram(f:QuantumTest):‖embed (Dc f)‖^2 ≤ (2/3:ℝ)*coframeGram f := by
  have hcenter:Dc=(2/3:ℂ) • (∑b:Fin 3,centeredBlock b) := by
    unfold Dc
    rw [SourceCoframeDilation.dilation_operator]
    simp [centeredBlock,blockMomentum,blockDensity,blockIndices,eulerAction,GaussCoframeCore.momentum,Fin.sum_univ_succ]
    module
  have ht:=norm_sum_le (Finset.univ:Finset (Fin 3)) (fun b=>embed (centeredBlock b f))
  have ht2:=pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hs:=sq_sum_le_card_mul_sum_sq (s:=(Finset.univ:Finset (Fin 3))) (f:=fun b=>‖embed (centeredBlock b f)‖)
  norm_num only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] at hs
  have hn:‖embed (Dc f)‖^2 ≤ (4/3:ℝ)*(∑b:Fin 3,‖embed (centeredBlock b f)‖^2) := by
    rw [hcenter]
    simp only [LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,norm_smul,mul_pow]
    norm_num
    nlinarith only [ht2,hs]
  have hc:=original_coframe_three_block_hardy f
  have hnum:=number_nonnegative f
  nlinarith only [hn,hc,hnum,sq_nonneg ‖embed (number f)‖,sq_nonneg ‖embed f‖]
private theorem norm_complex_mixed(f g:QuantumTest)(t:ℝ):
    ‖embed (f+((t:ℂ)*Complex.I) • g)‖^2=‖embed f‖^2+t^2*‖embed g‖^2-2*t*(sourcePair f g).im := by
  simp only [map_add,map_smul]
  rw [norm_add_sq (𝕜:=ℂ)]
  simp only [norm_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,mul_pow,sq_abs,
    inner_smul_right,RCLike.re_to_complex,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,mul_one,add_zero,sub_zero,sourcePair]
  ring
private theorem bracket_add (B C E:End):bracket B (C+E)=bracket B C+bracket B E := by
  unfold bracket;noncomm_ring
private theorem weighted_current_pair(w:QuantumTest):
    sourcePair w (U (bracket D H0 w))=
      -sourcePair (U (D w)) (H0 w)-sourcePair (H0 w) (U (D w))-
        sourcePair (bracket H0 U w) (D w) := by
  have h1:sourcePair w (U (D (H0 w)))= -sourcePair (U (D w)) (H0 w):=weighted_pair _ _
  have h2:sourcePair w (U (H0 (D w)))=
      sourcePair (H0 w) (U (D w))+sourcePair (bracket H0 U w) (D w) := by
    rw [weight_pair,diagonalAction_pair]
    have he:H0 (U w)=U (H0 w)+bracket H0 U w := by
      simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
      module
    rw [he,pair_add_l,←weight_pair]
  change sourcePair w (U (D (H0 w)-H0 (D w)))=_
  rw [map_sub,pair_sub_r,h1,h2]
  ring
private theorem coframe_current_pair(w:QuantumTest):
    (sourcePair (bracket H0 U w) (D w)).re=
      -(3*n/4)*(sourcePair (U (D w)) (Dc (U w))).im := by
  have hu:=SourceScalarInverseRetardedBudget.original_inverse_current
  change bracket H0 U=(3*Complex.I*(n:ℂ)/4) • (U*Dc*U) at hu
  rw [hu]
  simp only [LinearMap.smul_apply,Module.End.mul_apply,pair_smul_l]
  rw [←weight_pair,←pair_star (U (D w)) (Dc (U w))]
  norm_num only [map_div₀,map_mul,map_ofNat,Complex.conj_I,Complex.conj_ofReal,
    Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.normSq_apply,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
    mul_zero,zero_mul,zero_add,add_zero,sub_zero,neg_zero]
  ring
private theorem actual_weighted_current(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (sourcePair (normalizedState m ell F z hz g)
      (U (bracket D H0 (normalizedState m ell F z hz g)))).re=
      -2*(sourcePair (U (D (normalizedState m ell F z hz g))) (normalizedForcing m ell F z hz g)).re+
      2*z.im*(sourcePair (U (D (normalizedState m ell F z hz g))) (normalizedState m ell F z hz g)).im+
      coframeContact m ell F z hz g := by
  let w:=normalizedState m ell F z hz g
  have hp:=congrArg Complex.re (weighted_current_pair w)
  simp only [Complex.sub_re,Complex.neg_re,pair_sym_re (H0 w) (U (D w)),coframe_current_pair] at hp
  have hs:=full_source m ell F z hz g
  change H0 w=normalizedForcing m ell F z hz g+z • w at hs
  rw [hs] at hp
  simp only [pair_add_r,pair_smul_r,Complex.add_re,Complex.mul_re,weighted_self_real,
    mul_zero,zero_sub] at hp
  change (sourcePair w (U (bracket D H0 w))).re=
    -2*(sourcePair (U (D w)) (normalizedForcing m ell F z hz g)).re+
      2*z.im*(sourcePair (U (D w)) w).im+(3*n/4)*(sourcePair (U (D w)) (Dc (U w))).im
  linear_combination (norm:=ring) hp

private theorem clock_current_real (f : QuantumTest) : (sourcePair f (clockCurrent f)).im=0 := by
  have hc := GaussNativeForm.pair_conjugate f (clockCurrent f)
  rw [←SourceClockFixedInputSeed.original_clock_current_pair] at hc
  have h := congrArg Complex.im hc
  simp only [Complex.conj_im] at h
  linarith only [h]

private theorem inverse_clock_real (f : QuantumTest) : (sourcePair f (inverseVolumeAction f)).im=0 := by
  have hc := GaussNativeForm.pair_conjugate f (inverseVolumeAction f)
  have hp : sourcePair f (inverseVolumeAction f)=sourcePair (inverseVolumeAction f) f := multiply_pair _ _ _ _
  rw [←hp] at hc
  have h := congrArg Complex.im hc
  simp only [Complex.conj_im] at h
  linarith only [h]

private theorem completed_pair_source (f : QuantumTest) :
    (sourcePair f (completedAcceleration f)).re=
      2*(sourcePair (diagonalAction f) (clockCurrent f)).im+
      (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) (diagonalAction f)).re := by
  have hJ := SourceClockFixedInputSeed.original_clock_current_pair f (diagonalAction f)
  have hH := diagonalAction_pair f (clockCurrent f)
  have hV : sourcePair f (inverseVolumeAction (diagonalAction f))=
      sourcePair (inverseVolumeAction f) (diagonalAction f) := multiply_pair _ _ _ _
  have hVH := diagonalAction_pair f (inverseVolumeAction f)
  have hconj := GaussNativeForm.pair_conjugate (diagonalAction f) (clockCurrent f)
  have hconjV := GaussNativeForm.pair_conjugate (inverseVolumeAction f) (diagonalAction f)
  unfold completedAcceleration clockAcceleration
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    pair_add_r,pair_sub_r,pair_smul_r]
  change (((-Complex.I)*(sourcePair f (diagonalAction (clockCurrent f))-
    sourcePair f (clockCurrent (diagonalAction f))))+
    ((sourceTime 0:ℂ)/4)*(sourcePair f (inverseVolumeAction (diagonalAction f))+
      sourcePair f (diagonalAction (inverseVolumeAction f)))).re=_
  rw [hJ,hH,hV,hVH,←hconj,←hconjV]
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.div_re,Complex.div_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re]
  norm_num
  simp only [sourcePair]
  ring

private def localClockPrice (z : ℂ) (f u : QuantumTest) : ℝ :=
  2*(sourcePair u (clockCurrent f)).im-2*z.im*(sourcePair f (clockCurrent f)).re+
    (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) u).re+
    (sourceTime 0/2)*z.re*(sourcePair f (inverseVolumeAction f)).re+
    (sourceTime 0)^2*spinForm (inverseVolumeAction f)+
    (sourceTime 0)^2*densityForm (inverseVolumeAction f)-
    sourceTime 0*gaugeForm (inverseVolumeAction f)-sourceTime 0*spatialForm (inverseVolumeAction f)

private theorem positive_price_source (z : ℂ) (f u : QuantumTest)
    (he : diagonalAction f=u+z • f) :
    localClockPrice z f u=
      (sourceTime 0)^2/4*coframeGram (inverseVolumeAction f)+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction f)+
      2*(sourceTime 0)^2*radiusForm f := by
  have hb := completed_pair_source f
  rw [he] at hb
  simp only [pair_add_l,pair_smul_l,pair_add_r,pair_smul_r] at hb
  change (sourcePair f (completedAcceleration f)).re=
    2*(sourcePair u (clockCurrent f)+(starRingEnd ℂ z)*sourcePair f (clockCurrent f)).im+
      (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) u+z*sourcePair (inverseVolumeAction f) f).re at hb
  have hv : sourcePair (inverseVolumeAction f) f=sourcePair f (inverseVolumeAction f) := (multiply_pair _ _ _ _).symm
  rw [hv] at hb
  simp only [Complex.add_im,Complex.add_re,Complex.mul_im,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    clock_current_real,inverse_clock_real,mul_zero,sub_zero] at hb
  have hs := original_completed_square_form f
  unfold localClockPrice
  linarith only [hb,hs]


/-- The third homogeneous current retains the entire native70 positive block. -/
def nativePressureOperator:End:=bracket A (bracket A H0)+(3:ℂ) • (U*bracket D H0)+
  (2:ℂ) • (U*GaussMatterCore.matterAction)+(8/5:ℂ) • (U*vacuumConstantAction)
def nativePressure(f:QuantumTest):ℝ:=(sourcePair f (nativePressureOperator f)).re
def shiftedColumn40(i:ScalarIndex):End:=shiftedColumn i+
  ((inner ℝ vacuum (scalarBasis i)/10:ℝ):ℂ) • (1:End)
def shiftedMoment40(f:QuantumTest):ℝ:=∑i:ScalarIndex,‖embed (shiftedColumn40 i f)‖^2
def matchedColumn:End:=U*D+(3*Complex.I:ℂ) • (Dc*U)
def matchedTester:End:=matchedColumn+(2:ℂ) • U
def matchedPrice(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  let w:=normalizedState m ell F z hz g
  nativePressure w+12*localClockPrice z w (normalizedForcing m ell F z hz g)/n-
    3*coframeContact m ell F z hz g
/-- The same-state clock has been expanded before the whole source is estimated. -/
def matchedForcingWord(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  let w:=normalizedState m ell F z hz g
  (sourcePair w ((bracket A (bracket A (compressionCore F))+bracket A (bracket A (defectAction F))+
    (2:ℂ) • (U*GaussMatterCore.matterAction)+(8/5:ℂ) • (U*vacuumConstantAction)) w)).re-
    6*(sourcePair (normalizedForcing m ell F z hz g) (matchedTester w)).re+
    6*z.re*(sourcePair w (U w)).re+12*n*spinForm (U w)+12*n*densityForm (U w)-
    12*gaugeForm (U w)-12*spatialForm (U w)

private theorem first_source:bracket D H0=(-2:ℂ) • scalarKinetic+(2:ℂ) • gaugeKinetic+
    (2:ℂ) • centeredAction-(2:ℂ) • vacuumLinearAction-(4:ℂ) • magneticAction-
    GaussMatterCore.matterAction := by
  have hp:=SourceScalarAffineScaleTransport.generator_commutator H0
  have hg:=SourceGaugeScaleTransport.generator_commutator H0
  have hs:=original_scalar_gauge_current
  have he:bracket D H0=deltaPhi H0-SourceScalarGaugeScale.deltaGauge H0 := by
    unfold D combinedGenerator bracket
    rw [sub_mul,mul_sub]
    linear_combination (norm:=module) hp-hg
  rw [he]
  exact hs
private theorem operator_difference:nativePressureOperator=combinedPressureOperator+
    U*((-2:ℂ) • scalarKinetic+(2:ℂ) • gaugeKinetic+(2:ℂ) • centeredAction-
      (2:ℂ) • vacuumLinearAction-(4:ℂ) • magneticAction+(19/40:ℂ) • vacuumConstantAction) := by
  unfold nativePressureOperator combinedPressureOperator
  change bracket A (bracket A H0)+(3:ℂ) • (U*bracket D H0)+(2:ℂ) • (U*GaussMatterCore.matterAction)+
    (8/5:ℂ) • (U*vacuumConstantAction)=_
  rw [first_source]
  simp only [mul_add,mul_sub,mul_smul_comm]
  module
private theorem root_form(B:End)(hc:Commute a B)(f:QuantumTest):
    sourcePair f ((U*B) f)=sourcePair (a f) (B (a f)) := by
  have hs:a*a=U:=LinearMap.ext inverse_root_square
  rw [←hs]
  change sourcePair f (a (a (B f)))=_
  rw [show sourcePair f (a (a (B f)))=sourcePair (a f) (a (B f)) from multiply_pair _ _ _ _]
  exact congrArg (sourcePair (a f)) (LinearMap.congr_fun hc.eq f)
private theorem scalar_weight:multiply scalarWeight scalarWeight_smooth=(-(n:ℂ)) • U := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (scalarWeight x:ℂ) • f x=(-(n:ℂ)) • ((reciprocalVolume x:ℂ) • f x)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1
private theorem scalar_form(f:QuantumTest):(sourcePair f ((U*scalarKinetic) f)).re=
    -(n/2)*scalarForm (U f) := by
  have hr(i:ScalarIndex):sourcePair (U f)
      (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth f)=
      -(n:ℂ)*sourcePair (covariantMomentum (scalarDirection i) (U f))
        (covariantMomentum (scalarDirection i) (U f)) := by
    change sourcePair (U f) (GaussMomentumAdjoint.adjoint (scalarDirection i)
      (multiply scalarWeight scalarWeight_smooth (covariantMomentum (scalarDirection i) f)))=_
    rw [adjoint_pair,scalar_weight]
    simp only [LinearMap.smul_apply,pair_smul_r]
    have hc:=LinearMap.congr_fun (original_native_inverse_commute (scalarDirection i)).eq f
    change covariantMomentum (scalarDirection i) (U f)=U (covariantMomentum (scalarDirection i) f) at hc
    rw [←hc]
  change (sourcePair f (U (scalarKinetic f))).re=_
  rw [weight_pair]
  have he:sourcePair (U f) (scalarKinetic f)=
      (1/2:ℂ)*∑i:ScalarIndex,-(n:ℂ)*sourcePair (covariantMomentum (scalarDirection i) (U f))
        (covariantMomentum (scalarDirection i) (U f)) := by
    simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,
      map_smul,map_sum,inner_smul_right,inner_sum] at hr ⊢
    exact congrArg (fun c:ℂ=>(1/2:ℂ)*c) (Finset.sum_congr rfl (fun i _=>hr i))
  rw [he]
  simp only [self_pair,←Finset.mul_sum,←Complex.ofReal_pow,←Complex.ofReal_sum,
    Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_im,
    neg_zero,mul_zero,sub_zero]
  norm_num
  unfold scalarForm
  ring
private theorem shifted40_point (i:ScalarIndex)(f:QuantumTest)(x:SourceCoordinateSlice) :
    shiftedColumn40 i f x=(inner ℝ (scalarField x-(2/5:ℝ) • vacuum) (scalarBasis i):ℂ) • f x := by
  change (shiftedCoordinate i x:ℂ) • f x+((inner ℝ vacuum (scalarBasis i)/10:ℝ):ℂ) • f x=_
  rw [←add_smul,←Complex.ofReal_add]
  congr 2
  unfold shiftedCoordinate
  simp only [inner_sub_left,real_inner_smul_left]
  ring
private theorem shifted40_pair (i:ScalarIndex)(f g:QuantumTest) :
    sourcePair f (shiftedColumn40 i g)=sourcePair (shiftedColumn40 i f) g := by
  have hs:sourcePair f (shiftedColumn i g)=sourcePair (shiftedColumn i f) g := multiply_pair _ _ _ _
  simp only [shiftedColumn40,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,hs,Complex.conj_ofReal]
private theorem potential_completion :
    U*((10:ℂ) • centeredAction-(8:ℂ) • vacuumLinearAction+(8/5:ℂ) • vacuumConstantAction)=
      (10*(n:ℂ)) • ∑i:ScalarIndex,shiftedColumn40 i*shiftedColumn40 i := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  have hs:(∑i:ScalarIndex,(inner ℝ (scalarField x-(2/5:ℝ) • vacuum) (scalarBasis i))^2)=
      ‖scalarField x-(2/5:ℝ) • vacuum‖^2 := scalarBasis.sum_sq_inner_left _
  have hp:10*‖scalarField x‖^2-8*inner ℝ vacuum (scalarField x)+(8/5:ℝ)*‖vacuum‖^2=
      10*‖scalarField x-(2/5:ℝ) • vacuum‖^2 := by
    rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
      real_inner_comm vacuum (scalarField x)]
    norm_num
    ring
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply]
  change (reciprocalVolume x:ℂ) • ((10:ℂ) • ((n*volume x*‖scalarField x‖^2:ℝ):ℂ) • f x-
    (8:ℂ) • ((n*volume x*inner ℝ vacuum (scalarField x):ℝ):ℂ) • f x+
    (8/5:ℂ) • ((n*volume x*‖vacuum‖^2:ℝ):ℂ) • f x)=
      (10*(n:ℂ)) • ((∑i:ScalarIndex,shiftedColumn40 i (shiftedColumn40 i f)) x)
  rw [sum_apply]
  simp only [shifted40_point,smul_smul,←pow_two,←Finset.sum_smul,←Complex.ofReal_pow,
    ←Complex.ofReal_sum,hs]
  by_cases hx:x ∈ physicalChart
  · have hc:reciprocalVolume x*(10*(n*volume x*‖scalarField x‖^2)-
        8*(n*volume x*inner ℝ vacuum (scalarField x))+(8/5:ℝ)*(n*volume x*‖vacuum‖^2))=
        10*n*‖scalarField x-(2/5:ℝ) • vacuum‖^2 := by
      unfold reciprocalVolume
      have hv:volume x≠0:=(volume_pos ⟨x,hx⟩).ne'
      field_simp [hv]
      linear_combination (norm:=ring) (5*n)*hp
    simp only [←add_smul,←sub_smul,smul_smul]
    simpa only [Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_div,
      Complex.ofReal_ofNat] using congrArg (fun c:ℝ=>(c:ℂ) • f x) hc
  · rw [image_eq_zero_of_notMem_tsupport (fun h=>hx (f.tsupport_subset h))]
    simp only [smul_zero,sub_self,zero_add]
private theorem shifted40_square_pair (f:QuantumTest) :
    sourcePair f ((∑i:ScalarIndex,shiftedColumn40 i*shiftedColumn40 i) f)=
      (shiftedMoment40 f:ℂ) := by
  simp only [LinearMap.sum_apply,Module.End.mul_apply,pair_sum_r,shifted40_pair,self_pair,
    ←Complex.ofReal_pow,←Complex.ofReal_sum,shiftedMoment40]

private theorem shifted38_point (i:ScalarIndex)(f:QuantumTest)(x:SourceCoordinateSlice) :
    shiftedColumn38 i f x=(inner ℝ (scalarField x-(3/8:ℝ) • vacuum) (scalarBasis i):ℂ) • f x := by
  change (shiftedCoordinate i x:ℂ) • f x+((inner ℝ vacuum (scalarBasis i)/8:ℝ):ℂ) • f x=_
  rw [←add_smul,←Complex.ofReal_add]
  congr 2
  unfold shiftedCoordinate
  simp only [inner_sub_left,real_inner_smul_left]
  ring
private theorem shifted38_pair (i:ScalarIndex)(f g:QuantumTest) :
    sourcePair f (shiftedColumn38 i g)=sourcePair (shiftedColumn38 i f) g := by
  have hs:sourcePair f (shiftedColumn i g)=sourcePair (shiftedColumn i f) g := multiply_pair _ _ _ _
  simp only [shiftedColumn38,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,hs,Complex.conj_ofReal]
private theorem potential38_completion :
    U*((8:ℂ) • centeredAction-(6:ℂ) • vacuumLinearAction+(9/8:ℂ) • vacuumConstantAction)=
      (8*(n:ℂ)) • ∑i:ScalarIndex,shiftedColumn38 i*shiftedColumn38 i := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  have hs:(∑i:ScalarIndex,(inner ℝ (scalarField x-(3/8:ℝ) • vacuum) (scalarBasis i))^2)=
      ‖scalarField x-(3/8:ℝ) • vacuum‖^2 := scalarBasis.sum_sq_inner_left _
  have hp:8*‖scalarField x‖^2-6*inner ℝ vacuum (scalarField x)+(9/8:ℝ)*‖vacuum‖^2=
      8*‖scalarField x-(3/8:ℝ) • vacuum‖^2 := by
    rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
      real_inner_comm vacuum (scalarField x)]
    norm_num
    ring
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply]
  change (reciprocalVolume x:ℂ) • ((8:ℂ) • ((n*volume x*‖scalarField x‖^2:ℝ):ℂ) • f x-
    (6:ℂ) • ((n*volume x*inner ℝ vacuum (scalarField x):ℝ):ℂ) • f x+
    (9/8:ℂ) • ((n*volume x*‖vacuum‖^2:ℝ):ℂ) • f x)=
      (8*(n:ℂ)) • ((∑i:ScalarIndex,shiftedColumn38 i (shiftedColumn38 i f)) x)
  rw [sum_apply]
  simp only [shifted38_point,smul_smul,←pow_two,←Finset.sum_smul,←Complex.ofReal_pow,
    ←Complex.ofReal_sum,hs]
  by_cases hx:x ∈ physicalChart
  · have hc:reciprocalVolume x*(8*(n*volume x*‖scalarField x‖^2)-
        6*(n*volume x*inner ℝ vacuum (scalarField x))+(9/8:ℝ)*(n*volume x*‖vacuum‖^2))=
        8*n*‖scalarField x-(3/8:ℝ) • vacuum‖^2 := by
      unfold reciprocalVolume
      have hv:volume x≠0:=(volume_pos ⟨x,hx⟩).ne'
      field_simp [hv]
      linear_combination (norm:=ring) (8*n)*hp
    simp only [←add_smul,←sub_smul,smul_smul]
    simpa only [Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_div,
      Complex.ofReal_ofNat] using congrArg (fun c:ℝ=>(c:ℂ) • f x) hc
  · rw [image_eq_zero_of_notMem_tsupport (fun h=>hx (f.tsupport_subset h))]
    simp only [smul_zero,sub_self,zero_add]
private theorem shifted38_square_pair (f:QuantumTest) :
    sourcePair f ((∑i:ScalarIndex,shiftedColumn38 i*shiftedColumn38 i) f)=
      (shiftedMoment38 f:ℂ) := by
  simp only [LinearMap.sum_apply,Module.End.mul_apply,pair_sum_r,shifted38_pair,self_pair,
    ←Complex.ofReal_pow,←Complex.ofReal_sum,shiftedMoment38]


private theorem potential_difference(f:QuantumTest):8*n*shiftedMoment38 f+
    (sourcePair f ((U*((2:ℂ) • centeredAction-(2:ℂ) • vacuumLinearAction+
      (19/40:ℂ) • vacuumConstantAction)) f)).re=10*n*shiftedMoment40 f := by
  have ho:(8*(n:ℂ)) • (∑i:ScalarIndex,shiftedColumn38 i*shiftedColumn38 i)+
      U*((2:ℂ) • centeredAction-(2:ℂ) • vacuumLinearAction+(19/40:ℂ) • vacuumConstantAction)=
        (10*(n:ℂ)) • (∑i:ScalarIndex,shiftedColumn40 i*shiftedColumn40 i) := by
    rw [←potential38_completion,←potential_completion]
    simp only [mul_add,mul_sub,mul_smul_comm]
    module
  have h:=congrArg (fun B:End=>(sourcePair f (B f)).re) ho
  simp only [LinearMap.add_apply,LinearMap.smul_apply,pair_add_r,pair_smul_r,
    shifted38_square_pair,shifted40_square_pair,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
    mul_zero,sub_zero] at h
  exact h
private theorem native_pressure_source(f:QuantumTest):nativePressure f=
    (3*n/8)*‖embed (U (D f))‖^2+n*scalarForm (U f)+
      10*(sourcePair (a f) (gaugeKinetic (a f))).re+
      4*(sourcePair (a f) (magneticAction (a f))).re+10*n*shiftedMoment40 f := by
  have ho:nativePressureOperator=combinedPressureOperator+
      (-2:ℂ) • (U*scalarKinetic)+(2:ℂ) • (U*gaugeKinetic)-(4:ℂ) • (U*magneticAction)+
      U*((2:ℂ) • centeredAction-(2:ℂ) • vacuumLinearAction+(19/40:ℂ) • vacuumConstantAction) := by
    rw [operator_difference]
    simp only [mul_add,mul_sub,mul_smul_comm]
    module
  unfold nativePressure
  rw [ho]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,pair_add_r,pair_sub_r,pair_smul_r,
    Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero,neg_zero]
  change combinedPressure f+(-2)*(sourcePair f ((U*scalarKinetic) f)).re+
    2*(sourcePair f ((U*gaugeKinetic) f)).re-4*(sourcePair f ((U*magneticAction) f)).re+_= _
  rw [(original_combined_pressure_source f).1,scalar_form,
    root_form gaugeKinetic inverse_root_electric,root_form magneticAction (inverse_root_real _ _)]
  linear_combination (norm:=ring) potential_difference f
private theorem native_floor(f:QuantumTest):(3*n/8)*‖embed (U (D f))‖^2+
    n*scalarForm (U f)+10*n*shiftedMoment40 f ≤ nativePressure f := by
  rw [native_pressure_source]
  have hg:=original_gauge_kinetic_nonnegative (a f)
  have hm:=SourceClockPhiSecondBulk.original_magnetic_nonnegative (a f)
  linarith
private theorem density_nonnegative (f : QuantumTest) (z : SourceCoordinateSlice) : 0 ≤ (densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · have h := GaussBoundedMultiplier.weighted_square (fun N => GaussDensityCore.density N z)
      (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
    exact (sq_nonneg _).trans_eq h.symm
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem radius_floor (f : QuantumTest) : 3*‖embed f‖^2 ≤ radiusForm f := by
  let c : SourceCoordinateSlice → ℝ := fun z => 4*(GaussYukawaCoefficient.radius z)^2-1
  have hc : ContDiff ℝ ∞ c := (contDiff_const.mul (GaussYukawaCoefficient.radius_smooth.pow 2)).sub contDiff_const
  let A : End := multiply c (fun _ => hc.contDiffAt)
  have hr : radiusForm f=(sourcePair f (A f)).re := rfl
  have hpair : (sourcePair f (A f)).re=∫ z : SourceCoordinateSlice,(densityPair f (A f) z).re
      ∂GaussHistoryHilbert.configurationMeasure := by
    rw [sourcePair_integral]
    exact (integral_re (densityPair_integrable f (A f))).symm
  rw [hr,hpair,GaussBoundedMultiplier.norm_square_integral,←integral_const_mul]
  apply integral_mono ((densityPair_integrable f f).re.const_mul 3) (densityPair_integrable f (A f)).re
  intro z
  change 3*(densityPair f f z).re ≤ (densityPair f (A f) z).re
  have he : densityPair f (A f) z=(c z:ℂ)*densityPair f f z := inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hr := GaussRadialDomain.one_le_radius z
  have hc3 : 3 ≤ c z := by dsimp only [c];nlinarith only [hr]
  exact mul_le_mul_of_nonneg_right hc3 (density_nonnegative f z)



private theorem local_clock_floor(z:ℂ)(f u:QuantumTest)(he:H0 f=u+z • f):
    n^2/4*coframeGram (U f)+n^2/2*scalarForm (U f)+6*n^2*‖embed f‖^2 ≤ localClockPrice z f u := by
  rw [positive_price_source z f u he]
  have hr:=radius_floor f
  have hs:=mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*n^2 by positivity)
  change n^2/4*coframeGram (U f)+n^2/2*scalarForm (U f)+6*n^2*‖embed f‖^2 ≤
    n^2/4*coframeGram (U f)+n^2/2*scalarForm (U f)+2*n^2*radiusForm f
  linarith only [hs]
private theorem local_dilation_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (3*n/8)*‖embed (Dc (U (normalizedState m ell F z hz g)))‖^2 ≤
      localClockPrice z (normalizedState m ell F z hz g) (normalizedForcing m ell F z hz g)/n := by
  let w:=normalizedState m ell F z hz g
  have hd:=dilation_gram (U w)
  have hp:=local_clock_floor z w (normalizedForcing m ell F z hz g) (full_source m ell F z hz g)
  have hs:0 ≤ scalarForm (U w):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hn:=lapse_pos
  apply (le_div_iff₀ hn).mpr
  have hmul:=mul_le_mul_of_nonneg_left hd (show 0 ≤ 3*n^2/8 by positivity)
  nlinarith only [hp,hmul,mul_nonneg (show 0 ≤ n^2/2 by positivity) hs,
    show 0 ≤ 6*n^2*‖embed w‖^2 by positivity]
private theorem matched_slots(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (3*n/8)*‖embed (matchedColumn (normalizedState m ell F z hz g))‖^2+
      n*scalarForm (U (normalizedState m ell F z hz g))+10*n*shiftedMoment40 (normalizedState m ell F z hz g)+
      3*localClockPrice z (normalizedState m ell F z hz g) (normalizedForcing m ell F z hz g)/n ≤
        matchedPrice m ell F z hz g ∧
    nativePressure (normalizedState m ell F z hz g) ≤ 4*matchedPrice m ell F z hz g := by
  let w:=normalizedState m ell F z hz g
  let x:=U (D w)
  let y:=Dc (U w)
  have hp:=native_floor w
  have hd:=local_dilation_price m ell F z hz g
  have hs:0 ≤ scalarForm (U w):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hm:0 ≤ shiftedMoment40 w:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have he3:=norm_complex_mixed x y 3
  have he4:=norm_complex_mixed x y 4
  have hn:=lapse_pos
  have hh:=sq_nonneg ‖embed (x+(4*Complex.I:ℂ) • y)‖
  have hstrong:=mul_nonneg (show 0 ≤ 3*n/8 by positivity) hh
  change (3*n/8)*‖embed x‖^2+n*scalarForm (U w)+10*n*shiftedMoment40 w ≤ nativePressure w at hp
  change (3*n/8)*‖embed y‖^2 ≤ localClockPrice z w (normalizedForcing m ell F z hz g)/n at hd
  change (3*n/8)*‖embed (x+(3*Complex.I:ℂ) • y)‖^2+n*scalarForm (U w)+10*n*shiftedMoment40 w+
    3*localClockPrice z w (normalizedForcing m ell F z hz g)/n ≤
      nativePressure w+12*localClockPrice z w (normalizedForcing m ell F z hz g)/n-
        3*((3*n/4)*(sourcePair x y).im) ∧
    nativePressure w ≤ 4*(nativePressure w+12*localClockPrice z w (normalizedForcing m ell F z hz g)/n-
        3*((3*n/4)*(sourcePair x y).im))
  norm_num only [Complex.ofReal_ofNat] at he3 he4
  rw [he3]
  rw [he4] at hstrong
  simp only [div_eq_mul_inv] at hp hd hstrong ⊢
  constructor
  · nlinarith only [hp,hd]
  · nlinarith only [hp,hd,hstrong,mul_nonneg hn.le hs,mul_nonneg hn.le hm]
private theorem inverse_dilation : dilation*inverseVolumeAction-inverseVolumeAction*dilation=
    (2*Complex.I) • inverseVolumeAction := by
  have h := congrArg (fun A : End => (-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) •
      (dilation*inverseVolumeAction-inverseVolumeAction*dilation))=
    (-2*Complex.I/3) • ((-3:ℂ) • inverseVolumeAction) at h
  simp only [smul_smul] at h
  have hi : (-2*Complex.I/3)*(3*Complex.I/2)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring


private theorem clock_current_return:clockCurrent=(3*(n:ℂ)/4) • (Dc*U-Complex.I • U) := by
  have hi:=inverse_dilation
  change Dc*U-U*Dc=(2*Complex.I) • U at hi
  rw [original_clock_current]
  change (3*(n:ℂ)/8) • (U*Dc+Dc*U)=(3*(n:ℂ)/4) • (Dc*U-Complex.I • U)
  linear_combination (norm:=module) (-(3*(n:ℂ)/8)) • hi
private theorem matched_tester_return:matchedTester=U*D+Complex.I •
    (U*((3:ℂ) • Dc+(4*Complex.I:ℂ) • (1:End))) := by
  have hi:=inverse_dilation
  change Dc*U-U*Dc=(2*Complex.I) • U at hi
  have he:Dc*U=U*Dc+(2*Complex.I) • U:=by linear_combination (norm:=module) hi
  have hh:Complex.I*(4*Complex.I)=(-4:ℂ):=by
    calc _=4*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  have h6:(3*Complex.I)*(2*Complex.I)=(-6:ℂ):=by
    calc _=6*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  unfold matchedTester matchedColumn
  rw [he]
  simp only [mul_add,mul_smul_comm,mul_one,smul_add,smul_smul,hh,h6]
  module
private theorem clock_forcing_return(f w:QuantumTest):
    -6*(sourcePair (U (D w)) f).re+24/n*(sourcePair f (clockCurrent w)).im+
      6*(sourcePair (U w) f).re= -6*(sourcePair f (matchedTester w)).re := by
  rw [clock_current_return]
  simp only [matchedTester,matchedColumn,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.mul_apply,pair_add_r,pair_sub_r,pair_smul_r]
  rw [pair_sym_re (U (D w)) f,pair_sym_re (U w) f]
  norm_num only [Complex.add_re,Complex.sub_re,Complex.add_im,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.normSq_apply,
    Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,Complex.I_re,Complex.I_im,
    zero_mul,mul_zero,zero_add,add_zero,sub_zero,mul_one,one_mul]
  field_simp [lapse_pos.ne']
  ring
private theorem clock_phase_return(w:QuantumTest)(σ:ℝ):
    6*σ*(sourcePair (U (D w)) w).im-24*σ/n*(sourcePair w (clockCurrent w)).re=
      6*σ*(sourcePair (matchedColumn w) w).im := by
  rw [clock_current_return]
  simp only [matchedColumn,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.mul_apply,pair_add_l,pair_sub_r,pair_smul_l,pair_smul_r]
  have hu:(sourcePair w (U w)).im=0:=inverse_clock_real w
  have hc:=pair_sym_re w (Dc (U w))
  norm_num only [map_mul,map_ofNat,Complex.conj_I,Complex.conj_ofReal,
    Complex.add_re,Complex.sub_re,Complex.add_im,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.normSq_apply,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,
    Complex.im_ofNat,Complex.I_re,Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,
    sub_zero,mul_one,one_mul,hu]
  rw [hc]
  field_simp [lapse_pos.ne']
  ring
private theorem matched_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    matchedPrice m ell F z hz g=matchedForcingWord m ell F z hz g+
      6*z.im*(sourcePair (matchedColumn (normalizedState m ell F z hz g))
        (normalizedState m ell F z hz g)).im := by
  let w:=normalizedState m ell F z hz g
  let f:=normalizedForcing m ell F z hz g
  have hH:H0=compressionCore F+defectAction F:=by unfold defectAction;module
  have hb:bracket A (bracket A H0)=bracket A (bracket A (compressionCore F))+
      bracket A (bracket A (defectAction F)):=by rw [hH,bracket_add,bracket_add]
  have hc:=actual_weighted_current m ell F z hz g
  have hf:=clock_forcing_return f w
  have hphase:=clock_phase_return w z.im
  unfold matchedPrice nativePressure nativePressureOperator matchedForcingWord localClockPrice
  rw [hb]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,pair_add_r,pair_smul_r,
    Complex.add_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  dsimp only [w,f] at hc hf hphase
  rw [hc]
  field_simp [lapse_pos.ne'] at hf hphase ⊢
  linear_combination (norm:=ring) 2*hf+2*z.im*hphase

private theorem matched_expanded_slots(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (3*n/8)*‖embed (matchedColumn (normalizedState m ell F z hz g))‖^2+
      (5*n/2)*scalarForm (U (normalizedState m ell F z hz g))+
      10*n*shiftedMoment40 (normalizedState m ell F z hz g)+
      (3*n/4)*coframeGram (U (normalizedState m ell F z hz g))+
      18*n*‖embed (normalizedState m ell F z hz g)‖^2 ≤ matchedPrice m ell F z hz g := by
  let w:=normalizedState m ell F z hz g
  have hj:=(matched_slots m ell F z hz g).1
  have hc:=local_clock_floor z w (normalizedForcing m ell F z hz g) (full_source m ell F z hz g)
  have he:(3*n/4)*coframeGram (U w)+(3*n/2)*scalarForm (U w)+18*n*‖embed w‖^2 ≤
      3*localClockPrice z w (normalizedForcing m ell F z hz g)/n := by
    apply (le_div_iff₀ lapse_pos).mpr
    nlinarith only [hc]
  change (3*n/8)*‖embed (matchedColumn w)‖^2+n*scalarForm (U w)+10*n*shiftedMoment40 w+
    3*localClockPrice z w (normalizedForcing m ell F z hz g)/n ≤ matchedPrice m ell F z hz g at hj
  change (3*n/8)*‖embed (matchedColumn w)‖^2+(5*n/2)*scalarForm (U w)+10*n*shiftedMoment40 w+
    (3*n/4)*coframeGram (U w)+18*n*‖embed w‖^2 ≤ matchedPrice m ell F z hz g
  linarith only [hj,he]

/-- Native70, the matched original coframe word and all same-CF forcing share one source price. -/
theorem actual_native_matched_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    matchedTester=U*D+Complex.I • (U*((3:ℂ) • Dc+(4*Complex.I:ℂ) • (1:End))) ∧
    matchedPrice m ell F z hz g=matchedForcingWord m ell F z hz g+
      6*z.im*(sourcePair (matchedColumn (normalizedState m ell F z hz g))
        (normalizedState m ell F z hz g)).im ∧
    (3*n/8)*‖embed (matchedColumn (normalizedState m ell F z hz g))‖^2+
      (5*n/2)*scalarForm (U (normalizedState m ell F z hz g))+10*n*shiftedMoment40 (normalizedState m ell F z hz g)+
      (3*n/4)*coframeGram (U (normalizedState m ell F z hz g))+
      18*n*‖embed (normalizedState m ell F z hz g)‖^2 ≤
        matchedPrice m ell F z hz g ∧
    nativePressure (normalizedState m ell F z hz g) ≤ 4*matchedPrice m ell F z hz g :=
  ⟨matched_tester_return,matched_source m ell F z hz g,matched_expanded_slots m ell F z hz g,(matched_slots m ell F z hz g).2⟩
private theorem young(x y t:ℝ)(ht:0<t):x*y ≤ t*x^2+y^2/(4*t) := by
  have he:(4*t)*(y^2/(4*t))=y^2:=by field_simp
  nlinarith only [sq_nonneg (2*t*x-y),he,ht]
private theorem phase_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    |6*z.im*(sourcePair (matchedColumn (normalizedState m ell F z hz g)) (normalizedState m ell F z hz g)).im| ≤
      η*matchedPrice m ell F z hz g+24*z.im^2/(n*η)*‖embed (normalizedState m ell F z hz g)‖^2 := by
  let w:=normalizedState m ell F z hz g
  have hj:=(matched_slots m ell F z hz g).1
  have hm:0 ≤ shiftedMoment40 w:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hs:0 ≤ scalarForm (U w):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hc:=local_clock_floor z w (normalizedForcing m ell F z hz g) (full_source m ell F z hz g)
  have hcf:=original_coframe_gram_nonnegative (U w)
  have hn:=lapse_pos
  have hpp:0 ≤ localClockPrice z w (normalizedForcing m ell F z hz g) := by
    nlinarith only [hc,mul_nonneg (show 0 ≤ n^2/4 by positivity) hcf,
      mul_nonneg (show 0 ≤ n^2/2 by positivity) hs,show 0 ≤ 6*n^2*‖embed w‖^2 by positivity]
  have hD:(3*n/8)*‖embed (matchedColumn w)‖^2 ≤ matchedPrice m ell F z hz g := by
    have h3:0 ≤ 3*localClockPrice z w (normalizedForcing m ell F z hz g)/n:=by positivity
    nlinarith only [hj,h3,mul_nonneg hn.le hm,mul_nonneg hn.le hs]
  have hi:|(sourcePair (matchedColumn w) w).im| ≤ ‖embed (matchedColumn w)‖*‖embed w‖ := by
    exact (Complex.abs_im_le_norm _).trans (by unfold sourcePair;exact norm_inner_le_norm _ _)
  have ha:|6*z.im*(sourcePair (matchedColumn w) w).im| ≤ 6*|z.im| *‖embed (matchedColumn w)‖*‖embed w‖ := by
    rw [abs_mul,abs_mul]
    norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
    have ht:=mul_le_mul_of_nonneg_left hi (show 0 ≤ 6*|z.im| by positivity)
    nlinarith only [ht]
  have hy:=young ‖embed (matchedColumn w)‖ (6*|z.im| *‖embed w‖) (η*3*n/8) (by positivity)
  have he:(6*|z.im| *‖embed w‖)^2/(4*(η*3*n/8))=24*z.im^2/(n*η)*‖embed w‖^2 := by
    rw [mul_pow,mul_pow,sq_abs]
    field_simp
    ring
  rw [he] at hy
  have hpay:=mul_le_mul_of_nonneg_left hD hη.le
  change |6*z.im*(sourcePair (matchedColumn w) w).im| ≤ η*matchedPrice m ell F z hz g+
    24*z.im^2/(n*η)*‖embed w‖^2
  nlinarith only [ha,hy,hpay]
private theorem frequency_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(t:ℝ):
    (actualFrequency advanced μ t).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'

private theorem actual_matched_phase_common_tail(μ:ℝ)(hμ:0<μ)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀advanced:Bool,(∫⁻t:ℝ,ENNReal.ofReal
        (|6*(actualFrequency advanced μ t).im*(sourcePair
          (matchedColumn (normalizedState m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g))
          (normalizedState m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g)).im|-
          η*matchedPrice m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  let K:ℝ:=24*μ^2/(n*η)
  have hK:0 ≤ K:=by dsimp only [K];have hn:=lapse_pos;positivity
  obtain ⟨N,hN⟩:=actual_normalized_response_common_tail μ hμ g (ε/(K+1)) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  calc
    _ ≤ ∫⁻t:ℝ,ENNReal.ofReal K*ENNReal.ofReal
        (normalizedEnergy m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g) := by
      apply lintegral_mono
      intro t
      have hp:=phase_price m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g η hη
      have hi:(actualFrequency advanced μ t).im^2=μ^2 := by
        cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
          Complex.star_def,Complex.conj_im,line_im,neg_sq]
      have he:‖embed (normalizedState m ell F (actualFrequency advanced μ t)
          (frequency_nonreal advanced μ hμ t) g)‖^2=
          normalizedEnergy m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g := by
        unfold normalizedEnergy
        rw [normalized_return]
      rw [hi,he] at hp
      change _ ≤ ENNReal.ofReal K*ENNReal.ofReal (normalizedEnergy m ell F (actualFrequency advanced μ t)
        (frequency_nonreal advanced μ hμ t) g)
      rw [←ENNReal.ofReal_mul hK]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [K]
      linarith only [hp]
    _ = ENNReal.ofReal K*(∫⁻t:ℝ,ENNReal.ofReal (normalizedEnergy m ell F (actualFrequency advanced μ t)
        (frequency_nonreal advanced μ hμ t) g)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal K*ENNReal.ofReal (ε/(K+1)) :=
      mul_le_mul_of_nonneg_left (hF advanced) (show 0 ≤ ENNReal.ofReal K from zero_le)
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hK]
      apply ENNReal.ofReal_le_ofReal
      have hk:0<K+1:=by positivity
      rw [←mul_div_assoc]
      apply (div_le_iff₀ hk).mpr
      nlinarith only [hε]

private theorem ofReal_two_mul(c:ℝ):ENNReal.ofReal (2*c)=(2:ENNReal)*ENNReal.ofReal c := by
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- The complete matched source is returned after both causal joint phases are paid internally. -/
theorem actual_native_matched_common_payment(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀advanced:Bool,(∫⁻t:ℝ,ENNReal.ofReal
        (matchedPrice m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g-
          2*matchedForcingWord m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_matched_phase_common_tail μ hμ g (1/2) (by norm_num) (ε/2) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  calc
    _ ≤ ∫⁻t:ℝ,(2:ENNReal)*ENNReal.ofReal
        (|6*(actualFrequency advanced μ t).im*(sourcePair
          (matchedColumn (normalizedState m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g))
          (normalizedState m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g)).im|-
          (1/2:ℝ)*matchedPrice m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g) := by
      apply lintegral_mono
      intro t
      have h:=actual_native_matched_source m ell F (actualFrequency advanced μ t)
        (frequency_nonreal advanced μ hμ t) g
      have ha:=le_abs_self (6*(actualFrequency advanced μ t).im*(sourcePair
          (matchedColumn (normalizedState m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g))
          (normalizedState m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g)).im)
      dsimp only
      rw [←ofReal_two_mul]
      apply ENNReal.ofReal_le_ofReal
      linarith only [h.2.1,ha]
    _ ≤ (2:ENNReal)*ENNReal.ofReal (ε/2) := by
      rw [lintegral_const_mul' _ _ (by norm_num : (2:ENNReal)≠⊤)]
      exact mul_le_mul_of_nonneg_left (hF advanced) zero_le
    _ = ENNReal.ofReal ε := by
      rw [←ofReal_two_mul]
      congr 1
      ring

end LowEnergy.SourceClockPhiNativeMatchedSource
