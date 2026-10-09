import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCombinedScalePressure
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusNormalizedFluxBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockSourceTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiJointScaleNoether
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarVirialBulk SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNormalizedScalarBudget
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiRadiusNormalizedFluxBudget
open SourceClockReflectedForm SourceClockSourceTail SourceCoframeBlockHardy GaussCoframeForm
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceLocalizedInverseFormPayment
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest
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

def jointColumn(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  U (D (normalizedState m ell F z hz g))+(2*Complex.I:ℂ) • Dc (U (normalizedState m ell F z hz g))
def coframeContact(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  (3*n/4)*(sourcePair (U (D (normalizedState m ell F z hz g)))
    (Dc (U (normalizedState m ell F z hz g)))).im
def jointPrice(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  combinedPressure (normalizedState m ell F z hz g)+8*phiPositivePrice m ell F z hz g/n-
    2*coframeContact m ell F z hz g
def wholeForcingWord(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  let w:=normalizedState m ell F z hz g
  (sourcePair w ((bracket A (bracket A (compressionCore F))+bracket A (bracket A (defectAction F))) w)).re-
    4*(sourcePair (U (D w)) (normalizedForcing m ell F z hz g)).re+
    (sourcePair w ((U*GaussMatterCore.matterAction+(9/8:ℂ) • (U*vacuumConstantAction)) w)).re+
    8*phiPositivePrice m ell F z hz g/n

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
private theorem phi_reciprocal_smooth : ContDiff ℝ ∞ phiReciprocal := by
  apply SourceClockRadiusResponseAffine.affine_radius_smooth.inv
  intro z
  change Real.sqrt (1+‖scalarField z‖^2/4)≠0
  positivity
private theorem inverse_euler(z:SourceCoordinateSlice):fderiv ℝ phiReciprocal z (SourceCoframeVolume.euler z)=0 := by
  have hp:HasDerivAt (fun t:ℝ=>z+t • SourceCoframeVolume.euler z) (SourceCoframeVolume.euler z) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const (SourceCoframeVolume.euler z) |>.const_add z
  have hd:HasFDerivAt phiReciprocal (fderiv ℝ phiReciprocal z) z:=
    (phi_reciprocal_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hh:=hd.comp_hasDerivAt_of_eq 0 hp (by simp)
  have he:(fun t:ℝ=>phiReciprocal (z+t • SourceCoframeVolume.euler z))=fun _=>phiReciprocal z := by
    funext t
    unfold phiReciprocal phiRadius SourceClockRadiusResponseAffine.affineRadius scalarField SourceCoframeVolume.euler
    simp only [Prod.smul_mk,Prod.snd_add,smul_zero,add_zero]
  change HasDerivAt (fun t:ℝ=>phiReciprocal (z+t • SourceCoframeVolume.euler z))
    (fderiv ℝ phiReciprocal z (SourceCoframeVolume.euler z)) 0 at hh
  rw [he] at hh
  exact hh.unique (hasDerivAt_const 0 _)
private theorem dilation_inverse : Commute Dc S := by
  have h:=SourceDilationMultiplier.homogeneous_multiplier phiReciprocal
    (fun _=>phi_reciprocal_smooth.contDiffAt) 0 (fun z=>by simpa only [zero_mul] using inverse_euler z)
  simp only [Complex.ofReal_zero,mul_zero,zero_smul] at h
  exact sub_eq_zero.mp h
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
private theorem dilation_weight_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (3*n/8)*‖embed (Dc (U (normalizedState m ell F z hz g)))‖^2 ≤ phiPositivePrice m ell F z hz g/n := by
  let v:=phiResponseCore m ell F z hz g
  have hu:Commute U S:=real_commute _ _ _ _
  have he: Dc (U (normalizedState m ell F z hz g))=S (Dc (U v)) := by
    rw [normalized_return]
    have h1:=LinearMap.congr_fun hu.eq v
    have h2:=LinearMap.congr_fun dilation_inverse.eq (U v)
    change U (S v)=S (U v) at h1
    change Dc (S (U v))=S (Dc (U v)) at h2
    rw [h1,h2]
  have hn:‖embed (Dc (U (normalizedState m ell F z hz g)))‖ ≤ ‖embed (Dc (U v))‖ := by
    rw [he,←phi_inverse_core]
    exact (phiInverseBounded.le_opNorm _).trans ((mul_le_mul_of_nonneg_right phi_inverse_norm
      (norm_nonneg _)).trans_eq (one_mul _))
  have hn2:=sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hn
  have hd:=dilation_gram (U v)
  have hp:=actual_phi_positive_slots m ell F z hz g
  have hscalar:0 ≤ scalarForm (U v):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hs:=mul_nonneg (show 0 ≤ n^2/2 by positivity) hscalar
  have hv:0 ≤ 6*n^2*‖embed v‖^2:=by positivity
  change n^2/4*coframeGram (U v)+n^2/2*scalarForm (U v)+6*n^2*‖embed v‖^2 ≤
    phiPositivePrice m ell F z hz g at hp
  apply (le_div_iff₀ lapse_pos).mpr
  have hscale:=mul_le_mul_of_nonneg_left (hn2.trans hd) (show 0 ≤ 3*n^2/8 by positivity)
  nlinarith only [hp,hs,hv,hscale]
private theorem norm_complex_mixed(f g:QuantumTest)(t:ℝ):
    ‖embed (f+((t:ℂ)*Complex.I) • g)‖^2=‖embed f‖^2+t^2*‖embed g‖^2-2*t*(sourcePair f g).im := by
  simp only [map_add,map_smul]
  rw [norm_add_sq (𝕜:=ℂ)]
  simp only [norm_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,mul_pow,sq_abs,
    inner_smul_right,RCLike.re_to_complex,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,mul_one,add_zero,sub_zero,sourcePair]
  ring
private theorem joint_slots(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (3*n/8)*‖embed (jointColumn m ell F z hz g)‖^2+
      8*n*shiftedMoment38 (normalizedState m ell F z hz g)+4*phiPositivePrice m ell F z hz g/n ≤
        jointPrice m ell F z hz g ∧
    combinedPressure (normalizedState m ell F z hz g) ≤ 2*jointPrice m ell F z hz g := by
  let w:=normalizedState m ell F z hz g
  let x:=U (D w)
  let y:=Dc (U w)
  have hp:=(original_combined_pressure_source w).2
  have hd:=dilation_weight_price m ell F z hz g
  change (3*n/8)*‖embed x‖^2+8*n*shiftedMoment38 w ≤ combinedPressure w at hp
  change (3*n/8)*‖embed y‖^2 ≤ phiPositivePrice m ell F z hz g/n at hd
  have hm:0 ≤ shiftedMoment38 w:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have he2:=norm_complex_mixed x y 2
  have he4:=norm_complex_mixed x y 4
  have hn:=lapse_pos
  have hh:=sq_nonneg ‖embed (x+(4*Complex.I:ℂ) • y)‖
  have hstrong:=mul_nonneg (show 0 ≤ 3*n/8 by positivity) hh
  change (3*n/8)*‖embed (x+(2*Complex.I:ℂ) • y)‖^2+8*n*shiftedMoment38 w+
    4*phiPositivePrice m ell F z hz g/n ≤ combinedPressure w+8*phiPositivePrice m ell F z hz g/n-
      2*((3*n/4)*(sourcePair x y).im) ∧
    combinedPressure w ≤ 2*(combinedPressure w+8*phiPositivePrice m ell F z hz g/n-
      2*((3*n/4)*(sourcePair x y).im))
  norm_num only [Complex.ofReal_ofNat] at he2 he4
  rw [he2]
  simp only [div_eq_mul_inv] at hp hd ⊢
  constructor
  · nlinarith only [hp,hd]
  · rw [he4] at hstrong
    simp only [div_eq_mul_inv] at hstrong
    nlinarith only [hp,hd,hstrong,mul_nonneg hn.le hm]

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

/-- The full same-compression curvature, defect and forcing return to one generated positive joint word. -/
theorem actual_joint_scale_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    jointPrice m ell F z hz g=wholeForcingWord m ell F z hz g+
      4*z.im*(sourcePair (U (D (normalizedState m ell F z hz g))) (normalizedState m ell F z hz g)).im ∧
    (3*n/8)*‖embed (jointColumn m ell F z hz g)‖^2+
      8*n*shiftedMoment38 (normalizedState m ell F z hz g)+4*phiPositivePrice m ell F z hz g/n ≤
        jointPrice m ell F z hz g ∧
    combinedPressure (normalizedState m ell F z hz g) ≤ 2*jointPrice m ell F z hz g := by
  refine ⟨?_,joint_slots m ell F z hz g⟩
  have hH:H0=compressionCore F+defectAction F := by
    unfold defectAction
    change diagonalAction=compressionCore F+(diagonalAction-compressionCore F)
    module
  have hb:bracket A (bracket A H0)=bracket A (bracket A (compressionCore F))+
      bracket A (bracket A (defectAction F)) := by
    rw [hH,bracket_add,bracket_add]
  let w:=normalizedState m ell F z hz g
  have hc:=actual_weighted_current m ell F z hz g
  unfold jointPrice combinedPressure combinedPressureOperator wholeForcingWord
  change (sourcePair w ((bracket A (bracket A H0)+(2:ℂ) • (U*bracket D H0)+
    U*GaussMatterCore.matterAction+(9/8:ℂ) • (U*vacuumConstantAction)) w)).re+
      8*phiPositivePrice m ell F z hz g/n-2*coframeContact m ell F z hz g=_
  rw [hb]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,pair_add_r,pair_smul_r,
    Complex.add_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  rw [hc]
  ring

private theorem young(x y t:ℝ)(ht:0<t):x*y ≤ t*x^2+y^2/(4*t) := by
  have he:(4*t)*(y^2/(4*t))=y^2:=by field_simp
  nlinarith only [sq_nonneg (2*t*x-y),he,ht]
private theorem phase_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    |4*z.im*(sourcePair (U (D (normalizedState m ell F z hz g))) (normalizedState m ell F z hz g)).im| ≤
      η*jointPrice m ell F z hz g+64*z.im^2/(3*n*η)*‖embed (normalizedState m ell F z hz g)‖^2 := by
  let w:=normalizedState m ell F z hz g
  have hp:=(original_combined_pressure_source w).2
  have hj:=(joint_slots m ell F z hz g).2
  have hm:0 ≤ shiftedMoment38 w:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hn:=lapse_pos
  have hD:(3*n/16)*‖embed (U (D w))‖^2 ≤ jointPrice m ell F z hz g := by
    nlinarith only [hp,hj,mul_nonneg hn.le hm]
  have hi:|(sourcePair (U (D w)) w).im| ≤ ‖embed (U (D w))‖*‖embed w‖ := by
    exact (Complex.abs_im_le_norm _).trans (by unfold sourcePair;exact norm_inner_le_norm _ _)
  have ha:|4*z.im*(sourcePair (U (D w)) w).im| ≤ 4*|z.im| *‖embed (U (D w))‖*‖embed w‖ := by
    rw [abs_mul,abs_mul]
    norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    have ht:=mul_le_mul_of_nonneg_left hi (show 0 ≤ 4*|z.im| by positivity)
    nlinarith only [ht]
  have hy:=young ‖embed (U (D w))‖ (4*|z.im| *‖embed w‖) (η*3*n/16) (by positivity)
  have he:(4*|z.im| *‖embed w‖)^2/(4*(η*3*n/16))=64*z.im^2/(3*n*η)*‖embed w‖^2 := by
    rw [mul_pow,mul_pow,sq_abs]
    field_simp
    ring
  rw [he] at hy
  have hpay:=mul_le_mul_of_nonneg_left hD hη.le
  change |4*z.im*(sourcePair (U (D w)) w).im| ≤ η*jointPrice m ell F z hz g+
    64*z.im^2/(3*n*η)*‖embed w‖^2
  nlinarith only [ha,hy,hpay]
private theorem frequency_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(t:ℝ):
    (actualFrequency advanced μ t).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'

/-- Both causal signs pay the complete joint Noether phase by the same original normalized response tail. -/
theorem actual_joint_scale_phase_common_tail(μ:ℝ)(hμ:0<μ)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀advanced:Bool,(∫⁻t:ℝ,ENNReal.ofReal
        (|4*(actualFrequency advanced μ t).im*(sourcePair
          (U (D (normalizedState m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g)))
          (normalizedState m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g)).im|-
          η*jointPrice m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  let K:ℝ:=64*μ^2/(3*n*η)
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

end LowEnergy.SourceClockPhiJointScaleNoether
