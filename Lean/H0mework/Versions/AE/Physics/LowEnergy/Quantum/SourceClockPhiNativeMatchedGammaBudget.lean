import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiNativeMatchedSource
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusNormalizedFluxBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockRadiusAffineCutoff
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaQ8RadiusBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiNativeMatchedGammaBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiNormalizedScalarBudget
open SourceClockPhiCombinedScalePressure SourceClockPhiRadiusNormalizedFluxBudget
open SourceClockPhiNativeMatchedSource SourceClockReflectedForm
open SourceClockYukawaQ8RadiusBudget SourceClockYukawaRadialGammaNativeBudget
open SourceScalarPairedTransport SourceScalarVirialBulk SourceScalarGaugeScale
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceHamiltonianVolume
open SourceScalarDoubleCurrent SourceScalarInverseNativeEnergy SourceClockSourceTail SourceScalarPositiveBulkWard FullYSourceResolventGraphSplice
open SourcePhysicalKineticSquare SourceLocalizedInverseFormPayment SourceMixedNativeReturn SourceFourPoleEnergyClosed SourceResolventBandLimit
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
attribute [local irreducible] diagonalAction compressionCore defectAction resolventCore sourcePair embed sourceRead finiteResolvent

private theorem lapse_pos : 0<n := by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private def shiftedFieldCoordinate (c : ℝ) (i : ScalarIndex) (x : SourceCoordinateSlice) : ℝ :=
  inner ℝ (scalarField x-c • vacuum) (scalarBasis i)
private theorem shiftedFieldCoordinate_smooth (c : ℝ) (i : ScalarIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (shiftedFieldCoordinate c i) z.val := by
  unfold shiftedFieldCoordinate
  exact ((scalarField_smooth.sub contDiff_const).inner ℝ contDiff_const).contDiffAt
private def shiftedFieldColumn (c : ℝ) (i : ScalarIndex) : End :=
  multiply (shiftedFieldCoordinate c i) (shiftedFieldCoordinate_smooth c i)
private theorem shiftedFieldColumn_point (c : ℝ) (i : ScalarIndex) (f : QuantumTest)
    (x : SourceCoordinateSlice) :
    shiftedFieldColumn c i f x=(shiftedFieldCoordinate c i x : ℂ) • f x := rfl
private theorem shifted40_column (i : ScalarIndex) :
    shiftedColumn40 i=shiftedFieldColumn (2/5) i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change (shiftedCoordinate i x : ℂ) • f x+
    ((inner ℝ vacuum (scalarBasis i)/10 : ℝ) : ℂ) • f x =
    (shiftedFieldCoordinate (2/5) i x : ℂ) • f x
  rw [←add_smul,←Complex.ofReal_add]
  congr 2
  unfold shiftedCoordinate shiftedFieldCoordinate
  simp only [inner_sub_left,real_inner_smul_left]
  ring

private theorem phi_square (x : SourceCoordinateSlice) :
    (phiRadius x)^2=1+‖scalarField x‖^2/4 := by
  change (Real.sqrt (1+‖scalarField x‖^2/4))^2=1+‖scalarField x‖^2/4
  exact Real.sq_sqrt (by positivity)

private theorem radius_completion : r*r=
    ((1+2*‖vacuum‖^2/25 : ℝ) : ℂ) • (1:End)+
      (1/2:ℂ) • (∑ i:ScalarIndex,shiftedColumn40 i*shiftedColumn40 i)-
      (1/4:ℂ) • (∑ i:ScalarIndex,
        shiftedFieldColumn (4/5) i*shiftedFieldColumn (4/5) i) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  have hs:(∑ i:ScalarIndex,(shiftedFieldCoordinate (2/5) i x)^2)=
      ‖scalarField x-(2/5:ℝ) • vacuum‖^2 := scalarBasis.sum_sq_inner_left _
  have hq:(∑ i:ScalarIndex,(shiftedFieldCoordinate (4/5) i x)^2)=
      ‖scalarField x-(4/5:ℝ) • vacuum‖^2 := scalarBasis.sum_sq_inner_left _
  have hr:(phiRadius x)^2=1+2*‖vacuum‖^2/25+
      (1/2:ℝ)*(∑ i:ScalarIndex,(shiftedFieldCoordinate (2/5) i x)^2)-
      (1/4:ℝ)*(∑ i:ScalarIndex,(shiftedFieldCoordinate (4/5) i x)^2) := by
    rw [phi_square,hs,hq]
    simp only [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs]
    norm_num
    ring
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    LinearMap.sum_apply,Module.End.mul_apply]
  change (phiRadius x:ℂ) • ((phiRadius x:ℂ) • f x)=
    ((1+2*‖vacuum‖^2/25:ℝ):ℂ) • f x+(1/2:ℂ) •
      ((∑ i:ScalarIndex,shiftedColumn40 i (shiftedColumn40 i f)) x)-
      (1/4:ℂ) • ((∑ i:ScalarIndex,shiftedFieldColumn (4/5) i
        (shiftedFieldColumn (4/5) i f)) x)
  simp only [shifted40_column]
  rw [sum_apply,sum_apply]
  change (phiRadius x:ℂ) • ((phiRadius x:ℂ) • f x)=
    ((1+2*‖vacuum‖^2/25:ℝ):ℂ) • f x+(1/2:ℂ) •
      (∑ i:ScalarIndex,(shiftedFieldCoordinate (2/5) i x:ℂ) •
        ((shiftedFieldCoordinate (2/5) i x:ℂ) • f x))-
      (1/4:ℂ) • (∑ i:ScalarIndex,(shiftedFieldCoordinate (4/5) i x:ℂ) •
        ((shiftedFieldCoordinate (4/5) i x:ℂ) • f x))
  simp only [smul_smul,←pow_two,←Finset.sum_smul,←Complex.ofReal_pow,←Complex.ofReal_sum,
    ←Complex.ofReal_ofNat,←Complex.ofReal_one,←Complex.ofReal_div,←Complex.ofReal_mul]
  rw [←add_smul,←sub_smul,←Complex.ofReal_add,←Complex.ofReal_sub,hr]

private theorem self_pair (f : QuantumTest) :
    sourcePair f f=((‖embed f‖^2:ℝ):ℂ) := by
  simpa only [sourcePair,Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (embed f)
private theorem pair_add_r (f g h : QuantumTest) :
    sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r (f g h : QuantumTest) :
    sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r (c:ℂ)(f g:QuantumTest) :
    sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_sum_r {ι:Type*}[Fintype ι](f:QuantumTest)(g:ι → QuantumTest) :
    sourcePair f (∑i,g i)=∑i,sourcePair f (g i) := by
  simp only [sourcePair,map_sum,inner_sum]

private theorem radius_square_pair (f : QuantumTest) :
    ‖embed (r f)‖^2=(1+2*‖vacuum‖^2/25)*‖embed f‖^2+
      (1/2:ℝ)*shiftedMoment40 f-
      (1/4:ℝ)*(∑ i:ScalarIndex,‖embed (shiftedFieldColumn (4/5) i f)‖^2) := by
  have hp:=congrArg (fun A:End=>sourcePair f (A f)) radius_completion
  have hr:sourcePair f ((r*r) f)=sourcePair (r f) (r f) := multiply_pair _ _ _ _
  have hs (i:ScalarIndex):sourcePair f ((shiftedColumn40 i*shiftedColumn40 i) f)=
      sourcePair (shiftedColumn40 i f) (shiftedColumn40 i f) := by
    rw [shifted40_column]
    exact multiply_pair _ _ _ _
  have hq (i:ScalarIndex):sourcePair f ((shiftedFieldColumn (4/5) i*
      shiftedFieldColumn (4/5) i) f)=
      sourcePair (shiftedFieldColumn (4/5) i f) (shiftedFieldColumn (4/5) i f) :=
    multiply_pair _ _ _ _
  rw [hr] at hp
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    Module.End.one_apply,pair_add_r,pair_sub_r,pair_smul_r] at hp
  rw [pair_sum_r,pair_sum_r] at hp
  simp_rw [hs,hq,self_pair] at hp
  have hre:=congrArg Complex.re hp
  norm_num only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.div_re,Complex.div_im,Complex.normSq_apply,Complex.re_ofNat,Complex.im_ofNat,
    Complex.one_re,Complex.one_im,Complex.re_sum,Complex.im_sum,
    mul_zero,zero_mul,sub_zero,add_zero] at hre
  change ‖embed (r f)‖^2=(1+2*‖vacuum‖^2/25)*‖embed f‖^2+
    (1/2:ℝ)*shiftedMoment40 f-
    (1/4:ℝ)*(∑ i:ScalarIndex,‖embed (shiftedFieldColumn (4/5) i f)‖^2) at hre
  exact hre

private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
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
private theorem normalized_radius (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    r (normalizedState m ell F z hz g)=phiResponseCore m ell F z hz g := by
  rw [normalized_return]
  exact LinearMap.congr_fun radius_inverse _
private theorem frequency_nonreal (advanced:Bool)(μ t:ℝ)(hμ:0<μ):
    (actualFrequency advanced μ t).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'

private theorem radius_shifted_norm(f:QuantumTest):
    ‖embed (r f)‖^2 ≤ (1+2*‖vacuum‖^2/25)*‖embed f‖^2+(1/2:ℝ)*shiftedMoment40 f := by
  have h:=radius_square_pair f
  have hq:0 ≤ ∑i:ScalarIndex,‖embed (shiftedFieldColumn (4/5) i f)‖^2:=
    Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  linarith only [h,hq]

/-- The actual shift40 floor pays the original radius response from its own matched source price. -/
theorem actual_original_native_matched_radius_budget(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    ‖embed (phiResponseCore m ell F z hz g)‖^2 ≤
      (1+2*‖vacuum‖^2/25)*‖embed (normalizedState m ell F z hz g)‖^2+
      matchedPrice m ell F z hz g/(20*n) := by
  let w:=normalizedState m ell F z hz g
  have hs:0 ≤ scalarForm (inverseVolumeAction w):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hc:=original_coframe_gram_nonnegative (inverseVolumeAction w)
  have hn:=lapse_pos
  have hj:=(actual_native_matched_source m ell F z hz g).2.2.1
  change (3*n/8)*‖embed (matchedColumn w)‖^2+(5*n/2)*scalarForm (inverseVolumeAction w)+
    10*n*shiftedMoment40 w+(3*n/4)*coframeGram (inverseVolumeAction w)+18*n*‖embed w‖^2 ≤
    matchedPrice m ell F z hz g at hj
  have hfloor:10*n*shiftedMoment40 w ≤ matchedPrice m ell F z hz g := by
    nlinarith only [hj,mul_nonneg (by positivity : 0 ≤ 3*n/8) (sq_nonneg ‖embed (matchedColumn w)‖),
      mul_nonneg (by positivity : 0 ≤ 5*n/2) hs,mul_nonneg (by positivity : 0 ≤ 3*n/4) hc,
      mul_nonneg (by positivity : 0 ≤ 18*n) (sq_nonneg ‖embed w‖)]
  have hp:(1/2:ℝ)*shiftedMoment40 w ≤ matchedPrice m ell F z hz g/(20*n) := by
    apply (le_div_iff₀ (by positivity : 0<20*n)).mpr
    nlinarith only [hfloor]
  have hr:=radius_shifted_norm w
  rw [normalized_radius] at hr
  exact hr.trans (add_le_add le_rfl hp)

/-- The literal complete matched forcing word, clipped once on the original retarded source line. -/
def matchedBudget(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):ENNReal:=
  ∫⁻t:ℝ,ENNReal.ofReal (matchedForcingWord m ell F (line μ t)
    (by simpa only [line_im] using hμ.ne') g)
private def matchedErrorBudget(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):ENNReal:=
  ∫⁻t:ℝ,ENNReal.ofReal (matchedPrice m ell F (line μ t)
    (by simpa only [line_im] using hμ.ne') g-2*matchedForcingWord m ell F (line μ t)
    (by simpa only [line_im] using hμ.ne') g)
private def pressureFactor(μ:ℝ):ℝ:=μ/(20*n)
private def normFactor(μ:ℝ):ℝ:=μ*(1+2*‖vacuum‖^2/25)
private theorem factor_nonnegative(μ:ℝ)(hμ:0<μ):0 ≤ pressureFactor μ := by
  unfold pressureFactor;have hn:=lapse_pos;positivity
private theorem norm_factor_nonnegative(μ:ℝ)(hμ:0<μ):0 ≤ normFactor μ := by
  unfold normFactor;positivity
private theorem finite_star (F:Index)(z:ℂ):finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced:Bool)(F:Index)(μ:ℝ)(hμ:0<μ):
    Continuous (fun t:ℝ=>finiteResolvent F (actualFrequency advanced μ t)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have he:(fun t:ℝ=>finiteResolvent F (actualFrequency true μ t))=
        (fun t:ℝ=>(finiteResolvent F (line μ t)).adjoint) := by
      funext t;exact finite_star F _
    exact he ▸ (ContinuousLinearMap.adjoint.continuous.comp
      (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F))
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
private theorem normalized_measurable (m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)
    (g:diagonal.domain)(advanced:Bool):
    Measurable (fun t:ℝ=>ENNReal.ofReal (‖embed (normalizedState m ell F
      (actualFrequency advanced μ t) (frequency_nonreal advanced μ t hμ) g)‖^2)) := by
  simp_rw [normalized_read]
  have hg:Continuous (fun t:ℝ=>finiteResolvent F (actualFrequency advanced μ t) (g:H)) :=
    (frequency_continuous advanced F μ hμ).clm_apply continuous_const
  have hh:Continuous (fun t:ℝ=>finiteResolvent F (actualFrequency advanced μ t) (phiRadiusSource g:H)) :=
    (frequency_continuous advanced F μ hμ).clm_apply continuous_const
  exact ((((sourceRead F g (T m ell)).continuous.comp hg).sub
    ((sourceRead F (phiRadiusSource g) (S*T m ell)).continuous.comp hh)).norm.pow 2).measurable.ennreal_ofReal
private theorem source_action_read(A:End)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    embed (A (resolventCore F z hz (coreEquiv.symm g)))=
      sourceRead F g A (finiteResolvent F z (g:H)) := by
  simpa only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply,
    SourceScalarPositiveBulkWard.state] using! (source_read_resolvent F g A z hz).symm
private theorem source_action_continuous(A:End)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>embed (A (resolventCore F (line μ t) (by simpa only [line_im] using hμ.ne') (coreEquiv.symm g)))) := by
  simp_rw [source_action_read]
  exact (sourceRead F g A).continuous.comp
    ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const)
private theorem normalized_action_continuous(A:End)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>embed (A (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g))) := by
  have hh:r (coreEquiv.symm g)=coreEquiv.symm (phiRadiusSource g):=
    (coreEquiv.symm_apply_apply _).symm
  unfold normalizedState
  simp only [map_sub,hh]
  exact (source_action_continuous (A*T m ell) F μ hμ g).sub
    (source_action_continuous (A*(S*T m ell)) F μ hμ (phiRadiusSource g))
private theorem normalized_pair_continuous(A B:End)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>sourcePair (A (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g))
      (B (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g))) := by
  unfold sourcePair
  exact (normalized_action_continuous A m ell F μ hμ g).inner (𝕜:=ℂ)
    (normalized_action_continuous B m ell F μ hμ g)
private theorem forcing_continuous(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>embed (normalizedForcing m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g)) := by
  have hh:r (coreEquiv.symm g)=coreEquiv.symm (phiRadiusSource g):=
    (coreEquiv.symm_apply_apply _).symm
  unfold normalizedForcing
  simp only [map_sub,map_add,hh]
  exact (((source_action_continuous (bracket diagonalAction (T m ell)) F μ hμ g).sub
    (source_action_continuous (bracket diagonalAction (S*T m ell)) F μ hμ (phiRadiusSource g))).add
    (source_action_continuous (T m ell*defectAction F) F μ hμ g)).sub
    (source_action_continuous (S*T m ell*defectAction F) F μ hμ (phiRadiusSource g))
private theorem spin_continuous(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>spinForm (inverseVolumeAction (normalizedState m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g))) := by
  unfold spinForm
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((normalized_action_continuous (GaussCoframeSpin.current i*inverseVolumeAction)
    m ell F μ hμ g).norm.pow 2)
private theorem density_continuous(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>densityForm (inverseVolumeAction (normalizedState m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g))) := by
  unfold densityForm numberForm
  exact ((continuous_const.mul ((normalized_action_continuous (GaussCoframeForm.number*inverseVolumeAction)
    m ell F μ hμ g).norm.pow 2)).add
    (continuous_const.mul (Complex.continuous_re.comp (normalized_pair_continuous inverseVolumeAction
      (GaussCoframeForm.number*inverseVolumeAction) m ell F μ hμ g)))).add
    (continuous_const.mul ((normalized_action_continuous inverseVolumeAction m ell F μ hμ g).norm.pow 2))
private theorem gauge_continuous(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>gaugeForm (inverseVolumeAction (normalizedState m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g))) := by
  unfold gaugeForm
  apply Continuous.const_mul
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  simp only [←Module.End.mul_apply]
  exact normalized_pair_continuous _ _ m ell F μ hμ g
private theorem spatial_continuous(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>spatialForm (inverseVolumeAction (normalizedState m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g))) := by
  unfold spatialForm
  apply Complex.continuous_re.comp
  simp only [←Module.End.mul_apply]
  exact normalized_pair_continuous _ _ m ell F μ hμ g
private theorem matched_word_measurable(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Measurable (fun t:ℝ=>ENNReal.ofReal (matchedForcingWord m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g)) := by
  have hb:Continuous (fun t:ℝ=>(sourcePair (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)
      ((bracket combinedConjugate (bracket combinedConjugate (compressionCore F))+
        bracket combinedConjugate (bracket combinedConjugate (defectAction F))+
        (2:ℂ) • (inverseVolumeAction*GaussMatterCore.matterAction)+
        (8/5:ℂ) • (inverseVolumeAction*SourceScalarVirialBulk.vacuumConstantAction))
        (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g))).re) :=
    Complex.continuous_re.comp (normalized_pair_continuous 1 _ m ell F μ hμ g)
  have hf:Continuous (fun t:ℝ=>(sourcePair (normalizedForcing m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)
      (matchedTester (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g))).re) := by
    unfold sourcePair
    exact Complex.continuous_re.comp ((forcing_continuous m ell F μ hμ g).inner (𝕜:=ℂ)
      (normalized_action_continuous matchedTester m ell F μ hμ g))
  have hu:Continuous (fun t:ℝ=>(sourcePair (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)
      (inverseVolumeAction (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g))).re) :=
    Complex.continuous_re.comp (normalized_pair_continuous 1 inverseVolumeAction m ell F μ hμ g)
  have hre(t:ℝ):(line μ t).re=t := by simp [line]
  have hw:Continuous (fun t:ℝ=>matchedForcingWord m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g) := by
    unfold matchedForcingWord
    simp only [hre]
    exact (((((hb.sub (continuous_const.mul hf)).add
      ((continuous_const.mul continuous_id).mul hu)).add
      (continuous_const.mul (spin_continuous m ell F μ hμ g))).add
      (continuous_const.mul (density_continuous m ell F μ hμ g))).sub
      (continuous_const.mul (gauge_continuous m ell F μ hμ g))).sub
      (continuous_const.mul (spatial_continuous m ell F μ hμ g))
  exact hw.measurable.ennreal_ofReal

private theorem integrated_matched_price(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    phiResponseBudget m ell F μ hμ g ≤
      ENNReal.ofReal (normFactor μ)*(∫⁻t:ℝ,ENNReal.ofReal (‖embed (normalizedState m ell F (line μ t)
        (by simpa only [line_im] using hμ.ne') g)‖^2))+
      ENNReal.ofReal (pressureFactor μ)*(2*matchedBudget m ell F μ hμ g+matchedErrorBudget m ell F μ hμ g) := by
  have hm:=normalized_measurable m ell F μ hμ g false
  change Measurable (fun t:ℝ=>ENNReal.ofReal (‖embed (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)‖^2)) at hm
  unfold phiResponseBudget matchedBudget matchedErrorBudget
  calc
    _ ≤ ∫⁻t:ℝ,ENNReal.ofReal (normFactor μ)*ENNReal.ofReal (‖embed (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)‖^2)+
        ENNReal.ofReal (pressureFactor μ)*(2*ENNReal.ofReal (matchedForcingWord m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)+
          ENNReal.ofReal (matchedPrice m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g-2*matchedForcingWord m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)) := by
      apply lintegral_mono
      intro t
      have hr:=mul_le_mul_of_nonneg_left (actual_original_native_matched_radius_budget m ell F
        (line μ t) (by simpa only [line_im] using hμ.ne') g) hμ.le
      have hpoint:μ*‖embed (phiResponseCore m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)‖^2 ≤
        normFactor μ*‖embed (normalizedState m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)‖^2+
        pressureFactor μ*(2*matchedForcingWord m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g+
          (matchedPrice m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g-2*matchedForcingWord m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)) :=
        hr.trans_eq (by unfold normFactor pressureFactor;ring)
      have hw:ENNReal.ofReal (2*matchedForcingWord m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g)=
        (2:ENNReal)*ENNReal.ofReal (matchedForcingWord m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          norm_num
      exact (ENNReal.ofReal_le_ofReal hpoint).trans
        (ENNReal.ofReal_add_le.trans (add_le_add
          (le_of_eq (ENNReal.ofReal_mul (norm_factor_nonnegative μ hμ)))
          ((le_of_eq (ENNReal.ofReal_mul (factor_nonnegative μ hμ))).trans
            (mul_le_mul_of_nonneg_left (by rw [←hw];exact ENNReal.ofReal_add_le) zero_le))))
    _=_ := by
      rw [lintegral_add_left (hm.const_mul _),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left ((matched_word_measurable m ell F μ hμ g).const_mul 2),
        lintegral_const_mul' _ _ (by norm_num : (2:ENNReal)≠⊤)]
private theorem matched_common_payment(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠF in (sourceFilter:Filter Index),
      phiResponseBudget m ell F μ hμ g ≤ ENNReal.ofReal ε+
        ENNReal.ofReal (2*pressureFactor μ)*matchedBudget m ell F μ hμ g := by
  intro ε hε
  have hnf:=norm_factor_nonnegative μ hμ
  have hpf:=factor_nonnegative μ hμ
  let δ:=ε/(normFactor μ+pressureFactor μ+1)
  have hd:0<δ := by dsimp [δ];positivity
  obtain ⟨N1,h1⟩:=actual_normalized_response_common_tail μ hμ g δ hd
  obtain ⟨N2,h2⟩:=actual_native_matched_common_payment μ hμ g δ hd
  refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hn hp
  have hn0:=hn false
  change (∫⁻t:ℝ,ENNReal.ofReal (‖embed (S (phiResponseCore m ell F (line μ t) (by simpa only [line_im] using hμ.ne') g))‖^2)) ≤ ENNReal.ofReal δ at hn0
  simp_rw [←normalized_return] at hn0
  have hp0:=hp false
  change matchedErrorBudget m ell F μ hμ g ≤ ENNReal.ofReal δ at hp0
  have hb:=(integrated_matched_price m ell F μ hμ g).trans
    (add_le_add (mul_le_mul le_rfl hn0 zero_le zero_le)
      (mul_le_mul le_rfl (add_le_add le_rfl hp0) zero_le zero_le))
  have halloc:(normFactor μ+pressureFactor μ)*δ ≤ ε := by
    dsimp only [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<normFactor μ+pressureFactor μ+1)).mpr
    nlinarith only [hε]
  calc
    _ ≤ ENNReal.ofReal (normFactor μ)*ENNReal.ofReal δ+
        ENNReal.ofReal (pressureFactor μ)*(2*matchedBudget m ell F μ hμ g+ENNReal.ofReal δ) := hb
    _=ENNReal.ofReal ((normFactor μ+pressureFactor μ)*δ)+
        ENNReal.ofReal (2*pressureFactor μ)*matchedBudget m ell F μ hμ g := by
      rw [mul_add,←mul_assoc,show (2:ENNReal)=ENNReal.ofReal (2:ℝ) by norm_num,
        ←ENNReal.ofReal_mul hpf,←ENNReal.ofReal_mul hnf,←ENNReal.ofReal_mul hpf]
      rw [add_comm (ENNReal.ofReal (pressureFactor μ*2)*matchedBudget m ell F μ hμ g)
        (ENNReal.ofReal (pressureFactor μ*δ)),←add_assoc,
        ←ENNReal.ofReal_add (mul_nonneg hnf hd.le) (mul_nonneg hpf hd.le)]
      rw [show normFactor μ*δ+pressureFactor μ*δ=(normFactor μ+pressureFactor μ)*δ by ring,
        show pressureFactor μ*2=2*pressureFactor μ by ring]
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal halloc) le_rfl
/-- Every original sharp Gamma sink consumes the literal complete matched word, with ordinary norm and joint-phase tails paid internally at one N and F. -/
theorem actual_original_native_matched_Gamma_budget (μ:ℝ)(hμ:0<μ)(g k:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠF in (sourceFilter:Filter Index),∀sharp:Bool,
      ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤ ENNReal.ofReal ε+
        ENNReal.ofReal (48*sourceMuFactor μ k*radiusPrice*(μ/(20*n)))*
          matchedBudget m ell F μ hμ g := by
  intro ε hε
  let C:=6*sourceMuFactor μ k*radiusPrice
  have hC:0 ≤ C := by dsimp [C];unfold sourceMuFactor radiusPrice;positivity
  let δ:=ε/(10*(C+1))
  have hd:0<δ := by dsimp [δ];positivity
  obtain ⟨N1,h1⟩:=actual_original_Q8_radius_response_budget μ hμ g k (ε/2) (by positivity)
  obtain ⟨N2,h2⟩:=actual_original_radius_homogeneous_budget μ hμ g δ hd
  obtain ⟨N3,h3⟩:=matched_common_payment μ hμ g δ hd
  refine ⟨max N1 (max N2 N3),fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml,h3 m (by omega) ell hml] with F hg hr hp
  intro sharp
  have hp0:=hp
  change phiResponseBudget m ell F μ hμ g ≤ ENNReal.ofReal δ+
    ENNReal.ofReal (2*pressureFactor μ)*matchedBudget m ell F μ hμ g at hp0
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
  have hcoef:ENNReal.ofReal C*4*ENNReal.ofReal (2*pressureFactor μ)=
      ENNReal.ofReal (48*sourceMuFactor μ k*radiusPrice*(μ/(20*n))) := by
    rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num,
      ←ENNReal.ofReal_mul hC,←ENNReal.ofReal_mul (mul_nonneg hC (by norm_num))]
    congr 1;unfold pressureFactor;dsimp only [C];ring
  change _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal (5*δ)+
    4*(ENNReal.ofReal (2*pressureFactor μ)*matchedBudget m ell F μ hμ g)) at hb
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal (5*δ)+
      4*(ENNReal.ofReal (2*pressureFactor μ)*matchedBudget m ell F μ hμ g)) := hb
    _=ENNReal.ofReal (ε/2+C*(5*δ))+
      ENNReal.ofReal (48*sourceMuFactor μ k*radiusPrice*(μ/(20*n)))*
        matchedBudget m ell F μ hμ g := by
      rw [mul_add,←mul_assoc,←mul_assoc,hcoef,←ENNReal.ofReal_mul hC,←add_assoc,
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal halloc) le_rfl

end LowEnergy.SourceClockPhiNativeMatchedGammaBudget
