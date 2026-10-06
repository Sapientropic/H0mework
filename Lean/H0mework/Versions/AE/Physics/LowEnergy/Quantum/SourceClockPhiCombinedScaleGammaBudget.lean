import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiCombinedScalePressure
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusNormalizedFluxBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockRadiusAffineCutoff
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaQ8RadiusBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiCombinedScaleGammaBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiNormalizedScalarBudget
open SourceClockPhiCombinedScalePressure SourceClockPhiRadiusNormalizedFluxBudget
open SourceClockYukawaQ8RadiusBudget SourceClockYukawaRadialGammaNativeBudget
open SourceScalarPairedTransport SourceScalarVirialBulk SourceScalarGaugeScale
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceHamiltonianVolume
open SourceScalarInverseNativeEnergy SourceClockSourceTail SourceScalarPositiveBulkWard FullYSourceResolventGraphSplice
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
private theorem shifted38_column (i : ScalarIndex) :
    shiftedColumn38 i=shiftedFieldColumn (3/8) i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change (shiftedCoordinate i x : ℂ) • f x+
    ((inner ℝ vacuum (scalarBasis i)/8 : ℝ) : ℂ) • f x =
    (shiftedFieldCoordinate (3/8) i x : ℂ) • f x
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
    ((1+9*‖vacuum‖^2/128 : ℝ) : ℂ) • (1:End)+
      (1/2:ℂ) • (∑ i:ScalarIndex,shiftedColumn38 i*shiftedColumn38 i)-
      (1/4:ℂ) • (∑ i:ScalarIndex,
        shiftedFieldColumn (3/4) i*shiftedFieldColumn (3/4) i) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  have hs:(∑ i:ScalarIndex,(shiftedFieldCoordinate (3/8) i x)^2)=
      ‖scalarField x-(3/8:ℝ) • vacuum‖^2 := scalarBasis.sum_sq_inner_left _
  have hq:(∑ i:ScalarIndex,(shiftedFieldCoordinate (3/4) i x)^2)=
      ‖scalarField x-(3/4:ℝ) • vacuum‖^2 := scalarBasis.sum_sq_inner_left _
  have hr:(phiRadius x)^2=1+9*‖vacuum‖^2/128+
      (1/2:ℝ)*(∑ i:ScalarIndex,(shiftedFieldCoordinate (3/8) i x)^2)-
      (1/4:ℝ)*(∑ i:ScalarIndex,(shiftedFieldCoordinate (3/4) i x)^2) := by
    rw [phi_square,hs,hq]
    simp only [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs]
    norm_num
    ring
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    LinearMap.sum_apply,Module.End.mul_apply]
  change (phiRadius x:ℂ) • ((phiRadius x:ℂ) • f x)=
    ((1+9*‖vacuum‖^2/128:ℝ):ℂ) • f x+(1/2:ℂ) •
      ((∑ i:ScalarIndex,shiftedColumn38 i (shiftedColumn38 i f)) x)-
      (1/4:ℂ) • ((∑ i:ScalarIndex,shiftedFieldColumn (3/4) i
        (shiftedFieldColumn (3/4) i f)) x)
  simp only [shifted38_column]
  rw [sum_apply,sum_apply]
  change (phiRadius x:ℂ) • ((phiRadius x:ℂ) • f x)=
    ((1+9*‖vacuum‖^2/128:ℝ):ℂ) • f x+(1/2:ℂ) •
      (∑ i:ScalarIndex,(shiftedFieldCoordinate (3/8) i x:ℂ) •
        ((shiftedFieldCoordinate (3/8) i x:ℂ) • f x))-
      (1/4:ℂ) • (∑ i:ScalarIndex,(shiftedFieldCoordinate (3/4) i x:ℂ) •
        ((shiftedFieldCoordinate (3/4) i x:ℂ) • f x))
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
    ‖embed (r f)‖^2=(1+9*‖vacuum‖^2/128)*‖embed f‖^2+
      (1/2:ℝ)*shiftedMoment38 f-
      (1/4:ℝ)*(∑ i:ScalarIndex,‖embed (shiftedFieldColumn (3/4) i f)‖^2) := by
  have hp:=congrArg (fun A:End=>sourcePair f (A f)) radius_completion
  have hr:sourcePair f ((r*r) f)=sourcePair (r f) (r f) := multiply_pair _ _ _ _
  have hs (i:ScalarIndex):sourcePair f ((shiftedColumn38 i*shiftedColumn38 i) f)=
      sourcePair (shiftedColumn38 i f) (shiftedColumn38 i f) := by
    rw [shifted38_column]
    exact multiply_pair _ _ _ _
  have hq (i:ScalarIndex):sourcePair f ((shiftedFieldColumn (3/4) i*
      shiftedFieldColumn (3/4) i) f)=
      sourcePair (shiftedFieldColumn (3/4) i f) (shiftedFieldColumn (3/4) i f) :=
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
  change ‖embed (r f)‖^2=(1+9*‖vacuum‖^2/128)*‖embed f‖^2+
    (1/2:ℝ)*shiftedMoment38 f-
    (1/4:ℝ)*(∑ i:ScalarIndex,‖embed (shiftedFieldColumn (3/4) i f)‖^2) at hre
  exact hre

/-- The full source pressure pays the original radius point cost with no mass-gap denominator. -/
theorem original_combined_radius_pressure (f : QuantumTest) :
    ‖embed (r f)‖^2 ≤ (1+9*‖vacuum‖^2/128)*‖embed f‖^2+
      combinedPressure f/(16*n) := by
  have hr:=radius_square_pair f
  have hq:0≤∑ i:ScalarIndex,‖embed (shiftedFieldColumn (3/4) i f)‖^2 :=
    Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hp:= (original_combined_pressure_source f).2
  have hn:=lapse_pos
  have hnon:0 ≤ (3*n/8)*‖embed (inverseVolumeAction (combinedGenerator f))‖^2 := by positivity
  change (3*n/8)*‖embed (inverseVolumeAction (combinedGenerator f))‖^2+
    8*n*shiftedMoment38 f ≤ combinedPressure f at hp
  have hfloor:8*n*shiftedMoment38 f ≤ combinedPressure f := by linarith only [hp,hnon]
  have he:(1/2:ℝ)*shiftedMoment38 f ≤ combinedPressure f/(16*n) := by
    apply (le_div_iff₀ (by positivity : 0<16*n)).mpr
    nlinarith only [hfloor]
  linarith only [hr,hq,he]

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

/-- The complete combined pressure of the original two-seed normalized response. -/
def combinedPressureBudget (m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain)
    (advanced:Bool):ENNReal :=
  ∫⁻ t:ℝ,ENNReal.ofReal (combinedPressure (normalizedState m ell F
    (actualFrequency advanced μ t) (frequency_nonreal advanced μ t hμ) g))
private def pressureFactor (μ:ℝ):ℝ := μ/(16*n)
private def normFactor (μ:ℝ):ℝ := μ*(1+9*‖vacuum‖^2/128)
private theorem factor_nonnegative (μ:ℝ)(hμ:0<μ):0 ≤ pressureFactor μ := by
  unfold pressureFactor;have hn:=lapse_pos;positivity
private theorem norm_factor_nonnegative (μ:ℝ)(hμ:0<μ):0 ≤ normFactor μ := by
  unfold normFactor;positivity
private theorem response_price (m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)
    (g:diagonal.domain)(advanced:Bool)(t:ℝ):
    μ*‖embed (phiResponseCore m ell F (actualFrequency advanced μ t)
      (frequency_nonreal advanced μ t hμ) g)‖^2 ≤
    pressureFactor μ*combinedPressure (normalizedState m ell F (actualFrequency advanced μ t)
      (frequency_nonreal advanced μ t hμ) g)+
    normFactor μ*‖embed (normalizedState m ell F (actualFrequency advanced μ t)
      (frequency_nonreal advanced μ t hμ) g)‖^2 := by
  have h:=original_combined_radius_pressure (normalizedState m ell F (actualFrequency advanced μ t)
    (frequency_nonreal advanced μ t hμ) g)
  rw [normalized_radius] at h
  exact (mul_le_mul_of_nonneg_left h hμ.le).trans_eq (by
    unfold pressureFactor normFactor
    ring)
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
private def responseIntegral (m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)
    (g:diagonal.domain)(advanced:Bool):ENNReal :=
  ∫⁻ t:ℝ,ENNReal.ofReal (μ*‖embed (phiResponseCore m ell F (actualFrequency advanced μ t)
    (frequency_nonreal advanced μ t hμ) g)‖^2)
private theorem integrated_price (m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)
    (g:diagonal.domain)(advanced:Bool):
    responseIntegral m ell F μ hμ g advanced ≤
    ENNReal.ofReal (pressureFactor μ)*combinedPressureBudget m ell F μ hμ g advanced+
    ENNReal.ofReal (normFactor μ)*(∫⁻ t:ℝ,ENNReal.ofReal (‖embed (normalizedState m ell F
      (actualFrequency advanced μ t) (frequency_nonreal advanced μ t hμ) g)‖^2)) := by
  unfold responseIntegral combinedPressureBudget
  calc
    _ ≤ ∫⁻t:ℝ,ENNReal.ofReal (pressureFactor μ)*ENNReal.ofReal (combinedPressure (normalizedState m ell F
        (actualFrequency advanced μ t) (frequency_nonreal advanced μ t hμ) g))+
      ENNReal.ofReal (normFactor μ)*ENNReal.ofReal (‖embed (normalizedState m ell F
        (actualFrequency advanced μ t) (frequency_nonreal advanced μ t hμ) g)‖^2) := by
      apply lintegral_mono;intro t
      exact (ENNReal.ofReal_le_ofReal (response_price m ell F μ hμ g advanced t)).trans
        (ENNReal.ofReal_add_le.trans (add_le_add
          (le_of_eq (ENNReal.ofReal_mul (factor_nonnegative μ hμ)))
          (le_of_eq (ENNReal.ofReal_mul (norm_factor_nonnegative μ hμ)))))
    _=_ := by
      rw [lintegral_add_right _ ((normalized_measurable m ell F μ hμ g advanced).const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
private theorem normalized_common_payment (μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      responseIntegral m ell F μ hμ g advanced ≤ ENNReal.ofReal ε+
        ENNReal.ofReal (pressureFactor μ)*combinedPressureBudget m ell F μ hμ g advanced := by
  intro ε hε
  let δ:=ε/(normFactor μ+1)
  have hn:=norm_factor_nonnegative μ hμ
  have hd:0<δ := by dsimp [δ];positivity
  obtain ⟨N,hN⟩:=actual_normalized_response_common_tail μ hμ g δ hd
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have ht:=hF advanced
  change (∫⁻t:ℝ,ENNReal.ofReal (‖embed (S (phiResponseCore m ell F
    (actualFrequency advanced μ t) _ g))‖^2)) ≤ ENNReal.ofReal δ at ht
  simp_rw [←normalized_return] at ht
  have hb:=(integrated_price m ell F μ hμ g advanced).trans
    (add_le_add le_rfl (mul_le_mul le_rfl ht zero_le zero_le))
  have ha:normFactor μ*δ ≤ ε := by
    dsimp only [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<normFactor μ+1)).mpr
    nlinarith only [hε]
  rw [←ENNReal.ofReal_mul hn] at hb
  exact hb.trans ((add_le_add le_rfl (ENNReal.ofReal_le_ofReal ha)).trans_eq (add_comm _ _))

/-- Original Gamma consumes the complete combined pressure at any positive source-line frequency,
with the two fixed-input normalized norm tails paid internally at the same N and F. -/
theorem actual_original_combined_pressure_Gamma_budget (μ:ℝ)(hμ:0<μ)(g k:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠF in (sourceFilter:Filter Index),∀sharp:Bool,
      ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤ ENNReal.ofReal ε+
        ENNReal.ofReal (24*sourceMuFactor μ k*radiusPrice*(μ/(16*n)))*
          combinedPressureBudget m ell F μ hμ g false := by
  intro ε hε
  let C:=6*sourceMuFactor μ k*radiusPrice
  have hC:0 ≤ C := by dsimp [C];unfold sourceMuFactor radiusPrice;positivity
  let δ:=ε/(10*(C+1))
  have hd:0<δ := by dsimp [δ];positivity
  obtain ⟨N1,h1⟩:=actual_original_Q8_radius_response_budget μ hμ g k (ε/2) (by positivity)
  obtain ⟨N2,h2⟩:=actual_original_radius_homogeneous_budget μ hμ g δ hd
  obtain ⟨N3,h3⟩:=normalized_common_payment μ hμ g δ hd
  refine ⟨max N1 (max N2 N3),fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml,h3 m (by omega) ell hml] with F hg hr hp
  intro sharp
  have hp0:=hp false
  change phiResponseBudget m ell F μ hμ g ≤ ENNReal.ofReal δ+
    ENNReal.ofReal (pressureFactor μ)*combinedPressureBudget m ell F μ hμ g false at hp0
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
  have hcoef:ENNReal.ofReal C*4*ENNReal.ofReal (pressureFactor μ)=
      ENNReal.ofReal (24*sourceMuFactor μ k*radiusPrice*(μ/(16*n))) := by
    rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num,
      ←ENNReal.ofReal_mul hC,←ENNReal.ofReal_mul (mul_nonneg hC (by norm_num))]
    congr 1;unfold pressureFactor;dsimp only [C];ring
  change _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal (5*δ)+
    4*(ENNReal.ofReal (pressureFactor μ)*combinedPressureBudget m ell F μ hμ g false)) at hb
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal (5*δ)+
      4*(ENNReal.ofReal (pressureFactor μ)*combinedPressureBudget m ell F μ hμ g false)) := hb
    _=ENNReal.ofReal (ε/2+C*(5*δ))+
      ENNReal.ofReal (24*sourceMuFactor μ k*radiusPrice*(μ/(16*n)))*
        combinedPressureBudget m ell F μ hμ g false := by
      rw [mul_add,←mul_assoc,←mul_assoc,hcoef,←ENNReal.ofReal_mul hC,←add_assoc,
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal halloc) le_rfl

end LowEnergy.SourceClockPhiCombinedScaleGammaBudget
