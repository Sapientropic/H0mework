import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedCovarianceSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatRadialCovariancePair
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileCoframeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileCoframeRemainingWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCoframeHamiltonianWork
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiHeatCorrectedCoframeWork
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeDilation GaussCoframeCore
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore ClockPhiHeatComparisonWork
open ClockPhiHeatCorrectedCovarianceSource ClockPhiHeatRadialCovariancePair SourceClockPhiProfileCoframeReturn
open ClockPhiHeatHamiltonianWork ClockPhiHeatCoframeHamiltonianWork SourceClockPhiCombinedScalePressure
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private theorem ratio_smooth(t:ℝ)(_ht:0<t)(z:physicalChart):ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
  (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
private def rowRate(t:ℝ)(z:SourceCoordinateSlice):ℝ:=((forwardRatio t z)^(1/3:ℝ))⁻¹*forwardRatio t z/6
private theorem rowRate_smooth(t:ℝ)(ht:0<t)(z:physicalChart):ContDiffAt ℝ ∞ (rowRate t) z.val:=by
  have hr:=ratio_smooth t ht z
  have hp:0<(forwardRatio t z.val)^(1/3:ℝ):=Real.rpow_pos_of_pos (forward_ratio_pos t ht.le z) _
  exact (((hr.rpow_const_of_ne (forward_ratio_pos t ht.le z).ne').inv hp.ne').mul hr).div_const 6
private def noiseWeight(t ξ η:ℝ)(z:SourceCoordinateSlice):ℝ:=rowRate t z*covarianceNoise t ξ η z
private theorem noiseWeight_smooth(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (noiseWeight t ξ η) z.val:=(rowRate_smooth t ht z).mul (noise_smooth t ht ξ η z)
def correctedNoiseRow(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6):End:=
  radialColumn (noiseWeight t ξ η) (noiseWeight_smooth t ht ξ η) i*combinedGenerator
def correctedCovariantRow(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6):End:=
  deterministicCoframeRow t ht i+correctedNoiseRow t ht ξ η i
private theorem coefficient_first(t ξ η:ℝ):
    ∀x y:SourceCoordinateSlice,x.1=y.1→correctedCoefficient t ξ η x=correctedCoefficient t ξ η y:=by
  intro x y h
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  dsimp at h
  subst y₁
  rfl
private theorem corrected_core_profile(t:ℝ)(ht:0<t)(ξ η:ℝ):
    correctedCompleteCore t ht ξ η=
      profileCompleteCore t ht (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (fun _ _=>rfl):=rfl
private theorem corrected_bare_row(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6):
    profileCoframeRow t ht (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) i=
      heatCoframeRow t ht 0 i+correctedNoiseRow t ht ξ η i:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · apply PiLp.ext
    intro word
    change ((((forwardRatio t z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
      (momentum i f z word-(3*Complex.I*t:ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
        SourceClockPhiNativeMatchedSource.matchedTester f z word)+
        Complex.I*(((profileNoiseColumn t (correctedCoefficient t ξ η) i z:ℝ):ℂ)*combinedGenerator f z word))=
      ((((forwardRatio t z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
      (momentum i f z word-(3*Complex.I*t:ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
        SourceClockPhiNativeMatchedSource.matchedTester f z word)+
        (Complex.I*0)*(((forwardRatio t z*heatKappa t z/6*volumeGradient z i:ℝ):ℂ)*combinedGenerator f z word))+
        Complex.I*((noiseWeight t ξ η z:ℂ)*((volumeGradient z i:ℂ)*combinedGenerator f z word))
    have hb:profileNoiseColumn t (correctedCoefficient t ξ η) i z=
        forwardRatio t z*covarianceNoise t ξ η z*volumeGradient z i/6:=
      actual_corrected_row_coefficient t ht ξ η ⟨z,hz⟩ i
    rw [hb]
    unfold noiseWeight rowRate
    push_cast
    ring
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem noise_row_affine(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6):
    correctedNoiseRow t ht ξ η i=(ξ:ℂ) • correctedNoiseRow t ht 1 0 i+(η:ℂ) • correctedNoiseRow t ht 0 1 i:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change Complex.I • ((noiseWeight t ξ η z:ℂ) • ((volumeGradient z i:ℂ) • combinedGenerator f z))=
    (ξ:ℂ) • (Complex.I • ((noiseWeight t 1 0 z:ℂ) • ((volumeGradient z i:ℂ) • combinedGenerator f z)))+
    (η:ℂ) • (Complex.I • ((noiseWeight t 0 1 z:ℂ) • ((volumeGradient z i:ℂ) • combinedGenerator f z)))
  unfold noiseWeight
  rw [actual_covariance_noise_affine t ξ η z]
  simp only [Complex.ofReal_mul,Complex.ofReal_add,smul_smul,mul_add]
  module
private theorem corrected_row_affine(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6)(f:QuantumTest):
    correctedCovariantRow t ht ξ η i f=deterministicCoframeRow t ht i f+
      (ξ:ℂ) • correctedNoiseRow t ht 1 0 i f+(η:ℂ) • correctedNoiseRow t ht 0 1 i f:=by
  unfold correctedCovariantRow
  rw [noise_row_affine t ht ξ η i]
  simp only [LinearMap.add_apply,LinearMap.smul_apply]
  module

private theorem corrected_rows_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>∑i:Fin 6,∑j:Fin 6,sourcePair (correctedCovariantRow t ht x.1 x.2 i f)
      (SourceCoframeCovariantAction.metricAction i j (correctedCovariantRow t ht x.1 x.2 j g))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,(∑i:Fin 6,∑j:Fin 6,sourcePair (correctedCovariantRow t ht x.1 x.2 i f)
      (SourceCoframeCovariantAction.metricAction i j (correctedCovariantRow t ht x.1 x.2 j g))) ∂γ.prod γ)=
      ∑i:Fin 6,∑j:Fin 6,(sourcePair (deterministicCoframeRow t ht i f)
        (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))+
        sourcePair (correctedNoiseRow t ht 1 0 i f) (SourceCoframeCovariantAction.metricAction i j (correctedNoiseRow t ht 1 0 j g))+
        sourcePair (correctedNoiseRow t ht 0 1 i f) (SourceCoframeCovariantAction.metricAction i j (correctedNoiseRow t ht 0 1 j g))):=by
  have h(i j:Fin 6):=SourceClockPhiGaussianPlaneSource.actual_gaussian_affine_source_pair
    (deterministicCoframeRow t ht i f) (correctedNoiseRow t ht 1 0 i f) (correctedNoiseRow t ht 0 1 i f)
    (deterministicCoframeRow t ht j g) (correctedNoiseRow t ht 1 0 j g) (correctedNoiseRow t ht 0 1 j g)
    (SourceCoframeCovariantAction.metricAction i j)
  have hi(i j:Fin 6):Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCovariantRow t ht x.1 x.2 i f)
      (SourceCoframeCovariantAction.metricAction i j (correctedCovariantRow t ht x.1 x.2 j g))) (γ.prod γ):=by
    simpa only [corrected_row_affine] using (h i j).1
  refine ⟨integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>hi i j)),?_⟩
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _=>hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [corrected_row_affine] using (h i j).2

def correctedCoframeCovariance(t:ℝ)(ht:0<t):End:=
  radialPrice (noiseWeight t 1 0) (noiseWeight_smooth t ht 1 0)+
  radialPrice (noiseWeight t 0 1) (noiseWeight_smooth t ht 0 1)-
  kappaAction t ht*(radialPrice (rowRate t) (rowRate_smooth t ht)*kappaAction t ht)
private theorem old_stochastic_radial(t:ℝ)(ht:0<t)(i:Fin 6):
    stochasticCoframeRow t ht i=radialColumn (rowRate t) (rowRate_smooth t ht) i*kappaAction t ht*combinedGenerator:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change ((((forwardRatio t z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
    (momentum i f z word-(3*Complex.I*t:ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
      SourceClockPhiNativeMatchedSource.matchedTester f z word)+
      (Complex.I*1)*(((forwardRatio t z*heatKappa t z/6*volumeGradient z i:ℝ):ℂ)*combinedGenerator f z word))-
    ((((forwardRatio t z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
    (momentum i f z word-(3*Complex.I*t:ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
      SourceClockPhiNativeMatchedSource.matchedTester f z word)+
      (Complex.I*0)*(((forwardRatio t z*heatKappa t z/6*volumeGradient z i:ℝ):ℂ)*combinedGenerator f z word))=
    Complex.I*((rowRate t z:ℂ)*((volumeGradient z i:ℂ)*((heatKappa t z:ℂ)*combinedGenerator f z word)))
  unfold rowRate
  push_cast
  ring
private theorem old_stochastic_pair(t:ℝ)(ht:0<t)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,sourcePair (stochasticCoframeRow t ht i f)
      (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow t ht j g)))=
      sourcePair (combinedGenerator f)
        ((kappaAction t ht*(radialPrice (rowRate t) (rowRate_smooth t ht)*kappaAction t ht)) (combinedGenerator g)):=by
  simp_rw [old_stochastic_radial]
  simp only [Module.End.mul_apply]
  rw [actual_radial_covariance_pair]
  exact (multiply_pair _ _ _ _).symm
private theorem corrected_stochastic_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,sourcePair (correctedNoiseRow t ht ξ η i f)
      (SourceCoframeCovariantAction.metricAction i j (correctedNoiseRow t ht ξ η j g)))=
      sourcePair (combinedGenerator f)
        (radialPrice (noiseWeight t ξ η) (noiseWeight_smooth t ht ξ η) (combinedGenerator g)):=by
  exact actual_radial_covariance_pair _ _ _ _
private theorem corrected_gram_comparison(t:ℝ)(ht:0<t)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,(sourcePair (deterministicCoframeRow t ht i f)
      (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))+
      sourcePair (correctedNoiseRow t ht 1 0 i f) (SourceCoframeCovariantAction.metricAction i j (correctedNoiseRow t ht 1 0 j g))+
      sourcePair (correctedNoiseRow t ht 0 1 i f) (SourceCoframeCovariantAction.metricAction i j (correctedNoiseRow t ht 0 1 j g))))=
    (∑i:Fin 6,∑j:Fin 6,(sourcePair (deterministicCoframeRow t ht i f)
      (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))+
      sourcePair (stochasticCoframeRow t ht i f) (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow t ht j g))))+
      sourcePair (combinedGenerator f) (correctedCoframeCovariance t ht (combinedGenerator g)):=by
  simp only [Finset.sum_add_distrib]
  rw [corrected_stochastic_pair,corrected_stochastic_pair,old_stochastic_pair]
  simp only [correctedCoframeCovariance,LinearMap.add_apply,LinearMap.sub_apply,
    sourcePair,map_add,map_sub,inner_add_right,inner_sub_right]
  abel

theorem actual_corrected_covariance_point(t:ℝ)(ht:0<t)(f:QuantumTest)(z:physicalChart):
    correctedCoframeCovariance t ht f z.val=
      (((3*sourceTime 0/4)*volume z.val*(rowRate t z.val)^2*
        ((1/2)*(reciprocalVolume z.val^2-(SourceClockPhiForwardNativeReturn.forwardU t z.val)^2)-heatKappa t z.val^2):ℝ):ℂ) • f z.val:=by
  have hs:=actual_covariance_noise_square t ht z
  apply PiLp.ext
  intro word
  change (((3*sourceTime 0/4)*volume z.val*(noiseWeight t 1 0 z.val)^2:ℝ):ℂ)*f z.val word+
    (((3*sourceTime 0/4)*volume z.val*(noiseWeight t 0 1 z.val)^2:ℝ):ℂ)*f z.val word-
    (heatKappa t z.val:ℂ)*((((3*sourceTime 0/4)*volume z.val*(rowRate t z.val)^2:ℝ):ℂ)*
      ((heatKappa t z.val:ℂ)*f z.val word))=_
  have he:(3*sourceTime 0/4)*volume z.val*(noiseWeight t 1 0 z.val)^2+
      (3*sourceTime 0/4)*volume z.val*(noiseWeight t 0 1 z.val)^2-
      heatKappa t z.val*((3*sourceTime 0/4)*volume z.val*(rowRate t z.val)^2*heatKappa t z.val)=
      (3*sourceTime 0/4)*volume z.val*(rowRate t z.val)^2*
        ((1/2)*(reciprocalVolume z.val^2-(SourceClockPhiForwardNativeReturn.forwardU t z.val)^2)-heatKappa t z.val^2):=by
    unfold noiseWeight
    linear_combination (norm:=ring_nf) (3*sourceTime 0/4)*volume z.val*(rowRate t z.val)^2*hs
  have hc:=congrArg (fun r:ℝ=>(r:ℂ)*f z.val word) he
  simp only [PiLp.smul_apply,smul_eq_mul]
  push_cast at hc ⊢
  linear_combination (norm:=ring) hc

private theorem corrected_covariant_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6):
    SourceCoframeCovariantAction.covariantMomentum i*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*correctedCovariantRow t ht ξ η i:=by
  have hc:=SourceClockPhiProfileCoframeRemainingWork.actual_profile_complete_connection_return
    t ht (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (coefficient_first t ξ η) i
  have hp:=actual_profile_complete_coframe_return t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun _ _=>rfl) (coefficient_first t ξ η) i
  change SourceCoframeCovariantAction.connectionAction i*correctedCompleteCore t ht ξ η=
    correctedCompleteCore t ht ξ η*(_*SourceCoframeCovariantAction.connectionAction i) at hc
  change momentum i*correctedCompleteCore t ht ξ η=
    correctedCompleteCore t ht ξ η*profileCoframeRow t ht (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) i at hp
  rw [SourceCoframeCovariantAction.covariantMomentum,add_mul,hp,hc,corrected_bare_row]
  change correctedCompleteCore t ht ξ η*(heatCoframeRow t ht 0 i+correctedNoiseRow t ht ξ η i)+
    correctedCompleteCore t ht ξ η*(_*SourceCoframeCovariantAction.connectionAction i)=
    correctedCompleteCore t ht ξ η*((heatCoframeRow t ht 0 i+_*SourceCoframeCovariantAction.connectionAction i)+correctedNoiseRow t ht ξ η i)
  noncomm_ring
private theorem corrected_covariant_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f)
      (SourceCoframeCovariantAction.covariantKinetic (correctedCompleteCore t ht ξ η g))=
      ∑i:Fin 6,∑j:Fin 6,sourcePair (correctedCovariantRow t ht ξ η i f)
        (SourceCoframeCovariantAction.metricAction i j (correctedCovariantRow t ht ξ η j g)):=by
  simp only [SourceCoframeCovariantAction.covariantKinetic,LinearMap.sum_apply,sourcePair,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change sourcePair _ (SourceCoframeCovariantAction.covariantAdjoint i (SourceCoframeCovariantAction.metricAction i j
    (SourceCoframeCovariantAction.covariantMomentum j (correctedCompleteCore t ht ξ η g))))=_
  have had(p q:QuantumTest):sourcePair p (SourceCoframeCovariantAction.covariantAdjoint i q)=
      sourcePair (SourceCoframeCovariantAction.covariantMomentum i p) q:=by
    simp only [SourceCoframeCovariantAction.covariantAdjoint,SourceCoframeCovariantAction.covariantMomentum,
      LinearMap.add_apply,sourcePair,map_add,inner_add_right,inner_add_left]
    exact congrArg₂ (·+·) (GaussCoframeKinetic.adjoint_pair i p q)
      (SourceCoframeCovariantAction.original_connection_pair i p q)
  rw [had]
  have hi:=LinearMap.congr_fun (corrected_covariant_return t ht ξ η i) f
  have hj:=LinearMap.congr_fun (corrected_covariant_return t ht ξ η j) g
  simp only [Module.End.mul_apply] at hi hj
  rw [hi,hj]
  exact actual_profile_complete_metric_pair t ht (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (fun _ _=>rfl) i j _ _
private theorem pair_add_r(p f g:QuantumTest):sourcePair p (f+g)=sourcePair p f+sourcePair p g:=by
  simp only [sourcePair,map_add,inner_add_right]
theorem actual_corrected_coframe_source(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f)
      (GaussCoframeForm.coframeAction (correctedCompleteCore t ht ξ η g))=
      (∑i:Fin 6,∑j:Fin 6,sourcePair (correctedCovariantRow t ht ξ η i f)
        (SourceCoframeCovariantAction.metricAction i j (correctedCovariantRow t ht ξ η j g)))+localCoframePair t ht f g:=by
  have hs:=SourceClockPhiProfileCoframeRemainingWork.actual_profile_complete_spin_remainder_pair
    t ht (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (coefficient_first t ξ η) f g
  have hn:=SourceClockPhiProfileCoframeRemainingWork.actual_profile_complete_number_shift_pair
    t ht (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (coefficient_first t ξ η) f g
  have hv:=SourceClockPhiProfileCoframeRemainingWork.actual_profile_complete_coframe_volume_pair
    t ht (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (coefficient_first t ξ η) f g
  change sourcePair (correctedCompleteCore t ht ξ η f) (SourceCoframeCovariantSquare.spinRemainder (correctedCompleteCore t ht ξ η g))=_ at hs
  change sourcePair (correctedCompleteCore t ht ξ η f) (GaussCoframeForm.numberShift (correctedCompleteCore t ht ξ η g))=_ at hn
  change sourcePair (correctedCompleteCore t ht ξ η f) (multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth (correctedCompleteCore t ht ξ η g))=_ at hv
  rw [SourceCoframeCovariantSquare.original_coframe_covariant]
  simp only [LinearMap.add_apply,pair_add_r]
  rw [corrected_covariant_pair,hs,hn,hv]
  simp only [localCoframePair,←add_assoc]
  rfl

theorem actual_corrected_coframe_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (GaussCoframeForm.coframeAction (correctedCompleteCore t ht x.1 x.2 g))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (GaussCoframeForm.coframeAction (correctedCompleteCore t ht x.1 x.2 g)) ∂γ.prod γ)=
      (∫ξ:ℝ,sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
        (GaussCoframeForm.coframeAction (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g)) ∂γ)+
      sourcePair (combinedGenerator f) (correctedCoframeCovariance t ht (combinedGenerator g)):=by
  have h:=corrected_rows_gaussian t ht f g
  have hc:Integrable (fun _:ℝ×ℝ=>localCoframePair t ht f g) (γ.prod γ):=integrable_const _
  refine ⟨(h.1.add hc).congr (Eventually.of_forall (fun x=>(actual_corrected_coframe_source t ht x.1 x.2 f g).symm)),?_⟩
  simp_rw [actual_corrected_coframe_source]
  rw [integral_add h.1 hc,h.2,corrected_gram_comparison,
    (actual_complete_coframe_gaussian t ht f g).2]
  simp only [integral_const,probReal_univ,one_smul]
  ring

private theorem correction_scalar_nonneg(t:ℝ)(ht:0<t)(z:physicalChart):
    0≤(3*sourceTime 0/4)*volume z.val*(rowRate t z.val)^2*
      ((1/2)*(reciprocalVolume z.val^2-(SourceClockPhiForwardNativeReturn.forwardU t z.val)^2)-heatKappa t z.val^2):=by
  have h:=SourceClockPhiHeatComparisonPrice.clock_comparison_price (volume z.val) t (volume_pos z) ht
  have he:1+18*t*reciprocalVolume z.val=(volume z.val+18*t)/volume z.val:=by
    unfold reciprocalVolume
    field_simp [(volume_pos z).ne']
  have hp:heatKappa t z.val^2+(1/2:ℝ)*(SourceClockPhiForwardNativeReturn.forwardU t z.val)^2≤
      (1/2:ℝ)*reciprocalVolume z.val^2:=by
    dsimp only [heatKappa,ClockPhiConservativeHeatSource.heatLog,SourceClockPhiForwardNativeReturn.forwardU]
    rw [he]
    simpa only [reciprocalVolume,one_div] using h
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hv:=volume_pos z
  apply mul_nonneg
  · positivity
  · linarith

theorem actual_corrected_covariance_nonneg(t:ℝ)(ht:0<t)(f:QuantumTest):
    0≤(sourcePair f (correctedCoframeCovariance t ht f)).re:=by
  rw [sourcePair_integral]
  change 0≤RCLike.re (∫z,densityPair f (correctedCoframeCovariance t ht f) z ∂GaussHistoryHilbert.configurationMeasure)
  rw [←integral_re (densityPair_integrable f (correctedCoframeCovariance t ht f))]
  apply integral_nonneg
  intro z
  by_cases hz:z∈physicalChart
  · have hp:=actual_corrected_covariance_point t ht f ⟨z,hz⟩
    change 0≤(inner ℂ (GaussFockWeights.weight (fun N=>GaussDensityCore.complexDensity N z) (f z))
      (correctedCoframeCovariance t ht f z)).re
    rw [hp,inner_smul_right]
    change 0≤(((_ :ℝ):ℂ)*densityPair f f z).re
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    apply mul_nonneg (correction_scalar_nonneg t ht ⟨z,hz⟩)
    have hw:=GaussBoundedMultiplier.weighted_square (fun N=>GaussDensityCore.density N z)
      (fun N=>(GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
    change (densityPair f f z).re=_ at hw
    rw [hw]
    positivity
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp [densityPair,hf]

end LowEnergy.ClockPhiHeatCorrectedCoframeWork
