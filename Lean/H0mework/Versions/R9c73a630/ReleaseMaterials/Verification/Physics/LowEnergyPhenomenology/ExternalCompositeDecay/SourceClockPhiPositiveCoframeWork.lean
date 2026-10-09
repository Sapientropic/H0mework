import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedCoframeWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0FirstJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedWeightTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PositiveClockGenerator
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeDilation GaussCoframeCore
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore ClockPhiHeatComparisonWork
open ClockPhiHeatCorrectedCovarianceSource ClockPhiHeatRadialCovariancePair SourceClockPhiProfileCoframeReturn
open ClockPhiHeatHamiltonianWork ClockPhiHeatCoframeHamiltonianWork SourceClockPhiCombinedScalePressure
open ClockPhiHeatCorrectedCoframeWork MeasureTheory Set Filter
open SourceClockPhiOriginalGaussianH0FirstJet SourceClockPhiCorrectedWeightTransport
open scoped ContDiff Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private def rowRate(t:ℝ)(z:SourceCoordinateSlice):ℝ:=((forwardRatio t z)^(1/3:ℝ))⁻¹*forwardRatio t z/6
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
  · rw [LinearMap.add_apply]
    apply PiLp.ext
    intro word
    simp only [add_apply,PiLp.add_apply]
    change ((((forwardRatio t z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
      (momentum i f z word-(3*Complex.I*t:ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
        SourceClockPhiNativeMatchedSource.matchedTester f z word)+
        Complex.I*(((profileNoiseColumn t (correctedCoefficient t ξ η) i z:ℝ):ℂ)*combinedGenerator f z word))=
      ((((forwardRatio t z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
      (momentum i f z word-(3*Complex.I*t:ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
        SourceClockPhiNativeMatchedSource.matchedTester f z word)+
        (Complex.I*0)*(((forwardRatio t z*heatKappa t z/6*volumeGradient z i:ℝ):ℂ)*combinedGenerator f z word))+
        Complex.I*(((rowRate t z*covarianceNoise t ξ η z:ℝ):ℂ)*((volumeGradient z i:ℂ)*combinedGenerator f z word))
    have hb:profileNoiseColumn t (correctedCoefficient t ξ η) i z=
        forwardRatio t z*covarianceNoise t ξ η z*volumeGradient z i/6:=
      actual_corrected_row_coefficient t ht ξ η ⟨z,hz⟩ i
    rw [hb]
    unfold rowRate
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
  simp only [LinearMap.add_apply,LinearMap.smul_apply,add_apply,smul_apply]
  change Complex.I • (((rowRate t z*covarianceNoise t ξ η z:ℝ):ℂ) • ((volumeGradient z i:ℂ) • combinedGenerator f z))=
    (ξ:ℂ) • (Complex.I • (((rowRate t z*covarianceNoise t 1 0 z:ℝ):ℂ) • ((volumeGradient z i:ℂ) • combinedGenerator f z)))+
    (η:ℂ) • (Complex.I • (((rowRate t z*covarianceNoise t 0 1 z:ℝ):ℂ) • ((volumeGradient z i:ℂ) • combinedGenerator f z)))
  rw [actual_covariance_noise_affine t ξ η z]
  simp only [Complex.ofReal_mul,Complex.ofReal_add,smul_smul,mul_add]
  module
theorem corrected_row_affine(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6)(f:QuantumTest):
    correctedCovariantRow t ht ξ η i f=deterministicCoframeRow t ht i f+
      (ξ:ℂ) • correctedNoiseRow t ht 1 0 i f+(η:ℂ) • correctedNoiseRow t ht 0 1 i f:=by
  unfold correctedCovariantRow
  rw [noise_row_affine t ht ξ η i]
  simp only [LinearMap.add_apply,LinearMap.smul_apply]
  module

theorem corrected_covariant_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6):
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

theorem corrected_covariant_metric_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(i j:Fin 6)(f g:QuantumTest):
    sourcePair (SourceCoframeCovariantAction.covariantMomentum i (correctedCompleteCore t ht ξ η f))
      (SourceCoframeCovariantAction.metricAction i j
        (SourceCoframeCovariantAction.covariantMomentum j (correctedCompleteCore t ht ξ η g)))=
    sourcePair (correctedCovariantRow t ht ξ η i f)
      (SourceCoframeCovariantAction.metricAction i j (correctedCovariantRow t ht ξ η j g)):=by
  have hi:=LinearMap.congr_fun (corrected_covariant_return t ht ξ η i) f
  have hj:=LinearMap.congr_fun (corrected_covariant_return t ht ξ η j) g
  simp only [Module.End.mul_apply] at hi hj
  rw [hi,hj]
  exact actual_profile_complete_metric_pair t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun _ _=>rfl) i j _ _

theorem actual_corrected_covariant_metric_integrable(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>
      sourcePair (SourceCoframeCovariantAction.covariantMomentum i (correctedCompleteCore t ht x.1 x.2 f))
        (SourceCoframeCovariantAction.metricAction i j
          (SourceCoframeCovariantAction.covariantMomentum j (correctedCompleteCore t ht x.1 x.2 g)))) (γ.prod γ):=by
  have h:=SourceClockPhiGaussianPlaneSource.actual_gaussian_affine_source_pair
    (deterministicCoframeRow t ht i f) (correctedNoiseRow t ht 1 0 i f) (correctedNoiseRow t ht 0 1 i f)
    (deterministicCoframeRow t ht j g) (correctedNoiseRow t ht 1 0 j g) (correctedNoiseRow t ht 0 1 j g)
    (SourceCoframeCovariantAction.metricAction i j)
  simpa only [corrected_covariant_metric_pair,corrected_row_affine] using h.1

theorem corrected_covariant_inverse_metric_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(i j:Fin 6)(f g:QuantumTest):
    sourcePair (SourceCoframeCovariantAction.covariantMomentum i (correctedCompleteCore t ht ξ η f))
      (inverseVolumeAction (SourceCoframeCovariantAction.metricAction i j
        (SourceCoframeCovariantAction.covariantMomentum j (correctedCompleteCore t ht ξ η g))))=
    sourcePair (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le
        (correctedCovariantRow t ht ξ η i f))
      (SourceCoframeCovariantAction.metricAction i j (correctedCovariantRow t ht ξ η j g)):=by
  have hi:=LinearMap.congr_fun (corrected_covariant_return t ht ξ η i) f
  have hj:=LinearMap.congr_fun (corrected_covariant_return t ht ξ η j) g
  simp only [Module.End.mul_apply] at hi hj
  rw [hi,hj]
  have hp(p q:QuantumTest):sourcePair p (inverseVolumeAction q)=sourcePair (inverseVolumeAction p) q:=multiply_pair _ _ _ _
  rw [hp]
  have hU:=LinearMap.congr_fun
    (SourceClockPhiCorrectedWeightTransport.actual_corrected_complete_inverse_volume t ht ξ η)
    (correctedCovariantRow t ht ξ η i f)
  simp only [Module.End.mul_apply] at hU
  rw [hU]
  exact actual_profile_complete_metric_pair t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun _ _=>rfl) i j _ _

theorem actual_corrected_covariant_inverse_metric_integrable(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>
      sourcePair (SourceCoframeCovariantAction.covariantMomentum i (correctedCompleteCore t ht x.1 x.2 f))
        (inverseVolumeAction (SourceCoframeCovariantAction.metricAction i j
          (SourceCoframeCovariantAction.covariantMomentum j (correctedCompleteCore t ht x.1 x.2 g))))) (γ.prod γ):=by
  let U:=SourceClockPhiForwardNativeReturn.forwardUAction t ht.le
  have h:=SourceClockPhiGaussianPlaneSource.actual_gaussian_affine_source_pair
    (U (deterministicCoframeRow t ht i f)) (U (correctedNoiseRow t ht 1 0 i f)) (U (correctedNoiseRow t ht 0 1 i f))
    (deterministicCoframeRow t ht j g) (correctedNoiseRow t ht 1 0 j g) (correctedNoiseRow t ht 0 1 j g)
    (SourceCoframeCovariantAction.metricAction i j)
  simpa only [corrected_covariant_inverse_metric_pair,corrected_row_affine,map_add,map_smul] using h.1


private def currentValue(i:Fin 6)(z:SourceCoordinateSlice):ℝ:=reciprocalVolume z*volumeGradient z i
private theorem currentValue_smooth(i:Fin 6)(z:physicalChart):ContDiffAt ℝ ∞ (currentValue i) z.val:=by
  have h:ContDiff ℝ ∞ (fun z:SourceCoordinateSlice=>volumeGradient z i):=by
    fin_cases i <;> dsimp [volumeGradient] <;> fun_prop
  exact (reciprocal_volume_smooth z).mul h.contDiffAt
private theorem currentValue_first(i:Fin 6)(x y:SourceCoordinateSlice)(h:x.1=y.1):
    currentValue i x=currentValue i y:=by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  dsimp at h
  subst y₁
  rfl
private theorem forwardCurrent_smooth(t:ℝ)(ht:0<t)(i:Fin 6)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun w=>currentValue i (forwardPoint t w)) z.val:=
  ContDiffAt.comp (f:=forwardPoint t) z.val
    (currentValue_smooth i ⟨_,forward_chart t ht.le z⟩) (forward_smooth t ht.le z)
def returnedCurrentColumn(t:ℝ)(ht:0<t)(i:Fin 6):End:=
  multiply (fun z=>currentValue i (forwardPoint t z)) (forwardCurrent_smooth t ht i)
private theorem current_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6)(f:QuantumTest):
    sourceCurrentColumn i (correctedCompleteCore t ht ξ η f)=
      correctedCompleteCore t ht ξ η (returnedCurrentColumn t ht i f):=by
  exact LinearMap.congr_fun (actual_corrected_complete_coframe_multiplier t ht ξ η
    (currentValue i) (currentValue_smooth i) (currentValue_first i)) f
private theorem noise_action_affine(t:ℝ)(ht:0<t)(ξ η:ℝ):
    noiseAction t ht ξ η=(ξ:ℂ) • noiseAction t ht 1 0+(η:ℂ) • noiseAction t ht 0 1:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (covarianceNoise t ξ η z:ℂ) • f z=
    (ξ:ℂ) • ((covarianceNoise t 1 0 z:ℂ) • f z)+(η:ℂ) • ((covarianceNoise t 0 1 z:ℂ) • f z)
  rw [actual_covariance_noise_affine]
  simp only [Complex.ofReal_add,Complex.ofReal_mul,add_smul,mul_smul]
def returnedDriftZero(t:ℝ)(ht:0<t)(i:Fin 6):End:=
  (-3*Complex.I:ℂ) • (returnedCurrentColumn t ht i*SourceClockPhiNativeMatchedSource.matchedTester)
def returnedDriftNoise(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6):End:=
  (3*Complex.I:ℂ) • (returnedCurrentColumn t ht i*noiseAction t ht ξ η*combinedGenerator)
theorem corrected_drift_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6)(f:QuantumTest):
    coframeDriftColumn i (correctedCompleteCore t ht ξ η f)=
      correctedCompleteCore t ht ξ η
        (returnedDriftZero t ht i f+(ξ:ℂ) • returnedDriftNoise t ht 1 0 i f+
          (η:ℂ) • returnedDriftNoise t ht 0 1 i f):=by
  change (-3*Complex.I:ℂ) • sourceCurrentColumn i
    (SourceClockPhiNativeMatchedSource.matchedTester (correctedCompleteCore t ht ξ η f))=_
  rw [actual_corrected_complete_matched_tester,current_return,noise_action_affine]
  simp only [returnedDriftZero,returnedDriftNoise,Module.End.mul_apply,LinearMap.add_apply,
    LinearMap.smul_apply,map_sub,map_add,map_smul]
  module

private theorem affine_metric_integrable(t:ℝ)(ht:0<t)(i j:Fin 6)(A B C D E F:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair
      (correctedCompleteCore t ht x.1 x.2 (A+(x.1:ℂ) • B+(x.2:ℂ) • C))
      (SourceCoframeCovariantAction.metricAction i j
        (correctedCompleteCore t ht x.1 x.2 (D+(x.1:ℂ) • E+(x.2:ℂ) • F)))) (γ.prod γ):=by
  have he(x:ℝ×ℝ):sourcePair
      (correctedCompleteCore t ht x.1 x.2 (A+(x.1:ℂ) • B+(x.2:ℂ) • C))
      (SourceCoframeCovariantAction.metricAction i j
        (correctedCompleteCore t ht x.1 x.2 (D+(x.1:ℂ) • E+(x.2:ℂ) • F)))=
      sourcePair (A+(x.1:ℂ) • B+(x.2:ℂ) • C)
        (SourceCoframeCovariantAction.metricAction i j (D+(x.1:ℂ) • E+(x.2:ℂ) • F)):=
    actual_profile_complete_metric_pair t ht (correctedCoefficient t x.1 x.2)
      (coefficient_smooth t ht x.1 x.2) (fun _ _=>rfl) i j _ _
  simpa only [he] using
    (SourceClockPhiGaussianPlaneSource.actual_gaussian_affine_source_pair A B C D E F
      (SourceCoframeCovariantAction.metricAction i j)).1
private theorem covariance_return_point(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6)(f:QuantumTest):
    SourceCoframeCovariantAction.covariantMomentum i (correctedCompleteCore t ht ξ η f)=
      correctedCompleteCore t ht ξ η
        (deterministicCoframeRow t ht i f+(ξ:ℂ) • correctedNoiseRow t ht 1 0 i f+
          (η:ℂ) • correctedNoiseRow t ht 0 1 i f):=by
  have h:=LinearMap.congr_fun (corrected_covariant_return t ht ξ η i) f
  simpa only [Module.End.mul_apply,corrected_row_affine] using h
private theorem drift_covariant_integrable(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (coframeDriftColumn i (correctedCompleteCore t ht x.1 x.2 f))
      (SourceCoframeCovariantAction.metricAction i j
        (SourceCoframeCovariantAction.covariantMomentum j (correctedCompleteCore t ht x.1 x.2 g)))) (γ.prod γ):=by
  simp only [corrected_drift_return,covariance_return_point]
  exact affine_metric_integrable t ht i j
    (returnedDriftZero t ht i f) (returnedDriftNoise t ht 1 0 i f) (returnedDriftNoise t ht 0 1 i f)
    (deterministicCoframeRow t ht j g) (correctedNoiseRow t ht 1 0 j g) (correctedNoiseRow t ht 0 1 j g)
private theorem covariant_drift_integrable(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair
      (SourceCoframeCovariantAction.covariantMomentum i (correctedCompleteCore t ht x.1 x.2 f))
      (SourceCoframeCovariantAction.metricAction i j (coframeDriftColumn j (correctedCompleteCore t ht x.1 x.2 g)))) (γ.prod γ):=by
  simp only [corrected_drift_return,covariance_return_point]
  exact affine_metric_integrable t ht i j
    (deterministicCoframeRow t ht i f) (correctedNoiseRow t ht 1 0 i f) (correctedNoiseRow t ht 0 1 i f)
    (returnedDriftZero t ht j g) (returnedDriftNoise t ht 1 0 j g) (returnedDriftNoise t ht 0 1 j g)

theorem actual_corrected_deterministic_jet_integrable(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>deterministicPairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g)) (γ.prod γ):=by
  exact integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>
    (((actual_corrected_covariant_inverse_metric_integrable t ht i j f g).const_mul (-12:ℂ)).add
      (drift_covariant_integrable t ht i j f g)).add (covariant_drift_integrable t ht i j f g)))


def affinePairMean(A B C D E F:QuantumTest)(M:End):ℂ:=
  sourcePair A (M D)+sourcePair B (M E)+sourcePair C (M F)
private theorem affine_metric_mean(t:ℝ)(ht:0<t)(i j:Fin 6)(A B C D E F:QuantumTest):
    (∫x:ℝ×ℝ,sourcePair
      (correctedCompleteCore t ht x.1 x.2 (A+(x.1:ℂ) • B+(x.2:ℂ) • C))
      (SourceCoframeCovariantAction.metricAction i j
        (correctedCompleteCore t ht x.1 x.2 (D+(x.1:ℂ) • E+(x.2:ℂ) • F))) ∂γ.prod γ)=
      affinePairMean A B C D E F (SourceCoframeCovariantAction.metricAction i j):=by
  have he(x:ℝ×ℝ):sourcePair
      (correctedCompleteCore t ht x.1 x.2 (A+(x.1:ℂ) • B+(x.2:ℂ) • C))
      (SourceCoframeCovariantAction.metricAction i j
        (correctedCompleteCore t ht x.1 x.2 (D+(x.1:ℂ) • E+(x.2:ℂ) • F)))=
      sourcePair (A+(x.1:ℂ) • B+(x.2:ℂ) • C)
        (SourceCoframeCovariantAction.metricAction i j (D+(x.1:ℂ) • E+(x.2:ℂ) • F)):=
    actual_profile_complete_metric_pair t ht (correctedCoefficient t x.1 x.2)
      (coefficient_smooth t ht x.1 x.2) (fun _ _=>rfl) i j _ _
  simp_rw [he]
  exact (SourceClockPhiGaussianPlaneSource.actual_gaussian_affine_source_pair A B C D E F
    (SourceCoframeCovariantAction.metricAction i j)).2

def inverseMetricPositiveMean(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):ℂ:=
  affinePairMean
    (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le (deterministicCoframeRow t ht i f))
    (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le (correctedNoiseRow t ht 1 0 i f))
    (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le (correctedNoiseRow t ht 0 1 i f))
    (deterministicCoframeRow t ht j g) (correctedNoiseRow t ht 1 0 j g) (correctedNoiseRow t ht 0 1 j g)
    (SourceCoframeCovariantAction.metricAction i j)
def driftCovariantPositiveMean(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):ℂ:=
  affinePairMean
    (returnedDriftZero t ht i f) (returnedDriftNoise t ht 1 0 i f) (returnedDriftNoise t ht 0 1 i f)
    (deterministicCoframeRow t ht j g) (correctedNoiseRow t ht 1 0 j g) (correctedNoiseRow t ht 0 1 j g)
    (SourceCoframeCovariantAction.metricAction i j)
def covariantDriftPositiveMean(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):ℂ:=
  affinePairMean
    (deterministicCoframeRow t ht i f) (correctedNoiseRow t ht 1 0 i f) (correctedNoiseRow t ht 0 1 i f)
    (returnedDriftZero t ht j g) (returnedDriftNoise t ht 1 0 j g) (returnedDriftNoise t ht 0 1 j g)
    (SourceCoframeCovariantAction.metricAction i j)
private theorem inverse_metric_mean(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):
    (∫x:ℝ×ℝ,sourcePair
      (SourceCoframeCovariantAction.covariantMomentum i (correctedCompleteCore t ht x.1 x.2 f))
      (inverseVolumeAction (SourceCoframeCovariantAction.metricAction i j
        (SourceCoframeCovariantAction.covariantMomentum j (correctedCompleteCore t ht x.1 x.2 g)))) ∂γ.prod γ)=
      inverseMetricPositiveMean t ht i j f g:=by
  simp_rw [corrected_covariant_inverse_metric_pair,corrected_row_affine,map_add,map_smul]
  let U:=SourceClockPhiForwardNativeReturn.forwardUAction t ht.le
  simpa only [map_add,map_smul,inverseMetricPositiveMean,affinePairMean] using
    (SourceClockPhiGaussianPlaneSource.actual_gaussian_affine_source_pair
      (U (deterministicCoframeRow t ht i f)) (U (correctedNoiseRow t ht 1 0 i f)) (U (correctedNoiseRow t ht 0 1 i f))
      (deterministicCoframeRow t ht j g) (correctedNoiseRow t ht 1 0 j g) (correctedNoiseRow t ht 0 1 j g)
      (SourceCoframeCovariantAction.metricAction i j)).2
private theorem drift_covariant_mean(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):
    (∫x:ℝ×ℝ,sourcePair (coframeDriftColumn i (correctedCompleteCore t ht x.1 x.2 f))
      (SourceCoframeCovariantAction.metricAction i j
        (SourceCoframeCovariantAction.covariantMomentum j (correctedCompleteCore t ht x.1 x.2 g))) ∂γ.prod γ)=
      driftCovariantPositiveMean t ht i j f g:=by
  simp only [corrected_drift_return,covariance_return_point]
  exact affine_metric_mean t ht i j _ _ _ _ _ _
private theorem covariant_drift_mean(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):
    (∫x:ℝ×ℝ,sourcePair
      (SourceCoframeCovariantAction.covariantMomentum i (correctedCompleteCore t ht x.1 x.2 f))
      (SourceCoframeCovariantAction.metricAction i j (coframeDriftColumn j (correctedCompleteCore t ht x.1 x.2 g))) ∂γ.prod γ)=
      covariantDriftPositiveMean t ht i j f g:=by
  simp only [corrected_drift_return,covariance_return_point]
  exact affine_metric_mean t ht i j _ _ _ _ _ _

def deterministicPositiveMean(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  ∑i:Fin 6,∑j:Fin 6,((-12:ℂ)*inverseMetricPositiveMean t ht i j f g+
    driftCovariantPositiveMean t ht i j f g+covariantDriftPositiveMean t ht i j f g)

theorem actual_corrected_deterministic_jet_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>deterministicPairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,deterministicPairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g) ∂γ.prod γ)=deterministicPositiveMean t ht f g:=by
  refine ⟨actual_corrected_deterministic_jet_integrable t ht f g,?_⟩
  have hi(i j:Fin 6):=(((actual_corrected_covariant_inverse_metric_integrable t ht i j f g).const_mul (-12:ℂ)).add
    (drift_covariant_integrable t ht i j f g)).add (covariant_drift_integrable t ht i j f g)
  unfold deterministicPairJet deterministicPositiveMean
  erw [integral_finsetSum (Finset.univ:Finset (Fin 6))
    (fun i _=>integrable_finsetSum (Finset.univ:Finset (Fin 6)) (fun j _=>hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  erw [integral_finsetSum (Finset.univ:Finset (Fin 6)) (fun j _=>hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  erw [integral_add (((actual_corrected_covariant_inverse_metric_integrable t ht i j f g).const_mul (-12:ℂ)).add
      (drift_covariant_integrable t ht i j f g)) (covariant_drift_integrable t ht i j f g),
    integral_add ((actual_corrected_covariant_inverse_metric_integrable t ht i j f g).const_mul (-12:ℂ))
      (drift_covariant_integrable t ht i j f g),integral_const_mul,
    inverse_metric_mean,drift_covariant_mean,covariant_drift_mean]


private theorem current_forward_value(t:ℝ)(ht:0<t)(i:Fin 6)(z:physicalChart):
    currentValue i (forwardPoint t z.val)=(forwardRatio t z.val)^(-1/3:ℝ)*currentValue i z.val:=by
  let b:ℝ:=(forwardRatio t z.val)^(1/3:ℝ)
  have hb:0<b:=Real.rpow_pos_of_pos (forward_ratio_pos t ht.le z) _
  have hg:volumeGradient (forwardPoint t z.val) i=b^2*volumeGradient z.val i:=by
    fin_cases i <;> dsimp [volumeGradient,forwardPoint,scale,b] <;> ring
  have hcube:b^3=forwardRatio t z.val:=cube_root_cube _ (forward_ratio_pos t ht.le z).le
  have hw:volume z.val+18*t=b^3*volume z.val:=by
    rw [hcube]
    unfold forwardRatio
    exact (div_mul_cancel₀ _ (volume_pos z).ne').symm
  have hp:(forwardRatio t z.val)^(-1/3:ℝ)=b⁻¹:=by
    simpa only [b,neg_div] using Real.rpow_neg (forward_ratio_pos t ht.le z).le (1/3:ℝ)
  unfold currentValue reciprocalVolume
  rw [forward_volume t ht.le z,hg,hw,hp]
  field_simp [hb.ne',(volume_pos z).ne']

theorem returned_current_power(t:ℝ)(ht:0<t)(i:Fin 6):
    returnedCurrentColumn t ht i=
      SourceClockPhiHeatLocalNativeGaussian.gaussianProfileWeight t ht (-1/3)*sourceCurrentColumn i:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (currentValue i (forwardPoint t z):ℂ) • f z=
      (((forwardRatio t z)^(-1/3:ℝ):ℝ):ℂ) • ((currentValue i z:ℂ) • f z)
    rw [current_forward_value t ht i ⟨z,hz⟩,Complex.ofReal_mul,mul_smul]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

theorem returned_drift_zero_power(t:ℝ)(ht:0<t)(i:Fin 6):
    returnedDriftZero t ht i=SourceClockPhiHeatLocalNativeGaussian.gaussianProfileWeight t ht (-1/3)*coframeDriftColumn i:=by
  rw [returnedDriftZero,returned_current_power,coframeDriftColumn]
  simp only [mul_assoc,mul_smul_comm]

theorem returned_drift_noise_power(t:ℝ)(ht:0<t)(ξ η:ℝ)(i:Fin 6):
    returnedDriftNoise t ht ξ η i=(18:ℂ) •
      (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le*correctedNoiseRow t ht ξ η i):=by
  rw [returnedDriftNoise,returned_current_power]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · let zc:physicalChart:=⟨z,hz⟩
    have hp:(forwardRatio t z)^(-1/3:ℝ)=((forwardRatio t z)^(1/3:ℝ))⁻¹:=by
      simpa only [neg_div] using Real.rpow_neg (forward_ratio_pos t ht.le zc).le (1/3:ℝ)
    have hu:SourceClockPhiForwardNativeReturn.forwardU t z*forwardRatio t z=reciprocalVolume z:=by
      unfold SourceClockPhiForwardNativeReturn.forwardU forwardRatio reciprocalVolume
      have hV:(volume z)≠0:=(volume_pos zc).ne'
      have hW:(volume z+18*t)≠0:=by linarith [volume_pos zc]
      field_simp [hV,hW]
    apply PiLp.ext
    intro word
    simp only [LinearMap.smul_apply,Module.End.mul_apply,smul_apply,PiLp.smul_apply,smul_eq_mul]
    change (3*Complex.I:ℂ)*((((forwardRatio t z)^(-1/3:ℝ):ℝ):ℂ)*
      (((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
        ((covarianceNoise t ξ η z:ℂ)*combinedGenerator f z word)))=
      (18:ℂ)*((SourceClockPhiForwardNativeReturn.forwardU t z:ℂ)*
        (Complex.I*(((rowRate t z*covarianceNoise t ξ η z:ℝ):ℂ)*
          ((volumeGradient z i:ℂ)*combinedGenerator f z word))))
    rw [hp]
    have hu':(SourceClockPhiForwardNativeReturn.forwardU t z:ℂ)*(forwardRatio t z:ℂ)=(reciprocalVolume z:ℂ):=
      by exact_mod_cast hu
    unfold rowRate
    push_cast
    rw [←hu']
    ring
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

end LowEnergy.PositiveClockGenerator
