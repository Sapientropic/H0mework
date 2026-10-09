import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedWorkComposition
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFourGaussianAffineSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedCoframeWork
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiComposedCoframeGaussianWork
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeDilation GaussCoframeCore
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore ClockPhiHeatComparisonWork
open ClockPhiHeatCorrectedCovarianceSource ClockPhiHeatRadialCovariancePair SourceClockPhiProfileCoframeReturn
open ClockPhiHeatHamiltonianWork ClockPhiHeatCoframeHamiltonianWork SourceClockPhiCombinedScalePressure
open ClockPhiCorrectedWorkComposition ClockPhiHeatCorrectedCoframeWork MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev γ := ProbabilityTheory.gaussianReal 0 1
private abbrev γ4 := (γ.prod γ).prod (γ.prod γ)
private abbrev Four := (ℝ×ℝ)×(ℝ×ℝ)
private theorem composed_smooth (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(z:physicalChart):
    ContDiffAt ℝ ∞ (composedCoefficient s t x) z.val := by
  simpa only [composedCoefficient,Function.comp_def] using!
    ((coefficient_smooth s hs x.2.1 x.2.2 ⟨_,forward_chart t ht.le z⟩).comp z.val
      (forward_smooth t ht.le z)).add (coefficient_smooth t ht x.1.1 x.1.2 z)
private theorem composed_first (s t:ℝ)(x:Four):
    ∀a b:SourceCoordinateSlice,a.1=b.1→composedCoefficient s t x a=composedCoefficient s t x b := by
  intro a b h
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨b₁,b₂⟩
  dsimp at h
  subst b₁
  rfl
private theorem composed_invariant (s t:ℝ)(x:Four)(u:ℝ)(z:SourceCoordinateSlice):
    composedCoefficient s t x (combinedMap u z)=composedCoefficient s t x z := rfl
private theorem noise_smooth (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(z:physicalChart):
    ContDiffAt ℝ ∞ (composedNoise s t x) z.val := by
  simpa only [composedNoise,Function.comp_def] using!
    ((ClockPhiHeatCorrectedCovarianceSource.noise_smooth s hs x.2.1 x.2.2
      ⟨_,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z)).add
      (ClockPhiHeatCorrectedCovarianceSource.noise_smooth t ht x.1.1 x.1.2 z)
private def rowRate (T:ℝ)(z:SourceCoordinateSlice):ℝ :=
  ((forwardRatio T z)^(1/3:ℝ))⁻¹*forwardRatio T z/6
private theorem rowRate_smooth (T:ℝ)(hT:0<T)(z:physicalChart):ContDiffAt ℝ ∞ (rowRate T) z.val := by
  have hr : ContDiffAt ℝ ∞ (forwardRatio T) z.val :=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  have hp : 0<(forwardRatio T z.val)^(1/3:ℝ) := Real.rpow_pos_of_pos (forward_ratio_pos T hT.le z) _
  exact (((hr.rpow_const_of_ne (forward_ratio_pos T hT.le z).ne').inv hp.ne').mul hr).div_const 6
private def noiseWeight (s t:ℝ)(x:Four)(z:SourceCoordinateSlice):ℝ := rowRate (s+t) z*composedNoise s t x z
private theorem weight_smooth (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(z:physicalChart):
    ContDiffAt ℝ ∞ (noiseWeight s t x) z.val := (rowRate_smooth (s+t) (add_pos hs ht) z).mul (noise_smooth s t hs ht x z)
private def noiseRow (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(i:Fin 6):End :=
  radialColumn (noiseWeight s t x) (weight_smooth s t hs ht x) i*combinedGenerator
private def covariantRow (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(i:Fin 6):End :=
  deterministicCoframeRow (s+t) (add_pos hs ht) i+noiseRow s t hs ht x i
private theorem volume_euler (z:SourceCoordinateSlice):fderiv ℝ GaussNativeEnergy.volume z (euler z)=3*GaussNativeEnergy.volume z := by
  rw [volume_derivative]
  change z.1 0*z.1 2*z.1 5+z.1 0*z.1 2*z.1 5+z.1 0*z.1 2*z.1 5=_
  unfold GaussNativeEnergy.volume
  ring
private theorem composed_row_coefficient (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(z:physicalChart)(i:Fin 6):
    profileNoiseColumn (s+t) (composedCoefficient s t x) i z.val =
      forwardRatio (s+t) z.val*composedNoise s t x z.val*volumeGradient z.val i/6 := by
  unfold profileNoiseColumn
  rw [actual_composed_profile_gradient s t hs ht x z (coframeDirection i),
    actual_composed_profile_gradient s t hs ht x z (euler z.val),volume_coordinate_derivative,volume_euler]
  unfold reciprocalVolume SourceClockPhiForwardNativeReturn.forwardU forwardRatio
  have hW : 0<GaussNativeEnergy.volume z.val+18*(s+t) := by linarith [volume_pos z]
  have hm : (GaussNativeEnergy.volume z.val+18*(s+t))*(GaussNativeEnergy.volume z.val+18*(s+t))⁻¹=1 := mul_inv_cancel₀ hW.ne'
  field_simp [(volume_pos z).ne',hW.ne']
  linear_combination (norm:=ring_nf) volumeGradient z.val i*GaussNativeEnergy.volume z.val*hm
private theorem composed_core_profile (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four):
    composedCompleteCore s t hs ht x =
      profileCompleteCore (s+t) (add_pos hs ht) (composedCoefficient s t x)
        (composed_smooth s t hs ht x) (composed_invariant s t x) := rfl
private theorem composed_bare_row (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(i:Fin 6):
    profileCoframeRow (s+t) (add_pos hs ht) (composedCoefficient s t x) (composed_smooth s t hs ht x) i=
      heatCoframeRow (s+t) (add_pos hs ht) 0 i+noiseRow s t hs ht x i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · apply PiLp.ext
    intro word
    change ((((forwardRatio (s+t) z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
      (momentum i f z word-(3*Complex.I*((s+t:ℝ):ℂ):ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
        SourceClockPhiNativeMatchedSource.matchedTester f z word)+
        Complex.I*(((profileNoiseColumn (s+t) (composedCoefficient s t x) i z:ℝ):ℂ)*combinedGenerator f z word))=
      ((((forwardRatio (s+t) z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
      (momentum i f z word-(3*Complex.I*((s+t:ℝ):ℂ):ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
        SourceClockPhiNativeMatchedSource.matchedTester f z word)+
        (Complex.I*0)*(((forwardRatio (s+t) z*heatKappa (s+t) z/6*volumeGradient z i:ℝ):ℂ)*combinedGenerator f z word))+
        Complex.I*((noiseWeight s t x z:ℂ)*((volumeGradient z i:ℂ)*combinedGenerator f z word))
    rw [composed_row_coefficient s t hs ht x ⟨z,hz⟩ i]
    unfold noiseWeight rowRate
    push_cast
    ring
  · have h0 (q:QuantumTest):q z=0 := image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private def basis (k:Fin 4):Four := ![((1,0),(0,0)),((0,1),(0,0)),((0,0),(1,0)),((0,0),(0,1))] k
private theorem zero_noise (T:ℝ)(z:SourceCoordinateSlice):covarianceNoise T 0 0 z=0 := by
  rw [actual_covariance_noise_affine T 0 0 z]
  ring
private theorem noise_affine (s t:ℝ)(x:Four)(z:SourceCoordinateSlice):
    composedNoise s t x z=x.1.1*composedNoise s t (basis 0) z+
      x.1.2*composedNoise s t (basis 1) z+x.2.1*composedNoise s t (basis 2) z+
      x.2.2*composedNoise s t (basis 3) z := by
  have hS:=actual_covariance_noise_affine s x.2.1 x.2.2 (forwardPoint t z)
  have hT:=actual_covariance_noise_affine t x.1.1 x.1.2 z
  simp [composedNoise,basis,zero_noise]
  rw [hS,hT]
  ring
private theorem row_affine (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(i:Fin 6)(f:QuantumTest):
    covariantRow s t hs ht x i f=deterministicCoframeRow (s+t) (add_pos hs ht) i f+
      (x.1.1:ℂ) • noiseRow s t hs ht (basis 0) i f+
      (x.1.2:ℂ) • noiseRow s t hs ht (basis 1) i f+
      (x.2.1:ℂ) • noiseRow s t hs ht (basis 2) i f+
      (x.2.2:ℂ) • noiseRow s t hs ht (basis 3) i f := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change deterministicCoframeRow (s+t) (add_pos hs ht) i f z word+
    Complex.I*((noiseWeight s t x z:ℂ)*((volumeGradient z i:ℂ)*combinedGenerator f z word))=
    deterministicCoframeRow (s+t) (add_pos hs ht) i f z word+
    (x.1.1:ℂ)*(Complex.I*((noiseWeight s t (basis 0) z:ℂ)*((volumeGradient z i:ℂ)*combinedGenerator f z word)))+
    (x.1.2:ℂ)*(Complex.I*((noiseWeight s t (basis 1) z:ℂ)*((volumeGradient z i:ℂ)*combinedGenerator f z word)))+
    (x.2.1:ℂ)*(Complex.I*((noiseWeight s t (basis 2) z:ℂ)*((volumeGradient z i:ℂ)*combinedGenerator f z word)))+
    (x.2.2:ℂ)*(Complex.I*((noiseWeight s t (basis 3) z:ℂ)*((volumeGradient z i:ℂ)*combinedGenerator f z word)))
  have hb:noiseWeight s t x z=x.1.1*noiseWeight s t (basis 0) z+
      x.1.2*noiseWeight s t (basis 1) z+x.2.1*noiseWeight s t (basis 2) z+
      x.2.2*noiseWeight s t (basis 3) z := by
    unfold noiseWeight
    rw [noise_affine s t x z]
    ring
  have hc:=congrArg (fun r:ℝ=>(r:ℂ)) hb
  push_cast at hc
  linear_combination (norm:=ring) (Complex.I*(volumeGradient z i:ℂ)*combinedGenerator f z word)*hc
private theorem four_pair (A B C D E F G H I J:QuantumTest)(M:End):
    Integrable (fun x:Four=>sourcePair
      (A+(x.1.1:ℂ) • B+(x.1.2:ℂ) • C+(x.2.1:ℂ) • D+(x.2.2:ℂ) • E)
      (M (F+(x.1.1:ℂ) • G+(x.1.2:ℂ) • H+(x.2.1:ℂ) • I+(x.2.2:ℂ) • J))) γ4 ∧
    (∫x:Four,sourcePair
      (A+(x.1.1:ℂ) • B+(x.1.2:ℂ) • C+(x.2.1:ℂ) • D+(x.2.2:ℂ) • E)
      (M (F+(x.1.1:ℂ) • G+(x.1.2:ℂ) • H+(x.2.1:ℂ) • I+(x.2.2:ℂ) • J)) ∂γ4)=
        sourcePair A (M F)+sourcePair B (M G)+sourcePair C (M H)+sourcePair D (M I)+sourcePair E (M J) := by
  exact SourceClockPhiFourGaussianAffineSource.actual_gaussian_affine_four_expanded_source_pair A B C D E F G H I J M
private def meanRows (s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest):ℂ :=
  ∑i:Fin 6,∑j:Fin 6,(sourcePair (deterministicCoframeRow (s+t) (add_pos hs ht) i f)
      (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow (s+t) (add_pos hs ht) j g))+
    ∑k:Fin 4,sourcePair (noiseRow s t hs ht (basis k) i f)
      (SourceCoframeCovariantAction.metricAction i j (noiseRow s t hs ht (basis k) j g)))
private theorem rows_gaussian (s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:Four=>∑i:Fin 6,∑j:Fin 6,sourcePair (covariantRow s t hs ht x i f)
      (SourceCoframeCovariantAction.metricAction i j (covariantRow s t hs ht x j g))) γ4 ∧
    (∫x:Four,(∑i:Fin 6,∑j:Fin 6,sourcePair (covariantRow s t hs ht x i f)
      (SourceCoframeCovariantAction.metricAction i j (covariantRow s t hs ht x j g))) ∂γ4)=meanRows s t hs ht f g := by
  have h (i j:Fin 6):=four_pair
    (deterministicCoframeRow (s+t) (add_pos hs ht) i f)
    (noiseRow s t hs ht (basis 0) i f) (noiseRow s t hs ht (basis 1) i f)
    (noiseRow s t hs ht (basis 2) i f) (noiseRow s t hs ht (basis 3) i f)
    (deterministicCoframeRow (s+t) (add_pos hs ht) j g)
    (noiseRow s t hs ht (basis 0) j g) (noiseRow s t hs ht (basis 1) j g)
    (noiseRow s t hs ht (basis 2) j g) (noiseRow s t hs ht (basis 3) j g)
    (SourceCoframeCovariantAction.metricAction i j)
  have hi (i j:Fin 6):Integrable (fun x:Four=>sourcePair (covariantRow s t hs ht x i f)
      (SourceCoframeCovariantAction.metricAction i j (covariantRow s t hs ht x j g))) γ4 := by
    simpa only [row_affine] using (h i j).1
  refine ⟨integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>hi i j)),?_⟩
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>hi i j))]
  unfold meanRows
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _=>hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  simpa [row_affine,Fin.sum_univ_succ,add_assoc] using (h i j).2
private theorem covariant_return (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(i:Fin 6):
    SourceCoframeCovariantAction.covariantMomentum i*composedCompleteCore s t hs ht x=
      composedCompleteCore s t hs ht x*covariantRow s t hs ht x i := by
  have hc:=SourceClockPhiProfileCoframeRemainingWork.actual_profile_complete_connection_return
    (s+t) (add_pos hs ht) (composedCoefficient s t x) (composed_smooth s t hs ht x) (composed_first s t x) i
  have hp:=actual_profile_complete_coframe_return (s+t) (add_pos hs ht) (composedCoefficient s t x)
    (composed_smooth s t hs ht x) (composed_invariant s t x) (composed_first s t x) i
  change SourceCoframeCovariantAction.connectionAction i*composedCompleteCore s t hs ht x=
    composedCompleteCore s t hs ht x*(_*SourceCoframeCovariantAction.connectionAction i) at hc
  change momentum i*composedCompleteCore s t hs ht x=
    composedCompleteCore s t hs ht x*profileCoframeRow (s+t) (add_pos hs ht) (composedCoefficient s t x)
      (composed_smooth s t hs ht x) i at hp
  rw [SourceCoframeCovariantAction.covariantMomentum,add_mul,hp,hc,composed_bare_row]
  change composedCompleteCore s t hs ht x*(heatCoframeRow (s+t) (add_pos hs ht) 0 i+noiseRow s t hs ht x i)+
    composedCompleteCore s t hs ht x*(_*SourceCoframeCovariantAction.connectionAction i)=
    composedCompleteCore s t hs ht x*((heatCoframeRow (s+t) (add_pos hs ht) 0 i+_*SourceCoframeCovariantAction.connectionAction i)+noiseRow s t hs ht x i)
  noncomm_ring
private theorem covariant_pair (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(f g:QuantumTest):
    sourcePair (composedCompleteCore s t hs ht x f)
      (SourceCoframeCovariantAction.covariantKinetic (composedCompleteCore s t hs ht x g))=
      ∑i:Fin 6,∑j:Fin 6,sourcePair (covariantRow s t hs ht x i f)
        (SourceCoframeCovariantAction.metricAction i j (covariantRow s t hs ht x j g)) := by
  simp only [SourceCoframeCovariantAction.covariantKinetic,LinearMap.sum_apply,sourcePair,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change sourcePair _ (SourceCoframeCovariantAction.covariantAdjoint i (SourceCoframeCovariantAction.metricAction i j
    (SourceCoframeCovariantAction.covariantMomentum j (composedCompleteCore s t hs ht x g))))=_
  have had (p q:QuantumTest):sourcePair p (SourceCoframeCovariantAction.covariantAdjoint i q)=
      sourcePair (SourceCoframeCovariantAction.covariantMomentum i p) q := by
    simp only [SourceCoframeCovariantAction.covariantAdjoint,SourceCoframeCovariantAction.covariantMomentum,
      LinearMap.add_apply,sourcePair,map_add,inner_add_right,inner_add_left]
    exact congrArg₂ (·+·) (GaussCoframeKinetic.adjoint_pair i p q)
      (SourceCoframeCovariantAction.original_connection_pair i p q)
  rw [had]
  have hi:=LinearMap.congr_fun (covariant_return s t hs ht x i) f
  have hj:=LinearMap.congr_fun (covariant_return s t hs ht x j) g
  simp only [Module.End.mul_apply] at hi hj
  rw [hi,hj]
  exact actual_profile_complete_metric_pair (s+t) (add_pos hs ht) (composedCoefficient s t x)
    (composed_smooth s t hs ht x) (composed_invariant s t x) i j _ _
private theorem pair_add_r (p f g:QuantumTest):sourcePair p (f+g)=sourcePair p f+sourcePair p g := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem composed_coframe_source (s t:ℝ)(hs:0<s)(ht:0<t)(x:Four)(f g:QuantumTest):
    sourcePair (composedCompleteCore s t hs ht x f)
      (GaussCoframeForm.coframeAction (composedCompleteCore s t hs ht x g))=
      (∑i:Fin 6,∑j:Fin 6,sourcePair (covariantRow s t hs ht x i f)
        (SourceCoframeCovariantAction.metricAction i j (covariantRow s t hs ht x j g)))+
          localCoframePair (s+t) (add_pos hs ht) f g := by
  have hs0:=SourceClockPhiProfileCoframeRemainingWork.actual_profile_complete_spin_remainder_pair
    (s+t) (add_pos hs ht) (composedCoefficient s t x) (composed_smooth s t hs ht x) (composed_first s t x) f g
  have hn:=SourceClockPhiProfileCoframeRemainingWork.actual_profile_complete_number_shift_pair
    (s+t) (add_pos hs ht) (composedCoefficient s t x) (composed_smooth s t hs ht x) (composed_first s t x) f g
  have hv:=SourceClockPhiProfileCoframeRemainingWork.actual_profile_complete_coframe_volume_pair
    (s+t) (add_pos hs ht) (composedCoefficient s t x) (composed_smooth s t hs ht x) (composed_first s t x) f g
  change sourcePair (composedCompleteCore s t hs ht x f)
    (SourceCoframeCovariantSquare.spinRemainder (composedCompleteCore s t hs ht x g))=_ at hs0
  change sourcePair (composedCompleteCore s t hs ht x f)
    (GaussCoframeForm.numberShift (composedCompleteCore s t hs ht x g))=_ at hn
  change sourcePair (composedCompleteCore s t hs ht x f)
    (multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth (composedCompleteCore s t hs ht x g))=_ at hv
  rw [SourceCoframeCovariantSquare.original_coframe_covariant]
  simp only [LinearMap.add_apply,pair_add_r]
  rw [covariant_pair,hs0,hn,hv]
  simp only [localCoframePair,←add_assoc]
  rfl
private def fourPrice (s t:ℝ)(hs:0<s)(ht:0<t):End :=
  ∑k:Fin 4,radialPrice (noiseWeight s t (basis k)) (weight_smooth s t hs ht (basis k))
private theorem noise_square (s t:ℝ)(hs:0<s)(ht:0<t)(z:physicalChart):
    (∑k:Fin 4,(composedNoise s t (basis k) z.val)^2)=
      (1/2:ℝ)*(reciprocalVolume z.val^2-(SourceClockPhiForwardNativeReturn.forwardU (s+t) z.val)^2) := by
  have hS:=actual_covariance_noise_square s hs ⟨_,forward_chart t ht.le z⟩
  have hT:=actual_covariance_noise_square t ht z
  have hU:reciprocalVolume (forwardPoint t z.val)=SourceClockPhiForwardNativeReturn.forwardU t z.val := by
    unfold reciprocalVolume SourceClockPhiForwardNativeReturn.forwardU
    rw [forward_volume t ht.le z]
  have hu:SourceClockPhiForwardNativeReturn.forwardU s (forwardPoint t z.val)=
      SourceClockPhiForwardNativeReturn.forwardU (s+t) z.val := by
    unfold SourceClockPhiForwardNativeReturn.forwardU
    rw [forward_volume t ht.le z]
    congr 1
    ring
  rw [hU,hu] at hS
  simp [basis,composedNoise,zero_noise,Fin.sum_univ_succ]
  linarith [hS,hT]
private theorem four_price_point (s t:ℝ)(hs:0<s)(ht:0<t)(f:QuantumTest)(z:physicalChart):
    fourPrice s t hs ht f z.val=
      Complex.ofReal ((3*sourceTime 0/4)*GaussNativeEnergy.volume z.val*(rowRate (s+t) z.val)^2*
        ((1/2)*(reciprocalVolume z.val^2-(SourceClockPhiForwardNativeReturn.forwardU (s+t) z.val)^2))) • f z.val := by
  apply PiLp.ext
  intro word
  change (∑k:Fin 4,(((3*sourceTime 0/4)*GaussNativeEnergy.volume z.val*(noiseWeight s t (basis k) z.val)^2:ℝ):ℂ)*f z.val word)=_
  have he:(∑k:Fin 4,(3*sourceTime 0/4)*GaussNativeEnergy.volume z.val*(noiseWeight s t (basis k) z.val)^2)=
      (3*sourceTime 0/4)*GaussNativeEnergy.volume z.val*(rowRate (s+t) z.val)^2*
        ((1/2)*(reciprocalVolume z.val^2-(SourceClockPhiForwardNativeReturn.forwardU (s+t) z.val)^2)) := by
    unfold noiseWeight
    simp only [mul_pow,←Finset.mul_sum]
    rw [noise_square s t hs ht z]
    ring
  have hc:=congrArg (fun r:ℝ=>(r:ℂ)*f z.val word) he
  simp only [PiLp.smul_apply,smul_eq_mul]
  push_cast at hc ⊢
  simpa only [Finset.sum_mul] using hc
private def oldPrice (T:ℝ)(hT:0<T):End :=
  kappaAction T hT*(radialPrice (rowRate T) (rowRate_smooth T hT)*kappaAction T hT)
private theorem four_price_identity (s t:ℝ)(hs:0<s)(ht:0<t):
    fourPrice s t hs ht=oldPrice (s+t) (add_pos hs ht)+correctedCoframeCovariance (s+t) (add_pos hs ht) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hF:=four_price_point s t hs ht f ⟨z,hz⟩
    have hC:=actual_corrected_covariance_point (s+t) (add_pos hs ht) f ⟨z,hz⟩
    change correctedCoframeCovariance (s+t) (add_pos hs ht) f z=
      (((3*sourceTime 0/4)*GaussNativeEnergy.volume z*(rowRate (s+t) z)^2*
        ((1/2)*(reciprocalVolume z^2-(SourceClockPhiForwardNativeReturn.forwardU (s+t) z)^2)-heatKappa (s+t) z^2):ℝ):ℂ) • f z at hC
    change fourPrice s t hs ht f z=oldPrice (s+t) (add_pos hs ht) f z+correctedCoframeCovariance (s+t) (add_pos hs ht) f z
    rw [hF,hC]
    apply PiLp.ext
    intro word
    change (((3*sourceTime 0/4)*GaussNativeEnergy.volume z*(rowRate (s+t) z)^2*
      ((1/2)*(reciprocalVolume z^2-(SourceClockPhiForwardNativeReturn.forwardU (s+t) z)^2)):ℝ):ℂ)*f z word=
      (heatKappa (s+t) z:ℂ)*((((3*sourceTime 0/4)*GaussNativeEnergy.volume z*(rowRate (s+t) z)^2:ℝ):ℂ)*
        ((heatKappa (s+t) z:ℂ)*f z word))+
      (((3*sourceTime 0/4)*GaussNativeEnergy.volume z*(rowRate (s+t) z)^2*
        ((1/2)*(reciprocalVolume z^2-(SourceClockPhiForwardNativeReturn.forwardU (s+t) z)^2)-heatKappa (s+t) z^2):ℝ):ℂ)*f z word
    push_cast
    ring
  · have h0 (q:QuantumTest):q z=0 := image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem old_stochastic_radial (T:ℝ)(hT:0<T)(i:Fin 6):
    stochasticCoframeRow T hT i=radialColumn (rowRate T) (rowRate_smooth T hT) i*kappaAction T hT*combinedGenerator := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change ((((forwardRatio T z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
    (momentum i f z word-(3*Complex.I*T:ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
      SourceClockPhiNativeMatchedSource.matchedTester f z word)+
      (Complex.I*1)*(((forwardRatio T z*heatKappa T z/6*volumeGradient z i:ℝ):ℂ)*combinedGenerator f z word))-
    ((((forwardRatio T z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
    (momentum i f z word-(3*Complex.I*T:ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
      SourceClockPhiNativeMatchedSource.matchedTester f z word)+
      (Complex.I*0)*(((forwardRatio T z*heatKappa T z/6*volumeGradient z i:ℝ):ℂ)*combinedGenerator f z word))=
    Complex.I*((rowRate T z:ℂ)*((volumeGradient z i:ℂ)*((heatKappa T z:ℂ)*combinedGenerator f z word)))
  unfold rowRate
  push_cast
  ring
private theorem old_stochastic_pair (T:ℝ)(hT:0<T)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,sourcePair (stochasticCoframeRow T hT i f)
      (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow T hT j g)))=
        sourcePair (combinedGenerator f) (oldPrice T hT (combinedGenerator g)) := by
  simp_rw [old_stochastic_radial]
  simp only [Module.End.mul_apply]
  rw [actual_radial_covariance_pair]
  exact (multiply_pair _ _ _ _).symm
private theorem mean_rows_identity (s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest):
    meanRows s t hs ht f g=
      (∑i:Fin 6,∑j:Fin 6,(sourcePair (deterministicCoframeRow (s+t) (add_pos hs ht) i f)
        (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow (s+t) (add_pos hs ht) j g))+
        sourcePair (stochasticCoframeRow (s+t) (add_pos hs ht) i f)
        (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow (s+t) (add_pos hs ht) j g))))+
      sourcePair (combinedGenerator f) (correctedCoframeCovariance (s+t) (add_pos hs ht) (combinedGenerator g)) := by
  let N (i j:Fin 6)(k:Fin 4):ℂ:=sourcePair (noiseRow s t hs ht (basis k) i f)
      (SourceCoframeCovariantAction.metricAction i j (noiseRow s t hs ht (basis k) j g))
  have hN (k:Fin 4): (∑i:Fin 6,∑j:Fin 6,N i j k)=sourcePair (combinedGenerator f)
      (radialPrice (noiseWeight s t (basis k)) (weight_smooth s t hs ht (basis k)) (combinedGenerator g)) :=
    actual_radial_covariance_pair _ _ _ _
  have hsum:(∑i:Fin 6,∑j:Fin 6,∑k:Fin 4,N i j k)=∑k:Fin 4,∑i:Fin 6,∑j:Fin 6,N i j k := by
    calc
      _ = ∑i:Fin 6,∑k:Fin 4,∑j:Fin 6,N i j k := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hp:(∑k:Fin 4,sourcePair (combinedGenerator f)
      (radialPrice (noiseWeight s t (basis k)) (weight_smooth s t hs ht (basis k)) (combinedGenerator g)))=
        sourcePair (combinedGenerator f) (fourPrice s t hs ht (combinedGenerator g)) := by
    simp only [fourPrice,LinearMap.sum_apply,sourcePair,map_sum,inner_sum]
  unfold meanRows
  change (∑i:Fin 6,∑j:Fin 6,(sourcePair (deterministicCoframeRow (s+t) (add_pos hs ht) i f)
      (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow (s+t) (add_pos hs ht) j g))+
        ∑k:Fin 4,N i j k))=_
  simp only [Finset.sum_add_distrib]
  rw [hsum]
  simp_rw [hN]
  rw [hp,four_price_identity,old_stochastic_pair]
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right]
  ring

theorem actual_composed_coframe_gaussian (s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:Four=>sourcePair (composedCompleteCore s t hs ht x f)
      (GaussCoframeForm.coframeAction (composedCompleteCore s t hs ht x g))) γ4 ∧
    (∫x:Four,sourcePair (composedCompleteCore s t hs ht x f)
      (GaussCoframeForm.coframeAction (composedCompleteCore s t hs ht x g)) ∂γ4)=
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore (s+t) (add_pos hs ht) x.1 x.2 f)
      (GaussCoframeForm.coframeAction (correctedCompleteCore (s+t) (add_pos hs ht) x.1 x.2 g)) ∂γ.prod γ) := by
  have h:=rows_gaussian s t hs ht f g
  have hc:Integrable (fun _:Four=>localCoframePair (s+t) (add_pos hs ht) f g) γ4:=integrable_const _
  refine ⟨(h.1.add hc).congr (Eventually.of_forall (fun x=>(composed_coframe_source s t hs ht x f g).symm)),?_⟩
  simp_rw [composed_coframe_source]
  rw [integral_add h.1 hc,h.2,mean_rows_identity,
    (actual_corrected_coframe_gaussian (s+t) (add_pos hs ht) f g).2,
    (actual_complete_coframe_gaussian (s+t) (add_pos hs ht) f g).2]
  simp only [integral_const,probReal_univ,one_smul]
  ring
end LowEnergy.ClockPhiComposedCoframeGaussianWork
