import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPositiveCoframeWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0Closed
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedHamiltonianWorkGenerator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PositiveClockGenerator
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeDilation
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore ClockPhiHeatComparisonWork
open ClockPhiHeatCorrectedCovarianceSource SourceClockPhiProfileCoframeReturn SourceClockPhiProfileCoframeRemainingWork
open SourceClockPhiProfileNativeReturn SourceClockPhiProfileLocalNativeReturn SourceClockPhiCorrectedGaussianPair
open SourceClockPhiCorrectedWeightTransport SourceClockPhiForwardNativeReturn SourceClockPhiCombinedScalePressure
open SourceClockPhiOriginalGaussianH0FirstJet SourceClockPhiOriginalGaussianH0Closed SourceScalarVirialBulk
open SourceClockPhiHeatLocalNativeGaussian
open ClockPhiHeatCorrectedCoframeWork MeasureTheory Filter
open ClockPhiHeatRadialCovariancePair ClockPhiHeatCoframeHamiltonianWork GaussCoframeCore
open SourceClockPhiCompleteHeatHamiltonianSource
open scoped ContDiff Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
attribute [local irreducible] sourcePair embed GaussDiagonalHistory.diagonalAction
private theorem coeff_first(t ξ η:ℝ)(x y:SourceCoordinateSlice)(h:x.1=y.1):
    correctedCoefficient t ξ η x=correctedCoefficient t ξ η y:=by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  dsimp at h
  subst y₁
  rfl
private theorem U_pair(f g:QuantumTest):sourcePair f (inverseVolumeAction g)=sourcePair (inverseVolumeAction f) g:=
  multiply_pair _ _ _ _
private theorem forwardU_pair(t:ℝ)(ht:0<t)(f g:QuantumTest):
    sourcePair f (forwardUAction t ht.le g)=sourcePair (forwardUAction t ht.le f) g:=multiply_pair _ _ _ _
private theorem U_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    inverseVolumeAction (correctedCompleteCore t ht ξ η f)=
      correctedCompleteCore t ht ξ η (forwardUAction t ht.le f):=
  LinearMap.congr_fun (actual_corrected_complete_inverse_volume t ht ξ η) f
private theorem D_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    combinedGenerator (correctedCompleteCore t ht ξ η f)=
      correctedCompleteCore t ht ξ η (combinedGenerator f):=
  LinearMap.congr_fun (actual_corrected_complete_generator_commute t ht ξ η).eq f
private theorem complete_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (correctedCompleteCore t ht ξ η g)=
      sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) g):=by
  change sourcePair (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)))
    (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) g)))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact ClockPhiConservativeHeatSource.clockProfileAction_pair _ _ _ _ _ _
private theorem inverse_sector(t:ℝ)(ht:0<t)(X:End)(p q:ℝ)
    (law:∀ξ η:ℝ,∀f g:QuantumTest,
      sourcePair (correctedCompleteCore t ht ξ η f) (X (correctedCompleteCore t ht ξ η g))=
        sourcePair f (correctedProfileWeight t ht p q ξ η (X g))) (f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g)))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g))) ∂γ.prod γ)=
      sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (p+q*(q-3)/18) (X g)):=by
  have he(x:ℝ×ℝ):sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g)))=
      sourcePair (forwardUAction t ht.le f) (correctedProfileWeight t ht p q x.1 x.2 (X g)):=by
    rw [U_pair,U_return,law]
  simpa only [he] using
    actual_corrected_gaussian_weighted_source_pair t ht p q (forwardUAction t ht.le f) (X g)

def nativePositiveMean(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  (-14:ℂ)*sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (-7/9) (scalarKinetic g))
  +22*sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (11/9) (gaugeKinetic g))
  -2*sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (-1/9) (GaussMatterCore.matterAction g))
  +34*sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (17/9) (centeredAction g))
  -56*sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (14/9) (vacuumLinearAction g))
  +24*sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (12/9) (vacuumConstantAction g))
  +12*sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (6/9) (scalarSpatialAction g))
  +16*sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (8/9) (magneticAction g))

theorem actual_corrected_native_jet_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>nativePairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,nativePairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g) ∂γ.prod γ)=nativePositiveMean t ht f g:=by
  have h1:=inverse_sector t ht scalarKinetic (-2/3) (2)
    (fun ξ η p q=>actual_complete_profile_scalar_source t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have h2:=inverse_sector t ht gaugeKinetic (2/3) (-2)
    (fun ξ η p q=>actual_complete_profile_gauge_source t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have h3:=inverse_sector t ht GaussMatterCore.matterAction (0) (1)
    (fun ξ η p q=>actual_profile_complete_matter_pair t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have h4:=inverse_sector t ht centeredAction (4/3) (-2)
    (fun ξ η p q=>actual_profile_complete_centered_pair t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have h5:=inverse_sector t ht vacuumLinearAction (4/3) (-1)
    (fun ξ η p q=>actual_profile_complete_vacuum_linear_pair t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have h6:=inverse_sector t ht vacuumConstantAction (4/3) (0)
    (fun ξ η p q=>actual_profile_complete_vacuum_constant_pair t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have h7:=inverse_sector t ht scalarSpatialAction (2/3) (0)
    (fun ξ η p q=>actual_profile_complete_signed_spatial_pair t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have h8:=inverse_sector t ht magneticAction (2/3) (4)
    (fun ξ η p q=>actual_profile_complete_magnetic_pair t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have H1:=h1.1.const_mul (-14:ℂ)
  have H2:=h2.1.const_mul (22:ℂ)
  have H3:=h3.1.const_mul (-2:ℂ)
  have H4:=h4.1.const_mul (34:ℂ)
  have H5:=h5.1.const_mul (56:ℂ)
  have H6:=h6.1.const_mul (24:ℂ)
  have H7:=h7.1.const_mul (12:ℂ)
  have H8:=h8.1.const_mul (16:ℂ)
  refine ⟨(((((((H1.add H2).add H3).add H4).sub H5).add H6).add H7).add H8),?_⟩
  unfold nativePairJet
  erw [integral_add ((((((H1.add H2).add H3).add H4).sub H5).add H6).add H7) H8,
    integral_add (((((H1.add H2).add H3).add H4).sub H5).add H6) H7,
    integral_add ((((H1.add H2).add H3).add H4).sub H5) H6,
    integral_sub (((H1.add H2).add H3).add H4) H5,
    integral_add ((H1.add H2).add H3) H4,integral_add (H1.add H2) H3,integral_add H1 H2]
  simp only [integral_const_mul,h1.2,h2.2,h3.2,h4.2,h5.2,h6.2,h7.2,h8.2]
  norm_num [nativePositiveMean]; ring

private theorem actual_corrected_native_jet_integrable(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>nativePairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g)) (γ.prod γ):=
  (actual_corrected_native_jet_gaussian t ht f g).1

private abbrev localVolumeAction:End:=multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth
private theorem local_inverse_constant(t:ℝ)(ht:0<t)(X:End)(Y:QuantumTest→QuantumTest→ℂ)
    (law:∀ξ η:ℝ,∀f g:QuantumTest,
      sourcePair (correctedCompleteCore t ht ξ η f) (X (correctedCompleteCore t ht ξ η g))=Y f g) (f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g)))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g))) ∂γ.prod γ)=
      Y (forwardUAction t ht.le f) g:=by
  have he(x:ℝ×ℝ):sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g)))=Y (forwardUAction t ht.le f) g:=by
    rw [U_pair,U_return,law]
  refine ⟨?_,?_⟩
  · simpa only [he] using (integrable_const (μ:=γ.prod γ) (Y (forwardUAction t ht.le f) g))
  · simp only [he,integral_const,probReal_univ,one_smul]


def localPositiveMean(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  (-12:ℂ)*sourcePair (forwardUAction t ht.le f)
    (gaussianProfileWeight t ht (-2/3) (SourceCoframeCovariantSquare.spinRemainder g))+
  (-12:ℂ)*sourcePair (forwardUAction t ht.le f)
    (gaussianProfileWeight t ht (-2/3) (GaussCoframeForm.numberShift g))+
  (24:ℂ)*sourcePair (forwardUAction t ht.le f)
    (gaussianProfileWeight t ht (4/3) (localVolumeAction g))

theorem actual_corrected_local_jet_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>localPairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,localPairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g) ∂γ.prod γ)=localPositiveMean t ht f g:=by
  have h1:=local_inverse_constant t ht SourceCoframeCovariantSquare.spinRemainder
    (fun p q=>sourcePair p (gaussianProfileWeight t ht (-2/3) (SourceCoframeCovariantSquare.spinRemainder q)))
    (fun ξ η p q=>actual_profile_complete_spin_remainder_pair t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have h2:=local_inverse_constant t ht GaussCoframeForm.numberShift
    (fun p q=>sourcePair p (gaussianProfileWeight t ht (-2/3) (GaussCoframeForm.numberShift q)))
    (fun ξ η p q=>actual_profile_complete_number_shift_pair t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have h3:=local_inverse_constant t ht localVolumeAction
    (fun p q=>sourcePair p (gaussianProfileWeight t ht (4/3) (localVolumeAction q)))
    (fun ξ η p q=>actual_profile_complete_coframe_volume_pair t ht (correctedCoefficient t ξ η)
      (coefficient_smooth t ht ξ η) (coeff_first t ξ η) p q) f g
  have H1:=h1.1.const_mul (-12:ℂ)
  have H2:=h2.1.const_mul (-12:ℂ)
  have H3:=h3.1.const_mul (24:ℂ)
  refine ⟨(H1.add H2).add H3,?_⟩
  unfold localPairJet
  erw [integral_add (H1.add H2) H3,integral_add H1 H2]
  simp only [integral_const_mul,h1.2,h2.2,h3.2,localPositiveMean]

private theorem actual_corrected_local_jet_integrable(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>localPairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g)) (γ.prod γ):=
  (actual_corrected_local_jet_gaussian t ht f g).1

private theorem inverse_cube_volume(f:QuantumTest):
    inverseVolumeAction (inverseVolumeAction (inverseVolumeAction (volumeAction f)))=
      inverseVolumeAction (inverseVolumeAction f):=by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume z:ℂ) • ((reciprocalVolume z:ℂ) • ((reciprocalVolume z:ℂ) • ((volume z:ℂ) • f z)))=
      (reciprocalVolume z:ℂ) • ((reciprocalVolume z:ℂ) • f z)
    have hv:reciprocalVolume z*volume z=1:=inv_mul_cancel₀ (volume_pos ⟨z,hz⟩).ne'
    have hc:(reciprocalVolume z:ℂ) • ((volume z:ℂ) • f z)=f z:=by
      rw [smul_smul,←Complex.ofReal_mul,hv,Complex.ofReal_one,one_smul]
    rw [hc]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change (reciprocalVolume z:ℂ) • ((reciprocalVolume z:ℂ) • ((reciprocalVolume z:ℂ) • ((volume z:ℂ) • f z)))=
      (reciprocalVolume z:ℂ) • ((reciprocalVolume z:ℂ) • f z)
    simp only [hf,smul_zero]

def stochasticPositiveMean(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  (sourceTime 0/48:ℂ)*((18:ℂ)*sourcePair
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (combinedGenerator f))
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
      (forwardUAction t ht.le (forwardUAction t ht.le (combinedGenerator g)))))

theorem actual_corrected_stochastic_jet_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>stochasticPairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,stochasticPairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g) ∂γ.prod γ)=stochasticPositiveMean t ht f g:=by
  have he(x:ℝ×ℝ):stochasticPairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g)=
      (sourceTime 0/48:ℂ)*((18:ℂ)*sourcePair
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (combinedGenerator f))
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
          (forwardUAction t ht.le (forwardUAction t ht.le (combinedGenerator g))))):=by
    simp only [stochasticPairJet,inverse_cube_volume,D_return,U_return,complete_pair]
  refine ⟨?_,?_⟩
  · simpa only [he,stochasticPositiveMean] using (integrable_const (μ:=γ.prod γ) (stochasticPositiveMean t ht f g))
  · simp only [he,integral_const,probReal_univ,one_smul,stochasticPositiveMean]

private theorem actual_corrected_stochastic_jet_integrable(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>stochasticPairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g)) (γ.prod γ):=
  (actual_corrected_stochastic_jet_gaussian t ht f g).1

theorem actual_corrected_Q_H0_integrable(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      ((SourceClockPhiMatchedDiffusionSource.completeCurrent GaussDiagonalHistory.diagonalAction)
        (correctedCompleteCore t ht x.1 x.2 g))) (γ.prod γ):=by
  have h:=(((actual_corrected_native_jet_integrable t ht f g).add
    (actual_corrected_deterministic_jet_integrable t ht f g)).add
    (actual_corrected_stochastic_jet_integrable t ht f g)).add
    (actual_corrected_local_jet_integrable t ht f g)
  have he(x:ℝ×ℝ):wholePairJet (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 g)=
      sourcePair (correctedCompleteCore t ht x.1 x.2 f)
        ((SourceClockPhiMatchedDiffusionSource.completeCurrent GaussDiagonalHistory.diagonalAction)
          (correctedCompleteCore t ht x.1 x.2 g)):=actual_original_whole_pair_jet_Q_H0 _ _
  exact h.congr (Eventually.of_forall he)


def positiveGeneratorMean(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  nativePositiveMean t ht f g+deterministicPositiveMean t ht f g+
    stochasticPositiveMean t ht f g+localPositiveMean t ht f g

theorem actual_corrected_Q_H0_gaussian_source(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      ((SourceClockPhiMatchedDiffusionSource.completeCurrent GaussDiagonalHistory.diagonalAction)
        (correctedCompleteCore t ht x.1 x.2 g))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      ((SourceClockPhiMatchedDiffusionSource.completeCurrent GaussDiagonalHistory.diagonalAction)
        (correctedCompleteCore t ht x.1 x.2 g)) ∂γ.prod γ)=positiveGeneratorMean t ht f g:=by
  refine ⟨actual_corrected_Q_H0_integrable t ht f g,?_⟩
  have hN:=actual_corrected_native_jet_gaussian t ht f g
  have hD:=actual_corrected_deterministic_jet_gaussian t ht f g
  have hS:=actual_corrected_stochastic_jet_gaussian t ht f g
  have hL:=actual_corrected_local_jet_gaussian t ht f g
  simp_rw [←actual_original_whole_pair_jet_Q_H0]
  unfold wholePairJet positiveGeneratorMean
  erw [integral_add ((hN.1.add hD.1).add hS.1) hL.1,
    integral_add (hN.1.add hD.1) hS.1,integral_add hN.1 hD.1,hN.2,hD.2,hS.2,hL.2]


private theorem actual_corrected_zero_jet(f g:QuantumTest):
    Tendsto (fun h:ℝ=>if hh:0<h then (h:ℂ)⁻¹*
      ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianWork h hh f g else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 (sourcePair f ((SourceClockPhiMatchedDiffusionSource.completeCurrent GaussDiagonalHistory.diagonalAction) g))):=by
  have hA:=ClockPhiCorrectedCovarianceWeakJet.actual_corrected_hamiltonian_first_order_agreement f g
  have hO:=actual_original_whole_gaussian_first_jet_Q_H0 f g
  have h:=hA.add hO
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp:0<t:=ht
  simp only [dif_pos hp,ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianWork,
    ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianPair]
  ring

def positiveTimeQuotient(t:ℝ)(ht:0<t)(f g:QuantumTest)(h:ℝ)(x:ℝ×ℝ):ℂ:=
  if hh:0<h then (h:ℂ)⁻¹*ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianWork h hh
    (correctedCompleteCore t ht x.1 x.2 f) (correctedCompleteCore t ht x.1 x.2 g) else 0

theorem actual_corrected_positive_time_work_source(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      ((SourceClockPhiMatchedDiffusionSource.completeCurrent GaussDiagonalHistory.diagonalAction)
        (correctedCompleteCore t ht x.1 x.2 g))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      ((SourceClockPhiMatchedDiffusionSource.completeCurrent GaussDiagonalHistory.diagonalAction)
        (correctedCompleteCore t ht x.1 x.2 g)) ∂γ.prod γ)=positiveGeneratorMean t ht f g ∧
    (∀x:ℝ×ℝ,Tendsto (fun h=>positiveTimeQuotient t ht f g h x) (𝓝[>] (0:ℝ))
      (𝓝 (sourcePair (correctedCompleteCore t ht x.1 x.2 f)
        ((SourceClockPhiMatchedDiffusionSource.completeCurrent GaussDiagonalHistory.diagonalAction)
          (correctedCompleteCore t ht x.1 x.2 g))))) ∧
    ∀h:ℝ,∀hh:0<h,Integrable (positiveTimeQuotient t ht f g h) (γ.prod γ) ∧
      (h:ℂ)⁻¹*(ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianPair (t+h) (add_pos ht hh) f g-
        ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianPair t ht f g)=
          ∫x:ℝ×ℝ,positiveTimeQuotient t ht f g h x ∂γ.prod γ:=by
  have hQ:=actual_corrected_Q_H0_gaussian_source t ht f g
  refine ⟨hQ.1,hQ.2,?_,?_⟩
  · intro x
    exact actual_corrected_zero_jet _ _
  · intro h hh
    have hw:=ClockPhiCorrectedHamiltonianWorkGenerator.actual_corrected_hamiltonian_finite_work_increment h t hh ht f g
    refine ⟨?_,?_⟩
    · exact (hw.1.const_mul (h:ℂ)⁻¹).congr (Eventually.of_forall (fun x=>by
        simp only [positiveTimeQuotient,dif_pos hh]))
    · simp only [positiveTimeQuotient,dif_pos hh]
      rw [integral_const_mul,←hw.2]
      simp only [add_comm t h]


private theorem ratioPower_smooth(t:ℝ)(ht:0<t)(a:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun w:SourceCoordinateSlice=>(forwardRatio t w)^a) z.val:=by
  have hr:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact hr.rpow_const_of_ne (forward_ratio_pos t ht.le z).ne'
private theorem ratio_cocycle(s h:ℝ)(hs:0<s)(_hh:0<h)(z:physicalChart):
    forwardRatio h (forwardPoint s z.val)*forwardRatio s z.val=forwardRatio (s+h) z.val:=by
  unfold forwardRatio
  rw [forward_volume s hs.le z]
  have hv:(volume z.val)≠0:=(volume_pos z).ne'
  have hw:(volume z.val+18*s)≠0:=by linarith [volume_pos z]
  field_simp [hv,hw]
  ring
private theorem weighted_pair_rebase(s h:ℝ)(hs:0<s)(hh:0<h)(a:ℝ)(f g:QuantumTest):
    sourcePair (sourceForwardCore s hs.le f)
      (gaussianProfileWeight h hh a (sourceForwardCore s hs.le (gaussianProfileWeight s hs a g)))=
      sourcePair f (gaussianProfileWeight (s+h) (add_pos hs hh) a g):=by
  let b:SourceCoordinateSlice→ℝ:=fun z=>(forwardRatio h z)^a
  let hb:=ratioPower_smooth h hh a
  let c:SourceCoordinateSlice→ℝ:=fun z=>b (forwardPoint s z)
  let hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val:=fun z=>
    ContDiffAt.comp (f:=forwardPoint s) z.val (hb ⟨_,forward_chart s hs.le z⟩) (forward_smooth s hs.le z)
  have hm:=SourceClockPhiForwardGeneratorTransport.actual_forward_multiplier_transport s hs.le b hb
  change gaussianProfileWeight h hh a*sourceForwardCore s hs.le=
    sourceForwardCore s hs.le*multiply c hc at hm
  have he:multiply c hc*gaussianProfileWeight s hs a=gaussianProfileWeight (s+h) (add_pos hs hh) a:=by
    apply LinearMap.ext
    intro q
    apply DFunLike.ext
    intro z
    by_cases hz:z∈physicalChart
    · change (((forwardRatio h (forwardPoint s z))^a:ℝ):ℂ) • ((((forwardRatio s z)^a:ℝ):ℂ) • q z)=
        (((forwardRatio (s+h) z)^a:ℝ):ℂ) • q z
      rw [smul_smul,←Complex.ofReal_mul,
        ←Real.mul_rpow (forward_ratio_pos h hh.le ⟨_,forward_chart s hs.le ⟨z,hz⟩⟩).le
          (forward_ratio_pos s hs.le ⟨z,hz⟩).le,ratio_cocycle s h hs hh ⟨z,hz⟩]
    · have hq:q z=0:=image_eq_zero_of_notMem_tsupport (fun hz'=>hz (q.tsupport_subset hz'))
      change (c z:ℂ) • ((((forwardRatio s z)^a:ℝ):ℂ) • q z)=
        (((forwardRatio (s+h) z)^a:ℝ):ℂ) • q z
      simp only [hq,smul_zero]
  have hf:=LinearMap.congr_fun hm (gaussianProfileWeight s hs a g)
  have hg:=LinearMap.congr_fun he g
  simp only [Module.End.mul_apply] at hf hg
  rw [hg] at hf
  rw [hf,SourceClockPhiCoframeForwardPair.actual_forward_core_pair]

/-- The original compact source kernel generates the positive-clock slope by its exact forward cocycle. -/
theorem actual_gaussian_weighted_positive_time_jet(s:ℝ)(hs:0<s)(a:ℝ)(f g:QuantumTest):
    Tendsto (fun h:ℝ=>if hh:0<h then (h:ℂ)⁻¹*
      (sourcePair f (gaussianProfileWeight (s+h) (add_pos hs hh) a g)-
        sourcePair f (gaussianProfileWeight s hs a g)) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 ((18*a:ℂ)*sourcePair (forwardUAction s hs.le f) (gaussianProfileWeight s hs a g))):=by
  have hz:=actual_gaussian_weighted_source_pair_first_jet a
    (sourceForwardCore s hs.le f) (sourceForwardCore s hs.le (gaussianProfileWeight s hs a g))
  have htarget:sourcePair (sourceForwardCore s hs.le f)
      (inverseVolumeAction (sourceForwardCore s hs.le (gaussianProfileWeight s hs a g)))=
      sourcePair (forwardUAction s hs.le f) (gaussianProfileWeight s hs a g):=by
    have hu:=LinearMap.congr_fun (actual_forward_U_return s hs.le) (gaussianProfileWeight s hs a g)
    simp only [Module.End.mul_apply] at hu
    rw [hu,SourceClockPhiCoframeForwardPair.actual_forward_core_pair,forwardU_pair s hs]
  rw [htarget] at hz
  apply hz.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp:0<h:=hh
  simp only [dif_pos hp,weighted_pair_rebase s h hs hp,
    SourceClockPhiCoframeForwardPair.actual_forward_core_pair]

private def powerRowRate(t:ℝ)(z:SourceCoordinateSlice):ℝ:=
  ((forwardRatio t z)^(1/3:ℝ))⁻¹*forwardRatio t z/6
private theorem powerRowRate_smooth(t:ℝ)(ht:0<t)(z:physicalChart):
    ContDiffAt ℝ ∞ (powerRowRate t) z.val:=by
  have hr:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  have hp:0<(forwardRatio t z.val)^(1/3:ℝ):=Real.rpow_pos_of_pos (forward_ratio_pos t ht.le z) _
  exact (((hr.rpow_const_of_ne (forward_ratio_pos t ht.le z).ne').inv hp.ne').mul hr).div_const 6
private theorem powerRowRate_square(t:ℝ)(ht:0<t)(z:physicalChart):
    powerRowRate t z.val^2=(forwardRatio t z.val)^(4/3:ℝ)/36:=by
  have hr:=forward_ratio_pos t ht.le z
  have hs:((forwardRatio t z.val)^(1/3:ℝ))⁻¹*forwardRatio t z.val=
      (forwardRatio t z.val)^(2/3:ℝ):=by
    rw [show (2/3:ℝ)=1-(1/3:ℝ) by norm_num,Real.rpow_sub hr]
    simp only [Real.rpow_one,div_eq_mul_inv,mul_comm]
  have hq:((forwardRatio t z.val)^(2/3:ℝ))^2=(forwardRatio t z.val)^(4/3:ℝ):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    congr 1
    norm_num
  change (((forwardRatio t z.val)^(1/3:ℝ))⁻¹*forwardRatio t z.val/6)^2=_
  calc
    _=(((forwardRatio t z.val)^(1/3:ℝ))⁻¹*forwardRatio t z.val)^2/36:=by ring
    _=_:=by rw [hs,hq]
private theorem old_stochastic_radial(t:ℝ)(ht:0<t)(i:Fin 6):
    stochasticCoframeRow t ht i=radialColumn (powerRowRate t) (powerRowRate_smooth t ht) i*kappaAction t ht*combinedGenerator:=by
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
    Complex.I*((powerRowRate t z:ℂ)*((volumeGradient z i:ℂ)*((heatKappa t z:ℂ)*combinedGenerator f z word)))
  unfold powerRowRate
  push_cast
  ring
private theorem old_stochastic_pair(t:ℝ)(ht:0<t)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,sourcePair (stochasticCoframeRow t ht i f)
      (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow t ht j g)))=
      sourcePair (combinedGenerator f)
        ((kappaAction t ht*(radialPrice (powerRowRate t) (powerRowRate_smooth t ht)*kappaAction t ht)) (combinedGenerator g)):=by
  simp_rw [old_stochastic_radial]
  simp only [Module.End.mul_apply]
  rw [actual_radial_covariance_pair]
  exact (multiply_pair _ _ _ _).symm

private def powerNoiseWeight(t ξ η:ℝ)(z:SourceCoordinateSlice):ℝ:=
  powerRowRate t z*covarianceNoise t ξ η z
private theorem powerNoiseWeight_smooth(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (powerNoiseWeight t ξ η) z.val:=
  (powerRowRate_smooth t ht z).mul (noise_smooth t ht ξ η z)
private theorem corrected_noise_power_scalar(t:ℝ)(ht:0<t)(z:physicalChart):
    (3*sourceTime 0/4)*volume z.val*(powerNoiseWeight t 1 0 z.val)^2+
      (3*sourceTime 0/4)*volume z.val*(powerNoiseWeight t 0 1 z.val)^2=
      (sourceTime 0/96)*reciprocalVolume z.val*
        ((forwardRatio t z.val)^(4/3:ℝ)-(forwardRatio t z.val)^(-2/3:ℝ)):=by
  have hn:=actual_covariance_noise_square t ht z
  have hr:=forward_ratio_pos t ht.le z
  have hp:(forwardRatio t z.val)^(4/3:ℝ)=
      (forwardRatio t z.val)^(-2/3:ℝ)*(forwardRatio t z.val)^2:=by
    rw [←Real.rpow_natCast,←Real.rpow_add hr]
    norm_num
  have hv:(volume z.val)≠0:=(volume_pos z).ne'
  have hw:(volume z.val+18*t)≠0:=by linarith [volume_pos z]
  calc
    _=(3*sourceTime 0/4)*volume z.val*(powerRowRate t z.val)^2*
        (covarianceNoise t 1 0 z.val^2+covarianceNoise t 0 1 z.val^2):=by
      unfold powerNoiseWeight
      ring
    _=_:=by
      rw [hn,powerRowRate_square t ht z,hp]
      unfold reciprocalVolume forwardU forwardRatio
      field_simp [hv,hw]
      ring
private theorem corrected_noise_power_operator(t:ℝ)(ht:0<t):
    radialPrice (powerNoiseWeight t 1 0) (powerNoiseWeight_smooth t ht 1 0)+
      radialPrice (powerNoiseWeight t 0 1) (powerNoiseWeight_smooth t ht 0 1)=
      (sourceTime 0/96:ℂ) • (inverseVolumeAction*
        (gaussianProfileWeight t ht (4/3)-gaussianProfileWeight t ht (-2/3))):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (((3*sourceTime 0/4)*volume z*(powerNoiseWeight t 1 0 z)^2:ℝ):ℂ) • f z+
        (((3*sourceTime 0/4)*volume z*(powerNoiseWeight t 0 1 z)^2:ℝ):ℂ) • f z=
      (sourceTime 0/96:ℂ) • ((reciprocalVolume z:ℂ) •
        ((((forwardRatio t z)^(4/3:ℝ):ℝ):ℂ) • f z-(((forwardRatio t z)^(-2/3:ℝ):ℝ):ℂ) • f z))
    have h:=congrArg (fun r:ℝ=>(r:ℂ) • f z) (corrected_noise_power_scalar t ht ⟨z,hz⟩)
    simpa only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_div,
      Complex.ofReal_ofNat,add_smul,sub_smul,mul_smul] using h
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

def noisePowerPair(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  (sourceTime 0/96:ℂ)*(sourcePair (inverseVolumeAction (combinedGenerator f))
    (gaussianProfileWeight t ht (4/3) (combinedGenerator g))-
      sourcePair (inverseVolumeAction (combinedGenerator f))
        (gaussianProfileWeight t ht (-2/3) (combinedGenerator g)))

theorem actual_corrected_stochastic_power_pair(t:ℝ)(ht:0<t)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,sourcePair (stochasticCoframeRow t ht i f)
      (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow t ht j g)))+
      sourcePair (combinedGenerator f) (correctedCoframeCovariance t ht (combinedGenerator g))=
      noisePowerPair t ht f g:=by
  rw [old_stochastic_pair]
  have hc:correctedCoframeCovariance t ht=
      radialPrice (powerNoiseWeight t 1 0) (powerNoiseWeight_smooth t ht 1 0)+
        radialPrice (powerNoiseWeight t 0 1) (powerNoiseWeight_smooth t ht 0 1)-
          kappaAction t ht*(radialPrice (powerRowRate t) (powerRowRate_smooth t ht)*kappaAction t ht):=rfl
  have hcancel(p q r:QuantumTest):sourcePair p r+sourcePair p (q-r)=sourcePair p q:=by
    simp only [sourcePair,map_sub,inner_sub_right]
    ring
  rw [hc,LinearMap.sub_apply,hcancel,corrected_noise_power_operator]
  change sourcePair (combinedGenerator f)
    ((sourceTime 0/96:ℂ) • inverseVolumeAction
      (gaussianProfileWeight t ht (4/3) (combinedGenerator g)-
        gaussianProfileWeight t ht (-2/3) (combinedGenerator g)))=noisePowerPair t ht f g
  have hsmul(p q:QuantumTest)(c:ℂ):sourcePair p (c • q)=c*sourcePair p q:=by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [hsmul,U_pair]
  simp only [noisePowerPair,sourcePair,map_sub,inner_sub_right]

private theorem deterministic_row_source(t:ℝ)(ht:0<t)(i:Fin 6):
    deterministicCoframeRow t ht i=
      gaussianProfileWeight t ht (-1/3)*
        (SourceCoframeCovariantAction.covariantMomentum i+(t:ℂ) • coframeDriftColumn i):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  swap
  · have hzero(q:QuantumTest):q z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm
  apply PiLp.ext
  intro word
  simp only [deterministicCoframeRow,covariantHeatRow,
    ClockPhiHeatHamiltonianWork.heatCoframeRow,
    SourceCoframeCovariantAction.covariantMomentum,coframeDriftColumn,
    Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply]
  simp only [Complex.ofReal_zero,mul_zero,zero_smul,add_zero]
  change ((((forwardRatio t z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
      (GaussCoframeCore.momentum i f z word-(3*Complex.I*t:ℂ)*
        (((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
          SourceClockPhiNativeMatchedSource.matchedTester f z word))+
      (((forwardRatio t z)^(-1/3:ℝ):ℝ):ℂ)*
        (SourceCoframeCovariantAction.connectionAction i f z word)=
      (((forwardRatio t z)^(-1/3:ℝ):ℝ):ℂ)*
        (GaussCoframeCore.momentum i f z word+
          SourceCoframeCovariantAction.connectionAction i f z word+
          (t:ℂ)*((-3*Complex.I:ℂ)*
            (((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
              SourceClockPhiNativeMatchedSource.matchedTester f z word)))
  have hr:((forwardRatio t z)^(1/3:ℝ))⁻¹=(forwardRatio t z)^(-1/3:ℝ):=
    by simpa only [neg_div] using (Real.rpow_neg (forward_ratio_pos t ht.le ⟨z,hz⟩).le (1/3:ℝ)).symm
  rw [hr]
  ring

private theorem weighted_metric_pair(t:ℝ)(ht:0<t)(a:ℝ)(i j:Fin 6)(f g:QuantumTest):
    sourcePair (gaussianProfileWeight t ht a f)
      (SourceCoframeCovariantAction.metricAction i j (gaussianProfileWeight t ht a g))=
    sourcePair f (gaussianProfileWeight t ht (2*a)
      (SourceCoframeCovariantAction.metricAction i j g)):=by
  let M:=SourceCoframeCovariantAction.metricAction i j
  have hp:= (GaussNativeForm.multiply_pair
    (fun z=>(forwardRatio t z)^a)
    (ratioPower_smooth t ht a)
    f (M (gaussianProfileWeight t ht a g))).symm
  change sourcePair (gaussianProfileWeight t ht a f)
    (M (gaussianProfileWeight t ht a g))=
    sourcePair f (gaussianProfileWeight t ht a (M (gaussianProfileWeight t ht a g))) at hp
  rw [hp]
  congr 1
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (((forwardRatio t z)^a:ℝ):ℂ) •
      ((GaussCoframeKinetic.coefficient i j z:ℂ) •
        ((((forwardRatio t z)^a:ℝ):ℂ) • g z))=
      (((forwardRatio t z)^(2*a):ℝ):ℂ) •
        ((GaussCoframeKinetic.coefficient i j z:ℂ) • g z)
    have hr:((forwardRatio t z)^a)^2=(forwardRatio t z)^(2*a):=by
      rw [←Real.rpow_natCast,←Real.rpow_mul (forward_ratio_pos t ht.le ⟨z,hz⟩).le]
      congr 1
      ring
    have he:(forwardRatio t z)^a*(GaussCoframeKinetic.coefficient i j z*(forwardRatio t z)^a)=
        (forwardRatio t z)^(2*a)*GaussCoframeKinetic.coefficient i j z:=by
      calc
        _=((forwardRatio t z)^a)^2*GaussCoframeKinetic.coefficient i j z:=by ring
        _=_:=by rw [hr]
    simp only [smul_smul,←Complex.ofReal_mul,he]
  · have hzero(q:QuantumTest):q z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm

private theorem deterministic_pair_weighted(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):
    sourcePair (deterministicCoframeRow t ht i f)
      (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))=
    sourcePair (SourceCoframeCovariantAction.covariantMomentum i f+
      (t:ℂ) • coframeDriftColumn i f)
      (gaussianProfileWeight t ht (-2/3)
        (SourceCoframeCovariantAction.metricAction i j
          (SourceCoframeCovariantAction.covariantMomentum j g+
            (t:ℂ) • coframeDriftColumn j g))):=by
  rw [deterministic_row_source t ht i,deterministic_row_source t ht j]
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply]
  simpa only [show (2:ℝ)*(-1/3)=(-2/3:ℝ) by norm_num] using
    weighted_metric_pair t ht (-1/3) i j
      (SourceCoframeCovariantAction.covariantMomentum i f+(t:ℂ) • coframeDriftColumn i f)
      (SourceCoframeCovariantAction.covariantMomentum j g+(t:ℂ) • coframeDriftColumn j g)


def nativePowerPair(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  sourcePair f (gaussianProfileWeight t ht (-7/9) (scalarKinetic g))+
  sourcePair f (gaussianProfileWeight t ht (11/9) (gaugeKinetic g))+
  sourcePair f (gaussianProfileWeight t ht (-1/9) (GaussMatterCore.matterAction g))+
  sourcePair f (gaussianProfileWeight t ht (17/9) (centeredAction g))-
  2*sourcePair f (gaussianProfileWeight t ht (14/9) (vacuumLinearAction g))+
  sourcePair f (gaussianProfileWeight t ht (12/9) (vacuumConstantAction g))+
  sourcePair f (gaussianProfileWeight t ht (6/9) (scalarSpatialAction g))+
  sourcePair f (gaussianProfileWeight t ht (8/9) (magneticAction g))
def deterministicPowerPair(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  ∑i:Fin 6,∑j:Fin 6,sourcePair
    (SourceCoframeCovariantAction.covariantMomentum i f+(t:ℂ) • coframeDriftColumn i f)
    (gaussianProfileWeight t ht (-2/3) (SourceCoframeCovariantAction.metricAction i j
      (SourceCoframeCovariantAction.covariantMomentum j g+(t:ℂ) • coframeDriftColumn j g)))
def wholePowerPair(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  nativePowerPair t ht f g+deterministicPowerPair t ht f g+
    localCoframePair t ht f g+noisePowerPair t ht f g

/-- Actual two-noise, full-H₀ expectation in finite power form; covariance removes every κ/log term. -/
theorem actual_corrected_hamiltonian_power_source(t:ℝ)(ht:0<t)(f g:QuantumTest):
    ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianPair t ht f g=
      wholePowerPair t ht f g:=by
  have hn:=actual_corrected_stochastic_power_pair t ht f g
  change (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
    (GaussDiagonalHistory.diagonalAction (correctedCompleteCore t ht x.1 x.2 g)) ∂γ.prod γ)=_
  rw [(ClockPhiHeatCorrectedHamiltonianSource.actual_corrected_hamiltonian_gaussian t ht f g).2]
  unfold wholeGaussianHeatHamiltonianPair wholePowerPair nativePowerPair deterministicPowerPair
  simp only [Finset.sum_add_distrib,deterministic_pair_weighted]
  linear_combination (norm:=ring) hn


private def futureWeightPair(s:ℝ)(hs:0<s)(a:ℝ)(f g:QuantumTest)(h:ℝ):ℂ:=
  if hh:0<h then sourcePair f (gaussianProfileWeight (s+h) (add_pos hs hh) a g)
    else sourcePair f (gaussianProfileWeight s hs a g)
private theorem futureWeightPair_limit(s:ℝ)(hs:0<s)(a:ℝ)(f g:QuantumTest):
    Tendsto (futureWeightPair s hs a f g) (𝓝[>] (0:ℝ))
      (𝓝 (sourcePair f (gaussianProfileWeight s hs a g))):=by
  have hq:=actual_gaussian_weighted_positive_time_jet s hs a f g
  have hc:Tendsto (fun h:ℝ=>(h:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    have hreal:Tendsto Complex.ofReal (𝓝 (0:ℝ)) (𝓝 ((0:ℝ):ℂ)):=
      Complex.continuous_ofReal.continuousAt.tendsto
    simpa only [Complex.ofReal_zero] using hreal.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ))
  have h:=(hc.mul hq).add_const (sourcePair f (gaussianProfileWeight s hs a g))
  simp only [zero_mul,zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp:0<t:=ht
  have hn:(t:ℂ)≠0:=by exact_mod_cast hp.ne'
  simp only [futureWeightPair,dif_pos hp]
  rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul,sub_add_cancel]

private theorem affine_pair_expand(t:ℝ)(A B C D:QuantumTest)(M:End):
    sourcePair (A+(t:ℂ) • B) (M (C+(t:ℂ) • D))=
      sourcePair A (M C)+(t:ℂ)*sourcePair B (M C)+(t:ℂ)*sourcePair A (M D)+
        (t:ℂ)^2*sourcePair B (M D):=by
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,
    inner_smul_right,Complex.conj_ofReal]
  ring

private theorem affine_slope_algebra(t:ℂ)(ht:t≠0)(x y z w b:ℂ):
    t⁻¹*(x-b)+y+z+t*w=t⁻¹*(x+t*y+t*z+t^2*w-b):=by
  field_simp [ht]
  ring

private theorem affine_power_positive_jet(s:ℝ)(hs:0<s)(a:ℝ)(f₀ f₁ g₀ g₁:QuantumTest):
    Tendsto (fun h:ℝ=>if hh:0<h then (h:ℂ)⁻¹*
      (sourcePair (f₀+((s+h:ℝ):ℂ) • f₁)
        (gaussianProfileWeight (s+h) (add_pos hs hh) a (g₀+((s+h:ℝ):ℂ) • g₁))-
       sourcePair (f₀+(s:ℂ) • f₁) (gaussianProfileWeight s hs a (g₀+(s:ℂ) • g₁))) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 ((18*a:ℂ)*sourcePair (forwardUAction s hs.le (f₀+(s:ℂ) • f₁))
          (gaussianProfileWeight s hs a (g₀+(s:ℂ) • g₁))+
        sourcePair f₁ (gaussianProfileWeight s hs a (g₀+(s:ℂ) • g₁))+
        sourcePair (f₀+(s:ℂ) • f₁) (gaussianProfileWeight s hs a g₁))):=by
  let A:=f₀+(s:ℂ) • f₁
  let B:=g₀+(s:ℂ) • g₁
  have hq:=actual_gaussian_weighted_positive_time_jet s hs a A B
  have hl:=futureWeightPair_limit s hs a f₁ B
  have hr:=futureWeightPair_limit s hs a A g₁
  have hc:Tendsto (fun h:ℝ=>(h:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    have hreal:Tendsto Complex.ofReal (𝓝 (0:ℝ)) (𝓝 ((0:ℝ):ℂ)):=
      Complex.continuous_ofReal.continuousAt.tendsto
    simpa only [Complex.ofReal_zero] using hreal.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ))
  have h4:=hc.mul (futureWeightPair_limit s hs a f₁ g₁)
  have h:=((hq.add hl).add hr).add h4
  simp only [zero_mul,add_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp:0<t:=ht
  have hn:(t:ℂ)≠0:=by exact_mod_cast hp.ne'
  simp only [futureWeightPair,dif_pos hp]
  have hf:f₀+((s+t:ℝ):ℂ) • f₁=A+(t:ℂ) • f₁:=by
    simp only [A,Complex.ofReal_add,add_smul,add_assoc]
  have hg:g₀+((s+t:ℝ):ℂ) • g₁=B+(t:ℂ) • g₁:=by
    simp only [B,Complex.ofReal_add,add_smul,add_assoc]
  rw [hf,hg]
  rw [affine_pair_expand t A f₁ B g₁ (gaussianProfileWeight (s+t) (add_pos hs hp) a)]
  exact affine_slope_algebra (t:ℂ) hn _ _ _ _ _

def deterministicPowerJet(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  ∑i:Fin 6,∑j:Fin 6,(
    (-12:ℂ)*sourcePair
      (forwardUAction t ht.le (SourceCoframeCovariantAction.covariantMomentum i f+(t:ℂ) • coframeDriftColumn i f))
      (gaussianProfileWeight t ht (-2/3) (SourceCoframeCovariantAction.metricAction i j
        (SourceCoframeCovariantAction.covariantMomentum j g+(t:ℂ) • coframeDriftColumn j g)))+
    sourcePair (coframeDriftColumn i f)
      (gaussianProfileWeight t ht (-2/3) (SourceCoframeCovariantAction.metricAction i j
        (SourceCoframeCovariantAction.covariantMomentum j g+(t:ℂ) • coframeDriftColumn j g)))+
    sourcePair (SourceCoframeCovariantAction.covariantMomentum i f+(t:ℂ) • coframeDriftColumn i f)
      (gaussianProfileWeight t ht (-2/3) (SourceCoframeCovariantAction.metricAction i j (coframeDriftColumn j g))))
private theorem deterministic_power_positive_jet(s:ℝ)(hs:0<s)(f g:QuantumTest):
    Tendsto (fun h:ℝ=>if hh:0<h then (h:ℂ)⁻¹*
      (deterministicPowerPair (s+h) (add_pos hs hh) f g-deterministicPowerPair s hs f g) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (deterministicPowerJet s hs f g)):=by
  have hsum:=tendsto_finsetSum (Finset.univ:Finset (Fin 6)) (fun i _=>
    tendsto_finsetSum (Finset.univ:Finset (Fin 6)) (fun j _=>
      affine_power_positive_jet s hs (-2/3)
        (SourceCoframeCovariantAction.covariantMomentum i f) (coframeDriftColumn i f)
        (SourceCoframeCovariantAction.metricAction i j (SourceCoframeCovariantAction.covariantMomentum j g))
        (SourceCoframeCovariantAction.metricAction i j (coframeDriftColumn j g))))
  simp only [show (18:ℂ)*(((-2/3:ℝ):ℂ))=(-12:ℂ) by norm_num] at hsum
  unfold deterministicPowerJet
  simp only [map_add,map_smul] at hsum ⊢
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp:0<h:=hh
  simp only [dif_pos hp,deterministicPowerPair,map_add,map_smul,
    Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]


private theorem native_power_positive_jet(s:ℝ)(hs:0<s)(f g:QuantumTest):
    Tendsto (fun h:ℝ=>if hh:0<h then (h:ℂ)⁻¹*
      (nativePowerPair (s+h) (add_pos hs hh) f g-nativePowerPair s hs f g) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (nativePositiveMean s hs f g)):=by
  have h1:=actual_gaussian_weighted_positive_time_jet s hs (-7/9) f (scalarKinetic g)
  have h2:=actual_gaussian_weighted_positive_time_jet s hs (11/9) f (gaugeKinetic g)
  have h3:=actual_gaussian_weighted_positive_time_jet s hs (-1/9) f (GaussMatterCore.matterAction g)
  have h4:=actual_gaussian_weighted_positive_time_jet s hs (17/9) f (centeredAction g)
  have h5:=actual_gaussian_weighted_positive_time_jet s hs (14/9) f (vacuumLinearAction g)
  have h6:=actual_gaussian_weighted_positive_time_jet s hs (12/9) f (vacuumConstantAction g)
  have h7:=actual_gaussian_weighted_positive_time_jet s hs (6/9) f (scalarSpatialAction g)
  have h8:=actual_gaussian_weighted_positive_time_jet s hs (8/9) f (magneticAction g)
  have hsum:=(((((((h1.add h2).add h3).add h4).sub (h5.const_mul 2)).add h6).add h7).add h8)
  convert hsum using 1
  · funext h
    by_cases hh:0<h
    · simp only [dif_pos hh,nativePowerPair]
      ring
    · simp only [dif_neg hh]
      ring
  · apply congrArg (fun z:ℂ=>𝓝 z)
    unfold nativePositiveMean
    push_cast
    ring
private theorem local_pair_power(t:ℝ)(ht:0<t)(f g:QuantumTest):
    localCoframePair t ht f g=
      sourcePair f (gaussianProfileWeight t ht (-2/3) (SourceCoframeCovariantSquare.spinRemainder g))+
      sourcePair f (gaussianProfileWeight t ht (-2/3) (GaussCoframeForm.numberShift g))+
      sourcePair f (gaussianProfileWeight t ht (4/3) (localVolumeAction g)):=rfl
private theorem local_power_positive_jet(s:ℝ)(hs:0<s)(f g:QuantumTest):
    Tendsto (fun h:ℝ=>if hh:0<h then (h:ℂ)⁻¹*
      (localCoframePair (s+h) (add_pos hs hh) f g-localCoframePair s hs f g) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (localPositiveMean s hs f g)):=by
  have h1:=actual_gaussian_weighted_positive_time_jet s hs (-2/3) f (SourceCoframeCovariantSquare.spinRemainder g)
  have h2:=actual_gaussian_weighted_positive_time_jet s hs (-2/3) f (GaussCoframeForm.numberShift g)
  have h3:=actual_gaussian_weighted_positive_time_jet s hs (4/3) f (localVolumeAction g)
  have hsum:=(h1.add h2).add h3
  convert hsum using 1
  · funext h
    by_cases hh:0<h
    · simp only [dif_pos hh,local_pair_power]
      ring
    · simp only [dif_neg hh]
      ring
  · apply congrArg (fun z:ℂ=>𝓝 z)
    unfold localPositiveMean
    push_cast
    ring

def noisePowerJet(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  (sourceTime 0/96:ℂ)*((24:ℂ)*sourcePair
    (forwardUAction t ht.le (inverseVolumeAction (combinedGenerator f)))
      (gaussianProfileWeight t ht (4/3) (combinedGenerator g))+
    (12:ℂ)*sourcePair (forwardUAction t ht.le (inverseVolumeAction (combinedGenerator f)))
      (gaussianProfileWeight t ht (-2/3) (combinedGenerator g)))
private theorem noise_power_positive_jet(s:ℝ)(hs:0<s)(f g:QuantumTest):
    Tendsto (fun h:ℝ=>if hh:0<h then (h:ℂ)⁻¹*
      (noisePowerPair (s+h) (add_pos hs hh) f g-noisePowerPair s hs f g) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (noisePowerJet s hs f g)):=by
  have h1:=actual_gaussian_weighted_positive_time_jet s hs (4/3)
    (inverseVolumeAction (combinedGenerator f)) (combinedGenerator g)
  have h2:=actual_gaussian_weighted_positive_time_jet s hs (-2/3)
    (inverseVolumeAction (combinedGenerator f)) (combinedGenerator g)
  have hsum:=(h1.sub h2).const_mul (sourceTime 0/96:ℂ)
  convert hsum using 1
  · funext h
    by_cases hh:0<h
    · simp only [dif_pos hh,noisePowerPair]
      ring
    · simp only [dif_neg hh]
      ring
  · apply congrArg (fun z:ℂ=>𝓝 z)
    unfold noisePowerJet
    push_cast
    ring

def wholePowerJet(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  nativePositiveMean t ht f g+deterministicPowerJet t ht f g+
    localPositiveMean t ht f g+noisePowerJet t ht f g
private theorem whole_power_positive_jet(s:ℝ)(hs:0<s)(f g:QuantumTest):
    Tendsto (fun h:ℝ=>if hh:0<h then (h:ℂ)⁻¹*
      (wholePowerPair (s+h) (add_pos hs hh) f g-wholePowerPair s hs f g) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (wholePowerJet s hs f g)):=by
  have hsum:=(((native_power_positive_jet s hs f g).add (deterministic_power_positive_jet s hs f g)).add
    (local_power_positive_jet s hs f g)).add (noise_power_positive_jet s hs f g)
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp:0<h:=hh
  simp only [dif_pos hp,wholePowerPair]
  ring

/-- The full actual positive-time work has a source-generated right derivative, in finite power form. -/
theorem actual_corrected_hamiltonian_positive_time_power_jet(s:ℝ)(hs:0<s)(f g:QuantumTest):
    Tendsto (fun h:ℝ=>if hh:0<h then (h:ℂ)⁻¹*
      (ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianPair (s+h) (add_pos hs hh) f g-
        ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianPair s hs f g) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (wholePowerJet s hs f g)):=by
  simpa only [actual_corrected_hamiltonian_power_source] using whole_power_positive_jet s hs f g


private theorem forwardU_weight(t:ℝ)(ht:0<t)(a:ℝ)(f:QuantumTest):
    forwardUAction t ht.le (gaussianProfileWeight t ht a f)=
      gaussianProfileWeight t ht a (forwardUAction t ht.le f):=by
  apply DFunLike.ext
  intro z
  change (forwardU t z:ℂ) • ((((forwardRatio t z)^a:ℝ):ℂ) • f z)=
    (((forwardRatio t z)^a:ℝ):ℂ) • ((forwardU t z:ℂ) • f z)
  exact smul_comm _ _ _
private theorem forwardU_inverse(t:ℝ)(ht:0<t)(f:QuantumTest):
    inverseVolumeAction (forwardUAction t ht.le f)=forwardUAction t ht.le (inverseVolumeAction f):=by
  apply DFunLike.ext
  intro z
  change (reciprocalVolume z:ℂ) • ((forwardU t z:ℂ) • f z)=
    (forwardU t z:ℂ) • ((reciprocalVolume z:ℂ) • f z)
  exact smul_comm _ _ _
private theorem metric_forwardU_pair(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):
    sourcePair f (SourceCoframeCovariantAction.metricAction i j (forwardUAction t ht.le g))=
      sourcePair (forwardUAction t ht.le f) (SourceCoframeCovariantAction.metricAction i j g):=by
  have he:SourceCoframeCovariantAction.metricAction i j (forwardUAction t ht.le g)=
      forwardUAction t ht.le (SourceCoframeCovariantAction.metricAction i j g):=by
    apply DFunLike.ext
    intro z
    change (GaussCoframeKinetic.coefficient i j z:ℂ) • ((forwardU t z:ℂ) • g z)=
      (forwardU t z:ℂ) • ((GaussCoframeKinetic.coefficient i j z:ℂ) • g z)
    exact smul_comm _ _ _
  rw [he,forwardU_pair t ht]
private def baseCoframeRow(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):ℂ:=
  (-12:ℂ)*sourcePair (forwardUAction t ht.le (deterministicCoframeRow t ht i f))
    (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))+
  sourcePair (returnedDriftZero t ht i f) (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))+
  sourcePair (deterministicCoframeRow t ht i f) (SourceCoframeCovariantAction.metricAction i j (returnedDriftZero t ht j g))
private def noiseMetricRow(t:ℝ)(ht:0<t)(ξ η:ℝ)(i j:Fin 6)(f g:QuantumTest):ℂ:=
  sourcePair (forwardUAction t ht.le (correctedNoiseRow t ht ξ η i f))
    (SourceCoframeCovariantAction.metricAction i j (correctedNoiseRow t ht ξ η j g))
private theorem base_coframe_sum(t:ℝ)(ht:0<t)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,baseCoframeRow t ht i j f g)=deterministicPowerJet t ht f g:=by
  unfold deterministicPowerJet
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold baseCoframeRow
  simp only [returned_drift_zero_power,deterministic_row_source,
    Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply]
  rw [forwardU_weight,weighted_metric_pair,weighted_metric_pair,weighted_metric_pair]
  norm_num
private theorem affine_metric_mean_split(U M:End)
    (hm:∀p q:QuantumTest,sourcePair p (M (U q))=sourcePair (U p) (M q))
    (A B C D E F P Q:QuantumTest):
    (-12:ℂ)*affinePairMean (U A) (U B) (U C) D E F M+
      affinePairMean P ((18:ℂ) • U B) ((18:ℂ) • U C) D E F M+
      affinePairMean A B C Q ((18:ℂ) • U E) ((18:ℂ) • U F) M=
      (-12:ℂ)*sourcePair (U A) (M D)+sourcePair P (M D)+sourcePair A (M Q)+
        (24:ℂ)*(sourcePair (U B) (M E)+sourcePair (U C) (M F)):=by
  have hl(p q:QuantumTest):sourcePair ((18:ℂ) • p) q=18*sourcePair p q:=by
    simp only [sourcePair,map_smul,inner_smul_left]
    rw [starRingEnd_apply,star_ofNat]
  have hr(p q:QuantumTest):sourcePair p ((18:ℂ) • q)=18*sourcePair p q:=by
    simp only [sourcePair,map_smul,inner_smul_right]
  simp only [affinePairMean,map_smul,hl,hr,hm]
  ring
private theorem deterministic_mean_split(t:ℝ)(ht:0<t)(f g:QuantumTest):
    deterministicPositiveMean t ht f g=deterministicPowerJet t ht f g+
      (24:ℂ)*((∑i:Fin 6,∑j:Fin 6,noiseMetricRow t ht 1 0 i j f g)+
        (∑i:Fin 6,∑j:Fin 6,noiseMetricRow t ht 0 1 i j f g)):=by
  have he(i j:Fin 6):
      (-12:ℂ)*inverseMetricPositiveMean t ht i j f g+driftCovariantPositiveMean t ht i j f g+
        covariantDriftPositiveMean t ht i j f g=
      baseCoframeRow t ht i j f g+
        (24:ℂ)*(noiseMetricRow t ht 1 0 i j f g+noiseMetricRow t ht 0 1 i j f g):=by
    have h:=affine_metric_mean_split (forwardUAction t ht.le) (SourceCoframeCovariantAction.metricAction i j)
      (metric_forwardU_pair t ht i j)
      (deterministicCoframeRow t ht i f) (correctedNoiseRow t ht 1 0 i f) (correctedNoiseRow t ht 0 1 i f)
      (deterministicCoframeRow t ht j g) (correctedNoiseRow t ht 1 0 j g) (correctedNoiseRow t ht 0 1 j g)
      (returnedDriftZero t ht i f) (returnedDriftZero t ht j g)
    simpa only [inverseMetricPositiveMean,driftCovariantPositiveMean,covariantDriftPositiveMean,
      baseCoframeRow,noiseMetricRow,returned_drift_noise_power,Module.End.mul_apply,LinearMap.smul_apply] using h
  unfold deterministicPositiveMean
  simp_rw [he]
  simp only [mul_add,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [base_coframe_sum]
private theorem noise_metric_sum(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,noiseMetricRow t ht ξ η i j f g)=
      sourcePair (forwardUAction t ht.le (combinedGenerator f))
        (radialPrice (powerNoiseWeight t ξ η) (powerNoiseWeight_smooth t ht ξ η) (combinedGenerator g)):=by
  have hr(i:Fin 6)(q:QuantumTest):correctedNoiseRow t ht ξ η i q=
      radialColumn (powerNoiseWeight t ξ η) (powerNoiseWeight_smooth t ht ξ η) i (combinedGenerator q):=rfl
  have hu(i:Fin 6)(q:QuantumTest):forwardUAction t ht.le
      (radialColumn (powerNoiseWeight t ξ η) (powerNoiseWeight_smooth t ht ξ η) i q)=
      radialColumn (powerNoiseWeight t ξ η) (powerNoiseWeight_smooth t ht ξ η) i (forwardUAction t ht.le q):=by
    apply DFunLike.ext
    intro z
    change (forwardU t z:ℂ) • (Complex.I • ((powerNoiseWeight t ξ η z:ℂ) • ((volumeGradient z i:ℂ) • q z)))=
      Complex.I • ((powerNoiseWeight t ξ η z:ℂ) • ((volumeGradient z i:ℂ) • ((forwardU t z:ℂ) • q z)))
    module
  simp only [noiseMetricRow,hr,hu]
  exact actual_radial_covariance_pair _ _ _ _
private theorem two_noise_metric_power(t:ℝ)(ht:0<t)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,noiseMetricRow t ht 1 0 i j f g)+
      (∑i:Fin 6,∑j:Fin 6,noiseMetricRow t ht 0 1 i j f g)=
      (sourceTime 0/96:ℂ)*(sourcePair (forwardUAction t ht.le (inverseVolumeAction (combinedGenerator f)))
        (gaussianProfileWeight t ht (4/3) (combinedGenerator g))-
        sourcePair (forwardUAction t ht.le (inverseVolumeAction (combinedGenerator f)))
          (gaussianProfileWeight t ht (-2/3) (combinedGenerator g))):=by
  rw [noise_metric_sum,noise_metric_sum]
  have hadd(p q r:QuantumTest):sourcePair p q+sourcePair p r=sourcePair p (q+r):=by
    simp only [sourcePair,map_add,inner_add_right]
  rw [hadd,←LinearMap.add_apply,corrected_noise_power_operator]
  change sourcePair (forwardUAction t ht.le (combinedGenerator f))
    ((sourceTime 0/96:ℂ) • inverseVolumeAction
      (gaussianProfileWeight t ht (4/3) (combinedGenerator g)-gaussianProfileWeight t ht (-2/3) (combinedGenerator g)))=_
  have hsmul(p q:QuantumTest)(c:ℂ):sourcePair p (c • q)=c*sourcePair p q:=by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [hsmul,U_pair,forwardU_inverse t ht]
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem gain_square_inverse_power(t:ℝ)(ht:0<t)(f:QuantumTest):
    SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
        (forwardUAction t ht.le (forwardUAction t ht.le f)))=
      inverseVolumeAction (forwardUAction t ht.le (gaussianProfileWeight t ht (-2/3) f)):=by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hg:SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z^2=(forwardRatio t z)^(1/3:ℝ):=by
      unfold SourceClockPhiActualCovarianceStep.gainProfile
      rw [Real.sq_sqrt ht.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
      norm_num
    have hp:(forwardRatio t z)^(1/3:ℝ)=(forwardRatio t z)^(-2/3:ℝ)*forwardRatio t z:=by
      calc
        _=(forwardRatio t z)^((-2/3:ℝ)+1):=by norm_num
        _=(forwardRatio t z)^(-2/3:ℝ)*(forwardRatio t z)^(1:ℝ):=Real.rpow_add hr _ _
        _=_:=by rw [Real.rpow_one]
    have hu:forwardU t z*forwardRatio t z=reciprocalVolume z:=by
      unfold forwardU forwardRatio reciprocalVolume
      have hV:(volume z)≠0:=(volume_pos ⟨z,hz⟩).ne'
      have hW:(volume z+18*t)≠0:=by linarith [volume_pos ⟨z,hz⟩]
      field_simp [hV,hW]
    have he:SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z*
        (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z*(forwardU t z*forwardU t z))=
        reciprocalVolume z*(forwardU t z*(forwardRatio t z)^(-2/3:ℝ)):=by
      calc _=SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z^2*(forwardU t z)^2:=by ring
           _=_:=by rw [hg,hp];linear_combination (norm:=ring) (forwardU t z)*(forwardRatio t z)^(-2/3:ℝ)*hu
    change (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ) •
      ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ) • ((forwardU t z:ℂ) • ((forwardU t z:ℂ) • f z)))=
      (reciprocalVolume z:ℂ) • ((forwardU t z:ℂ) • ((((forwardRatio t z)^(-2/3:ℝ):ℝ):ℂ) • f z))
    simpa only [Complex.ofReal_mul,mul_smul] using congrArg (fun r:ℝ=>(r:ℂ) • f z) he
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem stochastic_mean_power(t:ℝ)(ht:0<t)(f g:QuantumTest):
    stochasticPositiveMean t ht f g=(sourceTime 0/96:ℂ)*(36:ℂ)*
      sourcePair (forwardUAction t ht.le (inverseVolumeAction (combinedGenerator f)))
        (gaussianProfileWeight t ht (-2/3) (combinedGenerator g)):=by
  unfold stochasticPositiveMean
  have hg(p q:QuantumTest):sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) p)
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) q)=
      sourcePair p (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) q)):=
    (multiply_pair _ _ _ _).symm
  rw [hg,gain_square_inverse_power t ht,U_pair,forwardU_pair t ht]
  ring

theorem actual_positive_generator_mean_recognition(t:ℝ)(ht:0<t)(f g:QuantumTest):
    wholePowerJet t ht f g=positiveGeneratorMean t ht f g:=by
  unfold wholePowerJet positiveGeneratorMean
  rw [deterministic_mean_split,two_noise_metric_power,stochastic_mean_power]
  unfold noisePowerJet
  ring

theorem actual_corrected_hamiltonian_positive_time_Q_H0(s:ℝ)(hs:0<s)(f g:QuantumTest):
    Tendsto (fun h:ℝ=>if hh:0<h then (h:ℂ)⁻¹*
      (ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianPair (s+h) (add_pos hs hh) f g-
        ClockPhiCorrectedHamiltonianWorkGenerator.correctedHamiltonianPair s hs f g) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore s hs x.1 x.2 f)
        ((SourceClockPhiMatchedDiffusionSource.completeCurrent GaussDiagonalHistory.diagonalAction)
          (correctedCompleteCore s hs x.1 x.2 g)) ∂γ.prod γ)):=by
  rw [(actual_corrected_Q_H0_gaussian_source s hs f g).2,←actual_positive_generator_mean_recognition]
  exact actual_corrected_hamiltonian_positive_time_power_jet s hs f g

end LowEnergy.PositiveClockGenerator
