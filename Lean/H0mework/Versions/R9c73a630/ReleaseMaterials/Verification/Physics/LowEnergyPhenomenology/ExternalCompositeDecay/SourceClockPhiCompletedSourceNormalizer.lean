import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFullSourceVarianceNormalizer
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGainedMixedMoment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.OriginalRCommutatorSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource
open ClockPhiHeatCorrectedCovarianceSource SourceClockPhiCorrectedWeightTransport
open SourceClockPhiCoframeForwardPair SourceClockPhiCoframeForwardCore ClockPhiConservativeHeatSource
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentWholeVariance GaussianProfileFirstMoment
open SourceScalarDoubleCurrent SourceClockPhiNormalizedScalarBudget MeasureTheory
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev K(s:ℝ)(hs:0<s)(x:ℝ×ℝ):End:=correctedCompleteCore s hs x.1 x.2
private abbrev G(s:ℝ):End:=SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)
private abbrev n:ℝ:=sourceTime 0
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ₂:=γ.prod γ
attribute [local irreducible] sourcePair embed diagonalAction correctedCompleteCore matchedTester normalizedState normalizedForcing
private theorem n_pos:0<n:=by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

def matchedClockDefect(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(w:QuantumTest):QuantumTest:=
  matchedTester (K s hs x w)-K s hs x (matchedTester w)
def matchedNoiseRow(s:ℝ)(hs:0<s)(axis:Bool)(w:QuantumTest):QuantumTest:=
  -(noiseAction s hs (if axis then 0 else 1) (if axis then 1 else 0) (combinedGenerator w))
def matchedNoiseSource(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(w:QuantumTest):QuantumTest:=
  (x.1:ℂ) • matchedNoiseRow s hs false w+(x.2:ℂ) • matchedNoiseRow s hs true w

/-- The actual matched current has exactly its two original noise rows; the entire deterministic input cancels from its clock commutator. -/
theorem actual_matched_clock_defect_source(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(w:QuantumTest):
    matchedClockDefect s hs x w=K s hs x (matchedNoiseSource s hs x w):=by
  unfold matchedClockDefect
  rw [actual_corrected_complete_matched_tester]
  have he:noiseAction s hs x.1 x.2 (combinedGenerator w)=
      (x.1:ℂ) • noiseAction s hs 1 0 (combinedGenerator w)+(x.2:ℂ) • noiseAction s hs 0 1 (combinedGenerator w):=by
    apply DFunLike.ext
    intro z
    change (covarianceNoise s x.1 x.2 z:ℂ) • combinedGenerator w z=_
    rw [actual_covariance_noise_affine]
    simp only [Complex.ofReal_add,Complex.ofReal_mul,add_smul,mul_smul]
    rfl
  simp only [he,matchedNoiseSource,matchedNoiseRow,Bool.false_eq_true,ite_false,ite_true,map_sub,map_add,map_smul,map_neg,smul_neg]
  module
theorem actual_complete_clock_pair(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (K s hs x f) (K s hs x g)=sourcePair (G s f) (G s g):=by
  unfold K correctedCompleteCore correctedHeatCore
  change sourcePair (sourceForwardCore s hs.le (correctedProfileCore s hs x.1 x.2 (G s f)))
    (sourceForwardCore s hs.le (correctedProfileCore s hs x.1 x.2 (G s g)))=_
  rw [actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _

def matchedDefectMean(s:ℝ)(hs:0<s)(f g:QuantumTest):ℂ:=
  sourcePair (G s (matchedNoiseRow s hs false f)) (G s (matchedNoiseRow s hs false g))+
    sourcePair (G s (matchedNoiseRow s hs true f)) (G s (matchedNoiseRow s hs true g))

/-- The matched-clock variance has its actual positive Gaussian price with both ordered source legs. -/
theorem actual_matched_clock_defect_gaussian(s:ℝ)(hs:0<s)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (matchedClockDefect s hs x f) (matchedClockDefect s hs x g)) γ₂ ∧
    (∫x:ℝ×ℝ,sourcePair (matchedClockDefect s hs x f) (matchedClockDefect s hs x g) ∂γ₂)=matchedDefectMean s hs f g:=by
  have h:=SourceClockPhiGaussianPlaneSource.actual_gaussian_affine_source_pair 0
    (G s (matchedNoiseRow s hs false f)) (G s (matchedNoiseRow s hs true f)) 0
    (G s (matchedNoiseRow s hs false g)) (G s (matchedNoiseRow s hs true g)) (1:End)
  simp only [Module.End.one_apply,sourcePair,map_zero,inner_zero_left,zero_add] at h
  have he(x:ℝ×ℝ):sourcePair (matchedClockDefect s hs x f) (matchedClockDefect s hs x g)=
      sourcePair ((x.1:ℂ) • G s (matchedNoiseRow s hs false f)+(x.2:ℂ) • G s (matchedNoiseRow s hs true f))
        ((x.1:ℂ) • G s (matchedNoiseRow s hs false g)+(x.2:ℂ) • G s (matchedNoiseRow s hs true g)):=by
    rw [actual_matched_clock_defect_source,actual_matched_clock_defect_source,actual_complete_clock_pair]
    simp only [matchedNoiseSource,map_add,map_smul]
  simpa only [he,matchedDefectMean,sourcePair] using h

/-- A transported original source has zero mixed mean against the actual matched-clock fluctuation. This removes the forcing input from the finite normalizer update. -/
theorem actual_matched_clock_centered(s:ℝ)(hs:0<s)(f w:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (K s hs x f) (matchedClockDefect s hs x w)) γ₂ ∧
    (∫x:ℝ×ℝ,sourcePair (K s hs x f) (matchedClockDefect s hs x w) ∂γ₂)=0:=by
  have h:=SourceClockPhiGaussianPlaneSource.actual_gaussian_affine_source_pair (G s f) 0 0 0
    (G s (matchedNoiseRow s hs false w)) (G s (matchedNoiseRow s hs true w)) (1:End)
  have he(x:ℝ×ℝ):sourcePair (K s hs x f) (matchedClockDefect s hs x w)=
      sourcePair (G s f) ((x.1:ℂ) • G s (matchedNoiseRow s hs false w)+(x.2:ℂ) • G s (matchedNoiseRow s hs true w)):=by
    rw [actual_matched_clock_defect_source,actual_complete_clock_pair]
    simp only [matchedNoiseSource,map_add,map_smul]
  simpa only [he,Module.End.one_apply,smul_zero,add_zero,zero_add,sourcePair,map_zero,inner_zero_left,inner_zero_right] using h

def forcingFluctuation(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(a:QuantumTest×QuantumTest):QuantumTest:=
  (clockSourcePair s hs x a).2-K s hs x a.2
def completedFluctuation(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(a:QuantumTest×QuantumTest):QuantumTest:=
  matchedTester (clockSourcePair s hs x a).1+((144/n:ℝ):ℂ) • (clockSourcePair s hs x a).2-
    K s hs x (matchedTester a.1+((144/n:ℝ):ℂ) • a.2)

theorem actual_full_forcing_fluctuation(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(a:QuantumTest×QuantumTest):
    forcingFluctuation s hs x a=actualClockDefect s hs x a.1 (diagonalAction a.1):=by
  simp only [forcingFluctuation,clockSourcePair,bracket,LinearMap.sub_apply,Module.End.mul_apply,actualClockDefect]
  module

theorem actual_completed_fluctuation_source(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(a:QuantumTest×QuantumTest):
    completedFluctuation s hs x a=matchedClockDefect s hs x a.1+((144/n:ℝ):ℂ) • forcingFluctuation s hs x a:=by
  simp only [completedFluctuation,forcingFluctuation,clockSourcePair,matchedClockDefect,bracket,
    Module.End.mul_apply,LinearMap.sub_apply,map_add,map_smul]
  module

/-- The full H0 fluctuation square cancels inside the original completed-square normalizer at finite clock. Its two surviving terms are the literal matched/full commutator cross and the negative matched variance. -/
theorem actual_finite_completed_normalizer(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(a:QuantumTest×QuantumTest):
    (432/n)*‖embed (forcingFluctuation s hs x a)‖^2-(n/48)*‖embed (completedFluctuation s hs x a)‖^2=
      -6*(sourcePair (matchedClockDefect s hs x a.1) (actualClockDefect s hs x a.1 (diagonalAction a.1))).re-
        (n/48)*‖embed (matchedClockDefect s hs x a.1)‖^2:=by
  rw [actual_completed_fluctuation_source,actual_full_forcing_fluctuation,map_add,map_smul]
  simpa only [sourcePair] using (FiniteCausalSylvester.noether_clock_square n n_pos
    (embed (matchedClockDefect s hs x a.1)) (embed (actualClockDefect s hs x a.1 (diagonalAction a.1)))).symm

/-- The cancellation is consumed by the exact wholeSourceNext chosen by the original physical R producer, with its complete original forcing. -/
theorem actual_whole_source_completed_normalizer(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):
    let a:=wholeSourceNext s hs half advanced m ell F g q
    (432/n)*‖embed (forcingFluctuation s hs x a)‖^2-(n/48)*‖embed (completedFluctuation s hs x a)‖^2=
      -6*(sourcePair (matchedClockDefect s hs x a.1) (actualClockDefect s hs x a.1 (diagonalAction a.1))).re-
        (n/48)*‖embed (matchedClockDefect s hs x a.1)‖^2:=
  actual_finite_completed_normalizer s hs x _
end LowEnergy.OriginalRCommutatorSource
