import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointForcingSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.FirstCurrentPayerNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiCombinedScalePressure SourceClockPhiCorrectedWeightTransport
open ClockPhiHeatCorrectedCovarianceSource SourceClockPhiNativeMatchedSource
open SourceClockPhiMatchedDiffusionSource SourceClockPhiNormalizedScalarBudget
open SourceClockPhiActualCovarianceStep SourceCoframeCovariantAction MeasureTheory
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev γ := ProbabilityTheory.gaussianReal 0 1
private abbrev G (t : ℝ) := sourceGain (Real.sqrt t)
private theorem n_positive : 0 < n := by
  change 0 < sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private def column (a : QuadraticIndex) (f : QuantumTest) : QuadraticIndex → QuantumTest :=
  fun b => if b=a then f else 0
private theorem single_source (a : QuadraticIndex) (f : QuantumTest) (x : ℝ×ℝ) :
    quadraticSource (column a f) x=(noiseQuadratic a x:ℂ) • f := by
  classical
  unfold quadraticSource column
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim
private theorem source_add (v w : QuadraticIndex → QuantumTest) (x : ℝ×ℝ) :
    quadraticSource (v+w) x=quadraticSource v x+quadraticSource w x := by
  simp only [quadraticSource,Pi.add_apply,smul_add,Finset.sum_add_distrib]
private theorem source_sub (v w : QuadraticIndex → QuantumTest) (x : ℝ×ℝ) :
    quadraticSource (v-w) x=quadraticSource v x-quadraticSource w x := by
  simp only [quadraticSource,Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]

def matchedGaussianColumn (t : ℝ) (ht : 0 < t) (w : QuantumTest) : QuadraticIndex → QuantumTest :=
  column (0,0) (matchedTester w)+column (1,0) (-(noiseAction t ht 1 0 (combinedGenerator w)))+
    column (2,0) (-(noiseAction t ht 0 1 (combinedGenerator w)))
def coframeForcingColumn (t : ℝ) (ht : 0 < t) (z : ℂ) (w : QuantumTest) : QuadraticIndex → QuantumTest :=
  (fun a => coframeQuadraticColumn t ht a w)-column (0,0) (z • w)
private theorem matched_return (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (w : QuantumTest) :
    matchedTester (correctedCompleteCore t ht x.1 x.2 w)=
      correctedCompleteCore t ht x.1 x.2 (quadraticSource (matchedGaussianColumn t ht w) x) := by
  unfold matchedGaussianColumn
  rw [source_add,source_add,single_source,single_source,single_source,
    actual_corrected_complete_matched_tester]
  simp only [noiseQuadratic,(noiseLinear_values x).1,(noiseLinear_values x).2.1,
    (noiseLinear_values x).2.2,mul_one,Complex.ofReal_one,one_smul,smul_neg]
  congr 1
  have hn : noiseAction t ht x.1 x.2 (combinedGenerator w)=
      (x.1:ℂ) • noiseAction t ht 1 0 (combinedGenerator w)+
      (x.2:ℂ) • noiseAction t ht 0 1 (combinedGenerator w) := by
    apply DFunLike.ext
    intro q
    change (covarianceNoise t x.1 x.2 q:ℂ) • combinedGenerator w q=_
    rw [actual_covariance_noise_affine]
    simp only [Complex.ofReal_add,Complex.ofReal_mul,add_smul,mul_smul]
    rfl
  rw [hn]
  module
private theorem coframe_return (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (z : ℂ) (w : QuantumTest) :
    coframeForcing t ht x z w=
      correctedCompleteCore t ht x.1 x.2 (quadraticSource (coframeForcingColumn t ht z w) x) := by
  unfold coframeForcing coframeForcingColumn
  rw [source_sub,single_source,actual_corrected_coframe_quadratic_return]
  simp only [noiseQuadratic,(noiseLinear_values x).1,one_mul,Complex.ofReal_one,one_smul,map_sub,map_smul]
private theorem complete_pair (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (v w : QuantumTest) :
    sourcePair (correctedCompleteCore t ht x.1 x.2 v) (correctedCompleteCore t ht x.1 x.2 w)=
      sourcePair (G t v) (G t w) := by
  change sourcePair (SourceClockPhiCoframeForwardCore.sourceForwardCore t ht.le
    (correctedProfileCore t ht x.1 x.2 (G t v)))
    (SourceClockPhiCoframeForwardCore.sourceForwardCore t ht.le
    (correctedProfileCore t ht x.1 x.2 (G t w)))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact ClockPhiConservativeHeatSource.clockProfileAction_pair _ _ _ _ _ _
private theorem gain_source (t : ℝ) (v : QuadraticIndex → QuantumTest) (x : ℝ×ℝ) :
    G t (quadraticSource v x)=quadraticSource (fun a => G t (v a)) x := by
  simp only [quadraticSource,map_sum,map_smul]
def coframeGaussianPair (t : ℝ) (v w : QuadraticIndex → QuantumTest) : ℂ :=
  ∑a,∑b,(quadraticMoment a b:ℂ)*sourcePair (G t (v a)) (G t (w b))
private theorem packet_pair (t : ℝ) (ht : 0 < t) (v w : QuadraticIndex → QuantumTest) :
    Integrable (fun x : ℝ×ℝ => sourcePair (correctedCompleteCore t ht x.1 x.2 (quadraticSource v x))
      (correctedCompleteCore t ht x.1 x.2 (quadraticSource w x))) (γ.prod γ) ∧
    (∫x : ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 (quadraticSource v x))
      (correctedCompleteCore t ht x.1 x.2 (quadraticSource w x)) ∂γ.prod γ)=coframeGaussianPair t v w := by
  simpa only [complete_pair,gain_source,Module.End.one_apply,coframeGaussianPair] using
    quadratic_gaussian_pair (fun a => G t (v a)) (fun a => G t (w a)) (1:End)

/-- The signed coframe price is generated before Gaussian integration, so its fourth-order squares
cancel jointly. Its remaining finite pairing has one affine and one quadratic original source leg. -/
theorem actual_normalized_signed_coframe_gaussian (t : ℝ) (ht : 0 < t)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    let price := fun x : ℝ×ℝ => (432/n)*‖embed (coframeForcing t ht x z w)‖^2-
      (n/48)*‖embed (coframeCompleted t ht x z w)‖^2
    Integrable price (γ.prod γ) ∧
    (∫x,price x ∂γ.prod γ)=
      -6*(coframeGaussianPair t (matchedGaussianColumn t ht w) (coframeForcingColumn t ht z w)).re-
      (n/48)*(coframeGaussianPair t (matchedGaussianColumn t ht w) (matchedGaussianColumn t ht w)).re := by
  intro w price
  have hcross := packet_pair t ht (matchedGaussianColumn t ht w) (coframeForcingColumn t ht z w)
  have hself := packet_pair t ht (matchedGaussianColumn t ht w) (matchedGaussianColumn t ht w)
  simp_rw [←matched_return,←coframe_return] at hcross hself
  have he (x : ℝ×ℝ) : price x=
      -6*(sourcePair (matchedTester (correctedCompleteCore t ht x.1 x.2 w)) (coframeForcing t ht x z w)).re-
      (n/48)*(sourcePair (matchedTester (correctedCompleteCore t ht x.1 x.2 w))
        (matchedTester (correctedCompleteCore t ht x.1 x.2 w))).re := by
    dsimp only [price,coframeCompleted]
    simp only [map_add,map_smul]
    rw [←FiniteCausalSylvester.noether_clock_square n n_positive]
    rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
    rfl
  have hc := hcross.1.re
  have hs := hself.1.re
  change Integrable (fun x : ℝ×ℝ => (sourcePair _ _).re) (γ.prod γ) at hc hs
  refine ⟨?_,?_⟩
  · exact ((hc.const_mul (-6)).sub (hs.const_mul (n/48))).congr
      (Filter.Eventually.of_forall fun x => (he x).symm)
  · simp_rw [he]
    rw [integral_sub (hc.const_mul (-6)) (hs.const_mul (n/48)),integral_const_mul,integral_const_mul]
    have hcr := Complex.reCLM.integral_comp_comm hcross.1
    have hsr := Complex.reCLM.integral_comp_comm hself.1
    simpa only [Complex.reCLM_apply,hcross.2,hself.2] using congrArg₂ (fun a b : ℝ => -6*a-(n/48)*b) hcr hsr
end LowEnergy.FirstCurrentPayerNext
