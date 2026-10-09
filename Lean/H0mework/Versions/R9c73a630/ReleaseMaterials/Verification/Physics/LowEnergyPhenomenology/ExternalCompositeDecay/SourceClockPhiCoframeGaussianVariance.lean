import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiQuadraticGaussianSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentPayerNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiCoframeForwardCore ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource
open ClockPhiHeatCorrectedCoframeWork ClockPhiHeatCoframeHamiltonianWork PositiveClockGenerator
open SourceCoframeCovariantAction SourceClockPhiNormalizedScalarBudget GaussDiagonalHistory GaussUnitaryHistory
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev γ := gaussianReal 0 1
private abbrev G (s : ℝ) := SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)

private def rightColumn (t : ℝ) (ht : 0 < t) (i : Fin 6) (a : Fin 3) : End :=
  ![deterministicCoframeRow t ht i,correctedNoiseRow t ht 1 0 i,correctedNoiseRow t ht 0 1 i] a
private def leftColumn (t : ℝ) (ht : 0 < t) (i : Fin 6) (a : Fin 3) : End :=
  ![deterministicCoframeRow t ht i - Complex.I •
      (returnedCurrentColumn t ht i*(GaussCoframeForm.number+(2:ℂ) • (1:End))),
    correctedNoiseRow t ht 1 0 i,correctedNoiseRow t ht 0 1 i] a
private theorem linear_values (a : Fin 3) (x : ℝ×ℝ) : noiseLinear a x = ![1,x.1,x.2] a := by
  fin_cases a
  · exact (noiseLinear_values x).1
  · exact (noiseLinear_values x).2.1
  · exact (noiseLinear_values x).2.2
private theorem row_expansion (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (i : Fin 6) :
    correctedCovariantRow t ht x.1 x.2 i = ∑ a : Fin 3,(noiseLinear a x:ℂ) • rightColumn t ht i a := by
  have he : (∑ a : Fin 3,(noiseLinear a x:ℂ) • rightColumn t ht i a) =
      deterministicCoframeRow t ht i+(x.1:ℂ) • correctedNoiseRow t ht 1 0 i+
        (x.2:ℂ) • correctedNoiseRow t ht 0 1 i := by
    norm_num [Fin.sum_univ_succ,rightColumn,Fin.succ,linear_values]
    module
  rw [he]
  apply LinearMap.ext
  intro f
  simpa only [LinearMap.add_apply,LinearMap.smul_apply] using corrected_row_affine t ht x.1 x.2 i f
private theorem adjoint_expansion (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (i : Fin 6) :
    returnedAdjointRow t ht x.1 x.2 i = ∑ a : Fin 3,(noiseLinear a x:ℂ) • leftColumn t ht i a := by
  change correctedCovariantRow t ht x.1 x.2 i - Complex.I •
    (returnedCurrentColumn t ht i*(GaussCoframeForm.number+(2:ℂ) • (1:End))) = _
  rw [row_expansion]
  norm_num [Fin.sum_univ_succ,rightColumn,leftColumn,Fin.succ,linear_values]
  module

def coframeQuadraticColumn (t : ℝ) (ht : 0 < t) (a : QuadraticIndex) : End :=
  ∑ i : Fin 6,∑ j : Fin 6,leftColumn t ht i a.1*returnedMetric t ht i j*rightColumn t ht j a.2

private theorem quadratic_expansion (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) :
    returnedCoframeKinetic t ht x.1 x.2 =
      ∑ a : QuadraticIndex,(noiseQuadratic a x:ℂ) • coframeQuadraticColumn t ht a := by
  unfold returnedCoframeKinetic
  simp_rw [adjoint_expansion,row_expansion]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext i
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type,noiseQuadratic,Complex.ofReal_mul,coframeQuadraticColumn,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (noiseLinear b x:ℂ) (noiseLinear a x:ℂ)]

private theorem complete_pair (t : ℝ) (ht : 0 < t) (ξ η : ℝ) (f g : QuantumTest) :
    sourcePair (correctedCompleteCore t ht ξ η f) (correctedCompleteCore t ht ξ η g) =
      sourcePair (G t f) (G t g) := by
  change sourcePair (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η (G t f)))
    (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η (G t g))) = _
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _
theorem actual_corrected_coframe_quadratic_return (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (f : QuantumTest) :
    covariantKinetic (correctedCompleteCore t ht x.1 x.2 f) =
      correctedCompleteCore t ht x.1 x.2 (quadraticSource (fun a => coframeQuadraticColumn t ht a f) x) := by
  have h := LinearMap.congr_fun (actual_corrected_coframe_second_order t ht x.1 x.2) f
  change covariantKinetic (correctedCompleteCore t ht x.1 x.2 f) = _ at h
  rw [quadratic_expansion] at h
  simpa only [Module.End.mul_apply,LinearMap.sum_apply,LinearMap.smul_apply,quadraticSource] using h
private theorem quadratic_gain (t : ℝ) (v : QuadraticIndex → QuantumTest) (x : ℝ×ℝ) :
    G t (quadraticSource v x) = quadraticSource (fun a => G t (v a)) x := by
  simp only [quadraticSource,map_sum,map_smul]

/-- Both original coframe second-order legs have genuine Gaussian integrability and all 81 cross terms. -/
theorem actual_corrected_coframe_square_gaussian (t : ℝ) (ht : 0 < t) (f g : QuantumTest) :
    Integrable (fun x : ℝ×ℝ => sourcePair (covariantKinetic (correctedCompleteCore t ht x.1 x.2 f))
      (covariantKinetic (correctedCompleteCore t ht x.1 x.2 g))) (γ.prod γ) ∧
    (∫ x : ℝ×ℝ, sourcePair (covariantKinetic (correctedCompleteCore t ht x.1 x.2 f))
      (covariantKinetic (correctedCompleteCore t ht x.1 x.2 g)) ∂γ.prod γ) =
      ∑ a,∑ b,(quadraticMoment a b:ℂ)*sourcePair (G t (coframeQuadraticColumn t ht a f))
        (G t (coframeQuadraticColumn t ht b g)) := by
  have he (x : ℝ×ℝ) : sourcePair (covariantKinetic (correctedCompleteCore t ht x.1 x.2 f))
      (covariantKinetic (correctedCompleteCore t ht x.1 x.2 g)) =
      sourcePair (quadraticSource (fun a => G t (coframeQuadraticColumn t ht a f)) x)
        (quadraticSource (fun b => G t (coframeQuadraticColumn t ht b g)) x) := by
    rw [actual_corrected_coframe_quadratic_return,actual_corrected_coframe_quadratic_return,complete_pair,quadratic_gain,quadratic_gain]
  simpa only [he,Module.End.one_apply] using
    quadratic_gaussian_pair (fun a => G t (coframeQuadraticColumn t ht a f))
      (fun a => G t (coframeQuadraticColumn t ht a g)) (1:End)

/-- The two legs are the unchanged normalized source at the original F and frequency. -/
theorem actual_normalized_coframe_square_source (t : ℝ) (ht : 0 < t)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    Integrable (fun x : ℝ×ℝ => ‖embed (covariantKinetic (correctedCompleteCore t ht x.1 x.2 w))‖^2) (γ.prod γ) ∧
    (∫ x : ℝ×ℝ, ‖embed (covariantKinetic (correctedCompleteCore t ht x.1 x.2 w))‖^2 ∂γ.prod γ) =
      (∑ a,∑ b,(quadraticMoment a b:ℂ)*sourcePair (G t (coframeQuadraticColumn t ht a w))
        (G t (coframeQuadraticColumn t ht b w))).re := by
  intro w
  have h := actual_corrected_coframe_square_gaussian t ht w w
  have he (x : ℝ×ℝ) : (sourcePair (covariantKinetic (correctedCompleteCore t ht x.1 x.2 w))
      (covariantKinetic (correctedCompleteCore t ht x.1 x.2 w))).re =
      ‖embed (covariantKinetic (correctedCompleteCore t ht x.1 x.2 w))‖^2 := by
    exact (norm_sq_eq_re_inner (𝕜:=ℂ) (embed (covariantKinetic (correctedCompleteCore t ht x.1 x.2 w)))).symm
  refine ⟨?_,?_⟩
  · simpa only [RCLike.re_eq_complex_re,he] using! h.1.re
  · rw [←h.2]
    have hre := Complex.reCLM.integral_comp_comm h.1
    change (∫ x : ℝ×ℝ, (sourcePair (covariantKinetic (correctedCompleteCore t ht x.1 x.2 w))
      (covariantKinetic (correctedCompleteCore t ht x.1 x.2 w))).re ∂γ.prod γ) = _ at hre
    simpa only [he,Complex.reCLM_apply] using! hre
end LowEnergy.FirstCurrentPayerNext
