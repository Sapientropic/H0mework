import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedCoframeWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteHeatHamiltonianSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedNativeGaussianWork
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiHeatCorrectedHamiltonianSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open ClockPhiHeatCorrectedCovarianceSource ClockPhiHeatCorrectedCoframeWork
open ClockPhiHeatCoframeHamiltonianWork SourceClockPhiCompleteHeatHamiltonianSource
open SourceClockPhiCombinedScalePressure SourceClockPhiCorrectedNativeGaussianWork MeasureTheory Filter
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev nativeHamiltonian:QuantumTest→ₗ[ℂ]QuantumTest:=nativeAction+GaussMatterCore.matterAction
private theorem whole_pair_split(f g:QuantumTest):
    sourcePair f (GaussDiagonalHistory.diagonalAction g)=
      sourcePair f (nativeHamiltonian g)+sourcePair f (GaussCoframeForm.coframeAction g):=by
  simp only [GaussDiagonalHistory.diagonalAction,nativeHamiltonian,LinearMap.add_apply,
    sourcePair,map_add,inner_add_right]
  ring

private theorem integral_sum {X:Type*}[MeasurableSpace X](μ:Measure X){F G:X→ℂ}
    (hF:Integrable F μ)(hG:Integrable G μ):
    (∫x,F x+G x ∂μ)=(∫x,F x ∂μ)+(∫x,G x ∂μ):=by
  convert! integral_add hF hG using 1

theorem actual_corrected_hamiltonian_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (GaussDiagonalHistory.diagonalAction (correctedCompleteCore t ht x.1 x.2 g))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (GaussDiagonalHistory.diagonalAction (correctedCompleteCore t ht x.1 x.2 g)) ∂γ.prod γ)=
      wholeGaussianHeatHamiltonianPair t ht f g+
        sourcePair (combinedGenerator f) (correctedCoframeCovariance t ht (combinedGenerator g)):=by
  have hN:=actual_corrected_native_gaussian t ht f g
  have hC:=actual_corrected_coframe_gaussian t ht f g
  have hO:=actual_complete_coframe_gaussian t ht f g
  have hH:=actual_complete_heat_hamiltonian_gaussian t ht f g
  have hi:Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (GaussDiagonalHistory.diagonalAction (correctedCompleteCore t ht x.1 x.2 g))) (γ.prod γ):=by
    apply (hN.1.add hC.1).congr
    exact Eventually.of_forall (fun x=>(whole_pair_split _ _).symm)
  refine ⟨hi,?_⟩
  have hOld:(∫ξ:ℝ,sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (GaussDiagonalHistory.diagonalAction (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g)) ∂γ)=
      (∫ξ:ℝ,sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (nativeHamiltonian (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g)) ∂γ)+
      (∫ξ:ℝ,sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (GaussCoframeForm.coframeAction (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g)) ∂γ):=by
    simp_rw [whole_pair_split]
    exact integral_sum γ hN.2.1 hO.1
  simp_rw [whole_pair_split]
  rw [integral_sum (γ.prod γ) hN.1 hC.1,hN.2.2,hC.2]
  rw [hH.2] at hOld
  rw [hOld]
  ring

theorem actual_corrected_hamiltonian_covariance(t:ℝ)(ht:0<t)(f:QuantumTest):
    (wholeGaussianHeatHamiltonianPair t ht f f).re≤
      (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
        (GaussDiagonalHistory.diagonalAction (correctedCompleteCore t ht x.1 x.2 f)) ∂γ.prod γ).re:=by
  rw [(actual_corrected_hamiltonian_gaussian t ht f f).2,Complex.add_re]
  exact le_add_of_nonneg_right (actual_corrected_covariance_nonneg t ht (combinedGenerator f))
end LowEnergy.ClockPhiHeatCorrectedHamiltonianSource
