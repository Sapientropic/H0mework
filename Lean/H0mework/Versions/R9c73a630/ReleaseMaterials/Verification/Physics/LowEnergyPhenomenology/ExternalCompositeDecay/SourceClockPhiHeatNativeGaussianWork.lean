import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatNativeHamiltonianWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatLocalNativeGaussian
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiHeatNativeGaussianWork
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussNativeForm
open SourceClockPhiCompleteHeatGainPayment SourceClockPhiHeatNativeHamiltonianWork
open SourceClockPhiHeatLocalNativeGaussian MeasureTheory

theorem actual_complete_scalar_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair (completeHeatCore t ht ξ f)
      (scalarKinetic (completeHeatCore t ht ξ g))) (ProbabilityTheory.gaussianReal 0 1) ∧
    (∫ξ:ℝ,sourcePair (completeHeatCore t ht ξ f)
      (scalarKinetic (completeHeatCore t ht ξ g)) ∂ProbabilityTheory.gaussianReal 0 1)=
      sourcePair f (gaussianProfileWeight t ht (-7/9) (scalarKinetic g)):=by
  have h:=actual_gaussian_weighted_source_pair t ht (-2/3) 2 f (scalarKinetic g)
  have he(ξ:ℝ):sourcePair (completeHeatCore t ht ξ f) (scalarKinetic (completeHeatCore t ht ξ g))=
      sourcePair f (heatProfileWeight t ht (-2/3) 2 ξ (scalarKinetic g)):=
    actual_complete_scalar_source t ht ξ f g
  constructor
  · exact h.1.congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm))
  · simp_rw [he]
    convert h.2 using 1; norm_num

theorem actual_complete_gauge_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair (completeHeatCore t ht ξ f)
      (gaugeKinetic (completeHeatCore t ht ξ g))) (ProbabilityTheory.gaussianReal 0 1) ∧
    (∫ξ:ℝ,sourcePair (completeHeatCore t ht ξ f)
      (gaugeKinetic (completeHeatCore t ht ξ g)) ∂ProbabilityTheory.gaussianReal 0 1)=
      sourcePair f (gaussianProfileWeight t ht (11/9) (gaugeKinetic g)):=by
  have h:=actual_gaussian_weighted_source_pair t ht (2/3) (-2) f (gaugeKinetic g)
  have he(ξ:ℝ):sourcePair (completeHeatCore t ht ξ f) (gaugeKinetic (completeHeatCore t ht ξ g))=
      sourcePair f (heatProfileWeight t ht (2/3) (-2) ξ (gaugeKinetic g)):=
    actual_complete_gauge_source t ht ξ f g
  constructor
  · exact h.1.congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm))
  · simp_rw [he]
    convert h.2 using 1; norm_num

end LowEnergy.SourceClockPhiHeatNativeGaussianWork
