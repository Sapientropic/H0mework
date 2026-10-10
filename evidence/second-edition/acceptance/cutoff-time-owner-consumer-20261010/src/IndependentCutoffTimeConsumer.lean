import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffTime
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.CutoffIndependentConsumer
open GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory GaussCoreLabel
open ActualThreeParticleCutoffGram ActualCutoffFrequencyBase ActualThreeParticleCutoffFamily
open SourceFamilyHilbert FullYSourceFiniteTimeIntegral FullYSourceCutoffVolterra
open FullYSourceResolventGraphSplice FullYPairedParseval FullYDynamicSourceNext
open SourceResolventBandLimit SourceResolventLorentzian MeasureTheory Filter Set
open scoped Topology InnerProductSpace FourierTransform Interval
private abbrev L2H := Lp H 2 (volume : Measure ℝ)
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H

open LowEnergy.ActualThreeParticleCutoffTime
example (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) : Integrable (fun t => ‖wave F n sharp advanced μ x t‖^2) := actual_wave_square_integrable F n sharp advanced μ hμ x

example (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) (ξ : ℝ) :
    ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) • 𝓕 (wave F n sharp advanced μ x) ξ =
      branchInverse F n sharp (sourceLine advanced μ ξ) x := actual_wave_fourier F n sharp advanced μ hμ x ξ

example (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) :
    (∫w : ℝ,‖branchInverse F n sharp (frequency advanced μ w) x‖^2)=
      (2*Real.pi)*(∫t : ℝ,‖wave F n sharp advanced μ x t‖^2) := actual_absolute_time_mass F n sharp advanced μ hμ x

end LowEnergy.CutoffIndependentConsumer
#print axioms LowEnergy.ActualThreeParticleCutoffTime.actual_wave_square_integrable
#print axioms LowEnergy.ActualThreeParticleCutoffTime.actual_wave_fourier
#print axioms LowEnergy.ActualThreeParticleCutoffTime.actual_absolute_time_mass
