import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualFourBlockRetarded
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterPositiveOutputMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockCausalMass
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDensityCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open ActualFourBlockSource ActualFourBlockRetarded
open FullYDynamicSource FullYDynamicResponse CompositeFullYBorn
open MeasureTheory Filter
open scoped ENNReal

/-- The complete primal source's original bounded reader pays the absolute
causal output mass of the four-block word, retaining all coherent terms. -/
theorem actual_absolute_output_mass (F : Index) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun w : ℝ => density F false q p advanced μ hμ w) ∧
      Integrable (fun t : ℝ => ‖causalOutput F false q p advanced μ t‖^2) ∧
      (∫w : ℝ,density F false q p advanced μ hμ w) =
        (2*Real.pi)*(∫t : ℝ,‖causalOutput F false q p advanced μ t‖^2) := by
  have h := FourGradeOutputParseval.actual_output_positive_mass F q advanced μ hμ
    (sourceReader F false q (coherentSource p))
  have hw (w : ℝ) :
      sourceReader F false q (coherentSource p)
        (embed (literalResponse F false q advanced μ hμ w)) =
        output F false q p advanced μ hμ w := by
    exact source_reader_return F false q _ (coherentSource p)
      (actual_response_orbit F false q advanced μ hμ w)
  simp_rw [hw] at h
  simpa only [ActualFourBlockRetarded.density,actual_causal_readout] using h

theorem actual_causal_spectrum_mass (F : Index) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    spectrum F false q p advanced μ hμ Set.univ =
      ENNReal.ofReal ((2*Real.pi)*(∫t : ℝ,‖causalOutput F false q p advanced μ t‖^2)) := by
  rw [(actual_spectrum_bands F false q p advanced μ hμ).1 Set.univ MeasurableSet.univ,
    Measure.restrict_univ,(actual_absolute_output_mass F q p advanced μ hμ).2.2]

end LowEnergy.ActualFourBlockCausalMass
