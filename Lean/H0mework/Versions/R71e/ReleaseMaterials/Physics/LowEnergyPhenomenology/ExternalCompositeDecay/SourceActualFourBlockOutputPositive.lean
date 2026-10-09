import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualRetardedOutputNonzero
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockOutputPositive
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDensityCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open ActualFourBlockSource ActualFourBlockRetarded ActualRetardedOutputNonzero MixedSpectatorCandidate
open SourceResolventBandLimit MeasureTheory Filter
open scoped Topology ENNReal
attribute [local irreducible] embed coherentSource coherentTree

/-- Exact high-frequency return of the original coherent four-block output. -/
theorem actual_coherent_scaled_return (F : Index) (sharp : Bool) (q : QuantumTest)
    (p : Kinematics) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Tendsto (fun w : ℝ => line (FullYPairedParseval.direction advanced*μ) w •
      output F sharp q p advanced μ hμ w) atTop (𝓝 (-embed (coherentSource p q))) :=
  actual_output_scaled_limit F sharp q (coherentSource p) advanced μ hμ

/-- Conditional consumer: the full coherent source nonzero witness is paid
by the separate exact elastic producer, not by this implication. -/
theorem actual_coherent_positive_spectrum (F : Index) (sharp : Bool) (q : QuantumTest)
    (p : Kinematics) (hq : coherentSource p q ≠ 0) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    (∀ᶠ w : ℝ in atTop, output F sharp q p advanced μ hμ w ≠ 0) ∧
      0 < spectrum F sharp q p advanced μ hμ Set.univ ∧
      spectrum F sharp q p advanced μ hμ Set.univ < ∞ := by
  have mass := actual_spectrum_bands F sharp q p advanced μ hμ
  refine ⟨actual_output_eventually_nonzero F sharp q (coherentSource p) hq advanced μ hμ,?_,mass.2⟩
  rw [mass.1 Set.univ MeasurableSet.univ,Measure.restrict_univ,ENNReal.ofReal_pos]
  exact (actual_output_total_pos F sharp q (coherentSource p) hq advanced μ hμ).2

theorem actual_coherent_positive_band (F : Index) (sharp : Bool) (q : QuantumTest)
    (p : Kinematics) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ)
    (hw : output F sharp q p advanced μ hμ w ≠ 0)
    (B : Set ℝ) (hB : MeasurableSet B) (hBw : B ∈ 𝓝 w) :
    0 < spectrum F sharp q p advanced μ hμ B := by
  rw [(actual_spectrum_bands F sharp q p advanced μ hμ).1 B hB,ENNReal.ofReal_pos]
  exact actual_output_neighbourhood_pos F sharp q (coherentSource p) advanced μ hμ w hw B hBw

/-- The original nonzero CAR output lifts through the same actual profile;
there is no new external-state or core-output certificate premise. -/
theorem actual_candidate_core_nonzero (p : Kinematics) (dual : Bool) (f : ScalarTest)
    (hf : f GaussHistoryHilbert.sourcePoint.val=1)
    (tree : coherentTree p (fiberCoordinates (candidate dual)) ≠ 0) :
    coherentSource p (candidateTest dual f) ≠ 0 := by
  intro h
  have hp := congrArg (fun u : QuantumTest => fiberCoordinates (u GaussHistoryHilbert.sourcePoint.val)) h
  rw [actual_coherent_source_point] at hp
  change coherentTree p (fiberCoordinates (f GaussHistoryHilbert.sourcePoint.val • candidate dual)) = 0 at hp
  rw [hf,one_smul] at hp
  exact tree hp

theorem actual_candidate_positive_spectrum (p : Kinematics) (dual : Bool) (f : ScalarTest)
    (hf : f GaussHistoryHilbert.sourcePoint.val=1)
    (tree : coherentTree p (fiberCoordinates (candidate dual)) ≠ 0)
    (F : Index) (sharp advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    0 < spectrum F sharp (candidateTest dual f) p advanced μ hμ Set.univ :=
  (actual_coherent_positive_spectrum F sharp (candidateTest dual f) p
    (actual_candidate_core_nonzero p dual f hf tree) advanced μ hμ).2.1

end LowEnergy.ActualFourBlockOutputPositive
