import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockOutputPositive
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockSharpCausalMass
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockOptical
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockCausalOnset
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaPositiveCorrection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockProfileFamily
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDensityCore
open GaussFockPair GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open ActualFourBlockSource ActualFourBlockRetarded ActualFourBlockDetector
open ActualFourBlockOutputPositive ActualFourBlockOptical ActualFourBlockCausalOnset
open MixedSpectatorCandidate FullYDynamicSource FullYDynamicResponse FullYPairedParseval
open GeneralThreeParticleResponse SourceResolventBandLimit SourceScalarPairedTransport
open MeasureTheory Filter
open scoped Topology ENNReal
attribute [local irreducible] embed coherentSource coherentTree sourcePair

private theorem bounded_Y_nonzero (dual : Bool) (f : ScalarTest)
    (hf : f GaussHistoryHilbert.sourcePoint.val = 1) :
    GaussYukawaOperator.bounded (embed (candidateTest dual f)) ≠ 0 := by
  intro hz
  rw [GaussYukawaOperator.bounded_core] at hz
  have ha : GaussYukawaCoefficient.action (candidateTest dual f) = 0 :=
    embed_injective (hz.trans (map_zero embed).symm)
  have ho : GaussYukawaOperator.originalAction (candidateTest dual f) = 0 := by
    rw [←GaussYukawaOperator.radius_action_return,ha,map_zero]
  exact actual_candidate_test_Y_nonzero dual f hf ho

/-- One original chart profile precedes both independent duals and every
regular external transfer. A separate actual exchange producer supplies the
nonzero tree at that transfer; all dynamic outputs consume this same profile. -/
theorem actual_generated_source_profile_family :
    ∃f : ScalarTest, f GaussHistoryHilbert.sourcePoint.val = 1 ∧
      (∀dual : Bool,∀F : Index,∀advanced : Bool,∀μ : ℝ,∀hμ : 0 < μ,
        0 < correctionMeasure F (candidateTest dual f) advanced μ hμ Set.univ) ∧
      ∀dual : Bool,∀p : Kinematics,
        coherentTree p (fiberCoordinates (candidate dual)) ≠ 0 →
        ∀F : Index,∀sharp advanced : Bool,∀μ : ℝ,∀hμ : 0 < μ,
        let q := candidateTest dual f
        let u := literalResponse F sharp q advanced μ hμ
        (∀ᶠw : ℝ in atTop,output F sharp q p advanced μ hμ w ≠ 0) ∧
        0 < spectrum F sharp q p advanced μ hμ Set.univ ∧
        spectrum F sharp q p advanced μ hμ Set.univ < ∞ ∧
        (∀ᶠw : ℝ in atTop,∀B : Set ℝ,MeasurableSet B → B ∈ 𝓝 w →
          0 < spectrum F sharp q p advanced μ hμ B) ∧
        0 < (∫t : ℝ,‖causalOutput F sharp q p advanced μ t‖^2) ∧
        spectrum F sharp q p advanced μ hμ Set.univ =
          ENNReal.ofReal ((2*Real.pi)*(∫t : ℝ,‖causalOutput F sharp q p advanced μ t‖^2)) ∧
        0 < direction advanced *
          ((∫w : ℝ,(sourcePair q (detector p (u w))).im) -
            (∫w : ℝ,(sourcePair (u w) (current p (u w))).im)/2 -
              (∫w : ℝ,(sourcePair (sourceY sharp (u w)) (detector p (u w))).im) +
                (∫w : ℝ,(sourcePair (defectAction F (u w)) (detector p (u w))).im)) ∧
        (∀t : ℝ,t ≤ 0 → causalOutput F sharp q p advanced μ t = 0) ∧
        Tendsto (causalOutput F sharp q p advanced μ) (𝓝[>] (0 : ℝ))
          (𝓝 (embed (coherentSource p q))) ∧
        (∀ᶠt : ℝ in 𝓝[>] (0 : ℝ),causalOutput F sharp q p advanced μ t ≠ 0) := by
  obtain ⟨f,hf⟩ := actual_scalar_test_exists
  refine ⟨f,hf,?_,?_⟩
  · intro dual F advanced μ hμ
    exact YukawaResolventDetection.actual_Y_correction_measure_pos F _
      (actual_candidate_test_sector dual f) (bounded_Y_nonzero dual f hf) advanced μ hμ
  · intro dual p htree F sharp advanced μ hμ
    dsimp only
    have hq := actual_candidate_core_nonzero p dual f hf htree
    have hout := actual_coherent_positive_spectrum F sharp (candidateTest dual f) p hq advanced μ hμ
    have hb : ∀ᶠw : ℝ in atTop,∀B : Set ℝ,MeasurableSet B → B ∈ 𝓝 w →
        0 < spectrum F sharp (candidateTest dual f) p advanced μ hμ B := by
      filter_upwards [hout.1] with w hw
      intro B hB hBw
      exact actual_coherent_positive_band F sharp _ p advanced μ hμ w hw B hB hBw
    have hm := ActualFourBlockSharpCausalMass.actual_causal_spectrum_mass F sharp
      (candidateTest dual f) p advanced μ hμ
    have ht := hout.2.1
    rw [hm,ENNReal.ofReal_pos] at ht
    have htime : 0 < (∫t : ℝ,‖causalOutput F sharp (candidateTest dual f) p advanced μ t‖^2) :=
      (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < 2*Real.pi)).mp ht
    have hp : 0 < ENNReal.ofReal μ *
        spectrum F sharp (candidateTest dual f) p advanced μ hμ Set.univ :=
      ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr hμ)) (ne_of_gt hout.2.1)
    rw [actual_optical_measure F sharp (candidateTest dual f) p advanced μ hμ
      Set.univ MeasurableSet.univ] at hp
    have hopt := ENNReal.ofReal_pos.mp hp
    simp only [Measure.restrict_univ] at hopt
    exact ⟨hout.1,hout.2.1,hout.2.2,hb,htime,hm,hopt,
      fun t ht => actual_causal_nonpositive_zero F sharp _ p advanced μ t ht,
      actual_causal_initial_return F sharp _ p advanced μ,
      actual_causal_initial_nonzero F sharp _ p hq advanced μ⟩

end LowEnergy.ActualFourBlockProfileFamily
