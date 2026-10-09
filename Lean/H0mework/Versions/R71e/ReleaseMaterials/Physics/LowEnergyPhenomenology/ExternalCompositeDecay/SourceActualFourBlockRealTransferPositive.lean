import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferWindow
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockProfileFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransferPositive
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDensityCore
open GaussFockPair GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open ActualFourBlockSource ActualFourBlockRetarded ActualFourBlockDetector
open ActualFourBlockOutputPositive ActualFourBlockOptical ActualFourBlockCausalOnset
open MixedSpectatorCandidate FullYDynamicSource FullYDynamicResponse FullYPairedParseval
open GeneralThreeParticleResponse SourceResolventBandLimit SourceScalarPairedTransport
open ActualFourBlockRealTransfer ActualFourBlockProfileFamily
open MeasureTheory Filter
open scoped Topology ENNReal
/-- The original source generates one real transfer window and one profile
before all real transfers, independent duals and finite response carriers. -/
theorem actual_generated_source_real_transfer_positive :
    ∃δ : ℝ,0 < δ ∧ ∃f : ScalarTest,f GaussHistoryHilbert.sourcePoint.val = 1 ∧
      (∀dual : Bool,∀F : Index,∀advanced : Bool,∀μ : ℝ,∀hμ : 0 < μ,
        0 < correctionMeasure F (candidateTest dual f) advanced μ hμ Set.univ) ∧
      ∀x : ℝ,0 < |x| → |x| < δ →
        ∃p : Kinematics,p.x = x ∧ p.k = 0 ∧ p.pLeft = 0 ∧ p.pRight = 0 ∧
          (∀dual : Bool,coherentTree p (fiberCoordinates (candidate dual)) ≠ 0) ∧
          ∀dual : Bool,∀F : Index,∀sharp advanced : Bool,∀μ : ℝ,∀hμ : 0 < μ,
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
  obtain ⟨δ,hδ,hwindow⟩ := actual_real_transfer_source_window
  obtain ⟨f,hf,hY,hfamily⟩ := actual_generated_source_profile_family
  refine ⟨δ,hδ,f,hf,hY,?_⟩
  intro x hx hxd
  obtain ⟨p,hx,hk,hleft,hright,hne⟩ := hwindow x hx hxd
  refine ⟨p,hx,hk,hleft,hright,hne,?_⟩
  intro dual F sharp advanced μ hμ
  exact hfamily dual p (hne dual) F sharp advanced μ hμ

end LowEnergy.ActualFourBlockRealTransferPositive
