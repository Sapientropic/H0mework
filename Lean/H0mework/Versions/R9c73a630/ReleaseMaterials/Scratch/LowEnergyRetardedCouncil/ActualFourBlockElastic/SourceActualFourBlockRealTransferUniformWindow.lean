import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferFiber
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferWindow
import Mathlib.Topology.Order.Compact
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreHilbert
open GaussCoreDifferential GaussUnitaryHistory
open ActualFourBlockSource ActualFourBlockDetector ActualFourBlockRetarded
open ActualFourBlockHilbertOperator FullYDynamicSource FullYDynamicResponse
open MeasureTheory Set

/-- The price is on the complete physical Hilbert space and is independent of
both response carriers; transfer is fixed while response frequency is integrated. -/
theorem actual_uniform_output_difference_bound (p : Kinematics) (C : ℝ)
    (hC : ‖coherentFiber p‖ ≤ C) (F G : Index) (sharp : Bool) (q : QuantumTest)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun w : ℝ =>
      ‖output F sharp q p advanced μ hμ w - output G sharp q p advanced μ hμ w‖^2) ∧
    (∫w : ℝ,‖output F sharp q p advanced μ hμ w - output G sharp q p advanced μ hμ w‖^2) ≤
      C^2 * (∫w : ℝ,‖embed (literalResponse F sharp q advanced μ hμ w) -
        embed (literalResponse G sharp q advanced μ hμ w)‖^2) := by
  obtain ⟨hi,hb⟩ := actual_output_difference_integral_bound F G sharp q p advanced μ hμ
  refine ⟨hi,hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hC 2)
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- One actual punctured source window supplies a uniform complete four-block
operator price on each closed subannulus, with both charge branches intact. -/
theorem actual_real_transfer_uniform_window :
    ∃δ : ℝ,0 < δ ∧ ∀a b : ℝ,0 < a → a ≤ b → b < δ →
      ∃C : ℝ,0 < C ∧ ∀x : ℝ,a ≤ |x| → |x| ≤ b →
        ∃p : Kinematics,p.x = x ∧ p.k = 0 ∧ p.pLeft = 0 ∧ p.pRight = 0 ∧
          (∀dual : Bool,coherentTree p (fiberCoordinates (MixedSpectatorCandidate.candidate dual)) ≠ 0) ∧
          ‖coherentFiber p‖ ≤ C ∧ ‖operator p‖ ≤ C ∧
          ∀F G : Index,∀sharp : Bool,∀q : QuantumTest,∀advanced : Bool,∀μ : ℝ,∀hμ : 0 < μ,
            Integrable (fun w : ℝ =>
              ‖output F sharp q p advanced μ hμ w - output G sharp q p advanced μ hμ w‖^2) ∧
            (∫w : ℝ,‖output F sharp q p advanced μ hμ w - output G sharp q p advanced μ hμ w‖^2) ≤
              C^2 * (∫w : ℝ,‖embed (literalResponse F sharp q advanced μ hμ w) -
                embed (literalResponse G sharp q advanced μ hμ w)‖^2) := by
  obtain ⟨δ,hδ,hw⟩ := actual_real_transfer_source_window
  refine ⟨δ,hδ,?_⟩
  intro a b ha _hab hb
  let K : Set ℝ := Icc (-b) b ∩ {x | a ≤ |x|}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hc : ContinuousOn (fun x : ℝ => axialFiber x) K := by
    intro x hx
    have hax : a ≤ |x| := hx.2
    have hxb : |x| ≤ b := abs_le.mpr ⟨hx.1.1,hx.1.2⟩
    obtain ⟨p,hpx,hpk,_,_,_⟩ := hw x (ha.trans_le hax) (hxb.trans_lt hb)
    have hC : MixedSpectatorCanonical79Exchange.RegularMomentum (x : ℂ) 0 := by
      simpa only [hpx,hpk] using p.canonicalRegular
    have hD : MixedSpectatorDual24Exchange.RegularMomentum (x : ℂ) 0 := by
      simpa only [hpx,hpk] using p.dualRegular
    have hS : MixedSpectatorScalar61Exchange.denominator
        (MixedSpectatorPairedSourceFrame.worldTransfer (x : ℂ) 0) ≠ 0 := by
      simpa only [hpx,hpk] using p.scalarRegular
    exact ((actual_axial_fiber_analytic x hC hD hS).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨c,hc⟩ := hK.bddAbove_image hc.norm
  refine ⟨max c 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x hax hxb
  obtain ⟨p,hpx,hpk,hpL,hpR,hn⟩ := hw x (ha.trans_le hax) (hxb.trans_lt hb)
  have hC : MixedSpectatorCanonical79Exchange.RegularMomentum (x : ℂ) 0 := by
    simpa only [hpx,hpk] using p.canonicalRegular
  have hD : MixedSpectatorDual24Exchange.RegularMomentum (x : ℂ) 0 := by
    simpa only [hpx,hpk] using p.dualRegular
  have hS : MixedSpectatorScalar61Exchange.denominator
      (MixedSpectatorPairedSourceFrame.worldTransfer (x : ℂ) 0) ≠ 0 := by
    simpa only [hpx,hpk] using p.scalarRegular
  have hp : p = axialKinematics x hC hD hS := by
    rcases p with ⟨px,pk,pL,pR,hpc,hpd,hps⟩
    dsimp only at hpx hpk hpL hpR
    subst px pk pL pR
    rfl
  have hbound : ‖coherentFiber p‖ ≤ max c 1 := by
    rw [hp,actual_axial_fiber]
    exact (hc (mem_image_of_mem _ ⟨abs_le.mp hxb,hax⟩)).trans (le_max_left _ _)
  refine ⟨p,hpx,hpk,hpL,hpR,hn,hbound,(actual_operator_bound p).trans hbound,?_⟩
  intro F G sharp q advanced μ hμ
  exact actual_uniform_output_difference_bound p (max c 1) hbound F G sharp q advanced μ hμ

end LowEnergy.ActualFourBlockRealTransfer
