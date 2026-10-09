import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockOptical.SourceActualFourBlockDetector
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualFourBlockRetarded
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussBoundedMultiplier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.ActualFourBlockHilbertOperator
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open ActualFourBlockSource ActualFourBlockDetector ActualFourBlockRetarded
open FullYDynamicSource FullYDynamicResponse FullYPairedParseval CompositeFullYBorn
open MeasureTheory Filter
open scoped ContDiff
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H

private theorem smooth (p : Kinematics) :
    ∀z : physicalChart, ContDiffAt ℝ ∞ (fun _ : SourceCoordinateSlice => coherentFiber p) z.val :=
  fun _ => contDiffAt_const

private theorem commutes (p : Kinematics) :
    ∀z : physicalChart,∀w : ℕ → ℂ,
      Commute (GaussFockWeights.weight w) ((fun _ : SourceCoordinateSlice => coherentFiber p) z) :=
  fun _ w => actual_coherent_weight p w

private theorem bound (p : Kinematics) :
    ∀z : physicalChart,∀v : FockFiber,
      ‖(fun _ : SourceCoordinateSlice => coherentFiber p) z v‖ ≤ ‖coherentFiber p‖*‖v‖ :=
  fun _ v => (coherentFiber p).le_opNorm v

/-- The original four-block finite Fock action extends on the original
Number-weighted Hilbert space before any finite response carrier is chosen. -/
def operator (p : Kinematics) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (fun _ => coherentFiber p) (smooth p) (commutes p)
    ‖coherentFiber p‖ (norm_nonneg _) (bound p)

theorem actual_operator_core (p : Kinematics) (q : QuantumTest) :
    operator p (embed q) = embed (coherentSource p q) := by
  rw [operator,GaussBoundedMultiplier.extension_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change coherentFiber p (q z) = coherentSource p q z
  exact (actual_coherent_fiber_point p q z).symm

theorem actual_operator_bound (p : Kinematics) : ‖operator p‖ ≤ ‖coherentFiber p‖ :=
  GaussBoundedMultiplier.extension_norm _ (smooth p) (commutes p)
    _ (norm_nonneg _) (bound p)

theorem actual_output_return (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    operator p (embed (literalResponse F sharp q advanced μ hμ w)) =
      output F sharp q p advanced μ hμ w :=
  actual_operator_core p _

theorem actual_causal_return (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (t : ℝ) :
    operator p (sourceWave F sharp q advanced μ t) = causalOutput F sharp q p advanced μ t := by
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · simp only [sourceWave,causalOutput,causalWave,Set.indicator_of_mem ht,map_smul,actual_operator_core]
  · simp only [sourceWave,causalOutput,causalWave,Set.indicator_of_notMem ht,map_zero]

theorem actual_output_difference_bound (F G : Index) (sharp : Bool) (q : QuantumTest)
    (p : Kinematics) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    ‖output F sharp q p advanced μ hμ w - output G sharp q p advanced μ hμ w‖ ≤
      ‖coherentFiber p‖ * ‖embed (literalResponse F sharp q advanced μ hμ w) -
        embed (literalResponse G sharp q advanced μ hμ w)‖ := by
  rw [←actual_output_return,←actual_output_return,←map_sub]
  exact ((operator p).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (actual_operator_bound p) (norm_nonneg _))

/-- The actual exchange price is uniform in both finite carriers. Only the
original fullY response difference remains to be paid by its cofinal producer. -/
theorem actual_output_difference_integral_bound (F G : Index) (sharp : Bool) (q : QuantumTest)
    (p : Kinematics) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun w : ℝ =>
      ‖output F sharp q p advanced μ hμ w - output G sharp q p advanced μ hμ w‖^2) ∧
      (∫w : ℝ,‖output F sharp q p advanced μ hμ w - output G sharp q p advanced μ hμ w‖^2) ≤
        ‖coherentFiber p‖^2 * (∫w : ℝ,
          ‖embed (literalResponse F sharp q advanced μ hμ w) -
            embed (literalResponse G sharp q advanced μ hμ w)‖^2) := by
  let u := fun w : ℝ => embed (literalResponse F sharp q advanced μ hμ w) -
    embed (literalResponse G sharp q advanced μ hμ w)
  have hF := (memLp_two_iff_integrable_sq_norm
    (actual_response_continuous F sharp q advanced μ hμ).aestronglyMeasurable).mpr
      (actual_response_square_integrable F sharp q advanced μ hμ)
  have hG := (memLp_two_iff_integrable_sq_norm
    (actual_response_continuous G sharp q advanced μ hμ).aestronglyMeasurable).mpr
      (actual_response_square_integrable G sharp q advanced μ hμ)
  have hu : Continuous u :=
    (actual_response_continuous F sharp q advanced μ hμ).sub
      (actual_response_continuous G sharp q advanced μ hμ)
  have hi : Integrable (fun w : ℝ => ‖u w‖^2) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp (hF.sub hG)
  have he (w : ℝ) : output F sharp q p advanced μ hμ w -
      output G sharp q p advanced μ hμ w = operator p (u w) := by
    rw [map_sub,actual_output_return,actual_output_return]
  simp_rw [he]
  have hb (w : ℝ) : ‖operator p (u w)‖^2 ≤ ‖coherentFiber p‖^2*‖u w‖^2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (((operator p).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (actual_operator_bound p) (norm_nonneg _))) 2).trans_eq
        (mul_pow _ _ _)
  have ho : Integrable (fun w : ℝ => ‖operator p (u w)‖^2) := by
    apply (hi.const_mul (‖coherentFiber p‖^2)).mono'
      (((operator p).continuous.comp hu).norm.pow 2).aestronglyMeasurable
    exact Eventually.of_forall (fun w => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hb w)
  refine ⟨ho,?_⟩
  calc
    _ ≤ ∫w : ℝ,‖coherentFiber p‖^2*‖u w‖^2 :=
      integral_mono ho (hi.const_mul _) hb
    _ = _ := integral_const_mul _ _

end LowEnergy.ActualFourBlockHilbertOperator
