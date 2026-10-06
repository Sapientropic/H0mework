import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricWindowDecay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseElectricMomentDecay
open GaussCoreHilbert GaussCoreDifferential GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceInverseElectricCurrentForm SourceInverseElectricCurrentEnergy SourceInverseElectricScalarEnergy
open SourceInverseElectricCurrentFactor SourceInverseElectricWindowDecay SourceScalarDoubleCurrent SourceMixedNativeReturn
open SourceScalarPairedTransport SourceScalarPositiveBulkWard FullYSourceResolventGraphSplice
open SourceInverseDefectCurrentResponse SourceResolventBandLimit MeasureTheory
open scoped InnerProductSpace ENNReal
attribute [local irreducible] state sourceRead SourceScalarDoubleCurrent.fullInsertion

def higherCurrentLeg (sharp : Bool) (p : QuantumTest) (r : Row) : QuantumTest :=
  higherEnvelopeAction sharp (gaugeDirection r.2.1 r.1) p

def weightedHigherCurrentLeg (sharp : Bool) (q : QuantumTest) (r : Row) : QuantumTest :=
  higherEnvelopeAction sharp (gaugeDirection r.2.2 r.1)
    (multiply (fun z => gaugeWeight z r.2.1 r.2.2) (gaugeWeight_smooth r.2.1 r.2.2) q)

/-- This genuine moving-input moment budget is independent of both cutoff endpoints. -/
def momentBudget (sharp : Bool) (p q : QuantumTest) : ℝ :=
  (1/2 : ℝ)*((∑ r : Row,‖embed (momentumLeg p r)‖^2)*
      (∑ r : Row,‖embed (weightedHigherCurrentLeg sharp q r)‖^2)+
    (∑ r : Row,‖embed (higherCurrentLeg (!sharp) p r)‖^2)*
      (∑ r : Row,‖embed (weightedMomentumLeg q r)‖^2))

private theorem scalar_budget_decay (sharp : Bool) (m ell : ℕ) (hle : m ≤ ell) (p q : QuantumTest) :
    scalarFormBudget sharp m ell p q ≤ (1/(m+2 : ℝ))^2*momentBudget sharp p q := by
  have hL : (∑ r : Row,‖embed (scalarCurrentLeg (!sharp) m ell p r)‖^2) ≤
      (1/(m+2 : ℝ))^2*∑ r : Row,‖embed (higherCurrentLeg (!sharp) p r)‖^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => actual_scalar_window_energy (!sharp) m ell hle _ p)
  have hR : (∑ r : Row,‖embed (weightedScalarCurrentLeg sharp m ell q r)‖^2) ≤
      (1/(m+2 : ℝ))^2*∑ r : Row,‖embed (weightedHigherCurrentLeg sharp q r)‖^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => actual_scalar_window_energy sharp m ell hle _ _)
  unfold scalarFormBudget momentBudget
  calc
    _ ≤ (1/2 : ℝ)*((∑ r : Row,‖embed (momentumLeg p r)‖^2)*
      ((1/(m+2 : ℝ))^2*∑ r : Row,‖embed (weightedHigherCurrentLeg sharp q r)‖^2)+
      ((1/(m+2 : ℝ))^2*∑ r : Row,‖embed (higherCurrentLeg (!sharp) p r)‖^2)*
      (∑ r : Row,‖embed (weightedMomentumLeg q r)‖^2)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hR (by positivity))
          (mul_le_mul_of_nonneg_right hL (by positivity))) (by norm_num)
    _ = _ := by ring

def momentResponseBudget (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) : ℝ :=
  momentBudget sharp
    (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
    (state F z hz g)

/-- The complete original electric response has explicit cutoff decay against a source moment with no cutoff dependence. -/
theorem actual_electric_moment_energy (sharp : Bool) (m ell : ℕ) (hle : m ≤ ell)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    ‖inner ℂ (k : H) ((finiteResolvent F z*sourceRead F g
      (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*finiteResolvent F z) (g : H))‖^2 ≤
      (1/(m+2 : ℝ))^2*momentResponseBudget sharp F z hz g k :=
  (actual_electric_scalar_response sharp m ell F z hz g k).trans
    (scalar_budget_decay sharp m ell hle _ _)

theorem actual_electric_moment_full_frequency (sharp : Bool) (m ell : ℕ) (hle : m ≤ ell)
    (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (k : H) ((finiteResolvent F (line μ w)*sourceRead F g
      (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*finiteResolvent F (line μ w)) (g : H))‖^2)) ≤
      ENNReal.ofReal ((1/(m+2 : ℝ))^2)*
        ∫⁻ w : ℝ,ENNReal.ofReal (momentResponseBudget sharp F (line μ w)
          (by simpa only [line_im] using hμ.ne') g k) := by
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal ((1/(m+2 : ℝ))^2*
      momentResponseBudget sharp F (line μ w) (by simpa only [line_im] using hμ.ne') g k) := by
        apply lintegral_mono
        intro w
        exact ENNReal.ofReal_le_ofReal (actual_electric_moment_energy sharp m ell hle F (line μ w)
          (by simpa only [line_im] using hμ.ne') g k)
    _ = _ := by
      simp only [ENNReal.ofReal_mul (sq_nonneg (1/(m+2 : ℝ)))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end LowEnergy.SourceInverseElectricMomentDecay
