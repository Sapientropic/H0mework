import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffGram
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCutoffFrequencyBase
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualThreeParticleCutoffFamily
open GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory GaussCoreLabel
open FullYSourceResolventGraphSplice FullYSourceCutoffVolterra ActualThreeParticleCutoffGram
open ActualCutoffFrequencyBase MeasureTheory Filter
open scoped BigOperators Topology
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H

def responsePrice (n : ℕ) (μ : ℝ) : ℝ := ∑j : Fin 4,(μ⁻¹*‖cutoff n‖)^j.val

theorem actual_response_price_nonnegative (n : ℕ) (μ : ℝ) (hμ : 0 < μ) :
    0 ≤ responsePrice n μ :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg (mul_nonneg (inv_nonneg.mpr hμ.le) (norm_nonneg _)) _)

theorem actual_frequency_resolvent_norm (F : Index) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    ‖finiteResolvent F (frequency advanced μ w)‖ ≤ μ⁻¹ := by
  simpa only [frequency_abs_im advanced μ hμ w,one_div] using
    finite_resolvent_norm F _ (frequency_nonreal advanced μ hμ w)

private theorem step_norm (F : Index) (n : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    ‖step F n (frequency advanced μ w)‖ ≤ μ⁻¹*‖cutoff n‖ := by
  rw [step,norm_neg]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (actual_frequency_resolvent_norm F advanced μ hμ w) (norm_nonneg _))

private theorem power_apply_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) (B : ℝ) (hB : 0 ≤ B) (hA : ‖A‖ ≤ B) (j : ℕ) (v : E) :
    ‖(A^j) v‖ ≤ B^j*‖v‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ',mul_apply_eq_comp,pow_succ]
    calc
      _ ≤ B*‖(A^j) v‖ := (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
      _ ≤ B*(B^j*‖v‖) := mul_le_mul_of_nonneg_left ih hB
      _ = _ := by ring

theorem actual_leg_price (F : Index) (n : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (w : ℝ) (j : ℕ) :
    ‖embed (leg F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q j)‖ ≤
      (μ⁻¹*‖cutoff n‖)^j*‖finiteResolvent F (frequency advanced μ w) (embed q)‖ := by
  rw [actual_leg_embed]
  exact power_apply_price _ _
    (mul_nonneg (inv_nonneg.mpr hμ.le) (norm_nonneg _))
    (step_norm F n advanced μ hμ w) j _

/-- The actual Number-three source truncates the original inverse before its
uniform frequency price is generated; no caller supplies a propagation bound. -/
theorem actual_response_price (F : Index) (n : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) (w : ℝ) :
    ‖inverse F n (frequency advanced μ w) (embed q)‖ ≤
      responsePrice n μ*‖finiteResolvent F (frequency advanced μ w) (embed q)‖ := by
  rw [actual_full_response F n _ (frequency_nonreal advanced μ hμ w) q hq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑j : Fin 4,(μ⁻¹*‖cutoff n‖)^j.val*
        ‖finiteResolvent F (frequency advanced μ w) (embed q)‖ :=
      Finset.sum_le_sum (fun j _ => actual_leg_price F n advanced μ hμ q w j.val)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem actual_inverse_frequency_continuous (F : Index) (n : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) : Continuous (fun w : ℝ => inverse F n (frequency advanced μ w)) := by
  have hr := actual_frequency_resolvent_continuous F advanced μ hμ
  have hs : Continuous (fun w : ℝ => step F n (frequency advanced μ w)) := by
    unfold step
    exact (hr.mul continuous_const).neg
  change Continuous (fun w : ℝ =>
    (∑j ∈ Finset.range 57,(step F n (frequency advanced μ w))^j)*
      finiteResolvent F (frequency advanced μ w))
  exact (continuous_finsetSum _ (fun j _ => hs.pow j)).mul hr

theorem actual_response_memLp (F : Index) (n : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) :
    MemLp (fun w : ℝ => inverse F n (frequency advanced μ w) (embed q)) 2 (volume : Measure ℝ) :=
  (actual_base_memLp F advanced μ hμ (embed q)).of_le_mul
    (((actual_inverse_frequency_continuous F n advanced μ hμ).clm_apply continuous_const).aestronglyMeasurable)
    (Eventually.of_forall (actual_response_price F n advanced μ hμ q hq))

end LowEnergy.ActualThreeParticleCutoffFamily
