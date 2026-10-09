import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffFamily
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualThreeParticleCutoffFamily
open GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory GaussCoreLabel
open ActualThreeParticleCutoffGram ActualCutoffFrequencyBase
open SourceFamilyHilbert FullYSourceResolventGraphSplice FullYSourceCutoffVolterra
open scoped BigOperators

private theorem coe_neg_act_act {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) (A B : SourceFamilyOperator.Operator I E) (f : Family E u) :
    ((-SourceFamilyOperator.act u A (SourceFamilyOperator.act u B f) : Family E u) : Hilbert E u) =
      -SourceFamilyOperator.lift u A (SourceFamilyOperator.lift u B (f : Hilbert E u)) := by
  rw [UniformSpace.Completion.coe_neg,←SourceFamilyOperator.lift_coe,←SourceFamilyOperator.lift_coe]

private theorem power_apply_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) (j : ℕ) (v : E) : (A^(j+1)) v = A ((A^j) v) := by
  rw [pow_succ',mul_apply_eq_comp]

private def familyValue (F : Index) : Family H sourceFilter →ₗ[ℂ] H where
  toFun f := value f F
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pointLegFamily (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (w : ℝ) (j : ℕ) : Family H sourceFilter where
  val F := embed (leg F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q j)
  property := by
    let B := μ⁻¹*‖cutoff n‖
    have hB : 0 ≤ B := mul_nonneg (inv_nonneg.mpr hμ.le) (norm_nonneg _)
    refine ⟨B^j*(μ⁻¹*‖embed q‖),mul_nonneg (pow_nonneg hB j)
      (mul_nonneg (inv_nonneg.mpr hμ.le) (norm_nonneg _)),?_⟩
    intro F
    apply (actual_leg_price F n advanced μ hμ q w j).trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB j)
    exact ((finiteResolvent F (frequency advanced μ w)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (actual_frequency_resolvent_norm F advanced μ hμ w) (norm_nonneg _))

def historyStep (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    HistorySpace →L[ℂ] HistorySpace :=
  -(sameResolvent (frequency advanced μ w) (frequency_nonreal advanced μ hμ w)*reader (cutoff n))

private theorem point_leg_zero (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (w : ℝ) :
    (pointLegFamily n advanced μ hμ q w 0 : HistorySpace) =
      sameResolvent (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) (inclusion (embed q)) := by
  have he : pointLegFamily n advanced μ hμ q w 0 =
      SourceFamilyOperator.act sourceFilter
        (resolventFamily (frequency advanced μ w) (frequency_nonreal advanced μ hμ w))
        (SourceFamilyHilbert.constant sourceFilter (embed q)) := by
    apply Family.ext
    funext F
    change embed (leg F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q 0) =
      finiteResolvent F (frequency advanced μ w) (embed q)
    simpa only [pow_zero,one_apply_eq_self] using
      actual_leg_embed F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q 0
  exact (congrArg (fun f : Family H sourceFilter => (f : HistorySpace)) he).trans
    (SourceFamilyOperator.lift_coe sourceFilter
      (resolventFamily (frequency advanced μ w) (frequency_nonreal advanced μ hμ w))
      (SourceFamilyHilbert.constant sourceFilter (embed q))).symm

private theorem point_leg_succ (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (w : ℝ) (j : ℕ) :
    (pointLegFamily n advanced μ hμ q w (j+1) : HistorySpace) =
      historyStep n advanced μ hμ w (pointLegFamily n advanced μ hμ q w j : HistorySpace) := by
  let R := resolventFamily (frequency advanced μ w) (frequency_nonreal advanced μ hμ w)
  let C : SourceFamilyOperator.Operator Index H := SourceFamilyOperator.constant (cutoff n)
  let f := pointLegFamily n advanced μ hμ q w j
  have he : pointLegFamily n advanced μ hμ q w (j+1) =
      -SourceFamilyOperator.act sourceFilter R (SourceFamilyOperator.act sourceFilter C f) := by
    apply Family.ext
    funext F
    change embed (leg F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q (j+1)) =
      -finiteResolvent F (frequency advanced μ w) (cutoff n (embed
        (leg F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q j)))
    calc
      _ = ((step F n (frequency advanced μ w))^(j+1))
          (finiteResolvent F (frequency advanced μ w) (embed q)) :=
        actual_leg_embed F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q (j+1)
      _ = step F n (frequency advanced μ w)
          (((step F n (frequency advanced μ w))^j)
            (finiteResolvent F (frequency advanced μ w) (embed q))) := power_apply_succ _ _ _
      _ = step F n (frequency advanced μ w)
          (embed (leg F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q j)) :=
        congrArg (step F n (frequency advanced μ w))
          (actual_leg_embed F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q j).symm
      _ = _ := by simp only [step,neg_apply,mul_apply_eq_comp]
  change (pointLegFamily n advanced μ hμ q w (j+1) : HistorySpace) =
    -SourceFamilyOperator.lift sourceFilter R (SourceFamilyOperator.lift sourceFilter C (f : HistorySpace))
  exact (congrArg (fun g : Family H sourceFilter => (g : HistorySpace)) he).trans
    (coe_neg_act_act sourceFilter R C f)

theorem actual_point_leg_word (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (w : ℝ) (j : ℕ) :
    (pointLegFamily n advanced μ hμ q w j : HistorySpace) =
      ((historyStep n advanced μ hμ w)^j)
        (sameResolvent (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) (inclusion (embed q))) := by
  induction j with
  | zero => simpa only [pow_zero,one_apply_eq_self] using point_leg_zero n advanced μ hμ q w
  | succ j ih =>
    exact (point_leg_succ n advanced μ hμ q w j).trans
      ((congrArg (historyStep n advanced μ hμ w) ih).trans (power_apply_succ _ _ _).symm)

/-- Both causal lines are generated on the original K by the same resolvent,
original cutoff reader and source input. No negative line is given a false positive-μ certificate. -/
theorem actual_source_point_word (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) (w : ℝ) :
    sourcePoint n advanced μ hμ q hq w = ∑j : Fin 4,
      ((historyStep n advanced μ hμ w)^j.val)
        (sameResolvent (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) (inclusion (embed q))) := by
  have he : pointFamily n advanced μ hμ q hq w =
      ∑j : Fin 4,pointLegFamily n advanced μ hμ q w j.val := by
    apply Family.ext
    funext F
    change inverse F n (frequency advanced μ w) (embed q) =
      familyValue F (∑j : Fin 4,pointLegFamily n advanced μ hμ q w j.val)
    rw [map_sum]
    change inverse F n (frequency advanced μ w) (embed q) = ∑j : Fin 4,
      embed (leg F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q j.val)
    exact actual_full_response F n (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q hq
  change (pointFamily n advanced μ hμ q hq w : HistorySpace) = _
  apply (congrArg (fun f : Family H sourceFilter => (f : HistorySpace)) he).trans
  change (UniformSpace.Completion.toComplL : Family H sourceFilter →L[ℂ] HistorySpace)
    (∑j : Fin 4,pointLegFamily n advanced μ hμ q w j.val) = _
  exact (map_sum (UniformSpace.Completion.toComplL : Family H sourceFilter →L[ℂ] HistorySpace) _ _).trans
    (Finset.sum_congr rfl (fun j _ => actual_point_leg_word n advanced μ hμ q w j.val))

end LowEnergy.ActualThreeParticleCutoffFamily
