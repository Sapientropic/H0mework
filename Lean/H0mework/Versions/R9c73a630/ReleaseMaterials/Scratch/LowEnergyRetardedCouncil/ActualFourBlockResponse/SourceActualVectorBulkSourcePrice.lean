import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointTail
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCutoffFrequencyBase
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeScalarInverseEnergyBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualVectorBulkSourcePrice
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeEnergy SourceMixedNativeReturn SourceScalarInverseNativeEnergy SourceScalarInverseEnergyBudget
open SourceScalarInverseRetardedBudget SourceScalarPositiveBulkWard SourceCutoffDilationWard
open SourceRelativePowerTail ActualVectorJointCost ActualCutoffFrequencyBase
open FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped InnerProductSpace ENNReal

private theorem n_pos : 0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

theorem causal_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (causalFrequency advanced μ w).im ≠ 0 := by
  cases advanced <;> simpa only [causalFrequency,Bool.false_eq_true,ite_false,ite_true,
    SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'

def formCoefficient (sharp : Bool) : ℝ := coefficientCost sharp/(2*sourceTime 0)
def normCoefficient (sharp : Bool) : ℝ :=
  2*‖constantBounded sharp SourceQuantumScalarChart.vacuum‖^2+
    coefficientCost sharp*‖SourceQuantumScalarChart.vacuum‖^2

theorem formCoefficient_nonnegative (sharp : Bool) : 0 ≤ formCoefficient sharp :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by have h := n_pos; positivity)
theorem normCoefficient_nonnegative (sharp : Bool) : 0 ≤ normCoefficient sharp := by
  unfold normCoefficient coefficientCost
  positivity

private theorem full_price_return (sharp : Bool) (f : QuantumTest) :
    fullPrice sharp f = formCoefficient sharp*inverseForm f+normCoefficient sharp*‖embed f‖^2 := by
  unfold fullPrice formCoefficient normCoefficient
  field_simp [n_pos.ne']
  ring

private theorem increment_full (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    literalIncrementAction sharp m ell f = fullAction sharp (theta m ell f) := by
  rw [literal_full_return]
  change fullAction sharp (SourceMixedNativeReturn.thetaAction m ell f) = _
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    embed (state F z hz g) = finiteResolvent F z (g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

theorem actual_theta_response_embed (advanced : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (w : ℝ) :
    embed (theta m ell (state F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) g)) =
      relativeTail m ell (finiteResolvent F (causalFrequency advanced μ w) (g : H)) := by
  rw [SourceNativeCutoffContact.theta_core,state_embed]

/-- Both real causal lines receive the unaltered full vacuum-plus-scalar source price. -/
theorem actual_full_input_price (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (w : ℝ) :
    ‖SourceEscapeSeedTail.actualIncrement sharp m ell
      (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2 ≤
      formCoefficient sharp*inverseForm (theta m ell (state F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w) g)) +
      normCoefficient sharp*‖embed (theta m ell (state F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w) g))‖^2 := by
  have hs := state_embed F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g
  rw [←hs,literal_increment_core,increment_full]
  exact (original_full_inverse sharp _).trans_eq (full_price_return sharp _)

private theorem outer_bound (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (w : ℝ) (v : H) :
    ‖finiteResolvent F (causalFrequency advanced μ w) v‖^2 ≤ μ⁻¹^2*‖v‖^2 := by
  have hb : ‖finiteResolvent F (causalFrequency advanced μ w)‖ ≤
      1/|(causalFrequency advanced μ w).im| := finite_resolvent_norm F _ (causal_nonreal advanced μ hμ w)
  have hi : |(causalFrequency advanced μ w).im| = μ := by
    cases advanced <;> simp only [causalFrequency,Bool.false_eq_true,ite_false,ite_true,
      SourceResolventBandLimit.line_im,abs_neg,abs_of_pos hμ]
  rw [hi] at hb
  have h := ((finiteResolvent F (causalFrequency advanced μ w)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  simpa only [mul_pow,one_div] using pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The actual outer resolvent removes every external reader from the full source bound. -/
theorem actual_two_resolvent_source_price (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (w : ℝ) :
    ‖finiteResolvent F (causalFrequency advanced μ w)
      (SourceEscapeSeedTail.actualIncrement sharp m ell
        (finiteResolvent F (causalFrequency advanced μ w) (g : H)))‖^2 ≤
      (μ⁻¹^2*formCoefficient sharp)*inverseForm (theta m ell (state F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w) g)) +
      (μ⁻¹^2*normCoefficient sharp)*‖embed (theta m ell (state F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w) g))‖^2 := by
  exact (outer_bound advanced F μ hμ w _).trans
    ((mul_le_mul_of_nonneg_left (actual_full_input_price advanced sharp m ell F μ hμ g w)
      (sq_nonneg _)).trans_eq (by ring))

theorem actual_theta_frequency_integrable (advanced : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    Integrable (fun w : ℝ => ‖embed (theta m ell (state F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) g))‖^2) := by
  have hb : MemLp (fun w : ℝ => finiteResolvent F (causalFrequency advanced μ w) (g : H)) 2 := by
    simpa only [frequency,causalFrequency] using actual_base_memLp F advanced μ hμ (g : H)
  have hm := (relativeTail m ell).comp_memLp' hb
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  apply hi.congr
  exact Eventually.of_forall (fun w => congrArg (fun x : H => ‖x‖^2)
    (actual_theta_response_embed advanced m ell F μ hμ g w).symm)

/-- The original whole-input theta tail pays a common frequency norm price before either cause. -/
theorem actual_theta_frequency_norm_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
      (∫w : ℝ,‖embed (theta m ell (state F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w) g))‖^2) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_bounded_theta_causal_tail μ hμ (1 : H →L[ℂ] H) (g : H) ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  intro advanced
  have ht := hF advanced
  change (∫⁻w : ℝ,ENNReal.ofReal (‖relativeTail m ell
    (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2)) ≤ ENNReal.ofReal ε at ht
  have hi := actual_theta_frequency_integrable advanced m ell F μ hμ g
  have he := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))
  have heL : (∫⁻w : ℝ,ENNReal.ofReal (‖embed (theta m ell (state F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) g))‖^2)) =
      (∫⁻w : ℝ,ENNReal.ofReal (‖relativeTail m ell
        (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2)) :=
    lintegral_congr (fun w => congrArg (fun x : H => ENNReal.ofReal (‖x‖^2))
      (actual_theta_response_embed advanced m ell F μ hμ g w))
  rw [heL] at he
  rw [←he] at ht
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp ht

end LowEnergy.ActualVectorBulkSourcePrice
