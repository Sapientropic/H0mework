import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorBulkSourcePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorRadiusPrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCausalBulkBudget
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarNoetherCommon

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualVectorBulkTimePrice
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeEnergy SourceScalarInverseNativeEnergy SourceScalarInverseRetardedBudget SourceScalarPositiveBulkWard
open ActualVectorBulkSourcePrice ActualVectorJointCost ActualCausalBulkTime
open FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped InnerProductSpace ENNReal

def timeCoefficient (sharp : Bool) (μ : ℝ) : ℝ :=
  2*Real.pi*μ⁻¹^2*formCoefficient sharp

theorem timeCoefficient_nonnegative (sharp : Bool) (μ : ℝ) : 0 ≤ timeCoefficient sharp μ := by
  unfold timeCoefficient
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (sq_nonneg _))
    (formCoefficient_nonnegative sharp)

/-- The complete two-resolvent vector uses one original bulk-time input price.
The vacuum norm and whole-input theta tail are paid before either cause. -/
theorem actual_vector_two_resolvent_time_price (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
      (∫w : ℝ,‖finiteResolvent F (causalFrequency advanced μ w)
        (SourceEscapeSeedTail.actualIncrement sharp m ell
          (finiteResolvent F (causalFrequency advanced μ w) (g : H)))‖^2) ≤ ε+
        timeCoefficient sharp μ*causalTimeEnergy advanced F μ (theta m ell) g := by
  intro ε hε
  let C := μ⁻¹^2*normCoefficient sharp
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (normCoefficient_nonnegative sharp)
  let δ := ε/(C+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨N,hN⟩ := actual_theta_frequency_norm_tail μ hμ g δ hδ
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  intro advanced
  have hb := actual_causal_bulk_parseval advanced F μ hμ (theta m ell) g
  have hi : Integrable (fun w : ℝ => inverseForm (theta m ell
      (state F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g))) := hb.1
  have he : (∫w : ℝ,inverseForm (theta m ell
      (state F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g))) =
      2*Real.pi*causalTimeEnergy advanced F μ (theta m ell) g := hb.2.2
  have hn := actual_theta_frequency_integrable advanced m ell F μ hμ g
  have hp := integral_mono
    (actual_vector_causal_integrable F advanced μ hμ (SourceEscapeSeedTail.actualIncrement sharp m ell) (g : H))
    ((hi.const_mul (μ⁻¹^2*formCoefficient sharp)).add (hn.const_mul C))
    (actual_two_resolvent_source_price advanced sharp m ell F μ hμ g)
  simp only [Pi.add_apply] at hp
  rw [integral_add (hi.const_mul (μ⁻¹^2*formCoefficient sharp)) (hn.const_mul C),
    integral_const_mul,integral_const_mul,he] at hp
  have ht := mul_le_mul_of_nonneg_left (hF advanced) hC
  have hd : C*δ ≤ ε := by
    dsimp only [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < C+1)).mpr
    nlinarith only [hε]
  have ha : (μ⁻¹^2*formCoefficient sharp)*(2*Real.pi*causalTimeEnergy advanced F μ (theta m ell) g) =
      timeCoefficient sharp μ*causalTimeEnergy advanced F μ (theta m ell) g := by
    unfold timeCoefficient
    ring
  rw [ha] at hp
  linarith only [hp,ht,hd]

open Lean Meta Elab Term
elab "paid_vector_reverse%" : term => do
  let name := Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorRadiusPrice 0) "LowEnergy") "ActualVectorJointCost")
    "joint_reverse_price"
  unless (←getEnv).contains name do throwError "Missing original source vector reverse price"
  mkConstWithFreshMVarLevels name

/-- All vector channels and interference remain; the Hardy price is paid internally. -/
theorem actual_vector_joint_time_price (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
      vectorJointCost advanced sharp m ell F μ (g : H) ≤ ε+
        2*timeCoefficient sharp μ*causalTimeEnergy advanced F μ (theta m ell) g := by
  intro ε hε
  obtain ⟨N1,h1⟩ := actual_vector_two_resolvent_time_price sharp μ hμ g (ε/4) (by positivity)
  obtain ⟨N2,h2⟩ := actual_hardy_price_causal_tail sharp μ hμ g (ε/4) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hell => ?_⟩
  filter_upwards [h1 m (by omega) ell hell,h2 m (by omega) ell hell] with F hF hG
  intro advanced
  have h := (paid_vector_reverse%) advanced sharp m ell F μ hμ (g : H)
  nlinarith only [h,hF advanced,hG advanced]

/-- The original complete signed current pays the reader-free full-vector price at its own source gap. -/
theorem actual_vector_two_resolvent_remaining_price (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (hgap : 2*sourceTime 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
      (∫w : ℝ,‖finiteResolvent F (causalFrequency advanced μ w)
        (SourceEscapeSeedTail.actualIncrement sharp m ell
          (finiteResolvent F (causalFrequency advanced μ w) (g : H)))‖^2) ≤ ε+
        (timeCoefficient sharp μ/(μ-2*sourceTime 0))*causalRemainingTime advanced F μ (theta m ell) g := by
  intro ε hε
  let P := timeCoefficient sharp μ
  let v := μ-2*sourceTime 0
  have hP : 0 ≤ P := timeCoefficient_nonnegative sharp μ
  have hv : 0 < v := sub_pos.mpr hgap
  let δ := v*(ε/2)/(P+1)
  have hδ : 0 < δ := div_pos (mul_pos hv (by positivity)) (by positivity)
  obtain ⟨N1,h1⟩ := actual_vector_two_resolvent_time_price sharp μ hμ g (ε/2) (by positivity)
  obtain ⟨N2,h2⟩ := actual_causal_shifted_time_energy_budget μ hμ g δ hδ
  refine ⟨max N1 N2,fun m hm ell hell => ?_⟩
  filter_upwards [h1 m (by omega) ell hell,h2 m (by omega) ell hell] with F hF hG
  intro advanced
  have hc := mul_le_mul_of_nonneg_left (hF advanced) hv.le
  have he := mul_le_mul_of_nonneg_left (hG advanced) hP
  have hd : P*δ ≤ v*(ε/2) := by
    dsimp only [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < P+1)).mpr
    nlinarith only [mul_nonneg hv.le hε.le]
  let E := ∫w : ℝ,‖finiteResolvent F (causalFrequency advanced μ w)
      (SourceEscapeSeedTail.actualIncrement sharp m ell
        (finiteResolvent F (causalFrequency advanced μ w) (g : H)))‖^2
  have hf : E*v ≤ v*ε+P*causalRemainingTime advanced F μ (theta m ell) g := by
    change v*E ≤ v*(ε/2+P*causalTimeEnergy advanced F μ (theta m ell) g) at hc
    change P*(v*causalTimeEnergy advanced F μ (theta m ell) g) ≤
      P*(δ+causalRemainingTime advanced F μ (theta m ell) g) at he
    nlinarith only [hc,he,hd]
  have hb := (le_div_iff₀ hv).mpr hf
  calc
    _ ≤ (v*ε+P*causalRemainingTime advanced F μ (theta m ell) g)/v := hb
    _ = _ := by change _ = ε+(P/v)*_; field_simp

/-- The whole four-pole vector Gram, with no external leg, consumes the same complete signed source current. -/
theorem actual_vector_joint_remaining_price (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (hgap : 2*sourceTime 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
      vectorJointCost advanced sharp m ell F μ (g : H) ≤ ε+
        (2*timeCoefficient sharp μ/(μ-2*sourceTime 0))*causalRemainingTime advanced F μ (theta m ell) g := by
  intro ε hε
  obtain ⟨N1,h1⟩ := actual_vector_two_resolvent_remaining_price sharp μ hμ hgap g (ε/4) (by positivity)
  obtain ⟨N2,h2⟩ := actual_hardy_price_causal_tail sharp μ hμ g (ε/4) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hell => ?_⟩
  filter_upwards [h1 m (by omega) ell hell,h2 m (by omega) ell hell] with F hF hG
  intro advanced
  have h := (paid_vector_reverse%) advanced sharp m ell F μ hμ (g : H)
  have he : 2*timeCoefficient sharp μ/(μ-2*sourceTime 0) =
      2*(timeCoefficient sharp μ/(μ-2*sourceTime 0)) := by ring
  rw [he]
  nlinarith only [h,hF advanced,hG advanced]

/-- The unchanged generated source scale pays its own numerical gap before the actual vector consumer. -/
theorem actual_original_vector_joint_remaining_price (sharp : Bool) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
      vectorJointCost advanced sharp m ell F SourceRetardedGraph.sourceMu (g : H) ≤ ε+
        (2*timeCoefficient sharp SourceRetardedGraph.sourceMu/
          (SourceRetardedGraph.sourceMu-2*sourceTime 0))*
          causalRemainingTime advanced F SourceRetardedGraph.sourceMu (theta m ell) g := by
  have hμ : 0 < SourceRetardedGraph.sourceMu :=
    lt_of_lt_of_le (by norm_num) SourceRetardedGraph.source_mu_large
  have hg := FirstCurrentJointBudget.actual_source_noether_gap false
  change 15 < SourceRetardedGraph.sourceMu-2*sourceTime 0 at hg
  have hgap : 2*sourceTime 0 < SourceRetardedGraph.sourceMu := by linarith only [hg]
  exact actual_vector_joint_remaining_price sharp SourceRetardedGraph.sourceMu hμ hgap g

end LowEnergy.ActualVectorBulkTimePrice
