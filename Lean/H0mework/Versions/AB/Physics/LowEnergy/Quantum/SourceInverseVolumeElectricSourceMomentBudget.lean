import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricMomentDecay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseElectricSourceMomentBudget
open GaussCoreHilbert GaussCoreDifferential GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceMixedNativeReturn SourceScalarPositiveBulkWard SourceScalarPairedTransport SourceScalarDoubleCurrent
open SourceInverseElectricCurrentEnergy SourceInverseElectricWindowDecay SourceInverseElectricMomentDecay
open SourceInverseDefectCurrentResponse FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory
open scoped InnerProductSpace ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourceRead state SourceScalarDoubleCurrent.fullInsertion

def leftMomentum (r : Row) : End := covariantMomentum (gaugeDirection r.2.1 r.1)
def rightMomentum (r : Row) : End :=
  multiply (fun z => gaugeWeight z r.2.1 r.2.2) (gaugeWeight_smooth r.2.1 r.2.2)*
    covariantMomentum (gaugeDirection r.2.2 r.1)
def leftMoment (sharp : Bool) (r : Row) : End := higherEnvelopeAction sharp (gaugeDirection r.2.1 r.1)
def rightMoment (sharp : Bool) (r : Row) : End :=
  higherEnvelopeAction sharp (gaugeDirection r.2.2 r.1)*
    multiply (fun z => gaugeWeight z r.2.1 r.2.2) (gaugeWeight_smooth r.2.1 r.2.2)

/-- Every price uses the actual input-span reader of its own external source. -/
def familyPrice (F : Index) (g : diagonal.domain) (A : Row → End) : ℝ :=
  ∑ r : Row,‖sourceRead F g (A r)‖^2

def sourceCoefficient (sharp : Bool) (F : Index) (g k : diagonal.domain) : ℝ :=
  (1/2 : ℝ)*(familyPrice F k leftMomentum*familyPrice F g (rightMoment sharp)+
    familyPrice F k (leftMoment (!sharp))*familyPrice F g rightMomentum)

def sourcePrice (sharp : Bool) (F : Index) (μ : ℝ) (g k : diagonal.domain) : ℝ :=
  (sourceCoefficient sharp F g k*(μ⁻¹*‖(k : H)‖)^2)*(Real.pi/μ*‖(g : H)‖^2)

private theorem familyPrice_nonneg (F : Index) (g : diagonal.domain) (A : Row → End) : 0 ≤ familyPrice F g A := by
  unfold familyPrice
  positivity
private theorem coefficient_nonneg (sharp : Bool) (F : Index) (g k : diagonal.domain) :
    0 ≤ sourceCoefficient sharp F g k := by
  unfold sourceCoefficient
  have h1 := familyPrice_nonneg F k leftMomentum
  have h2 := familyPrice_nonneg F g (rightMoment sharp)
  have h3 := familyPrice_nonneg F k (leftMoment (!sharp))
  have h4 := familyPrice_nonneg F g rightMomentum
  exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 h4))

private theorem actual_family_bound (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (A : Row → End) :
    (∑ r : Row,‖embed (A r (state F z hz g))‖^2) ≤ familyPrice F g A*‖finiteResolvent F z (g : H)‖^2 := by
  unfold familyPrice
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r _
  have hread : sourceRead F g (A r) (finiteResolvent F z (g : H))=embed (A r (state F z hz g)) := by
    unfold state
    exact source_read_resolvent F g (A r) z hz
  rw [←hread]
  exact (pow_le_pow_left₀ (norm_nonneg _) ((sourceRead F g (A r)).le_opNorm _) 2).trans_eq (mul_pow _ _ 2)

private theorem actual_moment_point (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    momentResponseBudget sharp F z hz g k ≤
      sourceCoefficient sharp F g k*‖finiteResolvent F (star z) (k : H)‖^2*‖finiteResolvent F z (g : H)‖^2 := by
  let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hLP := actual_family_bound F (star z) hs k leftMomentum
  have hRM := actual_family_bound F z hz g (rightMoment sharp)
  have hLM := actual_family_bound F (star z) hs k (leftMoment (!sharp))
  have hRP := actual_family_bound F z hz g rightMomentum
  change (1/2 : ℝ)*((∑ r : Row,‖embed (leftMomentum r (state F (star z) hs k))‖^2)*
      (∑ r : Row,‖embed (rightMoment sharp r (state F z hz g))‖^2)+
    (∑ r : Row,‖embed (leftMoment (!sharp) r (state F (star z) hs k))‖^2)*
      (∑ r : Row,‖embed (rightMomentum r (state F z hz g))‖^2)) ≤ _
  calc
    _ ≤ (1/2 : ℝ)*((familyPrice F k leftMomentum*‖finiteResolvent F (star z) (k : H)‖^2)*
      (familyPrice F g (rightMoment sharp)*‖finiteResolvent F z (g : H)‖^2)+
      (familyPrice F k (leftMoment (!sharp))*‖finiteResolvent F (star z) (k : H)‖^2)*
      (familyPrice F g rightMomentum*‖finiteResolvent F z (g : H)‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact mul_le_mul hLP hRM (by positivity) (mul_nonneg (familyPrice_nonneg _ _ _) (sq_nonneg _))
      · exact mul_le_mul hLM hRP (by positivity) (mul_nonneg (familyPrice_nonneg _ _ _) (sq_nonneg _))
    _ = _ := by unfold sourceCoefficient;ring

/-- The full moving moment has an explicit finite source price; F-dependence remains part of the generated output. -/
theorem actual_moment_source_budget (sharp : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (momentResponseBudget sharp F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k)) ≤ ENNReal.ofReal (sourcePrice sharp F μ g k) := by
  let C := sourceCoefficient sharp F g k*(μ⁻¹*‖(k : H)‖)^2
  have hC : 0 ≤ C := mul_nonneg (coefficient_nonneg sharp F g k) (sq_nonneg _)
  have hp (w : ℝ) : momentResponseBudget sharp F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k ≤ C*‖finiteResolvent F (line μ w) (g : H)‖^2 := by
    have h := actual_moment_point sharp F (line μ w) (by simpa only [line_im] using hμ.ne') g k
    rw [SourceInverseSourceLeg.actual_conjugate_leg_norm F (line μ w)
      (by simpa only [line_im] using hμ.ne')] at h
    have hk := pow_le_pow_left₀ (norm_nonneg _)
      (SourceRetardedBandCurrent.finite_input_bound μ hμ F (k : H) w) 2
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk (coefficient_nonneg sharp F g k)) (sq_nonneg _))
  have he : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2))=
      ENNReal.ofReal (Real.pi/μ*‖(g : H)‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using!
      SourceActualResolventEnergy.actual_square_lintegral F μ hμ (g : H)
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal C*ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (hp w)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,he,←ENNReal.ofReal_mul hC]
      rfl

theorem actual_moment_finite (sharp : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (momentResponseBudget sharp F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k)) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (actual_moment_source_budget sharp F μ hμ g k)

/-- The generated finite source price directly consumes the original electric response and cutoff rate. -/
theorem actual_electric_source_decay (sharp : Bool) (m ell : ℕ) (hle : m ≤ ell)
    (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (k : H) ((finiteResolvent F (line μ w)*sourceRead F g
      (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*finiteResolvent F (line μ w)) (g : H))‖^2)) ≤
      ENNReal.ofReal ((1/(m+2 : ℝ))^2*sourcePrice sharp F μ g k) := by
  apply (actual_electric_moment_full_frequency sharp m ell hle F μ hμ g k).trans
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (actual_moment_source_budget sharp F μ hμ g k) (by positivity)

end LowEnergy.SourceInverseElectricSourceMomentBudget
