import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceRadiusHalfKinetic
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceBulkParseval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceRadiusHalfKineticTime
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceRadiusHalfKinetic SourceScalarPositiveBulkWard
open SourceScalarInverseNativeEnergy SourceBulkParseval SourceResolventBandLimit SourceInverseSourceLeg
open FullYSourceResolventGraphSplice SourceRetardedBandCurrent MeasureTheory

/-- The signed kinetic IMS correction's positive size on the literal retarded source core. -/
def kineticError (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (w : ℝ) : ℝ :=
  let f := state F (line μ w) (by simpa only [line_im] using hμ.ne') g
  (sourceTime 0/2)*(contactGram m ell f f).re

/-- Full frequency payment uses the actual inverse-volume time energy of this F; it is not replaced by the free norm. -/
theorem actual_kinetic_contact_full_frequency (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (kineticError m ell F μ hμ g w)) ≤
      ENNReal.ofReal ((3/(1952*Real.sqrt 2*(m+1 : ℝ)))*(2*Real.pi*timeEnergy F μ 1 g)) := by
  have hc : 0 ≤ 3/(1952*Real.sqrt 2*(m+1 : ℝ)) := by positivity
  obtain ⟨hi,_,he⟩ := actual_bulk_parseval F μ hμ 1 g
  simp only [Module.End.one_apply] at hi he
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (3/(1952*Real.sqrt 2*(m+1 : ℝ)))*
        ENNReal.ofReal (inverseForm (state F (line μ w) (by simpa only [line_im] using hμ.ne') g)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal (original_kinetic_contact_price m ell _)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => original_inverse_nonnegative _)),
        he,←ENNReal.ofReal_mul hc]

/-- The advanced source leg remains in the same two-leg cost and is paid by its actual resolvent bound. -/
theorem actual_paired_kinetic_contact_price (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (star (line μ w)) (k : H)‖^2)*
      ENNReal.ofReal (kineticError m ell F μ hμ g w)) ≤
      ENNReal.ofReal ((3/(1952*Real.sqrt 2*(m+1 : ℝ)))*
        (2*Real.pi*μ⁻¹^2*‖(k : H)‖^2*timeEnergy F μ 1 g)) := by
  have hc : 0 ≤ μ⁻¹^2*‖(k : H)‖^2 := by positivity
  have hbound (w : ℝ) : ‖finiteResolvent F (star (line μ w)) (k : H)‖^2 ≤ μ⁻¹^2*‖(k : H)‖^2 := by
    rw [actual_conjugate_leg_norm F (line μ w) (by simpa only [line_im] using hμ.ne')]
    have h := pow_le_pow_left₀ (norm_nonneg _) (finite_input_bound μ hμ F (k : H) w) 2
    simpa only [mul_pow] using h
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (μ⁻¹^2*‖(k : H)‖^2)*
        ENNReal.ofReal (kineticError m ell F μ hμ g w) := by
      apply lintegral_mono
      intro w
      exact mul_le_mul (ENNReal.ofReal_le_ofReal (hbound w)) le_rfl bot_le bot_le
    _ = ENNReal.ofReal (μ⁻¹^2*‖(k : H)‖^2)*
        (∫⁻ w : ℝ,ENNReal.ofReal (kineticError m ell F μ hμ g w)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      have h := mul_le_mul (le_refl (ENNReal.ofReal (μ⁻¹^2*‖(k : H)‖^2)))
        (actual_kinetic_contact_full_frequency m ell F μ hμ g) bot_le bot_le
      rw [←ENNReal.ofReal_mul hc] at h
      exact h.trans_eq (congrArg ENNReal.ofReal (by ring))

end LowEnergy.SourceRadiusHalfKineticTime
