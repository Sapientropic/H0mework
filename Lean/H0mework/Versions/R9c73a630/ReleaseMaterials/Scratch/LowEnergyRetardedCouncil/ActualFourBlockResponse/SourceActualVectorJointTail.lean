import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointCost
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseNativeBudget
import Lean.Elab.Term

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualVectorJointCost
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceHardyRetardedTail
open SourceRelativePowerTail SourceLocalizedInverseFormPayment MeasureTheory Filter
open scoped BigOperators InnerProductSpace Topology ENNReal
open Lean Meta Elab Term

elab "paid_clock_tail%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseNativeBudget 0)
    "LowEnergy") "SourceClockPhiRadiusResponseNativeBudget"
  let name := Name.str ns field.getId.toString
  unless (←getEnv).contains name do throwError "Missing original paid clock fact"
  mkConstWithFreshMVarLevels name

elab "paid_hardy_tail%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceHardyRetardedTail 0)
    "LowEnergy") "SourceHardyRetardedTail"
  let name := Name.str ns field.getId.toString
  unless (←getEnv).contains name do throwError "Missing original paid Hardy fact"
  mkConstWithFreshMVarLevels name

private theorem causal_frequency_original (advanced : Bool) (μ w : ℝ) :
    causalFrequency advanced μ w = actualFrequency advanced μ w := by
  cases advanced
  · rfl
  · apply Complex.ext <;> simp [causalFrequency,actualFrequency,line]

private theorem causal_frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (F : Index) :
    Continuous (fun w : ℝ => finiteResolvent F (causalFrequency advanced μ w)) := by
  simp_rw [causal_frequency_original]
  exact (paid_clock_tail% frequency_continuous) advanced μ hμ F

private theorem causal_frequency_norm (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (F : Index) (g : H) (w : ℝ) :
    ‖finiteResolvent F (causalFrequency advanced μ w) g‖ =
      ‖finiteResolvent F (line μ w) g‖ := by
  rw [causal_frequency_original]
  exact (paid_clock_tail% frequency_norm) advanced μ hμ F g w

private theorem reader_energy_bound (A : H →L[ℂ] H) (x : ℝ → H) :
    (∫⁻w,ENNReal.ofReal (‖A (x w)‖^2)) ≤
      ENNReal.ofReal (‖A‖^2)*(∫⁻w,ENNReal.ofReal (‖x w‖^2)) := by
  calc
    _ ≤ ∫⁻w,ENNReal.ofReal (‖A‖^2)*ENNReal.ofReal (‖x w‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (x w)) 2)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The old whole-input TimeSpace tail is consumed before the two causal
choices. No descent from the common source carrier to H is required. -/
theorem actual_bounded_theta_causal_tail (μ : ℝ) (hμ : 0 < μ) (A : H →L[ℂ] H) (g : H) :
    ∀ε : ℝ,0 < ε → ∃N : ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool,
      (∫⁻w : ℝ,ENNReal.ofReal (‖A (relativeTail m ell
        (finiteResolvent F (causalFrequency advanced μ w) g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := ‖A‖^2+1
  have hC : 0 < C := by dsimp [C];positivity
  obtain ⟨N,hN⟩ := (paid_clock_tail% old_theta_tail) μ hμ g (ε/C) (div_pos hε hC)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  intro advanced
  have h := hF advanced
  simp_rw [←causal_frequency_original] at h
  have hb := (reader_energy_bound A (fun w => relativeTail m ell
    (finiteResolvent F (causalFrequency advanced μ w) g))).trans
      (mul_le_mul le_rfl h zero_le zero_le)
  apply hb.trans
  rw [←ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  apply (mul_le_mul_of_nonneg_right (show ‖A‖^2 ≤ C by dsimp [C];linarith)
    (div_pos hε hC).le).trans_eq
  field_simp

private theorem frequency_nonreal (advanced : Bool) (μ w : ℝ) (hμ : 0 < μ) :
    (causalFrequency advanced μ w).im ≠ 0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

private theorem causal_resolvent_bound (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (F : Index) (w : ℝ) : ‖finiteResolvent F (causalFrequency advanced μ w)‖ ≤ μ⁻¹ := by
  have h := finite_resolvent_norm F _ (frequency_nonreal advanced μ w hμ)
  cases advanced <;> simpa [causalFrequency,line_im,abs_of_pos hμ] using h

private theorem causal_outer_energy (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (F : Index) (x : ℝ → H) :
    (∫⁻w,ENNReal.ofReal (‖finiteResolvent F (causalFrequency advanced μ w) (x w)‖^2)) ≤
      ENNReal.ofReal (μ⁻¹^2)*(∫⁻w,ENNReal.ofReal (‖x w‖^2)) := by
  calc
    _ ≤ ∫⁻w,ENNReal.ofReal (μ⁻¹^2)*ENNReal.ofReal (‖x w‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have h := ((finiteResolvent F (causalFrequency advanced μ w)).le_opNorm (x w)).trans
        (mul_le_mul_of_nonneg_right (causal_resolvent_bound advanced μ hμ F w) (norm_nonneg _))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem causal_fixed_forcing_tail (μ : ℝ) (hμ : 0 < μ)
    (A : H →L[ℂ] H) (g : H) :
    ∀ε : ℝ,0 < ε → ∃N : ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →∀F : Index,∀advanced : Bool,
      (∫⁻w,ENNReal.ofReal (‖finiteResolvent F (causalFrequency advanced μ w)
        (A (relativeTail m ell g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := fixed_forcing_uniform_energy_tail μ hμ A g ε hε
  refine ⟨N,fun m hm ell hell F advanced => ?_⟩
  simpa only [causal_frequency_norm advanced μ hμ] using hN m hm ell hell F

/-- One source jet event pays both causal signs of the entire Hardy vector. -/
theorem actual_bounded_jet_causal_tail (μ : ℝ) (hμ : 0 < μ)
    (A : H →L[ℂ] H) (g : diagonal.domain) :
    ∀ε : ℝ,0 < ε → ∃N : ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool,
      (∫⁻w,ENNReal.ofReal (‖A (relativeTail m ell
        (finiteResolvent F (causalFrequency advanced μ w) (g : H))) +
        causalFrequency advanced μ w • finiteResolvent F (causalFrequency advanced μ w)
          (A (relativeTail m ell (finiteResolvent F (causalFrequency advanced μ w) (g : H))))‖^2)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  let C := 1+μ⁻¹^2
  let δ := ε/(6*C)
  have hC : 0 < C := by dsimp [C];positivity
  have hδ : 0 < δ := by dsimp [δ];positivity
  let dg : diagonal.domain := ⟨diagonal g,diagonal_invariant g⟩
  obtain ⟨N1,h1⟩ := actual_bounded_theta_causal_tail μ hμ A (g : H) δ hδ
  obtain ⟨N2,h2⟩ := actual_bounded_theta_causal_tail μ hμ A (dg : H) δ hδ
  obtain ⟨N3,h3⟩ := causal_fixed_forcing_tail μ hμ A (g : H) (ε/6) (by positivity)
  refine ⟨max N1 (max N2 N3),fun m hm ell hell => ?_⟩
  have hm1 : N1 ≤ m := (le_max_left _ _).trans hm
  have hm2 : N2 ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm3 : N3 ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  filter_upwards [h1 m hm1 ell hell,h2 m hm2 ell hell,SourceRetardedSourceJet.actual_source_jet g]
    with F hF1 hF2 hjet
  intro advanced
  have hF3 := h3 m hm3 ell hell F advanced
  have houter := (causal_outer_energy advanced μ hμ F
    (fun w => A (relativeTail m ell (finiteResolvent F (causalFrequency advanced μ w) (diagonal g))))).trans
      (mul_le_mul le_rfl (hF2 advanced) zero_le zero_le)
  have he (w : ℝ) :
      A (relativeTail m ell (finiteResolvent F (causalFrequency advanced μ w) (g : H))) +
        causalFrequency advanced μ w • finiteResolvent F (causalFrequency advanced μ w)
          (A (relativeTail m ell (finiteResolvent F (causalFrequency advanced μ w) (g : H)))) =
      A (relativeTail m ell (finiteResolvent F (causalFrequency advanced μ w) (g : H))) +
        (finiteResolvent F (causalFrequency advanced μ w)
          (A (relativeTail m ell (finiteResolvent F (causalFrequency advanced μ w) (diagonal g)))) -
        finiteResolvent F (causalFrequency advanced μ w) (A (relativeTail m ell (g : H)))) := by
    exact congrArg (fun x => A (relativeTail m ell
      (finiteResolvent F (causalFrequency advanced μ w) (g : H))) + x)
      (hjet _ (frequency_nonreal advanced μ w hμ) (A.comp (relativeTail m ell)))
  have hr := causal_frequency_continuous advanced μ hμ F
  have hcont (x : H) : Continuous (fun w : ℝ =>
      A (relativeTail m ell (finiteResolvent F (causalFrequency advanced μ w) x))) :=
    A.continuous.comp ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const))
  apply ((paid_hardy_tail% three_lintegral) _ _ _ _
    (hcont (g : H)) (hr.clm_apply (hcont (diagonal g))) he).trans
  calc
    _ ≤ ENNReal.ofReal 3*(ENNReal.ofReal δ+
        (ENNReal.ofReal (μ⁻¹^2)*ENNReal.ofReal δ+ENNReal.ofReal (ε/6))) := by
      gcongr
      exact hF1 advanced
    _ = _ := by
      rw [←ENNReal.ofReal_mul (sq_nonneg _),
        ←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add hδ.le (by positivity),←ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp [δ,C]
      field_simp
      ring

theorem actual_hardy_price_causal_tail (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) :
    ∀ε : ℝ,0 < ε → ∃N : ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool,
      hardyPrice advanced sharp m ell F μ (g : H) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_bounded_jet_causal_tail μ hμ (coefficientSolver sharp) g ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  intro advanced
  have h := hF advanced
  change (∫⁻w : ℝ,ENNReal.ofReal (‖hardyVector advanced sharp m ell F μ (g : H) w‖^2)) ≤
    ENNReal.ofReal ε at h
  have hi := actual_hardy_vector_integrable advanced sharp m ell F μ hμ (g : H)
  have he := (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun w => sq_nonneg ‖hardyVector advanced sharp m ell F μ (g : H) w‖))).symm
  rw [actual_hardy_vector_energy advanced sharp m ell F μ hμ (g : H)] at he
  rw [he] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp h

/-- Both actual causal lines consume the same source-owned Hardy tail.
The unresolved vector joint price is retained explicitly, not supplied by the caller. -/
theorem actual_first_leg_causal_paid_price (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) :
    ∀ε : ℝ,0 < ε → ∃N : ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool,
      (∫w : ℝ, ‖finiteResolvent F (causalFrequency advanced μ w)
        (SourceEscapeSeedTail.actualIncrement sharp m ell
          (finiteResolvent F (causalFrequency advanced μ w) (g : H)))‖^2) ≤
      2*vectorJointCost advanced sharp m ell F μ (g : H)+ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_hardy_price_causal_tail sharp μ hμ g (ε/2) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  intro advanced
  have h := actual_first_leg_vector_price advanced sharp m ell F μ hμ (g : H)
  linarith [hF advanced]

end LowEnergy.ActualVectorJointCost
