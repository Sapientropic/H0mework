import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceRetardedBandCurrent
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCornerForcing

/-! The actual weighted native/sharp forcing has an all-frequency tail before the filter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceRetardedForcingTail
open Filter MeasureTheory GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (Index sourceFilter)
open SourceFamilyHilbert SourceFamilyOperator SourceRelativePowerTail SourceRetardedBandCurrent
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open FullYSourceFiniteTimeIntegral FullYSourceTimeFamilyGraph FullYSourceCutoffTimeGraph
open scoped Topology

variable (ν : Measure ℝ) [IsFiniteMeasure ν] (μ : ℝ) (hμ : 0 < μ)
include hμ

def finiteTheta (F : Index) (m ell : ℕ) (g : H) : Lp H 2 ν :=
  (relativeTail m ell).compLpL 2 ν (finiteInput ν μ hμ F g)

def thetaFamily (m ell : ℕ) (g : H) : Family (Lp H 2 ν) sourceFilter :=
  act sourceFilter (SourceFamilyOperator.constant ((relativeTail m ell).compLpL 2 ν))
    (actualInputFamily ν μ hμ g)

theorem finite_theta_integral (F : Index) (m ell : ℕ) (g : H) :
    (∫⁻ t, ENNReal.ofReal
      (‖relativeTail m ell (finiteResolvent F (line μ t) g)‖^2) ∂ν) =
      ENNReal.ofReal (‖finiteTheta ν μ hμ F m ell g‖^2) := by
  have he : (fun t => ‖relativeTail m ell (finiteResolvent F (line μ t) g)‖^2) =ᵐ[ν]
      (fun t => ‖(finiteTheta ν μ hμ F m ell g) t‖^2) := by
    filter_upwards [(relativeTail m ell).coeFn_compLpL (finiteInput ν μ hμ F g),
      (finite_input_memLp ν μ hμ F g).coeFn_toLp] with t hA hR
    change _=‖((relativeTail m ell).compLpL 2 ν (finiteInput ν μ hμ F g)) t‖^2
    rw [hA]
    change _=‖relativeTail m ell (((finite_input_memLp ν μ hμ F g).toLp _) t)‖^2
    rw [hR]
  have hi := (square_integrable ν (finiteTheta ν μ hμ F m ell g)).congr he.symm
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _)),
    integral_congr_ae he, ←square_integral]

omit [IsFiniteMeasure ν] in
/-- Only the original fixed source jet pays the spectral tail; both cutoffs remain variable. -/
theorem actual_theta_full_frequency_tail (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ t, ENNReal.ofReal
          (‖relativeTail m ell (finiteResolvent F (line μ t) (g : H))‖^2)) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  let C := μ⁻¹*‖diagonal g‖+‖(g : H)‖
  let Λ := 1+4*C^2/ε
  have hΛ : 0 < Λ := by dsimp [Λ]; positivity
  have hsmall : C^2/Λ ≤ ε/4 := by
    apply (div_le_iff₀ hΛ).mpr
    dsimp [Λ]
    field_simp
    nlinarith [sq_nonneg C]
  let νΛ : Measure ℝ := volume.restrict (Set.Icc (-Λ) Λ)
  let : IsFiniteMeasure νΛ := inferInstance
  obtain ⟨N,hN⟩ := actual_retarded_relative_tail νΛ μ hμ (g : H)
    (Real.sqrt (ε/4)) (Real.sqrt_pos.mpr (by positivity))
  refine ⟨N,fun m hm ell hell => ?_⟩
  have hn := hN m hm ell hell
  change ‖lift sourceFilter (SourceFamilyOperator.constant ((relativeTail m ell).compLpL 2 νΛ))
    ((actualInputFamily νΛ μ hμ (g : H)) : TimeSpace νΛ)‖ < _ at hn
  rw [lift_coe, UniformSpace.Completion.norm_coe] at hn
  change ‖thetaFamily νΛ μ hμ m ell (g : H)‖ < Real.sqrt (ε/4) at hn
  have htarget : ‖thetaFamily νΛ μ hμ m ell (g : H)‖^2 < ε/2 := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ ε/4)
    nlinarith [norm_nonneg (thetaFamily νΛ μ hμ m ell (g : H)), Real.sqrt_nonneg (ε/4)]
  have hb := (square_tendsto sourceFilter (thetaFamily νΛ μ hμ m ell (g : H))).eventually
    (gt_mem_nhds htarget)
  filter_upwards [hb, source_retarded_high_frequency μ hμ g] with F hF htail
  have band : (∫⁻ t in Set.Icc (-Λ) Λ, ENNReal.ofReal
      (‖relativeTail m ell (finiteResolvent F (line μ t) (g : H))‖^2)) ≤
        ENNReal.ofReal (ε/2) := by
    change (∫⁻ t, ENNReal.ofReal
      (‖relativeTail m ell (finiteResolvent F (line μ t) (g : H))‖^2) ∂νΛ) ≤ _
    rw [finite_theta_integral νΛ μ hμ F m ell (g : H)]
    exact ENNReal.ofReal_le_ofReal hF.le
  have tails (negative : Bool) :
      (∫⁻ t in Set.Ioi Λ, ENNReal.ofReal
        (‖relativeTail m ell (finiteResolvent F
          (line μ (if negative then -t else t)) (g : H))‖^2)) ≤
        ENNReal.ofReal (ε/4) := by
    apply (inverse_square_lintegral_bound _ Λ C hΛ ?_).trans
      (ENNReal.ofReal_le_ofReal hsmall)
    intro t ht
    have htpos := hΛ.trans ht
    have ha : |(if negative then -t else t : ℝ)|=t := by
      cases negative <;> simp [abs_of_pos htpos]
    have hz : (if negative then -t else t : ℝ)≠0 := by
      apply abs_pos.mp
      rw [ha]
      exact htpos
    exact (relative_tail_contraction m ell hell _).trans (by
      simpa only [ha] using htail _ hz)
  apply (full_frequency_split_le (fun t => ENNReal.ofReal
    (‖relativeTail m ell (finiteResolvent F (line μ t) (g : H))‖^2)) Λ).trans
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4) := by
      have hp := tails false
      have hn := tails true
      simp only [Bool.false_eq_true,if_false,if_true] at hp hn
      exact add_le_add (add_le_add band hp) hn
    _ = _ := by
      rw [←ENNReal.ofReal_add (by positivity : 0 ≤ ε/2) (by positivity : 0 ≤ ε/4),
        ←ENNReal.ofReal_add (by positivity : 0 ≤ ε/2+ε/4) (by positivity : 0 ≤ ε/4)]
      congr 1
      ring

omit [IsFiniteMeasure ν] in
theorem bounded_forcing_full_frequency_tail (A : H →L[ℂ] H) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ t, ENNReal.ofReal
          (‖A (relativeTail m ell (finiteResolvent F (line μ t) (g : H)))‖^2)) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  let C := 1+‖A‖^2
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N,hN⟩ := actual_theta_full_frequency_tail μ hμ g (ε/C) (div_pos hε hC)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have hb (x : H) : ‖A x‖^2 ≤ C*‖x‖^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm x) 2
    rw [mul_pow] at h
    dsimp [C]
    nlinarith [sq_nonneg ‖x‖]
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal C * ENNReal.ofReal
        (‖relativeTail m ell (finiteResolvent F (line μ t) (g : H))‖^2) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [←ENNReal.ofReal_mul hC.le]
      exact ENNReal.ofReal_le_ofReal (hb _)
    _ = ENNReal.ofReal C * ∫⁻ t, ENNReal.ofReal
        (‖relativeTail m ell (finiteResolvent F (line μ t) (g : H))‖^2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (ε/C) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC.le, mul_div_cancel₀ ε (ne_of_gt hC)]

omit [IsFiniteMeasure ν] in
/-- This is the original cutoff difference after its generated physical forcing weight. -/
theorem actual_weighted_increment_tail (sharp : Bool) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ t, ENNReal.ofReal
          (‖SourceCornerForcing.weighted
            (SourceEscapeSeedTail.actualIncrement sharp m ell
              (finiteResolvent F (line μ t) (g : H)))‖^2)) ≤ ENNReal.ofReal ε := by
  have he (m ell : ℕ) (x : H) : SourceCornerForcing.weighted
      (SourceEscapeSeedTail.actualIncrement sharp m ell x) =
      SourceCornerForcing.coefficientMap sharp (relativeTail m ell x) :=
    congrArg (fun T : H →L[ℂ] H => T x) (SourceCornerForcing.weighted_increment sharp m ell)
  simp only [he]
  exact bounded_forcing_full_frequency_tail μ hμ (SourceCornerForcing.coefficientMap sharp) g

end LowEnergy.SourceRetardedForcingTail
