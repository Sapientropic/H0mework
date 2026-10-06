import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeSourceLeg

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.SourceInverseWeightedForcing
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory SourcePhysicalKineticSquare
open SourceScalarInverseEndpoint
open SourceScalarPositiveBulkWard SourceInverseDiagonalEndpoint SourceInverseSourceLeg
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ENNReal
attribute [local irreducible] GaussDiagonalHistory.diagonalAction
  SourceScalarPositiveBulkWard.fixedBulk

private theorem leg_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (k : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) k‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖k‖^2) := by
  simpa only [line,mul_comm (μ : ℂ) Complex.I] using!
    SourceActualResolventEnergy.actual_square_lintegral F μ hμ k
private theorem leg_measurable (F : Index) (μ : ℝ) (hμ : 0<μ) (k : H) :
    AEMeasurable (fun w : ℝ => ENNReal.ofReal (‖finiteResolvent F (line μ w) k‖^2)) volume := by
  have h := (SourceActualResolventEnergy.actual_square_integrable F μ hμ k).1.aemeasurable.ennreal_ofReal
  simpa only [line,mul_comm (μ : ℂ) Complex.I] using! h
private theorem leg_bound (F : Index) (μ : ℝ) (hμ : 0<μ) (w : ℝ) (k : H) :
    ‖finiteResolvent F (line μ w) k‖^2 ≤ ‖k‖^2/μ^2 := by
  have hn : ‖finiteResolvent F (line μ w)‖≤1/μ := by
    simpa only [line_im,abs_of_pos hμ] using!
      finite_resolvent_norm F (line μ w) (by simpa only [line_im] using hμ.ne')
  have h := ((finiteResolvent F (line μ w)).le_opNorm k).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg k))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (by ring)
private theorem young_leg (a b K δ : ℝ) (hK : a^2≤K) (hδ : 0<δ) :
    a^2*b ≤ δ*a^2+(K/(4*δ))*b^2 := by
  have he : K/(4*δ)*(4*δ)=K := div_mul_cancel₀ K (by positivity)
  have hs := mul_nonneg (sq_nonneg a) (sq_nonneg (b-2*δ))
  have hk := mul_le_mul_of_nonneg_right hK (sq_nonneg b)
  nlinarith

/-- Full-line exterior-source weighting converts the actual forcing L2 budget into the L1 cost in Gamma. -/
theorem actual_weighted_forcing_budget (m ell : ℕ) (F : Index) (μ δ : ℝ)
    (hμ : 0<μ) (hδ : 0<δ) (g : diagonal.domain) (k : H) :
    (∫⁻ w : ℝ, ENNReal.ofReal (‖finiteResolvent F (star (line μ w)) k‖^2*
      ‖fixedBulk F (line μ w) (line μ w)
        (by simpa only [line_im] using hμ.ne') (by simpa only [line_im] using hμ.ne') g g
        (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)‖)) ≤
      ENNReal.ofReal (δ*((Real.pi/μ)*‖k‖^2))+
      ENNReal.ofReal ((‖k‖^2/μ^2)/(4*δ))*(∫⁻ w : ℝ,ENNReal.ofReal
        (‖fixedBulk F (line μ w) (line μ w)
          (by simpa only [line_im] using hμ.ne') (by simpa only [line_im] using hμ.ne') g g
          (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)‖^2)) := by
  let B (w : ℝ) := ‖fixedBulk F (line μ w) (line μ w)
    (by simpa only [line_im] using hμ.ne') (by simpa only [line_im] using hμ.ne') g g
    (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)‖
  let C := (‖k‖^2/μ^2)/(4*δ)
  have hC : 0≤C := by dsimp [C];positivity
  simp_rw [actual_conjugate_leg_norm F (line μ _) (by simpa only [line_im] using hμ.ne')]
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal δ*ENNReal.ofReal (‖finiteResolvent F (line μ w) k‖^2)+
        ENNReal.ofReal C*ENNReal.ofReal (B w^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hδ.le,←ENNReal.ofReal_mul hC,
        ←ENNReal.ofReal_add (mul_nonneg hδ.le (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _))]
      exact ENNReal.ofReal_le_ofReal
        (young_leg _ _ _ δ (leg_bound F μ hμ w k) hδ)
    _ = ENNReal.ofReal δ*(∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) k‖^2))+
        ENNReal.ofReal C*(∫⁻ w : ℝ,ENNReal.ofReal (B w^2)) := by
      rw [lintegral_add_left' ((leg_measurable F μ hμ k).const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by rw [leg_energy F μ hμ k,←ENNReal.ofReal_mul hδ.le]

/-- The original fixed forcing vanishes in the full-frequency Gamma exterior-leg cost, uniformly in F. -/
theorem actual_weighted_forcing_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (k : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ, ENNReal.ofReal (‖finiteResolvent F (star (line μ w)) k‖^2*
        ‖fixedBulk F (line μ w) (line μ w)
          (by simpa only [line_im] using hμ.ne') (by simpa only [line_im] using hμ.ne') g g
          (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)‖)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let A := (Real.pi/μ)*‖k‖^2
  have hA : 0≤A := by dsimp [A];positivity
  let δ := ε/(2*(A+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  let C := (‖k‖^2/μ^2)/(4*δ)
  have hC : 0≤C := by dsimp [C];positivity
  let η := ε/(2*(C+1))
  have hη : 0<η := by dsimp [η];positivity
  obtain ⟨N,hN⟩ := actual_diagonal_fixed_tail μ hμ g η hη
  refine ⟨N,fun m hm ell hell F => (actual_weighted_forcing_budget m ell F μ δ hμ hδ g k).trans ?_⟩
  have h := mul_le_mul' (le_refl (ENNReal.ofReal C)) (hN m hm ell hell F)
  refine (add_le_add (le_refl (ENNReal.ofReal (δ*A))) h).trans ?_
  rw [←ENNReal.ofReal_mul hC,←ENNReal.ofReal_add (mul_nonneg hδ.le hA) (mul_nonneg hC hη.le)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : δ*(2*(A+1))=ε := div_mul_cancel₀ ε (by positivity)
  have h2 : η*(2*(C+1))=ε := div_mul_cancel₀ ε (by positivity)
  nlinarith

end LowEnergy.SourceInverseWeightedForcing
