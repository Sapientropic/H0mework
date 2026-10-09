import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPositiveOutputParseval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FourGradeOutputParseval
open MeasureTheory Filter Set FullYPairedParseval CompositeFullYBorn
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDiagonalHistory GaussFockPair
open FullYDynamicSource FullYDynamicResponse GaussDensityCore SourceResolventBandLimit
open ThreeParticleRetardedTime NamedMatterWedgeQt NativeHistoryGrade
open scoped FourierTransform InnerProductSpace BigOperators
attribute [local irreducible] embed literalCoreResolvent literalSharpResolvent NativeHistoryGrade.projection
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H

private def frequencyScale (advanced : Bool) : ℝ := -FullYPairedParseval.direction advanced*(2*Real.pi)
private theorem scale_ne (advanced : Bool) : frequencyScale advanced≠0 := by
  cases advanced <;> simp [frequencyScale,FullYPairedParseval.direction,Real.pi_ne_zero]
private theorem scale_abs (advanced : Bool) : |frequencyScale advanced|=2*Real.pi := by
  cases advanced <;> simp [frequencyScale,FullYPairedParseval.direction,abs_of_pos Real.pi_pos]
private theorem line_scale (advanced : Bool) (μ ξ : ℝ) :
    line (FullYPairedParseval.direction advanced*μ) (frequencyScale advanced*ξ)=sourceLine advanced μ ξ := by
  cases advanced <;> simp only [line,frequencyScale,sourceLine,FullYPairedParseval.direction,ite_true,
    Bool.false_eq_true,ite_false,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  all_goals ring
private theorem fourier_reader (P : H →L[ℂ] H) (u : ℝ → H) (hu : Integrable u) (ξ : ℝ) :
    𝓕 (fun t => P (u t)) ξ=P (𝓕 u ξ) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  rw [←ContinuousLinearMap.integral_comp_comm P (Real.fourierIntegral_convergent_iff ξ |>.mpr hu)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => (map_smul P _ _).symm)

/-- Every bounded output reads the same complete source inverse and causal Fourier history, with the original 2π frequency convention. -/
theorem actual_output_fourier_mass_return (F : Index) (g : QuantumTest) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (P : H →L[ℂ] H) (ξ : ℝ) :
    ‖P (embed (literalResponse F false g advanced μ hμ (frequencyScale advanced*ξ)))‖^2=
      ‖𝓕 (fun t => P (sourceWave F false g advanced μ t)) ξ‖^2 := by
  have he : embed (literalResponse F false g advanced μ hμ (frequencyScale advanced*ξ))=
      ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) • 𝓕 (sourceWave F false g advanced μ) ξ := by
    simp only [literalResponse,line_scale]
    exact (actual_source_wave_fourier F false g advanced μ hμ ξ).symm
  rw [he,map_smul,fourier_reader P _ (actual_source_wave_integrable F false g advanced μ hμ),norm_smul]
  cases advanced <;> simp [FullYPairedParseval.direction]

private theorem scale_mass_return (a b s : ℝ) (hs : s≠0) (h : s⁻¹*a=b) : a=s*b := by
  have he := congrArg (fun x : ℝ => s*x) h
  simpa only [←mul_assoc,mul_inv_cancel₀ hs,one_mul] using he

/-- Original source norm, its two jets and the positive baseline generate both positive output masses; no fullY norm conservation or output budget is supplied. -/
theorem actual_output_positive_mass (F : Index) (g : QuantumTest) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (P : H →L[ℂ] H) :
    Integrable (fun w : ℝ => ‖P (embed (literalResponse F false g advanced μ hμ w))‖^2) ∧
      Integrable (fun t : ℝ => ‖P (sourceWave F false g advanced μ t)‖^2) ∧
      (∫w : ℝ,‖P (embed (literalResponse F false g advanced μ hμ w))‖^2)=
        (2*Real.pi)*(∫t : ℝ,‖P (sourceWave F false g advanced μ t)‖^2) := by
  have hF : Integrable (fun w : ℝ => ‖P (embed (literalResponse F false g advanced μ hμ w))‖^2) := by
    apply ((actual_response_square_integrable F false g advanced μ hμ).const_mul (‖P‖^2)).mono'
      ((P.continuous.comp (actual_response_continuous F false g advanced μ hμ)).norm.pow 2).aestronglyMeasurable
    apply Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (P.le_opNorm _) 2).trans_eq (mul_pow _ _ _)
  have hT : Integrable (fun t : ℝ => ‖P (sourceWave F false g advanced μ t)‖^2) := by
    apply ((actual_source_time_square_integrable F g advanced μ hμ).const_mul (‖P‖^2)).mono'
      ((P.continuous.comp_aestronglyMeasurable
        (actual_source_wave_integrable F false g advanced μ hμ).aestronglyMeasurable).norm.pow 2)
    apply Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (P.le_opNorm _) 2).trans_eq (mul_pow _ _ _)
  refine ⟨hF,hT,?_⟩
  have h := (integral_congr_ae (Eventually.of_forall (actual_output_fourier_mass_return F g advanced μ hμ P))).trans
    (actual_source_output_parseval F g advanced μ hμ P)
  have hs := MeasureTheory.Measure.integral_comp_mul_left
    (fun w : ℝ => ‖P (embed (literalResponse F false g advanced μ hμ w))‖^2) (frequencyScale advanced)
  have h0 := hs.symm.trans h
  clear h
  simp only [abs_inv,scale_abs,smul_eq_mul] at h0
  exact scale_mass_return _ _ _ (by positivity : 2*Real.pi≠0) h0

/-- The four original output grades have exact positive frequency/time prices on the same complete retarded source. -/
theorem actual_four_grade_positive_mass (F : Index) (dual advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) (j : Fin 4) :
    (∫w : ℝ,‖projection (3,⟨j.val,by omega⟩)
      (embed (literalResponse F false (wedgeTest dual a f) advanced μ hμ w))‖^2)=
      (2*Real.pi)*(∫t : ℝ,‖gradeTimeWave F dual advanced a f μ j t‖^2) :=
  (actual_output_positive_mass F (wedgeTest dual a f) advanced μ hμ (projection (3,⟨j.val,by omega⟩))).2.2

/-- Complete primal frequency mass returns to the four finite positive time measures, including all three original Y leakage grades. -/
theorem actual_complete_four_grade_positive_mass (F : Index) (dual advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) :
    (∫w : ℝ,‖embed (literalResponse F false (wedgeTest dual a f) advanced μ hμ w)‖^2)=
      (2*Real.pi)*(∑j : Fin 4,∫t : ℝ,‖gradeTimeWave F dual advanced a f μ j t‖^2) := by
  have h := (actual_output_positive_mass F (wedgeTest dual a f) advanced μ hμ (ContinuousLinearMap.id ℂ H)).2.2
  simp only [ContinuousLinearMap.id_apply] at h
  rw [h]
  congr 1
  rw [←integral_finsetSum Finset.univ (fun j _ => actual_grade_time_square_integrable F dual advanced a f μ hμ j)]
  exact integral_congr_ae (Eventually.of_forall (actual_four_grade_causal_intensity F dual advanced a f μ))

end LowEnergy.FourGradeOutputParseval
