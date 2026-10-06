import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceHamiltonianSpectralMeasure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceHamiltonianSpectralEnergy
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceHamiltonianSpectralMeasure FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped InnerProductSpace Topology

private theorem resolvent_im {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) (x : E) :
    (inner ℂ x (FullYSourceResolventGraphSplice.resolvent C z x)).im=z.im*‖FullYSourceResolventGraphSplice.resolvent C z x‖^2 := by
  let y := FullYSourceResolventGraphSplice.resolvent C z x
  have he : C y-z • y=x := by
    have h := congrArg (fun A : E →L[ℂ] E => A x) (resolvent_right C hC z hz)
    simpa only [mul_apply_eq_comp,sub_apply,smul_apply,
      one_apply_eq_self,y] using h
  have him : (inner ℂ y x).im= -z.im*‖y‖^2 := by
    have hr : (inner ℂ y (C y)).im=0 := hC.isSymmetric.im_inner_self_apply y
    have hyy : inner ℂ y y=((‖y‖^2 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) y
    rw [←he,inner_sub_right,inner_smul_right,hyy]
    simp only [Complex.sub_im,Complex.mul_im,hr,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add,zero_sub,neg_mul]
  have hi := congrArg Complex.im (inner_conj_symm y x)
  simp only [Complex.conj_im] at hi
  change (inner ℂ x y).im=z.im*‖y‖^2
  linarith

/-- The original response energy is the absorptive scalar resolvent at the same nonreal frequency. -/
theorem actual_response_energy (F : Index) (g : H) (z : ℂ) (hz : z.im≠0) :
    ‖finiteResolvent F z g‖^2=(inner ℂ g (finiteResolvent F z g)).im/z.im := by
  apply (eq_div_iff hz).mpr
  exact (mul_comm _ _).trans (resolvent_im (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) z hz g).symm

private theorem pole_im (a : ℝ) (z : ℂ) :
    (((a : ℂ)-z)⁻¹).im=z.im*‖((a : ℂ)-z)⁻¹‖^2 := by
  rw [Complex.inv_im,norm_inv,inv_pow,←Complex.normSq_eq_norm_sq]
  simp only [Complex.sub_im,Complex.ofReal_im,zero_sub,neg_neg,div_eq_mul_inv]

private theorem measure_energy (ν : Measure ℝ) [IsFiniteMeasure ν] (z : ℂ) (hz : z.im≠0) :
    (∫ a : ℝ,‖((a : ℂ)-z)⁻¹‖^2 ∂ν)=(∫ a : ℝ,((a : ℂ)-z)⁻¹ ∂ν).im/z.im := by
  have hn (a : ℝ) : (a : ℂ)-z≠0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
    exact hz hi
  have hc : Continuous (fun a : ℝ => ((a : ℂ)-z)⁻¹) := Continuous.inv₀ (by fun_prop) hn
  have hb (a : ℝ) : ‖((a : ℂ)-z)⁻¹‖ ≤ |z.im|⁻¹ := by
    rw [norm_inv]
    apply inv_anti₀ (abs_pos.mpr hz)
    simpa only [Complex.sub_im,Complex.ofReal_im,zero_sub,abs_neg] using Complex.abs_im_le_norm ((a : ℂ)-z)
  have hi : Integrable (fun a : ℝ => ((a : ℂ)-z)⁻¹) ν :=
    Integrable.of_bound hc.aestronglyMeasurable _ (Eventually.of_forall hb)
  have him : (∫ a : ℝ,(((a : ℂ)-z)⁻¹).im ∂ν)=(∫ a : ℝ,((a : ℂ)-z)⁻¹ ∂ν).im := integral_im hi
  simp_rw [pole_im] at him
  rw [integral_const_mul] at him
  apply (eq_div_iff hz).mpr
  simpa only [mul_comm] using him

/-- One source measure simultaneously supplies the original amplitude and nonreal response energy. -/
theorem actual_source_energy_measure (g : diagonal.domain) :
    ∃ ν : Measure ℝ,IsFiniteMeasure ν ∧ ν Set.univ=ENNReal.ofReal (‖(g : H)‖^2) ∧
      ∀ (z : ℂ),z.im≠0 →
        Tendsto (fun F => inner ℂ (g : H) (finiteResolvent F z (g : H)))
          (sourceFilter : Filter Index) (𝓝 (∫ a : ℝ,((a : ℂ)-z)⁻¹ ∂ν)) ∧
        Tendsto (fun F => ‖finiteResolvent F z (g : H)‖^2)
          (sourceFilter : Filter Index) (𝓝 (∫ a : ℝ,‖((a : ℂ)-z)⁻¹‖^2 ∂ν)) := by
  obtain ⟨ν,hfinite,hm,hν⟩ := actual_source_spectral_measure g
  let := hfinite
  refine ⟨ν,hfinite,hm,fun z hz => ⟨hν z hz,?_⟩⟩
  have h := (Complex.continuous_im.tendsto _ |>.comp (hν z hz)).div_const z.im
  have he : (fun F => ‖finiteResolvent F z (g : H)‖^2)=(fun F => (inner ℂ (g : H) (finiteResolvent F z (g : H))).im/z.im) :=
    funext (fun F => actual_response_energy F (g : H) z hz)
  rw [he,measure_energy ν z hz]
  exact h

end LowEnergy.SourceHamiltonianSpectralEnergy
