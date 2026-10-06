import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceHamiltonianSpectralFrequency

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceHamiltonianSpectralPair
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceHamiltonianSpectralFrequency SourceResolventLorentzian SourceResolventBandLimit
open SourceActualResolventEnergy FullYSourceResolventGraphSplice SourceInverseSourceLeg MeasureTheory Filter
open scoped Topology InnerProductSpace

private theorem profile_nonneg (ν : Measure ℝ) (μ w : ℝ) : 0 ≤ profile ν μ w := by
  apply integral_nonneg
  intro a
  unfold kernel
  positivity

/-- The source mass controls the spectral profile at every frequency. -/
theorem spectral_profile_bound (ν : Measure ℝ) [IsFiniteMeasure ν] (μ : ℝ) (hμ : 0<μ) (w : ℝ) :
    profile ν μ w ≤ μ⁻¹^2*ν.real Set.univ := by
  have hb (a : ℝ) : kernel μ a w ≤ μ⁻¹^2 := by
    unfold kernel
    rw [inv_pow]
    exact inv_anti₀ (sq_pos_of_pos hμ) (by nlinarith [sq_nonneg (a-w)])
  have hc : Continuous (fun a : ℝ => kernel μ a w) := by
    unfold kernel
    exact Continuous.inv₀ (by fun_prop) (fun a => by positivity)
  have hn (a : ℝ) : ‖kernel μ a w‖ ≤ μ⁻¹^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by unfold kernel;positivity)]
    exact hb a
  have hi : Integrable (fun a : ℝ => kernel μ a w) ν :=
    Integrable.of_bound hc.aestronglyMeasurable _ (Eventually.of_forall hn)
  have h := integral_mono hi (integrable_const (μ⁻¹^2)) hb
  simpa only [profile,integral_const,smul_eq_mul,mul_comm] using! h

private theorem finite_bound (F : Index) (g : H) (μ : ℝ) (hμ : 0<μ) (w : ℝ) :
    ‖finiteResolvent F (line μ w) g‖^2 ≤ μ⁻¹^2*‖g‖^2 := by
  have h := ((finiteResolvent F (line μ w)).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right (line_resolvent_norm (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) μ hμ w) (norm_nonneg g))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2

attribute [local irreducible] finiteResolvent profile

private theorem pair_L1 {ι : Type*} (l : Filter ι) (f q : ι → ℝ → ℝ) (p r : ℝ → ℝ) (A B : ℝ)
    (hfi : ∀ i,Integrable (f i)) (hqi : ∀ i,Integrable (q i)) (hpi : Integrable p) (hri : Integrable r)
    (hq : ∀ i w,0 ≤ q i w ∧ q i w ≤ B) (hp : ∀ w,0 ≤ p w ∧ p w ≤ A)
    (hr : ∀ w,0 ≤ r w ∧ r w ≤ B)
    (hfL : Tendsto (fun i => ∫ w : ℝ,|f i w-p w|) l (𝓝 0))
    (hqL : Tendsto (fun i => ∫ w : ℝ,|q i w-r w|) l (𝓝 0)) :
    Integrable (fun w => p w*r w) ∧
    Tendsto (fun i => ∫ w : ℝ,|f i w*q i w-p w*r w|) l (𝓝 0) := by
  have hpq : Integrable (fun w => p w*r w) := hpi.mul_bdd hri.aestronglyMeasurable
    (Eventually.of_forall (fun w => by rw [Real.norm_eq_abs,abs_of_nonneg (hr w).1];exact (hr w).2))
  refine ⟨hpq,?_⟩
  have hbound (i : ι) : (∫ w : ℝ,|f i w*q i w-p w*r w|) ≤
      B*(∫ w : ℝ,|f i w-p w|)+A*(∫ w : ℝ,|q i w-r w|) := by
    have hprod : Integrable (fun w => f i w*q i w) := (hfi i).mul_bdd (hqi i).aestronglyMeasurable
      (Eventually.of_forall (fun w => by rw [Real.norm_eq_abs,abs_of_nonneg (hq i w).1];exact (hq i w).2))
    have hdiff : Integrable (fun w => |f i w*q i w-p w*r w|) := (hprod.sub hpq).abs
    have hf : Integrable (fun w => |f i w-p w|) := ((hfi i).sub hpi).abs
    have hg : Integrable (fun w => |q i w-r w|) := ((hqi i).sub hri).abs
    have hm := integral_mono hdiff ((hf.const_mul B).add (hg.const_mul A)) (fun w => by
      have he : f i w*q i w-p w*r w=(f i w-p w)*q i w+p w*(q i w-r w) := by ring
      rw [he]
      have h := abs_add_le ((f i w-p w)*q i w) (p w*(q i w-r w))
      rw [abs_mul,abs_mul,abs_of_nonneg (hq i w).1,abs_of_nonneg (hp w).1] at h
      exact h.trans (by dsimp only [Pi.add_apply];nlinarith [mul_le_mul_of_nonneg_left (hq i w).2 (abs_nonneg (f i w-p w)),
        mul_le_mul_of_nonneg_right (hp w).2 (abs_nonneg (q i w-r w))]))
    have ha := integral_add (hf.const_mul B) (hg.const_mul A)
    simp only [Pi.add_apply] at hm ha
    rw [ha,integral_const_mul,integral_const_mul] at hm
    exact hm
  apply squeeze_zero (fun i => integral_nonneg (fun w => abs_nonneg _)) hbound
  simpa only [mul_zero,add_zero] using (hfL.const_mul B).add (hqL.const_mul A)

/-- Both original causal legs use the same F and generate an integrable full-frequency product limit. -/
theorem actual_source_pair_measure (g k : diagonal.domain) :
    ∃ ν κ : Measure ℝ,IsFiniteMeasure ν ∧ IsFiniteMeasure κ ∧
      ν Set.univ=ENNReal.ofReal (‖(g : H)‖^2) ∧ κ Set.univ=ENNReal.ofReal (‖(k : H)‖^2) ∧
      ∀ (μ : ℝ),0<μ → Integrable (fun w => profile κ μ w*profile ν μ w) ∧
        Tendsto (fun F => ∫ w : ℝ,
          |‖finiteResolvent F (star (line μ w)) (k : H)‖^2*‖finiteResolvent F (line μ w) (g : H)‖^2-
            profile κ μ w*profile ν μ w|) (sourceFilter : Filter Index) (𝓝 0) := by
  obtain ⟨ν,hνfin,hνmass,hν⟩ := actual_source_frequency_measure g
  obtain ⟨κ,hκfin,hκmass,hκ⟩ := actual_source_frequency_measure k
  let := hνfin
  let := hκfin
  refine ⟨ν,κ,hνfin,hκfin,hνmass,hκmass,fun μ hμ => ?_⟩
  have hn : ν.real Set.univ=‖(g : H)‖^2 := by rw [Measure.real,hνmass,ENNReal.toReal_ofReal (sq_nonneg _)]
  have hk : κ.real Set.univ=‖(k : H)‖^2 := by rw [Measure.real,hκmass,ENNReal.toReal_ofReal (sq_nonneg _)]
  have hfi (x : H) (F : Index) : Integrable (fun w => ‖finiteResolvent F (line μ w) x‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! actual_square_integrable F μ hμ x
  have h := pair_L1 (sourceFilter : Filter Index)
    (fun F w => ‖finiteResolvent F (line μ w) (k : H)‖^2)
    (fun F w => ‖finiteResolvent F (line μ w) (g : H)‖^2)
    (profile κ μ) (profile ν μ) (μ⁻¹^2*‖(k : H)‖^2) (μ⁻¹^2*‖(g : H)‖^2)
    (hfi (k : H)) (hfi (g : H)) (hκ μ hμ).1 (hν μ hμ).1
    (fun F w => ⟨sq_nonneg _,finite_bound F (g : H) μ hμ w⟩)
    (fun w => ⟨profile_nonneg κ μ w,by simpa only [hk] using spectral_profile_bound κ μ hμ w⟩)
    (fun w => ⟨profile_nonneg ν μ w,by simpa only [hn] using spectral_profile_bound ν μ hμ w⟩)
    (hκ μ hμ).2.2 (hν μ hμ).2.2
  refine ⟨h.1,?_⟩
  have he (F : Index) (w : ℝ) : ‖finiteResolvent F (star (line μ w)) (k : H)‖=
      ‖finiteResolvent F (line μ w) (k : H)‖ :=
    actual_conjugate_leg_norm F (line μ w) (by simpa only [line_im] using hμ.ne') (k : H)
  simp_rw [he]
  exact h.2

end LowEnergy.SourceHamiltonianSpectralPair
