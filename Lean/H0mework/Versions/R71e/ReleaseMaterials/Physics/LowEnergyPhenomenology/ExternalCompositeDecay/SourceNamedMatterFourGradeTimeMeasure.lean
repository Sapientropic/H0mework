import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterFourGradeTime
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ThreeParticleRetardedTime
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open NativeHistoryGrade GaussCoreLabel NamedColorQtNext NamedMatterWedgeQt GaussDensityCore
open FullYDynamicSource FullYPairedParseval FullYDynamicSourceNext MeasureTheory
open scoped FourierTransform BigOperators Topology InnerProductSpace
attribute [local irreducible] embed literalCoreResolvent literalCoreTime NativeHistoryGrade.projection
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H

private theorem grade_norm_split (u : H) (hu : u=∑j : Fin 4,projection (3,⟨j.val,by omega⟩) u) :
    ‖u‖^2=∑j : Fin 4,‖projection (3,⟨j.val,by omega⟩) u‖^2 := by
  have hp (i j : Fin 4) :
      inner ℂ (projection (3,⟨i.val,by omega⟩) u) (projection (3,⟨j.val,by omega⟩) u)=
        if i=j then (‖projection (3,⟨j.val,by omega⟩) u‖^2 : ℂ) else 0 := by
    by_cases he : i=j
    · subst i
      simp only [if_true,inner_self_eq_norm_sq_to_K]
      norm_cast
    · have hl : ((3,⟨i.val,by omega⟩) : Label)≠((3,⟨j.val,by omega⟩) : Label) := by
        intro h; exact he (Fin.ext (congrArg (fun l : Label => l.2.val) h))
      have heq := projection_symmetric (3,⟨i.val,by omega⟩) u (projection (3,⟨j.val,by omega⟩) u)
      apply heq.trans
      rw [if_neg he]
      have ht := congrArg (fun A : H →L[ℂ] H => A u)
        (projection_product (3,⟨i.val,by omega⟩) (3,⟨j.val,by omega⟩))
      simp only [mul_apply_eq_comp,if_neg hl,zero_apply] at ht
      have hh := congrArg (fun v : H => inner ℂ u v) ht
      simpa only [inner_zero_right] using! hh
  have h : inner ℂ u u=∑j : Fin 4,(‖projection (3,⟨j.val,by omega⟩) u‖:ℂ)^2 := by
    conv_lhs => rw [hu]
    simp only [sum_inner,inner_sum,hp]
    simp
  rw [inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by simpa using h)

/-- Every real-time complete source intensity is exhausted by its four actual output grades. -/
theorem actual_fullY_four_grade_time_norm (F : Index) (dual : Bool) (a : WedgeFiber)
    (f : ScalarTest) (t : ℝ) :
    ‖embed (literalCoreTime F false (wedgeTest dual a f) t)‖^2 =
      ∑j : Fin 4,‖projection (3,⟨j.val,by omega⟩)
        (embed (literalCoreTime F false (wedgeTest dual a f) t))‖^2 :=
  grade_norm_split _ (actual_fullY_four_grade_time F dual a f t)

/-- The causal output grades are read from one actual source wave. -/
def gradeTimeWave (F : Index) (dual advanced : Bool) (a : WedgeFiber) (f : ScalarTest)
    (μ : ℝ) (j : Fin 4) (t : ℝ) : H :=
  projection (3,⟨j.val,by omega⟩) (sourceWave F false (wedgeTest dual a f) advanced μ t)

theorem actual_four_grade_causal_intensity (F : Index) (dual advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (μ t : ℝ) :
    ‖sourceWave F false (wedgeTest dual a f) advanced μ t‖^2 =
      ∑j : Fin 4,‖gradeTimeWave F dual advanced a f μ j t‖^2 := by
  apply grade_norm_split
  by_cases ht : t∈Set.Ioi (0:ℝ)
  · simp only [sourceWave,causalWave,Set.indicator_of_mem ht,map_smul]
    exact congrArg (fun x : H => (Real.exp (-μ*t):ℂ) • x)
      (actual_fullY_four_grade_time F dual a f (FullYPairedParseval.direction advanced*t)) |>.trans (by rw [Finset.smul_sum])
  · simp only [sourceWave,causalWave,Set.indicator_of_notMem ht,map_zero,Finset.sum_const_zero]


private theorem correction_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (u : ℝ → E) (hu : Integrable u) (huf : Integrable (𝓕 u)) (hc : Continuous u)
    (t : ℝ) : ‖u t‖≤∫ξ : ℝ,‖𝓕 u ξ‖ := by
  rw [←hu.fourierInv_fourier_eq huf hc.continuousAt,Real.fourierInv_eq_fourier_neg]
  exact fourier_bound (𝓕 u) (-t)

private theorem original_wave_bound (F : Index) (g : QuantumTest) (advanced : Bool) (μ : ℝ)
    (hμ : 0 < μ) : ∃M : ℝ, ∀t : ℝ, ‖sourceWave F false g advanced μ t‖≤M := by
  let u := waveCorrection F false g advanced μ
  let M := (∫ξ : ℝ,‖𝓕 u ξ‖)+‖embed g‖
  have hu := actual_wave_correction_integrable F false g advanced μ hμ
  have huf := actual_wave_correction_fourier_integrable F false g advanced μ hμ
  have hc := actual_wave_correction_continuous F false g advanced μ
  refine ⟨M,fun t => ?_⟩
  have he : sourceWave F false g advanced μ t = u t+causalWave μ (fun _ => embed g) t := by
    dsimp only [u,waveCorrection,Pi.sub_apply]
    abel
  have hb : ‖causalWave μ (fun _ => embed g) t‖≤‖embed g‖ := by
    by_cases ht : t∈Set.Ioi (0:ℝ)
    · simp only [causalWave,Set.indicator_of_mem ht,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
        change 0 < t at ht
        exact (neg_mul μ t).le.trans (neg_nonpos.mpr (mul_nonneg hμ.le ht.le))))
    · simp only [causalWave,Set.indicator_of_notMem ht,norm_zero]
      exact norm_nonneg _
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (correction_norm_bound u hu huf hc t) hb)

/-- The original two-jet Fourier source pays the squared complete time history, without a supplied time norm bound. -/
theorem actual_source_time_square_integrable (F : Index) (g : QuantumTest) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) : Integrable (fun t : ℝ => ‖sourceWave F false g advanced μ t‖^2) := by
  obtain ⟨M,hM⟩ := original_wave_bound F g advanced μ hμ
  have hu := actual_source_wave_integrable F false g advanced μ hμ
  apply (hu.norm.const_mul M).mono'
  · exact hu.aestronglyMeasurable.norm.pow 2
  · apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (hM t) (norm_nonneg (sourceWave F false g advanced μ t))

theorem actual_grade_time_square_integrable (F : Index) (dual advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) (j : Fin 4) :
    Integrable (fun t : ℝ => ‖gradeTimeWave F dual advanced a f μ j t‖^2) := by
  have hi := actual_source_time_square_integrable F (wedgeTest dual a f) advanced μ hμ
  have hm := (actual_source_wave_integrable F false (wedgeTest dual a f) advanced μ hμ).aestronglyMeasurable
  apply hi.mono' (((projection (3,⟨j.val,by omega⟩)).continuous.comp_aestronglyMeasurable hm).norm.pow 2)
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have h := actual_four_grade_causal_intensity F dual advanced a f μ t
  have hs := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 4))) => sq_nonneg
    ‖gradeTimeWave F dual advanced a f μ i t‖) (Finset.mem_univ j)
  exact hs.trans_eq h.symm

def gradeTimeMeasure (F : Index) (dual advanced : Bool) (a : WedgeFiber) (f : ScalarTest)
    (μ : ℝ) (j : Fin 4) : Measure ℝ := volume.withDensity
  (fun t => ENNReal.ofReal (‖gradeTimeWave F dual advanced a f μ j t‖^2))
def completeTimeMeasure (F : Index) (dual advanced : Bool) (a : WedgeFiber) (f : ScalarTest)
    (μ : ℝ) : Measure ℝ := volume.withDensity
  (fun t => ENNReal.ofReal (‖sourceWave F false (wedgeTest dual a f) advanced μ t‖^2))

/-- The complete physical half-line Born measure is exhausted by four finite positive source-generated grades on every Borel set. -/
theorem actual_four_grade_time_measure (F : Index) (dual advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) :
    (∀j : Fin 4,IsFiniteMeasure (gradeTimeMeasure F dual advanced a f μ j)) ∧
      IsFiniteMeasure (completeTimeMeasure F dual advanced a f μ) ∧
      ∀B : Set ℝ, MeasurableSet B → completeTimeMeasure F dual advanced a f μ B =
        ∑j : Fin 4, gradeTimeMeasure F dual advanced a f μ j B := by
  have hg (j : Fin 4) (B : Set ℝ) (hB : MeasurableSet B) :
      gradeTimeMeasure F dual advanced a f μ j B =
        ENNReal.ofReal (∫t in B,‖gradeTimeWave F dual advanced a f μ j t‖^2) := by
    rw [gradeTimeMeasure,withDensity_apply _ hB]
    exact (ofReal_integral_eq_lintegral_ofReal
      (actual_grade_time_square_integrable F dual advanced a f μ hμ j).restrict
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
  have hc (B : Set ℝ) (hB : MeasurableSet B) : completeTimeMeasure F dual advanced a f μ B =
      ENNReal.ofReal (∫t in B,‖sourceWave F false (wedgeTest dual a f) advanced μ t‖^2) := by
    rw [completeTimeMeasure,withDensity_apply _ hB]
    exact (ofReal_integral_eq_lintegral_ofReal
      (actual_source_time_square_integrable F (wedgeTest dual a f) advanced μ hμ).restrict
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
  refine ⟨fun j => ⟨?_⟩,⟨?_⟩,fun B hB => ?_⟩
  · rw [hg j Set.univ MeasurableSet.univ]; exact ENNReal.ofReal_lt_top
  · rw [hc Set.univ MeasurableSet.univ]; exact ENNReal.ofReal_lt_top
  · rw [hc B hB]
    simp_rw [hg _ B hB]
    rw [←ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg (fun _ => sq_nonneg _))]
    congr 1
    rw [←integral_finsetSum Finset.univ (fun j _ =>
      (actual_grade_time_square_integrable F dual advanced a f μ hμ j).restrict)]
    exact integral_congr_ae (Filter.Eventually.of_forall (actual_four_grade_causal_intensity F dual advanced a f μ))

end LowEnergy.ThreeParticleRetardedTime
