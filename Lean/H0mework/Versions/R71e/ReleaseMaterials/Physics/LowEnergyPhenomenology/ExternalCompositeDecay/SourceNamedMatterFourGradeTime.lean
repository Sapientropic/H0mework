import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterGradeBornBalance
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCausalCorrectionPrice
import Mathlib.Analysis.Fourier.Inversion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ThreeParticleRetardedTime
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open NativeHistoryGrade GaussCoreLabel NamedColorQtNext NamedMatterWedgeQt GaussDensityCore
open FullYDynamicSource FullYPairedParseval FullYDynamicSourceNext
open MeasureTheory
open scoped FourierTransform BigOperators Topology InnerProductSpace
attribute [local irreducible] embed literalCoreResolvent literalCoreTime waveCorrection
  NativeHistoryGrade.projection GaussCoreLabel.project
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H

/-- Four output grades are restrictions of the same original Number-three carrier. -/
def fourGradeReader : H →L[ℂ] H := ∑j : Fin 4, projection (3,⟨j.val,by omega⟩)

private theorem four_grade_word (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (dual : Bool) (a : WedgeFiber) (f : ScalarTest) (j : Fin 4) :
    fourGradeReader (embed (originalWedgeLeg F z hz dual a f j.val)) =
      embed (originalWedgeLeg F z hz dual a f j.val) := by
  let v := embed (originalWedgeLeg F z hz dual a f j.val)
  have hj : projection (3,⟨j.val,by omega⟩) v=v :=
    (embed_project _ _).symm.trans (congrArg embed (actual_four_channel_sector F z hz dual a f j))
  have he (i : Fin 4) : projection (3,⟨i.val,by omega⟩) v = if i=j then v else 0 := by
    by_cases h : i=j
    · subst i; simpa only [if_true] using hj
    · have hlabel : ((3,⟨i.val,by omega⟩) : Label) ≠ ((3,⟨j.val,by omega⟩) : Label) := by
        intro hh; exact h (Fin.ext (congrArg (fun l : Label => l.2.val) hh))
      have hp := congrArg (fun T : H →L[ℂ] H => T v) (projection_product (3,⟨i.val,by omega⟩) (3,⟨j.val,by omega⟩))
      simpa only [mul_apply_eq_comp,hj,if_neg hlabel,zero_apply,if_neg h] using hp
  change fourGradeReader v=v
  simp only [fourGradeReader,_root_.sum_apply,he]
  simp

/-- The full four-word source inverse stays in the generated Number-three grade carrier. -/
theorem actual_four_grade_inverse (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (dual : Bool) (a : WedgeFiber) (f : ScalarTest) :
    fourGradeReader (embed (literalCoreResolvent F z hz (wedgeTest dual a f))) =
      embed (literalCoreResolvent F z hz (wedgeTest dual a f)) := by
  rw [actual_fullY_four_channel_response]
  simp only [map_sum,four_grade_word]

private theorem four_grade_input (dual : Bool) (a : WedgeFiber) (f : ScalarTest) :
    fourGradeReader (embed (wedgeTest dual a f))=embed (wedgeTest dual a f) := by
  let q := embed (wedgeTest dual a f)
  have hq : projection (3,0) q=q :=
    (embed_project _ _).symm.trans (congrArg embed (actual_wedge_bottom_sector dual a f))
  have hp (j : Fin 4) : projection (3,⟨j.val,by omega⟩) q=if j=0 then q else 0 := by
    by_cases h : j=0
    · subst j
      have hi : (⟨0,by omega⟩ : Fin 57)=0 := rfl
      simpa only [Fin.val_zero,hi,if_true] using hq
    · have hl : ((3,⟨j.val,by omega⟩) : Label)≠(3,0) := by
        intro hh; apply h; exact Fin.ext (congrArg (fun l : Label => l.2.val) hh)
      have he := congrArg (fun T : H →L[ℂ] H => T q) (projection_product (3,⟨j.val,by omega⟩) (3,0))
      simpa only [mul_apply_eq_comp,hq,if_neg hl,zero_apply,if_neg h] using he
  change fourGradeReader q=q
  simp only [fourGradeReader,_root_.sum_apply,hp]
  simp

private theorem fourier_reader {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (P : E →L[ℂ] E) (u : ℝ → E) (hu : Integrable u) (ξ : ℝ) :
    𝓕 (fun t => P (u t)) ξ = P (𝓕 u ξ) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  rw [←ContinuousLinearMap.integral_comp_comm P (Real.fourierIntegral_convergent_iff ξ |>.mpr hu)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => (map_smul P _ _).symm)


private theorem source_fourier_fixed (F : Index) (dual advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) (ξ : ℝ) :
    fourGradeReader (𝓕 (sourceWave F false (wedgeTest dual a f) advanced μ) ξ) =
      𝓕 (sourceWave F false (wedgeTest dual a f) advanced μ) ξ := by
  let c : ℂ := (FullYPairedParseval.direction advanced:ℂ)*Complex.I
  have hc : c≠0 := by cases advanced <;> simp [c,FullYPairedParseval.direction]
  have h := actual_source_wave_fourier F false (wedgeTest dual a f) advanced μ hμ ξ
  simp only [Bool.false_eq_true,ite_false] at h
  change c • 𝓕 (sourceWave F false (wedgeTest dual a f) advanced μ) ξ = _ at h
  have hp := congrArg fourGradeReader h
  rw [map_smul,actual_four_grade_inverse] at hp
  have he := congrArg (fun x : H => c⁻¹ • x) (hp.trans h.symm)
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using he

private theorem correction_fourier_fixed (F : Index) (dual advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) (ξ : ℝ) :
    fourGradeReader (𝓕 (waveCorrection F false (wedgeTest dual a f) advanced μ) ξ) =
      𝓕 (waveCorrection F false (wedgeTest dual a f) advanced μ) ξ := by
  let q := wedgeTest dual a f
  let u := sourceWave F false q advanced μ
  let b := causalWave μ (fun _ => embed q)
  have hsub : 𝓕 (waveCorrection F false q advanced μ) ξ = 𝓕 u ξ-𝓕 b ξ := by
    rw [waveCorrection]
    exact fourier_sub_integrable u b (actual_source_wave_integrable F false q advanced μ hμ)
      (constant_wave_integrable μ hμ _) ξ
  have h1 : fourGradeReader (𝓕 u ξ)=𝓕 u ξ := source_fourier_fixed F dual advanced a f μ hμ ξ
  have h2 : fourGradeReader (𝓕 b ξ)=𝓕 b ξ := by
    have he := constant_wave_fourier μ hμ (embed q) ξ
    exact (congrArg fourGradeReader he).trans
      ((map_smul fourGradeReader _ _).trans ((congrArg (fun x : H => _ • x) (four_grade_input dual a f)).trans he.symm))
  exact (congrArg fourGradeReader hsub).trans
    ((map_sub fourGradeReader _ _).trans ((congrArg₂ (·-·) h1 h2).trans hsub.symm))

/-- The same four-grade source carrier returns the complete original causal correction history by Fourier inversion. -/
theorem actual_four_grade_correction_time (F : Index) (dual advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (μ : ℝ) (hμ : 0 < μ) (t : ℝ) :
    fourGradeReader (waveCorrection F false (wedgeTest dual a f) advanced μ t) =
      waveCorrection F false (wedgeTest dual a f) advanced μ t := by
  let u := waveCorrection F false (wedgeTest dual a f) advanced μ
  have hu : Integrable u := actual_wave_correction_integrable F false (wedgeTest dual a f) advanced μ hμ
  have huf : Integrable (𝓕 u) := actual_wave_correction_fourier_integrable F false (wedgeTest dual a f) advanced μ hμ
  have hc : Continuous u := actual_wave_correction_continuous F false (wedgeTest dual a f) advanced μ
  have he : 𝓕 (fun s => fourGradeReader (u s)) = 𝓕 u := by
    funext ξ
    exact (fourier_reader fourGradeReader u hu ξ).trans (correction_fourier_fixed F dual advanced a f μ hμ ξ)
  have hp : Integrable (fun s => fourGradeReader (u s)) := fourGradeReader.integrable_comp hu
  have hpf : Integrable (𝓕 (fun s => fourGradeReader (u s))) := he ▸ huf
  have ep := hp.fourierInv_fourier_eq hpf (fourGradeReader.continuous.comp hc).continuousAt (v:=t)
  rw [he,hu.fourierInv_fourier_eq huf hc.continuousAt] at ep
  exact ep.symm


private theorem oriented_time_fixed (F : Index) (dual advanced : Bool) (a : WedgeFiber)
    (f : ScalarTest) (t : ℝ) (ht : 0 < t) :
    fourGradeReader (embed (literalCoreTime F false (wedgeTest dual a f)
      (FullYPairedParseval.direction advanced*t))) =
      embed (literalCoreTime F false (wedgeTest dual a f) (FullYPairedParseval.direction advanced*t)) := by
  have h := actual_four_grade_correction_time F dual advanced a f 1 (by norm_num) t
  let c : ℂ := (Real.exp (-(1:ℝ)*t):ℂ)
  have hc : c≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  rw [waveCorrection] at h
  change fourGradeReader (sourceWave F false (wedgeTest dual a f) advanced 1 t-
    causalWave 1 (fun _ => embed (wedgeTest dual a f)) t) = _ at h
  have hmem : t ∈ Set.Ioi (0:ℝ) := ht
  simp only [Pi.sub_apply,sourceWave,causalWave,Set.indicator_of_mem hmem,map_sub,map_smul,four_grade_input] at h
  have he : c • fourGradeReader (embed (literalCoreTime F false (wedgeTest dual a f)
      (FullYPairedParseval.direction advanced*t))) =
      c • embed (literalCoreTime F false (wedgeTest dual a f) (FullYPairedParseval.direction advanced*t)) :=
    sub_left_inj.mp h
  have hi := congrArg (fun x : H => c⁻¹ • x) he
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hi

/-- Fourier inversion of the actual complete source correction returns exactly four grades at every real time. -/
theorem actual_fullY_four_grade_time (F : Index) (dual : Bool) (a : WedgeFiber)
    (f : ScalarTest) (t : ℝ) :
    embed (literalCoreTime F false (wedgeTest dual a f) t) =
      ∑j : Fin 4, projection (3,⟨j.val,by omega⟩)
        (embed (literalCoreTime F false (wedgeTest dual a f) t)) := by
  have h : fourGradeReader (embed (literalCoreTime F false (wedgeTest dual a f) t)) =
      embed (literalCoreTime F false (wedgeTest dual a f) t) := by
    rcases lt_trichotomy 0 t with ht | ht | ht
    · simpa only [FullYPairedParseval.direction,Bool.false_eq_true,ite_false,one_mul] using
        oriented_time_fixed F dual false a f t ht
    · subst t; simpa only [literal_core_time_zero] using four_grade_input dual a f
    · have he := oriented_time_fixed F dual true a f (-t) (by linarith)
      simpa only [FullYPairedParseval.direction,ite_true,neg_one_mul,neg_neg] using he
  simpa only [fourGradeReader,_root_.sum_apply] using h.symm

end LowEnergy.ThreeParticleRetardedTime
