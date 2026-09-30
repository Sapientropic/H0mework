import H0mework.NavierStokes.WindowSchurSchur.Form
import H0mework.NavierStokes.WindowSchurFrozen.Effective

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurWeightedInverse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryHeatDual (energy heat heatEnergy)
open NativeWindowHistoryEffectiveInverse (generator average)
open NativeWindowHistorySchurAction (effective cost)
open NativeWindowHistorySchurForm (cap)
noncomputable section
variable {nu : Viscosity}

theorem generator_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u v : physicalSpace (modes M)) :
    pairing (modes M) u (generator seed M time v)=inner ℝ (includeCLM (modes M) (modes_closed M) u)
      (includeCLM (modes M) (modes_closed M) v-effective seed M time (includeCLM (modes M) (modes_closed M) v)) := by
  rw [NativeWindowHistoryEffectiveInverse.generator_original,map_sub,inner_sub_right,
    include_inner (modes M) (modes_zero M),restrict_include,include_inner (modes M) (modes_zero M)]

private theorem cancel_square (x B : ℝ) (x0 : 0 ≤ x) (B0 : 0 ≤ B) (source : x^2 ≤ x*B) : x ≤ B := by
  by_cases zero:x=0
  · rw [zero]
    exact B0
  · have positive:0 < x:=lt_of_le_of_ne x0 (Ne.symm zero)
    exact (mul_le_mul_iff_left₀ positive).mp (by simpa only [pow_two,mul_comm] using source)

private theorem cancel_root (x e C : ℝ) (x0 : 0 ≤ x) (e0 : 0 ≤ e)
    (source : x ≤ C*Real.sqrt x*Real.sqrt e) : x ≤ C^2*e := by
  have squared:=pow_le_pow_left₀ x0 source 2
  rw [mul_pow,mul_pow,Real.sq_sqrt x0,Real.sq_sqrt e0] at squared
  apply cancel_square x (C^2*e) x0 (mul_nonneg (sq_nonneg C) e0)
  nlinarith only [squared]

theorem source_generator_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    heatEnergy nu M (generator seed M time v) ≤ cap seed horizon^2*energy nu M v := by
  let f:=generator seed M time v
  have paired:=NativeWindowHistorySchurForm.source_form_bound seed horizon M time inside (heat nu M f) v
  have read:inner ℝ (includeCLM (modes M) (modes_closed M) (heat nu M f))
      (includeCLM (modes M) (modes_closed M) v-effective seed M time (includeCLM (modes M) (modes_closed M) v))=heatEnergy nu M f :=
    (generator_pairing seed M time (heat nu M f) v).symm
  rw [read,abs_of_nonneg (NativeWindowHistoryHeatDual.heatEnergy_nonnegative nu M f),
    ← NativeWindowHistoryHeatDual.heatEnergy_self nu M f] at paired
  exact cancel_root _ _ _ (NativeWindowHistoryHeatDual.heatEnergy_nonnegative nu M f)
    (NativeWindowHistoryHeatDual.energy_nonnegative nu M v) paired

theorem generator_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    pairing (modes M) v (generator seed M time v)=energy nu M v+
      cost seed M time (includeCLM (modes M) (modes_closed M) v) := by
  rw [generator_pairing,inner_sub_right,include_inner (modes M) (modes_zero M),restrict_include,
    NativeWindowHistorySchurAction.effective_energy,NativeWindowHistoryMeanGradient.gradient_embed]
  have mass:pairing (modes M) v v=‖coefficients (modes M) v‖^2:=real_inner_self_eq_norm_sq (coefficients (modes M) v)
  rw [mass]
  unfold energy
  ring

theorem inverse_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    energy nu M (average seed M 0 time f) ≤ heatEnergy nu M f := by
  let v:=average seed M 0 time f
  have read:pairing (modes M) v f=energy nu M v+cost seed M time (includeCLM (modes M) (modes_closed M) v) :=
    (congrArg (pairing (modes M) v) (NativeWindowHistoryEffectiveInverse.left_inverse seed M time f)).symm.trans
      (generator_energy seed M time v)
  have energy0:=NativeWindowHistoryHeatDual.energy_nonnegative nu M v
  have below:energy nu M v ≤ pairing (modes M) v f := by
    rw [read]
    exact le_add_of_nonneg_right (NativeWindowHistorySchurAction.cost_nonnegative seed M time _)
  have squared:=(pow_le_pow_left₀ energy0 below 2).trans (NativeWindowHistoryHeatDual.dual_pairing_bound nu M v f)
  exact cancel_square _ _ energy0 (NativeWindowHistoryHeatDual.heatEnergy_nonnegative nu M f) squared

theorem source_weighted_inverse (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (f : physicalSpace (modes M)) :
    energy nu M (average seed M 0 time f) ≤ heatEnergy nu M f ∧
      heatEnergy nu M f ≤ cap seed horizon^2*energy nu M (average seed M 0 time f) := by
  refine ⟨inverse_energy seed M time f,?_⟩
  exact (congrArg (heatEnergy nu M) (NativeWindowHistoryEffectiveInverse.left_inverse seed M time f)).symm.trans_le
    (source_generator_bound seed horizon M time inside (average seed M 0 time f))

theorem source_time_word_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M order : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    energy nu M (average seed M order time (generator seed M time v)) ≤
      NativeWindowFiniteStressUniform.kernelBound order^2*cap seed horizon^2*energy nu M v := by
  have original:=congrArg (energy nu M) (NativeWindowHistoryEffectiveInverse.average_original seed M order time (generator seed M time v))
  exact original.trans_le ((NativeWindowHistoryHeatWindow.energy_bound seed M order time (generator seed M time v)).trans
    ((mul_le_mul_of_nonneg_left (source_generator_bound seed horizon M time inside v) (sq_nonneg _)).trans_eq (by ring)))

theorem source_composed_word_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M order : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (u v : physicalSpace (modes M)) :
    |pairing (modes M) u (generator seed M time (average seed M order time (generator seed M time v)))| ≤
      NativeWindowFiniteStressUniform.kernelBound order*cap seed horizon^2*Real.sqrt (energy nu M u)*Real.sqrt (energy nu M v) := by
  have cap0:=NativeWindowHistorySchurForm.cap_nonnegative seed horizon
  have kernel0:0 ≤ NativeWindowFiniteStressUniform.kernelBound order:=(NativeWindowFiniteStressUniform.kernelBound_positive order).le
  have bound:=Real.sqrt_le_sqrt (source_time_word_bound seed horizon M order time inside v)
  rw [Real.sqrt_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq kernel0,Real.sqrt_sq cap0] at bound
  have paid:=NativeWindowHistorySchurForm.source_form_bound seed horizon M time inside u
    (average seed M order time (generator seed M time v))
  rw [← generator_pairing seed M time u] at paid
  exact paid.trans ((mul_le_mul_of_nonneg_left bound (mul_nonneg cap0 (Real.sqrt_nonneg _))).trans_eq (by ring))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem composed_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    (average seed M order (step.2.clockAdvance+time)).comp (generator seed M (step.2.clockAdvance+time))=
      (average step.1 M order time).comp (generator step.1 M time) :=
  congrArg₂ (fun A J : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) => A.comp J)
    (NativeWindowHistoryEffectiveInverse.average_next seed M order step generated time nonnegative)
    (NativeWindowHistoryEffectiveInverse.generator_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurWeightedInverse
