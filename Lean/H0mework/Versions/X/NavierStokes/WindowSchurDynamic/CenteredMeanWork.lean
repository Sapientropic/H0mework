import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.AdjointHeatSource
import H0mework.Versions.X.NavierStokes.WindowSchurMean.JetEnergy

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointMeanWork
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction
open NativeWholeResolvent (wholePhysical)
open NativePhysicalPairing (includeCLM include_norm)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H rateHistory)
open NativeWindowHistoryMeanProjection (embed mean)
open NativeWindowHistoryMeanPhysicalJet (physicalJet)
open NativeWindowHistorySchurTemporalControl (energy temporalResponse temporalBudget)
open NativeWindowHistoryJacobianControl (form heat jacobian correction)
open NativeWindowHistoryAnnihilationControl (laplacianAction laplacianFiber)
noncomputable section
variable {nu : Viscosity}

def meanRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  embed (mean (rateHistory seed M time))

theorem meanRate_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    meanRate seed M time=embed (includeCLM (modes M) (modes_closed M) (physicalJet seed M 1 time)) := by
  apply congrArg embed
  apply Subtype.ext
  exact (NativeWindowHistoryMeanTime.source_rate seed M time).trans
    (NativeWindowHistoryMeanPhysicalJet.includeState_jet seed M 1 time).symm

theorem meanRate_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    energy nu M (meanRate seed M time)=NativeWindowHistoryHeatDual.energy nu M (physicalJet seed M 1 time) := by
  rw [meanRate_original,energy,NativeWindowHistoryMeanProjection.embed_norm,include_norm (modes M) (modes_zero M),
    NativeWindowHistoryMeanGradient.gradient_embed]
  rfl

theorem source_meanRate_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
    energy nu M (meanRate seed M time) ≤ NativeWindowHistoryMeanJetEnergy.budget seed 1 horizon :=
  (meanRate_energy seed M time).trans_le (NativeWindowHistoryMeanJetEnergy.source_energy seed 1 horizon M time inside)

theorem constant_orthogonal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    inner ℝ (temporalResponse seed M time) (embed v)=0 := by
  rw [real_inner_comm (F := H),NativeWindowHistoryMeanProjection.embed_pairing,
    NativeWindowHistoryCommonResponseWork.temporal_mean]
  exact inner_zero_right (𝕜 := ℝ) v

theorem constant_form (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    form nu M (temporalResponse seed M time) (embed v)=0 := by
  have gradient : laplacianAction nu M (embed v)=embed (laplacianFiber nu M v) :=
    NativeWindowHistoryMeanProjection.comp_embed (laplacianFiber nu M) v
  have split := NativeWindowHistoryJacobianControl.form_split nu M (temporalResponse seed M time) (embed v)
  have right := congrArg (fun a : H => inner ℝ (temporalResponse seed M time) a) gradient
  have zeroRight := right.trans (constant_orthogonal seed M time (laplacianFiber nu M v))
  exact split.trans ((congrArg₂ (fun a b : ℝ => a+nu.coeff*b)
    (constant_orthogonal seed M time v) zeroRight).trans (by ring))

def work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  2*form nu M (temporalResponse seed M time) (jacobian seed M time (meanRate seed M time))

private theorem subtract_form {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G R : E →L[ℝ] E) (w v : E) (zero : inner ℝ w (G v)=0) :
    2*inner ℝ w (G ((ContinuousLinearMap.id ℝ E-R) v))= -2*inner ℝ w (G (R v)) := by
  simp only [sub_apply,ContinuousLinearMap.id_apply,map_sub,inner_sub_right,zero]
  ring

theorem work_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    work seed M time= -2*form nu M (temporalResponse seed M time) (correction seed M time (meanRate seed M time)) := by
  simpa only [work,form,jacobian] using! subtract_form (E := H) (heat nu M) (correction seed M time)
    (temporalResponse seed M time) (meanRate seed M time) (constant_form seed M time (mean (rateHistory seed M time)))

theorem work_adjoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    work seed M time= -2*inner ℝ (NativeWindowHistoryAdjointHeatSource.source seed M time)
      (NativeWindowHistorySchurTranspose.transposeAction seed M time (meanRate seed M time)) :=
  (work_original seed M time).trans (congrArg (fun a : ℝ => -2*a)
    (NativeWindowHistoryAdjointHeatSource.source_pairing seed M time _))

theorem source_work_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time ∈ Icc 0 horizon,|work seed M time| ≤ C := by
  obtain ⟨low,A,A0,controlled⟩ := NativeWindowHistoryJacobianControl.source_correction_bound seed horizon nonnegative 1 (by norm_num)
  let Q := NativeWindowHistoryMeanJetEnergy.budget seed 1 horizon
  have Q0 : 0 ≤ Q := NativeWindowHistoryMeanJetEnergy.budget_nonnegative seed 1 horizon
  refine ⟨low,temporalBudget seed horizon+(1+A)*Q,add_nonneg
    (NativeWindowHistorySchurTemporalControl.temporalBudget_nonnegative seed horizon) (mul_nonneg (by linarith) Q0),?_⟩
  intro M above time inside
  let v := meanRate seed M time
  let w := temporalResponse seed M time
  have given : energy nu M v ≤ Q := source_meanRate_bound seed horizon M time inside
  have mass : ‖v‖^2 ≤ energy nu M v :=
    le_add_of_nonneg_right (mul_nonneg nu.coeff_pos.le (NativeWindowHistoryMeanGradient.gradient_nonnegative seed M v))
  have response := (controlled M above time inside v).trans (add_le_add (by simpa only [one_mul] using given)
    (mul_le_mul_of_nonneg_left (mass.trans given) A0))
  have wbound := NativeWindowHistorySchurTemporalControl.source_temporal_energy seed horizon M time inside
  have first := NativeWindowHistoryJacobianControl.form_young seed M w (correction seed M time v) 1
  have last := NativeWindowHistoryJacobianControl.form_young seed M w (correction seed M time v) (-1)
  rw [work_original]
  apply abs_le.mpr
  constructor <;> nlinarith only [first,last,wbound,response]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem meanRate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    meanRate seed M (step.2.clockAdvance+time)=meanRate step.1 M time :=
  congrArg (fun q : H => embed (mean q)) (NativeWindowHistoryOseen.rateHistory_next seed M step generated time time0)

theorem work_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    work seed M (step.2.clockAdvance+time)=work step.1 M time := by
  exact congrArg₂ (fun w q : H => 2*form nu M w q)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0)
    (congrArg₂ (fun (J : H →L[ℝ] H) (q : H) => J q)
      (NativeWindowHistoryJacobianControl.jacobian_next seed M step generated time time0) (meanRate_next seed M step generated time time0))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointMeanWork
