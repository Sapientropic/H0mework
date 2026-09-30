import H0mework.Versions.X.NavierStokes.WindowSchurSchur.SampleControl
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.TestProduct

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurAdvectorFiber
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H lift)
open NativeWindowHistoryMeanAction (frozen)
open NativeWindowHistoryMeanBlocks (diffusion)
open NativeWindowHistorySchurCompletion (completion commonForce)
open NativeWindowHistorySchurSampleControl (sample sampleEnergy)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativePhysicalFourier
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem difference_curl (nu : Viscosity) (M : ℕ) (u v : physicalSpace (modes M)) :
    ((frozen nu M u-frozen nu M 0) v).1=
      NativeAffineTransport.transport (modes M) nu (NativeWindowTraceAdjoint.curlMap M u) v.1 := by
  simpa only [sub_zero] using NativeWindowHistoryMeanAction.frozen_difference nu M u 0 v

def transportLinear (nu : Viscosity) (M : ℕ) :
    physicalSpace (modes M) →ₗ[ℝ] (physicalSpace (modes M) →L[ℝ] physicalSpace (modes M)) where
  toFun u:=frozen nu M u-frozen nu M 0
  map_add' u v:=by
    apply ContinuousLinearMap.ext
    intro w
    apply Subtype.ext
    change ((frozen nu M (u+v)-frozen nu M 0) w).1=
      ((frozen nu M u-frozen nu M 0) w).1+((frozen nu M v-frozen nu M 0) w).1
    simp only [difference_curl,map_add,add_apply]
  map_smul' s u:=by
    apply ContinuousLinearMap.ext
    intro w
    apply Subtype.ext
    change ((frozen nu M (s • u)-frozen nu M 0) w).1=s • ((frozen nu M u-frozen nu M 0) w).1
    simp only [difference_curl,map_smul,smul_apply]

def fiberLinear (nu : Viscosity) (M : ℕ) : physicalSpace (modes M) →ₗ[ℝ] (wholePhysical →L[ℝ] wholePhysical) where
  toFun u:=lift M (transportLinear nu M u)
  map_add' u v:=by
    apply ContinuousLinearMap.ext
    intro w
    simp only [map_add,lift,ContinuousLinearMap.comp_apply,add_apply]
  map_smul' s u:=by
    apply ContinuousLinearMap.ext
    intro w
    simp only [map_smul,lift,ContinuousLinearMap.comp_apply,smul_apply,RingHom.id_apply]

def family (nu : Viscosity) (M : ℕ) : wholePhysical →L[ℝ] wholePhysical →L[ℝ] wholePhysical :=
  (LinearMap.toContinuousLinearMap (fiberLinear nu M)).comp (restrictCLM (modes M) (modes_zero M) (modes_closed M))

theorem family_original (nu : Viscosity) (M : ℕ) (u v : wholePhysical) :
    family nu M u v=includeCLM (modes M) (modes_closed M)
      (NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M) nu
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) u)
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)) := by
  change includeCLM (modes M) (modes_closed M) ((frozen nu M
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) u)-frozen nu M 0)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))=_
  rw [NativeWindowHistoryCreationSource.frozen_transport,sub_zero]

theorem family_source (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    diffusion nu M v+family nu M (NativeWindowHistoryOseen.velocityPath seed M time) v=
      NativeWindowHistoryOseen.forwardFiber seed M time v := by
  change includeCLM (modes M) (modes_closed M) (frozen nu M 0 (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))+
    includeCLM (modes M) (modes_closed M) ((frozen nu M
      (restrictCLM (modes M) (modes_zero M) (modes_closed M)
        (includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.value seed M time)))-frozen nu M 0)
          (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))=_
  rw [restrict_include,sub_apply,← map_add]
  have scalar: frozen nu M 0 (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)+
      (frozen nu M (NativeWindowTraceAdjoint.value seed M time) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)-
        frozen nu M 0 (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))=
      frozen nu M (NativeWindowTraceAdjoint.value seed M time) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v) := by abel
  exact congrArg (includeCLM (modes M) (modes_closed M)) scalar

theorem completion_norm_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ∀ᵐ lag ∂averageMeasure,‖completion seed M time lag‖ ≤ ‖commonForce seed M time‖ := by
  filter_upwards [NativeWindowHistorySchurSampleControl.sample_equation seed M time,
    NativeWindowHistorySchurSampleControl.sample_include seed M time] with lag equation included
  have gradient0:=NativeWindowHistorySchurSampleControl.gradient_nonnegative M (sample seed M time lag)
  have cauchy:=real_inner_le_norm (includeCLM (modes M) (modes_closed M) (sample seed M time lag)) (commonForce seed M time)
  rw [include_norm (modes M) (modes_zero M)] at cauchy
  have mass:pairing (modes M) (sample seed M time lag) (sample seed M time lag)=
      ‖coefficients (modes M) (sample seed M time lag)‖^2:=real_inner_self_eq_norm_sq (coefficients (modes M) (sample seed M time lag))
  unfold sampleEnergy at equation
  have bounded:‖coefficients (modes M) (sample seed M time lag)‖ ≤ ‖commonForce seed M time‖ := by
    nlinarith only [equation,mass,cauchy,mul_nonneg nu.coeff_pos.le gradient0,
      norm_nonneg (coefficients (modes M) (sample seed M time lag)),norm_nonneg (commonForce seed M time)]
  rw [← included,include_norm (modes M) (modes_zero M)]
  exact bounded

theorem completion_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    MemLp (completion seed M time) ∞ averageMeasure :=
  MemLp.of_bound (Lp.memLp (completion seed M time)).aestronglyMeasurable ‖commonForce seed M time‖ (completion_norm_ae seed M time)

def xProfile (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : Lp wholePhysical ∞ averageMeasure :=
  (completion_memLp seed M time).toLp (completion seed M time)

theorem xProfile_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    xProfile seed M time=ᵐ[averageMeasure] completion seed M time := (completion_memLp seed M time).coeFn_toLp

def rawProfile (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : Lp wholePhysical ∞ averageMeasure :=
  NativeWindowHistoryOseen.profile (NativeWindowHistoryOseen.velocityPath seed M) (NativeWindowHistoryOseen.velocityPath_continuous seed M) time

theorem rawProfile_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    rawProfile seed M time=ᵐ[averageMeasure] finiteHistory seed time M :=
  (NativeWindowHistoryOseen.profile_ae _ (NativeWindowHistoryOseen.velocityPath_continuous seed M) time).trans
    (NativeWindowHistoryOseen.history_original seed M time).symm

def wProfile (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : Lp wholePhysical ∞ averageMeasure :=
  rawProfile seed M time-xProfile seed M time

theorem wProfile_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    wProfile seed M time=ᵐ[averageMeasure] NativeWindowHistorySchurTemporalControl.temporalResponse seed M time := by
  have identity:finiteHistory seed time M-completion seed M time=NativeWindowHistorySchurTemporalControl.temporalResponse seed M time := by
    rw [NativeWindowHistorySchurCompletion.source_split]
    abel
  filter_upwards [Lp.coeFn_sub (rawProfile seed M time) (xProfile seed M time),rawProfile_ae seed M time,xProfile_ae seed M time,
    Lp.coeFn_sub (finiteHistory seed time M) (completion seed M time)] with lag difference raw x original
  have read: wProfile seed M time lag=finiteHistory seed time M lag-completion seed M time lag := by
    rw [show wProfile seed M time lag=(rawProfile seed M time-xProfile seed M time) lag from rfl,difference,Pi.sub_apply,raw,x]
  exact read.trans (original.symm.trans (congrArg (fun h : H => h lag) identity))

def squareCap : ℝ := 36*Real.sqrt NativeUnheatedRieszKernel.constant*((2*Real.pi)^2)⁻¹

theorem squareCap_nonnegative : 0 ≤ squareCap := by unfold squareCap; positivity

theorem square_bound (M : ℕ) (v : physicalSpace (modes M)) :
    ‖NativeWindowStressHeatSource.physical (NativeWindowHistoryCreationGeometry.square (modes M) v)‖ ≤
      squareCap*curlPair (modes M) v.1 v.1 := by
  rw [NativeWindowHistoryCreationGeometry.square,map_sum]
  apply (norm_sum_le _ _).trans
  have paid:=Finset.sum_le_sum (s := (Finset.univ : Finset ThreeDimensionalPeriodicCoarseFilterCore.Coordinate)) fun i _ =>
    NativeWindowAugmentedTestProduct.product_bound (modes M) (modes M) v (modes_zero M) (modes_closed M) (modes_closed M) i i
  apply paid.trans_eq
  simp only [Fin.sum_univ_three]
  rw [NativeWindowAugmentedTestProduct.curl_original (modes M) v (modes_zero M)]
  unfold squareCap
  field_simp
  ring

theorem source_square_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ B : ℝ,0 ≤ B ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      ∀ᵐ lag ∂averageMeasure,‖NativeWindowStressHeatSource.physical
        (NativeWindowHistoryCreationGeometry.square (modes M) (sample seed M time lag))‖ ≤ B := by
  obtain ⟨low,C,C0,paid⟩:=NativeWindowHistorySchurSampleControl.source_sample_bound seed horizon nonnegative
  refine ⟨low,squareCap*(C/nu.coeff),mul_nonneg squareCap_nonnegative (div_nonneg C0 nu.coeff_pos.le),fun M above time inside => ?_⟩
  filter_upwards [paid M above time inside] with lag bound
  have mass0:0 ≤ pairing (modes M) (sample seed M time lag) (sample seed M time lag) :=
    real_inner_self_nonneg (x := coefficients (modes M) (sample seed M time lag))
  have grad:curlPair (modes M) (sample seed M time lag).1 (sample seed M time lag).1 ≤ C/nu.coeff := by
    apply (le_div_iff₀ nu.coeff_pos).mpr
    unfold sampleEnergy at bound
    nlinarith only [bound,mass0]
  exact (square_bound M (sample seed M time lag)).trans (mul_le_mul_of_nonneg_left grad squareCap_nonnegative)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem profiles_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    (xProfile seed M (step.2.clockAdvance+time),wProfile seed M (step.2.clockAdvance+time))=
      (xProfile step.1 M time,wProfile step.1 M time) := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [xProfile_ae seed M (step.2.clockAdvance+time),xProfile_ae step.1 M time] with lag first last
    rw [first,last,NativeWindowHistorySchurCompletion.completion_next seed M step generated time nonnegative]
  · apply Lp.ext
    filter_upwards [wProfile_ae seed M (step.2.clockAdvance+time),wProfile_ae step.1 M time] with lag first last
    rw [first,last,NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurAdvectorFiber
