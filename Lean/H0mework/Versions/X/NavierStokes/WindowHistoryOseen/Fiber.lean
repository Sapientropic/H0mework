import H0mework.Versions.X.NavierStokes.WindowEnergyTraceEndpoint.Window
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryOseen
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint NativeCommonAdvectorAction
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_inner restrict_include)
open NativeWindowTraceAdjoint (forward dual)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

abbrev H := Lp wholePhysical 2 averageMeasure

def lift (M : ℕ) (A : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M)) : wholePhysical →L[ℝ] wholePhysical :=
  (includeCLM (modes M) (modes_closed M)).comp (A.comp (restrictCLM (modes M) (modes_zero M) (modes_closed M)))

theorem lift_included (M : ℕ) (A : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M)) (v : physicalSpace (modes M)) :
    lift M A (includeCLM (modes M) (modes_closed M) v)=includeCLM (modes M) (modes_closed M) (A v) := by
  simp only [lift,ContinuousLinearMap.comp_apply,restrict_include]

def forwardFiber (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sampleTime : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  lift M (forward seed M sampleTime)

def dualFiber (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sampleTime : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  lift M (dual seed M sampleTime)

theorem forwardFiber_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (forwardFiber seed M) := by
  exact continuous_const.clm_comp ((NativeWindowTraceAdjoint.forward_continuous seed M).clm_comp continuous_const)

theorem dualFiber_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (dualFiber seed M) := by
  exact continuous_const.clm_comp ((NativeWindowTraceAdjoint.dual_continuous seed M).clm_comp continuous_const)

theorem fiber_adjoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sampleTime : ℝ) (u v : wholePhysical) :
    inner ℝ (forwardFiber seed M sampleTime u) v=inner ℝ u (dualFiber seed M sampleTime v) := by
  change inner ℝ (includeCLM (modes M) (modes_closed M)
    (forward seed M sampleTime (restrictCLM (modes M) (modes_zero M) (modes_closed M) u))) v=_
  rw [include_inner _ (modes_zero M),NativeWindowTraceAdjoint.adjoint_pairing]
  rw [← real_inner_comm u (dualFiber seed M sampleTime v)]
  change _=inner ℝ (includeCLM (modes M) (modes_closed M)
    (dual seed M sampleTime (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))) u
  rw [include_inner _ (modes_zero M),pairing_symmetric]

theorem fiber_dissipative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sampleTime : ℝ) (v : wholePhysical) :
    inner ℝ v (forwardFiber seed M sampleTime v)≤0 := by
  rw [real_inner_comm]
  change inner ℝ (includeCLM (modes M) (modes_closed M)
    (forward seed M sampleTime (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))) v≤0
  rw [include_inner _ (modes_zero M),pairing_symmetric]
  exact physicalOperator_dissipative (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceAdjoint.advector seed M sampleTime) (NativeWindowTraceAdjoint.advector_reality seed M sampleTime) _

def forwardField (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time shift : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  forwardFiber seed M (time-shift)

def dualField (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time shift : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  dualFiber seed M (time-shift)

private abbrev Lag := Icc (-2 : ℝ) (-1)

private def lagPull (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(Lag,E) →L[ℝ] Lp E ∞ averageMeasure :=
  (BoundedContinuousFunction.toLp ∞ averageMeasure ℝ).comp
    ((BoundedContinuousFunction.compContinuousCLM E ℝ
      ⟨fun shift => projIcc (-2 : ℝ) (-1) (by norm_num) shift,continuous_projIcc (h := by norm_num)⟩).comp
      (ContinuousMap.linearIsometryBoundedOfCompact Lag E ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

private def lagCurve {E : Type*} [NormedAddCommGroup E] (A : ℝ → E) (continuous : Continuous A) : C(ℝ,C(Lag,E)) :=
  (⟨fun z : ℝ × Lag => A (z.1-z.2.1),
    continuous.comp (continuous_fst.sub (continuous_subtype_val.comp continuous_snd))⟩ : C(ℝ × Lag,E)).curry

def profile {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E) (continuous : Continuous A) (time : ℝ) : Lp E ∞ averageMeasure :=
  lagPull E (lagCurve A continuous time)

theorem profile_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E) (continuous : Continuous A) (time : ℝ) :
    profile A continuous time =ᵐ[averageMeasure] fun shift => A (time-shift) := by
  have read : profile A continuous time =ᵐ[averageMeasure]
      fun shift => A (time-(projIcc (-2 : ℝ) (-1) (by norm_num) shift).1) :=
    BoundedContinuousFunction.coeFn_toLp ∞ averageMeasure ℝ _
  filter_upwards [read,NativeWindowTraceEndpointWindow.average_interval] with shift actual support
  rw [actual,projIcc_of_mem _ support]

theorem profile_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E) (continuous : Continuous A) : Continuous (profile A continuous) :=
  (lagPull E).continuous.comp (lagCurve A continuous).continuous

def forwardProfile (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : Lp (wholePhysical →L[ℝ] wholePhysical) ∞ averageMeasure :=
  profile (forwardFiber seed M) (forwardFiber_continuous seed M) time

def dualProfile (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : Lp (wholePhysical →L[ℝ] wholePhysical) ∞ averageMeasure :=
  profile (dualFiber seed M) (dualFiber_continuous seed M) time

theorem forwardProfile_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    forwardProfile seed M time =ᵐ[averageMeasure] forwardField seed M time :=
  profile_ae (E := wholePhysical →L[ℝ] wholePhysical) _ _ _

theorem dualProfile_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    dualProfile seed M time =ᵐ[averageMeasure] dualField seed M time :=
  profile_ae (E := wholePhysical →L[ℝ] wholePhysical) _ _ _

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryOseen
