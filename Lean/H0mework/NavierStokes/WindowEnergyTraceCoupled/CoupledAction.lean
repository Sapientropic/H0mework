import H0mework.NavierStokes.WindowEnergyTraceInverse.Integral

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCoupled
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint NativeCommonAdvectorAction
open NativeWindowTraceAdjoint (value forward dual propagated response)
open NativeWindowTraceDualEvolution (mass inverse lifted)
open NativeUnheatedGlobalNegativeOne (rate)
noncomputable section
variable {nu : Viscosity}

def combined (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (time : ℝ) : physicalSpace (modes M) :=
  value seed M time-propagated seed observation M F radius start finish ordered time

def drive (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : physicalSpace (modes M) :=
  NativeWindowStageNineSource.forcing seed M time-(2*nu.coeff) •
    NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu (value seed M time)

def input (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : NativeResolventCompactness.State :=
  (2 : ℝ) • rate seed time-NativeUnheatedSourceWeightedTail.nonlinear seed time-NativeUnheatedSourceQuadraticApprox.value M seed time

theorem action_sum (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    forward seed M time v+dual seed M time v= -(2*nu.coeff) •
      NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v := by
  change (physicalOperator (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time)) v+
      (physicalOperator (modes M) (modes_zero M) (modes_closed M) nu (-NativeWindowTraceAdjoint.advector seed M time)
        (negative_reality (NativeWindowTraceAdjoint.advector_reality seed M time))) v=_
  rw [NativeWindowOperatorGreen.operator_split (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time),
    NativeWindowOperatorGreen.adjoint_split (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time)]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply]
  module

theorem input_original_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : ∀ᵐ time : ℝ,0≤time →
    NativeWindowStageNineSource.lift (modes M) (input seed M time)=drive seed M time := by
  filter_upwards [NativeWindowStageNineSource.lift_gradient_ae seed M] with time generated nonnegative
  have viscous:=generated nonnegative
  have velocity:=NativeWindowStageNineSource.lift_load seed time nonnegative M
  rw [← velocity] at viscous
  have algebra:input seed M time=NativeUnheatedSourceWeightedTail.nonlinear seed time-
      NativeUnheatedSourceQuadraticApprox.value M seed time-(2*nu.coeff) •NativeWindowHistoryGradient.gradientState seed time := by
    unfold input NativeWindowHistoryGradient.gradientState
    rw [smul_smul,show (2*nu.coeff)*nu.coeff⁻¹=(2 : ℝ) by field_simp [nu.coeff_pos.ne']]
    module
  rw [algebra,map_sub,map_sub,map_smul,viscous,drive,NativeWindowStageNineSource.forcing,map_sub]
  rfl

theorem combined_derivative_ae (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (nonnegative : 0 ≤ start) :
    ∀ᵐ time : ℝ,time∈Ioo start finish →HasDerivAt (combined seed observation M F radius start finish ordered)
      (drive seed M time-dual seed M time (combined seed observation M F radius start finish ordered time)) time := by
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed,NativeWindowTraceAdjoint.source_action_ae seed M]
    with time actual source inside
  have first:HasDerivAt (value seed M) (NativeWindowStageNineSource.lift (modes M) (rate seed time)) time :=
    (NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt time actual
  have last:HasDerivAt (propagated seed observation M F radius start finish ordered)
      (-dual seed M time (propagated seed observation M F radius start finish ordered time)) time :=
    (NativeWindowTraceAdjoint.backward_derivative seed M start finish ordered _ time (Ioo_subset_Icc_self inside)).hasDerivAt
      (Icc_mem_nhds inside.1 inside.2)
  have derivative:=first.sub last
  rw [source (nonnegative.trans inside.1.le)] at derivative
  have same:=action_sum seed M time (value seed M time)
  convert! derivative using 1
  simp only [drive,combined,map_sub]
  rw [eq_sub_of_add_eq same]
  module

theorem combined_identity (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (time : ℝ)
    (actual : (mass seed M F radius observation).IsInvertible) :
    mass seed M F radius observation (value seed M time+
      lifted seed M F radius observation (response seed observation M F radius start finish ordered time))=
        combined seed observation M F radius start finish ordered time := by
  rw [map_add,show mass seed M F radius observation (lifted seed M F radius observation
    (response seed observation M F radius start finish ordered time))=response seed observation M F radius start finish ordered time from
      actual.self_apply_inverse _]
  simp only [response,NativeWindowTraceAdjoint.joint,NativeWindowTraceOperator.jointTest,LinearMap.sub_apply,LinearMap.id_apply,combined]
  change mass seed M F radius observation (value seed M time)+
    (value seed M time-mass seed M F radius observation (value seed M time)-_)=_
  abel

def cap (nu : Viscosity) : ℝ := 2*NativeNegativeOneMomentum.coefficient nu+2*Real.sqrt NativeMovingCriticalProductWeights.constant

theorem input_bound_ae (seed : GeneratedWholeRestartCurrent nu) : ∀ᵐ time : ℝ,0≤time →∀ M,
    ‖input seed M time‖≤cap nu*(1+NativeUnheatedSourceGradient.mass seed time) := by
  filter_upwards [NativeUnheatedSourceQuadraticApprox.value_bound_ae seed] with time projected nonnegative M
  have rateBound:=NativeUnheatedGlobalNegativeOne.rate_bound seed time
  have original:=NativeUnheatedSourceWeightedTail.nonlinear_bound seed time
  have finite:=projected nonnegative M
  have mass0:=NativeUnheatedSourceGradient.mass_nonnegative seed time
  have bound:‖input seed M time‖≤2*‖rate seed time‖+‖NativeUnheatedSourceWeightedTail.nonlinear seed time‖+
      ‖NativeUnheatedSourceQuadraticApprox.value M seed time‖ := by
    have first:=norm_sub_le ((2 : ℝ) • rate seed time) (NativeUnheatedSourceWeightedTail.nonlinear seed time)
    have last:=norm_sub_le ((2 : ℝ) • rate seed time-NativeUnheatedSourceWeightedTail.nonlinear seed time)
      (NativeUnheatedSourceQuadraticApprox.value M seed time)
    simp only [norm_smul,Real.norm_of_nonneg (by norm_num : 0≤(2 : ℝ))] at first
    exact last.trans (add_le_add_left first _)
  unfold cap
  nlinarith only [bound,rateBound,original,finite,mul_nonneg (Real.sqrt_nonneg NativeMovingCriticalProductWeights.constant) mass0,
    Real.sqrt_nonneg NativeMovingCriticalProductWeights.constant]

theorem input_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon) :
    Integrable (input seed M) (volume.restrict (Icc 0 horizon)) :=
  ((MeasureTheory.Integrable.smul (2 : ℝ) (NativeUnheatedGlobalNegativeOne.rate_integrable seed horizon nonnegative)).sub
    (NativeUnheatedSourceWeightedTail.nonlinear_integrable seed horizon nonnegative)).sub
      (NativeUnheatedSourceQuadraticApprox.value_integrable M seed horizon nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCoupled
