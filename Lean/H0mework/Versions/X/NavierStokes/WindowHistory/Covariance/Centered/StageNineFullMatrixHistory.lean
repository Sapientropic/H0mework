import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineFullMatrixGraph
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.History

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed
open NativePhysicalPairing (includeCLM include_inner include_norm restrict_include)
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
noncomputable section
variable {nu : Viscosity}

theorem finite_graph_lift (nu : Viscosity) (M : ℕ)
    (op : Module.End ℝ (NativeFiniteActionResolvent.physicalSpace (modes M)))
    (C : ℝ) (C0 : 0≤C)
    (source : ∀w : NativeFiniteActionResolvent.physicalSpace (modes M),
      ‖NativeFiniteActionResolvent.coefficients (modes M) (op w)‖^2≤
        C*(‖NativeFiniteActionResolvent.coefficients (modes M)
          (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M)
            (modes_closed M) nu w)‖^2+
          ‖NativeFiniteActionResolvent.coefficients (modes M) w‖^2) ∧
      -2*nu.coeff*NativeFiniteActionResolvent.pairing (modes M) (op w)
        (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M)
          (modes_closed M) nu w)≤
        -nu.coeff^2*‖NativeFiniteActionResolvent.coefficients (modes M)
          (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M)
            (modes_closed M) nu w)‖^2+
          C*‖NativeFiniteActionResolvent.coefficients (modes M) w‖^2)
    (v : NativeWindowTraceWholeHistory.H) :
    let T:=(NativeWindowHistoryOseen.lift M
      (LinearMap.toContinuousLinearMap op)).compLpL 2 NativeForwardWindowPairingReadout.averageMeasure
    ‖T v‖^2≤C*(‖laplacianAction nu M v‖^2+‖v‖^2) ∧
      -2*nu.coeff*inner ℝ (T v) (laplacianAction nu M v)≤
        -nu.coeff^2*‖laplacianAction nu M v‖^2+C*‖v‖^2 := by
  let T:=NativeWindowHistoryOseen.lift M (LinearMap.toContinuousLinearMap op)
  let L:=laplacianFiber nu M
  have point (x : wholePhysical) : ‖T x‖^2≤C*(‖L x‖^2+‖x‖^2) ∧
      -2*nu.coeff*inner ℝ (T x) (L x)≤-nu.coeff^2*‖L x‖^2+C*‖x‖^2 := by
    let w:=restrictCLM (modes M) (modes_zero M) (modes_closed M) x
    have original:=source w
    have mass:=pow_le_pow_left₀ (norm_nonneg (coefficients (modes M) w))
      (NativeWindowMetricGraphHistory.restricted_norm M x) 2
    have more:=mul_le_mul_of_nonneg_left mass C0
    have normRead : ‖T x‖=‖coefficients (modes M) (op w)‖ := by
      change ‖includeCLM (modes M) (modes_closed M) (op w)‖=_
      rw [include_norm (modes M) (modes_zero M)]
    have heatRead : inner ℝ (T x) (L x)=
        pairing (modes M) (op w)
          (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M)
            (modes_closed M) nu w) := by
      change inner ℝ (includeCLM (modes M) (modes_closed M) (op w)) (L x)=_
      rw [include_inner (modes M) (modes_zero M)]
      change pairing (modes M) _
        (restrictCLM (modes M) (modes_zero M) (modes_closed M)
          (includeCLM (modes M) (modes_closed M)
            (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M)
              (modes_closed M) nu w)))=_
      rw [restrict_include]
    constructor
    · rw [normRead,NativeWindowMetricGraphHistory.laplacian_norm]
      nlinarith only [original.1,more]
    · rw [heatRead,NativeWindowMetricGraphHistory.laplacian_norm]
      linarith only [original.2,more]
  exact ⟨NativeWindowMetricGraphHistory.lift_upper C T L (fun x => (point x).1) v,
    NativeWindowMetricGraphHistory.lift_heat nu.coeff C T L (fun x => (point x).2) v⟩

theorem metric_graph_of_test (seed : GeneratedWholeRestartCurrent nu)
    (S : Set ℝ) (low : ℕ) (C : ℝ) (C0 : 0≤C)
    (source : ∀radius≥low,∀outerRadius
      (M : Finset IntegerWavevector),
      ∀zero : 0∉M,
      ∀closed : ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.FiniteModeNegClosed M,
      ∀time∈S,∀v : NativeFiniteActionResolvent.physicalSpace M,
        ‖NativeFiniteActionResolvent.coefficients M
          (NativeWindowAugmentedFixedOperator.test seed time M M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v)‖^2≤
          C*(‖NativeFiniteActionResolvent.coefficients M
            (NativeWindowOperatorGreen.laplacian M zero closed nu v)‖^2+
            ‖NativeFiniteActionResolvent.coefficients M v‖^2) ∧
        -2*nu.coeff*NativeFiniteActionResolvent.pairing M
          (NativeWindowAugmentedFixedOperator.test seed time M M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v)
          (NativeWindowOperatorGreen.laplacian M zero closed nu v)≤
          -nu.coeff^2*‖NativeFiniteActionResolvent.coefficients M
            (NativeWindowOperatorGreen.laplacian M zero closed nu v)‖^2+
            C*‖NativeFiniteActionResolvent.coefficients M v‖^2) :
    ∀radius≥low,∀outerRadius M (time : ℝ),time∈S →
        ∀v : NativeWindowTraceWholeHistory.H,
          ‖fullMetricAction seed time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v‖^2≤
            C*(‖laplacianAction nu M v‖^2+‖v‖^2) ∧
          -2*nu.coeff*inner ℝ
            (fullMetricAction seed time M
              (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
                outerRadius) radius v)
            (laplacianAction nu M v)≤
            -nu.coeff^2*‖laplacianAction nu M v‖^2+C*‖v‖^2 := by
  intro radius above outerRadius M time inside v
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let op:=NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
  exact finite_graph_lift nu M op C C0
    (source radius above outerRadius (modes M) (modes_zero M)
      (modes_closed M) time inside) v

theorem source_full_metric_graph (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius M (time : ℝ),time∈Icc 0 horizon →
        ∀v : NativeWindowTraceWholeHistory.H,
          ‖fullMetricAction seed time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v‖^2≤
            C*(‖laplacianAction nu M v‖^2+‖v‖^2) ∧
          -2*nu.coeff*inner ℝ
            (fullMetricAction seed time M
              (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
                outerRadius) radius v)
            (laplacianAction nu M v)≤
            -nu.coeff^2*‖laplacianAction nu M v‖^2+C*‖v‖^2 := by
  obtain ⟨low,C,C0,source⟩ :=
    NativeStageNineFullMatrixPotential.source_full_test_graph seed horizon nonnegative
  exact ⟨low,C,C0,metric_graph_of_test seed (Icc 0 horizon) low C C0 source⟩
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
