import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWindowRead

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow (integerWaveFrequencyCube)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeFiniteActionResolvent (pairing coefficients)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeCommonAdvectorAction (curlPair)
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

theorem source_stage_nine_window_graph (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∀radius≥low,∀outerRadius M order : ℕ,
      ∀time∈Icc 0 horizon,
      NativeWindowHistoryAllOrderWord.energy seed M order time+
        (nu.coeff/2)*(∑index : FixedMatterSpatialWordIndex order,
          NativeWindowTraceWholeHistory.gradient M
            (NativeWindowHistoryMeanProjection.embed
              (NativeWindowHistoryAllOrderWord.value seed M index.toList time)))≤
        NativeWindowHierarchyHistory.history seed M order
          (integerWaveFrequencyCube outerRadius) radius 0 time := by
  obtain ⟨low,C,C0,control⟩:=NativeWindowStageNineWords.source_hierarchy_control
    seed horizon nonnegative
  refine ⟨low,fun radius above outerRadius M order time inside => ?_⟩
  let F:=integerWaveFrequencyCube outerRadius
  let mass (shift : ℝ) := ∑index : FixedMatterSpatialWordIndex order,
    pairing (modes M)
      (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift))
      (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift))
  let grad (shift : ℝ) := ∑index : FixedMatterSpatialWordIndex order,
    curlPair (modes M)
      (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift)).1
      (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift)).1
  let source (shift : ℝ) := NativeWindowHierarchyHistory.sampleEnergy
    seed time M order F radius (time-shift)
  have massI : Integrable mass averageMeasure :=
    integrable_finsetSum Finset.univ (fun index _ =>
      sample_mass_integrable seed M index.toList time)
  have gradI : Integrable grad averageMeasure :=
    integrable_finsetSum Finset.univ (fun index _ =>
      sample_gradient_integrable seed M index.toList time)
  have sourceI : Integrable source averageMeasure :=
    sample_energy_integrable seed M order F radius time
  have point : ∀ᵐ shift ∂averageMeasure,
      mass shift+(nu.coeff/2)*grad shift ≤ source shift :=
    Eventually.of_forall fun shift => by
      have generated := (control radius above outerRadius order
        (modes M) (modes_zero M) (modes_closed M) time inside
        (NativeWindowStageNineEnergy.values seed M order (time-shift))).1
      exact generated
  have averaged := integral_mono_ae
    (massI.add (gradI.const_mul (nu.coeff/2))) sourceI point
  have averaged' : (∫shift,mass shift ∂averageMeasure)+
      (nu.coeff/2)*(∫shift,grad shift ∂averageMeasure)≤
        NativeWindowHierarchyHistory.history seed M order F radius 0 time := by
    rw [hierarchy_history_lag seed M order F radius time]
    simp only [Pi.add_apply] at averaged
    rw [integral_add massI (gradI.const_mul (nu.coeff/2)),
      integral_const_mul] at averaged
    exact averaged
  have meanMass := all_word_window_energy_le seed M order time
  have meanGrad := all_word_window_gradient_le seed M order time
  have scaledGrad := mul_le_mul_of_nonneg_left meanGrad
    (by positivity [nu.coeff_pos] : 0≤nu.coeff/2)
  dsimp only [mass,grad,F] at averaged' meanMass scaledGrad
  linarith only [meanMass,scaledGrad,averaged']


end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
