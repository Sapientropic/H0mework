import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Mixed.Readout
import H0mework.Versions.X.NavierStokes.SourcePairing.SpacetimeEquation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeMixedHeatPhysical
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowSpacetimeFourier NativeMixedHeatSource NativeMixedHeatReadout NativeWindowTailMoments
noncomputable section
variable {nu : Viscosity}

def domain (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) : Set Spacetime :=
  Ioo (NativeAbsoluteEventualControl.startTime seed-1) H ×ˢ univ

theorem domain_open (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) : IsOpen (domain seed H) :=
  isOpen_Ioo.prod isOpen_univ

theorem domain_subset (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) :
    domain seed H ⊆ NativeWindowTailPhysical.support seed := fun _ inside => ⟨inside.1.1,trivial⟩

theorem velocity_scalar_smooth (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (i : Coordinate) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag i)) (domain seed H) := by
  by_cases zero : lag=0
  · subst lag
    exact (NativeWindowTailPhysical.velocity_scalar_smooth seed i).mono (domain_subset seed H)
  · exact (NativeWindowSpacetimeVelocity.scalar_smooth seed lag (lt_of_le_of_ne zero_le (Ne.symm zero)) i).contDiffOn

theorem stress_scalar_smooth (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (i : Coordinate × Coordinate) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (scalarField (NativeWindowSpacetimeStress.coefficient seed lag i)) (domain seed H) := by
  by_cases zero : lag=0
  · subst lag
    exact (NativeWindowTailPhysical.stress_scalar_smooth seed i).mono (domain_subset seed H)
  · exact (NativeWindowSpacetimeStress.scalar_smooth seed lag (lt_of_le_of_ne zero_le (Ne.symm zero)) i).contDiffOn

theorem velocity_product_jets (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (i j : Coordinate) (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (fun x : Spacetime =>
      scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag i) x*
        scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag j) x))
      (iteratedFDeriv ℝ n (fun x => scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 i) x*
        scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 j) x)) (𝓝 0) (domain seed H) := by
  have bounded (coordinate : Coordinate) : ∀ time ∈ Icc (NativeAbsoluteEventualControl.startTime seed-1) H,
      ∀ rank order wave, NativeFullOrderAction.frequencySize wave^order*
        ‖NativeWindowSpacetimeVelocity.coefficient seed 0 coordinate rank wave time‖ ≤
          velocityBudget seed H rank (order+4)*NativeFullOrderSynthesis.decay wave := by
    intro time inside rank order wave
    simpa only [NativeWindowSpacetimeVelocity.coefficient,NativeWindowHeatEvolution.velocityJet,
      NativeZeroHeatWindow.jet_zero] using window_velocity_decay seed H time inside rank order wave coordinate
  have result := product_heat_uniform nu (NativeWindowSpacetimeVelocity.coefficient seed 0 i)
    (NativeWindowSpacetimeVelocity.coefficient seed 0 j)
    (NativeWindowSpacetimeVelocity.coefficient_hasDerivAt seed 0 i)
    (NativeWindowSpacetimeVelocity.coefficient_hasDerivAt seed 0 j)
    (NativeAbsoluteEventualControl.startTime seed-1) H (fun rank order => velocityBudget seed H rank (order+4))
    (fun _ _ => mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (Real.sqrt_nonneg _))
    (bounded i) (bounded j) n
  have series (lag : ℝ≥0) (coordinate : Coordinate) (x : Spacetime) :=
    congrFun (velocity_series seed lag coordinate) x
  simpa only [← series,domain] using! result

def residualScalar (seed : GeneratedWholeRestartCurrent nu) (entry : Coordinate × Coordinate)
    (lag : ℝ≥0) (x : Spacetime) : ℂ :=
  scalarField (NativeWindowSpacetimeStress.coefficient seed lag entry) x+
    scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag entry.2) x*
      scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag entry.1) x

theorem residualScalar_smooth (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (entry : Coordinate × Coordinate) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (residualScalar seed entry lag) (domain seed H) :=
  (stress_scalar_smooth seed H entry lag).add
    ((velocity_scalar_smooth seed H entry.2 lag).mul (velocity_scalar_smooth seed H entry.1 lag))

theorem residualScalar_jets (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (entry : Coordinate × Coordinate) (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (residualScalar seed entry lag))
      (iteratedFDeriv ℝ n (residualScalar seed entry 0)) (𝓝 0) (domain seed H) :=
  add_jets_uniform _ _ _ _ (domain_open seed H) (stress_scalar_smooth seed H entry)
    (fun lag => (velocity_scalar_smooth seed H entry.2 lag).mul (velocity_scalar_smooth seed H entry.1 lag))
    (stress_scalar_smooth seed H entry 0)
    ((velocity_scalar_smooth seed H entry.2 0).mul (velocity_scalar_smooth seed H entry.1 0)) n
    (stress_scalar_jets seed H entry n) (velocity_product_jets seed H entry.2 entry.1 n)

theorem velocity_coordinate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (x : Spacetime)
    (inside : x∈NativeWindowTailPhysical.support seed) (i : Coordinate) :
    NativeWindowSpacetimeVelocity.jointField seed lag x i =
      (scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag i) x).re := by
  by_cases zero : lag=0
  · subst lag
    exact NativeWindowTailPhysical.velocity_coordinate seed x inside i
  · exact NativeWindowSpacetimeVelocity.jointField_coordinate seed lag
      (lt_of_le_of_ne zero_le (Ne.symm zero)) i x

theorem residual_coordinate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (x : Spacetime)
    (inside : x∈NativeWindowTailPhysical.support seed) (entry : Coordinate × Coordinate) :
    NativeWindowSpacetimeResidual.jointField seed lag x entry = (residualScalar seed entry lag x).re := by
  change (NativeWindowSpacetimeResidual.jointTensor seed lag x entry).re=_
  apply congrArg Complex.re
  by_cases zero : lag=0
  · subst lag
    exact NativeWindowTailPhysical.residual_coordinate seed x inside entry
  · exact NativeWindowSpacetimeResidual.jointTensor_coordinate seed lag
      (lt_of_le_of_ne zero_le (Ne.symm zero)) x entry

theorem velocity_jets (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (NativeWindowSpacetimeVelocity.jointField seed lag))
      (iteratedFDeriv ℝ n (NativeWindowSpacetimeVelocity.jointField seed 0)) (𝓝 0) (domain seed H) := by
  have result := assembly_jets_uniform (fun i lag => scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag i))
    (fun i => scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 i)) (domain_open seed H)
    (velocity_scalar_smooth seed H) (fun i => velocity_scalar_smooth seed H i 0) n
    (fun i => velocity_scalar_jets seed H i n)
  have same (lag : ℝ≥0) : EqOn (fun x : Spacetime =>
      (WithLp.toLp 2 fun i => (scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag i) x).re : PhysicalSpace))
      (NativeWindowSpacetimeVelocity.jointField seed lag) (domain seed H) := by
    intro x inside
    apply PiLp.ext
    intro i
    exact (velocity_coordinate seed lag x (domain_subset seed H inside) i).symm
  exact (result.congr (Eventually.of_forall fun lag => jets_eqOn_of_eqOn (domain_open seed H) (same lag) n)).congr_right
    (jets_eqOn_of_eqOn (domain_open seed H) (same 0) n)

theorem stress_jets (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (NativeWindowSpacetimeStress.jointField seed lag))
      (iteratedFDeriv ℝ n (NativeWindowSpacetimeStress.jointField seed 0)) (𝓝 0) (domain seed H) :=
  assembly_jets_uniform (fun i lag => scalarField (NativeWindowSpacetimeStress.coefficient seed lag i))
    (fun i => scalarField (NativeWindowSpacetimeStress.coefficient seed 0 i)) (domain_open seed H)
    (stress_scalar_smooth seed H) (fun i => stress_scalar_smooth seed H i 0) n
    (fun i => stress_scalar_jets seed H i n)

theorem residual_jets (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (NativeWindowSpacetimeResidual.jointField seed lag))
      (iteratedFDeriv ℝ n (NativeWindowSpacetimeResidual.jointField seed 0)) (𝓝 0) (domain seed H) := by
  have result := assembly_jets_uniform (residualScalar seed) (fun i => residualScalar seed i 0) (domain_open seed H)
    (residualScalar_smooth seed H) (fun i => residualScalar_smooth seed H i 0) n
    (fun i => residualScalar_jets seed H i n)
  have same (lag : ℝ≥0) : EqOn (fun x : Spacetime =>
      (WithLp.toLp 2 fun i => (residualScalar seed i lag x).re : EuclideanSpace ℝ (Coordinate × Coordinate)))
      (NativeWindowSpacetimeResidual.jointField seed lag) (domain seed H) := by
    intro x inside
    apply PiLp.ext
    intro i
    exact (residual_coordinate seed lag x (domain_subset seed H inside) i).symm
  exact (result.congr (Eventually.of_forall fun lag => jets_eqOn_of_eqOn (domain_open seed H) (same lag) n)).congr_right
    (jets_eqOn_of_eqOn (domain_open seed H) (same 0) n)

end
end SaturationMonoid.NavierStokes.NativeMixedHeatPhysical
