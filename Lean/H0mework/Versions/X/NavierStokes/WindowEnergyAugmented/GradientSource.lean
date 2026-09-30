import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.Gradient
import H0mework.Versions.X.NavierStokes.WindowEnergyJoint.EnergyGate

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAugmentedGradientSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeFiniteActionResolvent NativeWholeH1Mixed NativeWholeResolvent
open NativeWindowStressOseenSource (load)
open NativeWindowAugmentedGradient (derivative matrixGradient)
open NativeWindowAugmentedSourceForm (matrixRead matrixField)
open NativeWindowStressHeatSource (jetRead product_integrable productAverage)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def palinRead (nu : Viscosity) (L : ℕ) : wholePhysical →L[ℝ] EuclideanSpace ℂ (modes L × Coordinate) :=
  (LinearMap.toContinuousLinearMap ((coefficients (modes L)).comp
    (NativeWindowOperatorGreen.laplacian (modes L) (modes_zero L) (modes_closed L) nu))).comp (restrict L)

theorem palinRead_original (seed : GeneratedWholeRestartCurrent nu) (L : ℕ) (sample : ℝ) :
    ‖palinRead nu L (NativeUnheatedSourceQuadraticApprox.physicalSource seed sample)‖^2=
      pairing (modes L) (NativeWindowOperatorGreen.laplacian (modes L) (modes_zero L) (modes_closed L) nu (load L seed sample))
        (NativeWindowOperatorGreen.laplacian (modes L) (modes_zero L) (modes_closed L) nu (load L seed sample)) := by
  change ‖coefficients (modes L) _‖^2=inner ℝ (coefficients (modes L) _) (coefficients (modes L) _)
  rw [real_inner_self_eq_norm_sq]
  rfl

theorem palinRead_spectrum (seed : GeneratedWholeRestartCurrent nu) (L : ℕ) (sample : ℝ) (nonnegative : 0 ≤ sample) :
    ‖palinRead nu L (NativeUnheatedSourceQuadraticApprox.physicalSource seed sample)‖^2=
      ∑ k ∈ modes L,integerWaveViscousMultiplier k^2*∑ i : Coordinate,‖NativeUnheatedTriadRows.velocity seed sample k i‖^2 := by
  rw [palinRead_original,pairing_eq]
  apply Finset.sum_congr rfl
  intro k inside
  rw [NativeWindowOperatorGreen.laplacian_row,complexCoordinateRealInner_self]
  change complexCoordinateVectorNormSq ((integerWaveViscousMultiplier k:ℂ) • (load L seed sample).1 k)=_
  rw [complexCoordinateVectorNormSq_smul,Complex.normSq_ofReal,NativeWindowStressOseenSource.load,
    restrict_row,if_pos inside,NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos nonnegative]
  simp only [complexCoordinateVectorNormSq,Complex.normSq_eq_norm_sq,NativeUnheatedTriadRows.velocity_original,pow_two]
  rfl

theorem source_memLp (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    MemLp (fun shift => NativeUnheatedSourceQuadraticApprox.physicalSource seed (time-shift)) 2 averageMeasure := by
  have moved := (NativeUnheatedSourceQuadraticApprox.physicalSource_measurable seed).comp_measurePreserving
    (Measure.measurePreserving_sub_left (volume : Measure ℝ) time)
  have measured := moved.mono_ac (withDensity_absolutelyContinuous volume (fun shift =>
    (NativeForwardWindowPairingReadout.density shift:ℝ≥0∞)))
  refine MemLp.of_bound measured (NativeUnifiedCompleteSource.budget seed) (Eventually.of_forall fun shift => ?_)
  by_cases nonnegative : 0≤time-shift
  · rw [NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos nonnegative]
    exact NativeUnheatedSourceWeightedTail.velocity_bound seed (time-shift)
  · rw [NativeUnheatedSourceQuadraticApprox.physicalSource,dif_neg nonnegative,norm_zero]
    exact (norm_nonneg _).trans (NativeUnifiedCompleteSource.source_bound seed 0)

def palinstrophyWindow (seed : GeneratedWholeRestartCurrent nu) (L : ℕ) (time : ℝ) : ℝ :=
  ∫ shift,‖palinRead nu L (NativeUnheatedSourceQuadraticApprox.physicalSource seed (time-shift))‖^2 ∂averageMeasure

theorem palinstrophy_integrable (seed : GeneratedWholeRestartCurrent nu) (L : ℕ) (time : ℝ) :
    Integrable (fun shift => ‖palinRead nu L (NativeUnheatedSourceQuadraticApprox.physicalSource seed (time-shift))‖^2) averageMeasure := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    ((source_memLp seed time).continuousLinearMap_comp (palinRead nu L)).integrable_norm_rpow (by norm_num) (by norm_num)

theorem palinstrophy_nonnegative (seed : GeneratedWholeRestartCurrent nu) (L : ℕ) (time : ℝ) :
    0≤palinstrophyWindow seed L time := integral_nonneg (fun _ => sq_nonneg _)

theorem gradient_load (seed : GeneratedWholeRestartCurrent nu) (L : ℕ) (sample : ℝ) (nonnegative : 0 ≤ sample)
    (F : Finset IntegerWavevector) (cover : ∀ k∈F,k≠0 →k∈modes L) (j input : Coordinate) :
    NativeWindowStressOseenTest.evaluate (modes L) F input
      (derivative (modes L) (modes_zero L) (modes_closed L) j (load L seed sample))=
        jetRead F j 1 input (NativeUnifiedCompleteSource.source seed sample) := by
  have read (k : IntegerWavevector) (inside : k∈F) : (load L seed sample).1 k=
      NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed sample).fst k := by
    by_cases zero : k=0
    · subst k
      rw [physical_supported _ 0 (modes_zero L),NativeEndpointVelocityCarrier.wholeVelocity_zero]
    · change (restrict L (NativeUnheatedSourceQuadraticApprox.physicalSource seed sample)).1 k=_
      rw [restrict_row,if_pos (cover k inside zero),NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos nonnegative]
      rfl
  rw [NativeWindowAugmentedGradient.evaluate_derivative]
  ext point
  rw [NativeWindowStressHeatSource.jetRead_apply]
  simp only [NativeWindowPressureStrainPhysical.gradient,NativeWindowHighPressurePhysical.realSynthesis,ContinuousMap.sum_apply,
    NativeWindowStressHeatSource.polynomial,ContinuousMap.smul_apply,pow_one,smul_eq_mul,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k inside
  rw [read k inside]
  rfl

def matrixSample (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (radius : ℕ) (sample : ℝ) : ℝ :=
  ∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,matrixRead seed observation F radius output input
    (jetRead F j 1 output (NativeUnifiedCompleteSource.source seed sample)*jetRead F j 1 input (NativeUnifiedCompleteSource.source seed sample))

theorem matrixSample_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (radius L : ℕ) (cover : ∀ k∈F,k≠0 →k∈modes L) (sample : ℝ) (nonnegative : 0 ≤ sample) :
    matrixGradient seed observation (modes L) F (modes_zero L) (modes_closed L) radius (load L seed sample)=
      matrixSample seed observation F radius sample := by
  simp only [matrixGradient,gradient_load seed L sample nonnegative F cover,matrixSample,
    matrixRead,ContinuousLinearMap.comp_apply,innerSL_apply_apply]

theorem matrixSample_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (radius : ℕ) : Integrable (fun shift => matrixSample seed time F radius (time-shift)) averageMeasure :=
  integrable_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun output _ =>
    integrable_finsetSum Finset.univ (fun input _ => (matrixRead seed time F radius output input).integrable_comp
      (product_integrable seed time (jetRead F j 1 output) (jetRead F j 1 input)))))

theorem matrixSample_average (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) :
    (∫ shift,matrixSample seed time F radius (time-shift) ∂averageMeasure)=
      (∫ point : Torus,NativeWindowStressHeatSource.interaction seed time F point)+NativeWindowJointHeat.crossWork seed F radius time := by
  have paid (j output input : Coordinate) := (matrixRead seed time F radius output input).integrable_comp
    (product_integrable seed time (jetRead F j 1 output) (jetRead F j 1 input))
  unfold matrixSample
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ
    (fun output _ => integrable_finsetSum Finset.univ (fun input _ => paid j output input)))]
  simp_rw [integral_finsetSum Finset.univ (fun output _ => integrable_finsetSum Finset.univ (fun input _ => paid _ output input)),
    integral_finsetSum Finset.univ (fun input _ => paid _ _ input)]
  have row (j output input : Coordinate) : (∫ shift,matrixRead seed time F radius output input
      (jetRead F j 1 output (NativeUnifiedCompleteSource.source seed (time-shift))*
        jetRead F j 1 input (NativeUnifiedCompleteSource.source seed (time-shift))) ∂averageMeasure)=
      matrixRead seed time F radius output input (productAverage seed time (jetRead F j 1 output) (jetRead F j 1 input)) :=
    (matrixRead seed time F radius output input).integral_comp_comm (product_integrable seed time _ _)
  simp only [row]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (f := fun j input => matrixRead seed time F radius _ input (productAverage seed time (jetRead F j 1 _) (jetRead F j 1 input)))]
  simp only [← map_sum]
  change (∑ output : Coordinate,∑ input : Coordinate,matrixRead seed time F radius output input
    (NativeWindowStressHeatSource.diffusion seed time F output input))=_
  simp only [matrixRead,ContinuousLinearMap.comp_apply,innerSL_apply_apply,NativeWindowAugmentedSourceForm.matrixField,
    inner_add_left,Finset.sum_add_distrib,NativeWindowStressHeatSource.interaction_inner,NativeWindowJointHeat.crossWork]

theorem heat_graph_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ L : ℕ,∀ F : Finset IntegerWavevector,FiniteModeNegClosed F →
      (∀ k∈F,k≠0 →k∈modes L) →∀ time∈Icc 0 horizon,
        NativeWindowJointNormalForm.heatWork seed F radius time-2*nu.coeff^2*palinstrophyWindow seed L time≤
          -nu.coeff*NativeWindowJointHeat.dirichlet seed F radius time-nu.coeff^2*palinstrophyWindow seed L time := by
  obtain ⟨low,paid⟩ := NativeWindowAugmentedGradient.source_diffusion_coercivity seed horizon nonnegative
  refine ⟨low,fun radius above L F closed cover time inside => ?_⟩
  have point : ∀ᵐ shift ∂averageMeasure,(-2*nu.coeff)*matrixSample seed time F radius (time-shift)≤
      nu.coeff^2*‖palinRead nu L (NativeUnheatedSourceQuadraticApprox.physicalSource seed (time-shift))‖^2 := by
    filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
    have source := paid radius above (modes L) F (modes_zero L) (modes_closed L) closed time inside (load L seed (time-shift))
    rw [matrixSample_original seed time F radius L cover (time-shift) (by linarith [inside.1]),
      ← palinRead_original seed L (time-shift)] at source
    linarith only [source]
  have integrated := integral_mono_ae ((matrixSample_integrable seed time F radius).const_mul (-2*nu.coeff))
    ((palinstrophy_integrable seed L time).const_mul (nu.coeff^2)) point
  rw [integral_const_mul,integral_const_mul,matrixSample_average] at integrated
  change (-2*nu.coeff)*((∫ point : Torus,NativeWindowStressHeatSource.interaction seed time F point)+
    NativeWindowJointHeat.crossWork seed F radius time)≤nu.coeff^2*palinstrophyWindow seed L time at integrated
  rw [NativeWindowJointHeat.heatWork_identity seed F radius time closed]
  nlinarith only [integrated]

theorem eventual_heat_graph_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ F : Finset IntegerWavevector,FiniteModeNegClosed F →∀ᶠ L : ℕ in atTop,∀ time∈Icc 0 horizon,
      NativeWindowJointNormalForm.heatWork seed F radius time-2*nu.coeff^2*palinstrophyWindow seed L time≤
        -nu.coeff*NativeWindowJointHeat.dirichlet seed F radius time-nu.coeff^2*palinstrophyWindow seed L time := by
  obtain ⟨low,paid⟩ := heat_graph_coercivity seed horizon nonnegative
  refine ⟨low,fun radius above F closed => ?_⟩
  filter_upwards [NativeWindowStressOseenSource.cover_eventually F] with L cover time inside
  exact paid radius above L F closed cover time inside

theorem eventual_generator_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ F : Finset IntegerWavevector,FiniteModeNegClosed F →∀ᶠ L : ℕ in atTop,∀ time∈Icc 0 horizon,
      NativeWindowJointNormalForm.heatWork seed F radius time+NativeWindowJointNormalForm.retainedWork seed F radius time-
        2*nu.coeff^2*palinstrophyWindow seed L time≤
          -nu.coeff*NativeWindowJointHeat.dirichlet seed F radius time-nu.coeff^2*palinstrophyWindow seed L time+
            NativeWindowJointEnergyGate.lowAdvWork seed F radius time+NativeWindowJointEnergyGate.convectionWork seed F radius time+
              NativeWindowJointEnergyGate.lowPressureWork seed F radius time-
                ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (NativeWindowPressureStrainHistory.relative seed F radius time output input)
                  (NativeWindowStressHeatSource.physical (NativeWindowPressureStrainHistory.window seed radius time F output input)) := by
  obtain ⟨low,paid⟩ := eventual_heat_graph_coercivity seed horizon nonnegative
  refine ⟨low,fun radius above F closed => ?_⟩
  filter_upwards [paid radius above F closed] with L bounded time inside
  have heat := bounded time inside
  rw [NativeWindowJointEnergyGate.retainedWork_split seed F closed radius time]
  linarith only [heat]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem palinstrophyWindow_next (seed : GeneratedWholeRestartCurrent nu) (L : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    palinstrophyWindow seed L (step.2.clockAdvance+time)=palinstrophyWindow step.1 L time := by
  unfold palinstrophyWindow
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
  have sample0 : 0≤time-shift := by linarith
  have later : 0 ≤ step.2.clockAdvance+(time-shift) := add_nonneg step.2.clockAdvance_pos.le sample0
  have same : NativeUnheatedSourceQuadraticApprox.physicalSource seed (step.2.clockAdvance+(time-shift))=
      NativeUnheatedSourceQuadraticApprox.physicalSource step.1 (time-shift) := by
    rw [NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos later,
      NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos sample0]
    apply Subtype.ext
    change (NativeUnifiedCompleteSource.source seed (step.2.clockAdvance+(time-shift))).fst=
      (NativeUnifiedCompleteSource.source step.1 (time-shift)).fst
    rw [NativeUnifiedCompleteSource.source_generated_next seed step generated (time-shift) sample0]
  rw [add_sub_assoc,same]

end
end SaturationMonoid.NavierStokes.NativeWindowAugmentedGradientSource
