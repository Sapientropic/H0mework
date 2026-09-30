import H0mework.NavierStokes.WindowEnergyTraceTerminal.Graph
import H0mework.NavierStokes.WindowEnergyTraceTerminal.Window

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTerminalGraphHeat
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativeWindowStressHeatEnergy
open NativeWindowStressHeatSource (physical)
open NativeWindowConvectionCutoffAction (frequencies)
open NativeWindowConvectionCutoffTrace (relative correction coefficients dirichlet heatWork crossWork)
open NativeWindowTraceGradient (traceStress traceDiffusion traceInteraction)
open NativeWindowTraceTerminalGraph (heatRead remainderEnergy source_square)
open NativeWindowTraceEndpointWindow (terminalEnergy)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem mixed_green (A B : Finset IntegerWavevector) (a b : IntegerWavevector → ℂ) (j : Coordinate) :
    inner ℝ (field (finiteSequence A a)) (field (finiteJet B b j 2))=
      -inner ℝ (field (finiteJet A a j 1)) (field (finiteJet B b j 1)) := by
  have source : inner ℂ (field (finiteJet A a j 0)) (field (finiteJet B b j 2))=
      -inner ℂ (field (finiteJet A a j 1)) (field (finiteJet B b j 1)) := by
    simp only [field,LinearIsometryEquiv.inner_map_map]
    exact spectral_skew j _ _ _ _ (finiteJet_successor A a j 0) (finiteJet_successor B b j 1)
  have realPart:=congrArg Complex.re source
  simpa only [← NativeWindowTraceTerminalCubic.real_pairing,Complex.neg_re,finiteJet,pow_zero,one_mul] using! realPart

def stressJet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j : Coordinate) (order : ℕ) : ScalarField :=
  ∑ i : Coordinate,field (finiteJet (F+F) (fun k => NativeWindowFiniteGramFourier.coefficients seed time F k i i) j order)

def relativeJet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (j : Coordinate) (order : ℕ) : ScalarField :=
  -field (finiteJet (frequencies F) (coefficients seed F radius time) j order)

def correctionJet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (j : Coordinate) (order : ℕ) : ScalarField :=
  -relativeJet seed F radius time j order-stressJet seed F time j order

theorem stressJet_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (closed : ∀ k,k∈F →waveNeg k∈F) (j : Coordinate) : stressJet seed F time j 0=physical (traceStress seed time F) := by
  simp only [stressJet,finiteJet,pow_zero,one_mul,traceStress,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact NativeWindowFiniteGramFourier.stress_field seed time F closed i i

theorem relativeJet_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (j : Coordinate) : relativeJet seed F radius time j 0=relative seed F radius time := by
  simp only [relativeJet,finiteJet,pow_zero,one_mul]
  exact (NativeWindowConvectionCutoffTrace.relative_field seed F radius time closed).symm

theorem correctionJet_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (j : Coordinate) : correctionJet seed F radius time j 0=correction seed F radius time := by
  rw [correctionJet,relativeJet_zero seed F radius time closed,stressJet_zero seed F time closed,
    NativeWindowTraceTerminalOperator.trace_split]
  abel

theorem relative_gradient (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (j : Coordinate) :
    HasDerivAt (fun h => NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement j h)
      (relative seed F radius time)) (relativeJet seed F radius time j 1) 0 := by
  have source:=(finiteJet_hasDerivAt (frequencies F) (coefficients seed F radius time) j 0).neg
  rw [← relativeJet_zero seed F radius time closed j]
  simpa only [relativeJet,NativePhysicalTranslation.translate,map_neg,Pi.neg_apply] using! source

theorem correction_gradient (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (j : Coordinate) :
    HasDerivAt (fun h => NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement j h)
      (correction seed F radius time)) (correctionJet seed F radius time j 1) 0 := by
  have stress:=HasDerivAt.sum (u := Finset.univ) (fun i _ => finiteJet_hasDerivAt (F+F)
    (fun k => NativeWindowFiniteGramFourier.coefficients seed time F k i i) j 0)
  have source:=((relative_gradient seed F radius time closed j).neg).sub stress
  rw [← correctionJet_zero seed F radius time closed j]
  simpa only [correctionJet,relativeJet_zero seed F radius time closed,stressJet,
    NativePhysicalTranslation.translate,map_sub,map_neg,map_sum,Pi.neg_apply] using! source

def gradientCross (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ j : Coordinate,inner ℝ (relativeJet seed F radius time j 1) (correctionJet seed F radius time j 1)

theorem laplacian_pairing (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) :
    inner ℝ (relative seed F radius time) (∑ i : Coordinate,physical (NativeWindowStressHeatSource.laplacian seed time F i i))=
      dirichlet seed F radius time+gradientCross seed F radius time := by
  rw [NativeWindowConvectionCutoffTrace.relative_field seed F radius time closed]
  simp only [NativeWindowStressHeatSource.laplacian_field seed time F closed,inner_sum,inner_neg_left,mixed_green,neg_neg]
  rw [Finset.sum_comm]
  simp only [dirichlet,gradientCross,correctionJet,relativeJet,neg_neg,inner_sub_right,inner_neg_left,
    real_inner_self_eq_norm_sq,stressJet,inner_sum,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  ring

theorem raw_heat_pairing (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) :
    heatRead seed time F radius (∑ i : Coordinate,NativeWindowStressHeatSource.heat seed time F i i)=
      -nu.coeff*dirichlet seed F radius time-2*nu.coeff*(∫ point : Torus,traceInteraction seed time F point)-
        2*nu.coeff*crossWork seed F radius time-nu.coeff*gradientCross seed F radius time := by
  change inner ℝ (relative seed F radius time) (physical (∑ i : Coordinate,NativeWindowStressHeatSource.heat seed time F i i))=_
  simp only [NativeWindowStressHeatSource.heat,Finset.sum_add_distrib,← Finset.smul_sum,map_add,map_smul,map_sum,
    inner_add_right,real_inner_smul_right]
  rw [laplacian_pairing seed F radius time closed]
  have diffusion : (∑ i : Coordinate,physical (NativeWindowStressHeatSource.diffusion seed time F i i))=physical (traceDiffusion seed time F) := by
    simp only [traceDiffusion,map_sum]
  rw [diffusion,NativeWindowTraceTerminalOperator.trace_split,inner_sub_left,inner_neg_left,
    NativeWindowStressHeatSource.physical_inner]
  change _= -nu.coeff*dirichlet seed F radius time-2*nu.coeff*(∫ point : Torus,traceStress seed time F point*traceDiffusion seed time F point)-
    2*nu.coeff*crossWork seed F radius time-nu.coeff*gradientCross seed F radius time
  dsimp only [crossWork]
  ring

theorem source_square_energy (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (closed : ∀ k,k∈F →waveNeg k∈F)
    (cover : ∀ k∈F,k≠0 →k∈NativeWholeH1Mixed.modes M) : terminalEnergy seed time M F radius=
      nu.coeff^2*NativeWindowAugmentedGradientSource.palinstrophyWindow seed M time+
      nu.coeff*dirichlet seed F radius time+2*nu.coeff*(∫ point : Torus,traceInteraction seed time F point)+
      2*nu.coeff*crossWork seed F radius time+nu.coeff*gradientCross seed F radius time+remainderEnergy seed time M F radius := by
  rw [source_square seed time nonnegative M F radius closed cover,raw_heat_pairing seed F radius time closed]
  ring

theorem source_heat_identity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (closed : ∀ k,k∈F →waveNeg k∈F)
    (cover : ∀ k∈F,k≠0 →k∈NativeWholeH1Mixed.modes M) :
    terminalEnergy seed time M F radius+heatWork seed F radius time=
      nu.coeff^2*NativeWindowAugmentedGradientSource.palinstrophyWindow seed M time+
        nu.coeff*gradientCross seed F radius time+remainderEnergy seed time M F radius := by
  rw [source_square_energy seed time nonnegative M F radius closed cover,NativeWindowConvectionCutoffTrace.heatWork_identity seed F radius time closed]
  ring

theorem source_generator_identity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (closed : ∀ k,k∈F →waveNeg k∈F)
    (cover : ∀ k∈F,k≠0 →k∈NativeWholeH1Mixed.modes M) :
    deriv (NativeWindowConvectionCutoffTrace.energy seed F radius) time+terminalEnergy seed time M F radius=
      nu.coeff^2*NativeWindowAugmentedGradientSource.palinstrophyWindow seed M time+
      nu.coeff*gradientCross seed F radius time+remainderEnergy seed time M F radius+
      NativeWindowConvectionCutoffTrace.lowAdvWork seed F radius time+NativeWindowConvectionCutoffTrace.strainWork seed F radius time+
      NativeWindowConvectionCutoffTrace.lowPressureWork seed F radius time-NativeWindowConvectionCutoffTrace.timeWork seed F radius time := by
  rw [(NativeWindowConvectionCutoffTrace.energy_generator seed F radius time nonnegative closed).deriv]
  have source:=source_heat_identity seed time nonnegative M F radius closed cover
  linarith only [source]

theorem source_signed_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∃ C : ℝ,0≤C ∧
      ∀ radius≥low,∀ cutoff≥low,∀ M : ℕ,∀ time∈Icc 0 horizon,
        (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈NativeWholeH1Mixed.modes M) →
        let F:=integerWaveFrequencyCube cutoff
        nu.coeff*dirichlet seed F radius time+2*nu.coeff*(∫ point : Torus,traceInteraction seed time F point)+
          2*nu.coeff*crossWork seed F radius time+nu.coeff*gradientCross seed F radius time+remainderEnergy seed time M F radius≤
            epsilon*nu.coeff^2*NativeWindowAugmentedGradientSource.palinstrophyWindow seed M time+C := by
  obtain ⟨low,C,C0,paid⟩:=NativeWindowTraceTerminalWindow.source_bound seed horizon nonnegative epsilon positive
  refine ⟨low,C,C0,fun radius above cutoff covered M time inside cover => ?_⟩
  have bound:=paid radius above cutoff covered M time inside cover
  rw [source_square_energy seed time inside.1 M (integerWaveFrequencyCube cutoff) radius
    (NativeWindowFiniteGramFourier.cube_closed cutoff) cover] at bound
  dsimp only
  nlinarith only [bound]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceTerminalGraphHeat
