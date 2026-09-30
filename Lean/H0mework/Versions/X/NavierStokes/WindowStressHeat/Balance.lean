import H0mework.Versions.X.NavierStokes.WindowStressHeat.Time

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowStressHeatBalance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open NativePhysicalFourier NativePhysicalGradient NativeCompleteStressAction NativeResolventCompactness
open NativeUnheatedGlobalNegativeOne NativeForwardWindowPairingReadout NativeWindowStressHeatTime
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {nu : Viscosity}

def basis (wave : IntegerWavevector) : ℂ →L[ℝ] C(Torus,ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ Torus).comp
    ((ContinuousLinearMap.toSpanSingleton ℂ (UnitAddTorus.mFourier wave)).restrictScalars ℝ)

theorem read_apply (F : Finset IntegerWavevector) (coordinate : Coordinate) (value : State) :
    read F coordinate value = ∑ wave ∈ F, basis wave (NativeUnheatedTriadRows.decode wave coordinate value) := by
  unfold NativeWindowStressHeatTime.read basis
  simp only [ContinuousLinearMap.comp_apply,sum_apply,map_sum]

def viscousRead (F : Finset IntegerWavevector) (coordinate : Coordinate) : FullSpace →L[ℝ] C(Torus,ℝ) :=
  ∑ wave ∈ F, (-integerWaveViscousMultiplier wave) • ((basis wave).comp (velocityRead wave coordinate))

theorem rate_split_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) : ∀ᵐ time : ℝ, 0 ≤ time → fieldRate seed F coordinate time =
      fieldAction seed F coordinate time+nu.coeff • viscousRead F coordinate (NativeUnifiedCompleteSource.source seed time) := by
  filter_upwards [NativeUnheatedTriadRows.derivative_split_ae seed] with time actual nonnegative
  simp only [fieldRate,fieldAction,read_apply]
  change (∑ wave ∈ F, basis wave (NativeUnheatedTriadRows.derivative seed time wave coordinate)) = _
  simp only [actual nonnegative,map_sub,map_smul,Finset.sum_sub_distrib]
  have mean (wave : IntegerWavevector) : NativeUnheatedTriadRows.velocity seed time wave coordinate =
      velocityRead wave coordinate (NativeUnifiedCompleteSource.source seed time) :=
    NativeUnheatedTriadRows.velocity_original seed time wave coordinate
  simp only [mean,viscousRead,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,Finset.smul_sum,smul_smul]
  simp only [mul_neg,neg_smul,Finset.sum_neg_distrib,sub_eq_add_neg]
  rfl

theorem action_original_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ coordinate,
    let U := NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
    fieldAction seed F coordinate time = ∑ wave ∈ F, basis wave
      (NativeTimeJetCarrier.projectedDivergenceCLM wave (NativeHigherTimeJets.mixedFlux U U wave) coordinate) := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed] with time regular nonnegative coordinate
  simp only [fieldAction,read_apply]
  apply Finset.sum_congr rfl
  intro wave _
  exact congrArg (basis wave) (NativeUnheatedQuarticRows.source_action seed time nonnegative (regular nonnegative) wave coordinate)

theorem viscousRead_physical (F : Finset IntegerWavevector) (coordinate : Coordinate) (value : FullSpace) (x : PhysicalSpace) :
    viscousRead F coordinate value (NativeFullOrderSynthesis.circlePoint x) =
      ∑ direction : Coordinate, NativeWindowFiniteGramSource.secondRead F x direction coordinate value := by
  have single (wave : IntegerWavevector) : basis wave (velocityRead wave coordinate value)
      (NativeFullOrderSynthesis.circlePoint x) = NativeWindowFiniteGramSource.modeRead wave coordinate x value := by
    have original := NativeWindowFiniteGramFourier.read_physical {wave} coordinate value x
    simpa only [NativeWindowFiniteGramFourier.read,NativeWindowFiniteGramFourier.complexRead,Finset.sum_singleton,
      NativeWindowFiniteGramSource.fieldRead,NativeWindowFiniteGramSource.modeRead] using! original
  simp only [viscousRead,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,single,NativeWindowFiniteGramSource.secondRead]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro wave _
  simp only [smul_eq_mul,← Finset.sum_mul]
  congr 1
  simp only [integerWaveViscousMultiplier,integerWaveNormSq,integerAngularCoefficient,Finset.mul_sum,Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro direction _
  ring

def rawHeat (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  -nu.coeff • (NativeWindowStressHeatSource.productAverage seed time (viscousRead F output) (NativeWindowFiniteGramFourier.read F input)+
    NativeWindowStressHeatSource.productAverage seed time (NativeWindowFiniteGramFourier.read F output) (viscousRead F input))

theorem rawHeat_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) :
    rawHeat seed time F output input = NativeWindowStressHeatSource.heat seed time F output input := by
  ext point
  obtain ⟨x,rfl⟩ := NativeWindowStressHeatSource.circle_surjective point
  rw [NativeWindowStressHeatSource.heat_physical seed time F closed]
  simp only [rawHeat,ContinuousMap.smul_apply,ContinuousMap.add_apply,NativeWindowStressHeatSource.productAverage_apply,
    viscousRead_physical,NativeWindowFiniteGramFourier.read_physical,Matrix.smul_apply,smul_eq_mul,
    NativeWindowStressHeatGram.cross,Finset.sum_apply]
  have paired (first last : FullSpace →L[ℝ] ℝ) :
      (∫ shift, first (NativeUnifiedCompleteSource.source seed (time-shift))*last (NativeUnifiedCompleteSource.source seed (time-shift))
        ∂averageMeasure) = inner ℝ (NativeWindowFiniteGramSource.lift seed time first) (NativeWindowFiniteGramSource.lift seed time last) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [NativeWindowFiniteGramSource.lift_ae seed time first,NativeWindowFiniteGramSource.lift_ae seed time last]
      with shift firstEq lastEq
    rw [firstEq,lastEq]
    exact mul_comm _ _
  have lifted (coordinate : Coordinate) :
      (∑ direction : Coordinate, NativeWindowFiniteGramSource.second seed time F x direction coordinate) =
        NativeWindowFiniteGramSource.lift seed time (∑ direction : Coordinate, NativeWindowFiniteGramSource.secondRead F x direction coordinate) := by
    rw [map_sum]
    rfl
  rw [lifted output,lifted input]
  have first := paired (∑ j : Coordinate, NativeWindowFiniteGramSource.secondRead F x j output)
    (NativeWindowFiniteGramSource.fieldRead F x input)
  have last := paired (NativeWindowFiniteGramSource.fieldRead F x output)
    (∑ j : Coordinate, NativeWindowFiniteGramSource.secondRead F x j input)
  simp only [sum_apply] at first last
  rw [first,last]
  simp only [NativeWindowFiniteGramSource.value]
  ring

theorem action_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    IntervalIntegrable (fieldAction seed F coordinate) volume a b := by
  have paid : IntegrableOn (NativeUnheatedSourceWeightedTail.nonlinear seed) (Icc 0 (max a b)) :=
    NativeUnheatedSourceWeightedTail.nonlinear_integrable seed (max a b) (a0.trans (le_max_left _ _))
  have source := paid.mono_set
    (show uIcc a b ⊆ Icc 0 (max a b) from fun _ inside => ⟨(le_min a0 b0).trans inside.1,inside.2⟩)
  exact ⟨(read F coordinate).integrable_comp source.intervalIntegrable.1,
    (read F coordinate).integrable_comp source.intervalIntegrable.2⟩

theorem nonlinear_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    IntervalIntegrable (nonlinearPair seed F output input) volume a b :=
  ((action_integrable seed F output a b a0 b0).mul_continuousOn (field_ac seed F input a b a0 b0).continuousOn).add
    ((action_integrable seed F input a b a0 b0).continuousOn_mul (field_ac seed F output a b a0 b0).continuousOn)

def heatPair (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  -nu.coeff • (viscousRead F output (NativeUnifiedCompleteSource.source seed time)*field seed F input time+
    field seed F output time*viscousRead F input (NativeUnifiedCompleteSource.source seed time))

theorem productRate_split_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) : ∀ᵐ time : ℝ, 0 ≤ time → productRate seed F output input time =
      nonlinearPair seed F output input time-heatPair seed F output input time := by
  filter_upwards [rate_split_ae seed F output,rate_split_ae seed F input] with time left right nonnegative
  ext point
  simp only [productRate,left nonnegative,right nonnegative,nonlinearPair,heatPair,ContinuousMap.add_apply,
    ContinuousMap.sub_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
  ring

open NativeUnheatedStressPairEvolution

theorem heatPair_average (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) :
    (∫ actual in time+1..time+2, kernelWeight 0 time 0 actual • heatPair seed F output input actual) =
      rawHeat seed time F output input := by
  rw [← kernel_integral]
  simp only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero]
  rw [← density_integral]
  simp only [heatPair,field_original]
  rw [integral_smul,integral_add
    (NativeWindowStressHeatSource.product_integrable seed time (viscousRead F output) (NativeWindowFiniteGramFourier.read F input))
    (NativeWindowStressHeatSource.product_integrable seed time (NativeWindowFiniteGramFourier.read F output) (viscousRead F input))]
  rfl

def nonlinearWindow (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  -(∫ actual in time+1..time+2, kernelWeight 0 time 0 actual • nonlinearPair seed F output input actual)

theorem jet_generator (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) :
    -jet seed F output input 1 time = nonlinearWindow seed time F output input+
      NativeWindowStressHeatSource.heat seed time F output input := by
  have a0 : 0 ≤ time+1 := by linarith
  have b0 : 0 ≤ time+2 := by linarith
  have q := (nonlinear_integrable seed F output input (time+1) (time+2) a0 b0).continuousOn_smul
    (kernelWeight_continuous 0 time 0).continuousOn
  have p := (productRate_integrable seed F output input (time+1) (time+2) a0 b0).continuousOn_smul
    (kernelWeight_continuous 0 time 0).continuousOn
  have source : rawHeat seed time F output input =
      (∫ actual in time+1..time+2, kernelWeight 0 time 0 actual • nonlinearPair seed F output input actual)-
        jet seed F output input 1 time := by
    rw [← heatPair_average,jet_rate seed F output input time nonnegative,← intervalIntegral.integral_sub q p]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [productRate_split_ae seed F output input] with actual original inside
    have positive : 0 ≤ actual := (le_min a0 b0).trans (uIoc_subset_uIcc inside).1
    rw [original positive,smul_sub]
    abel
  rw [rawHeat_original seed time F closed] at source
  rw [source,nonlinearWindow]
  abel

def sigma (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (output input : Coordinate)
    (time : ℝ) : ScalarField := -NativeWindowStressHeatSource.physical (NativeWindowFiniteGramFourier.stress seed time F output input)

theorem sigma_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) :
    HasDerivAt (sigma seed F output input)
      (NativeWindowStressHeatSource.physical (nonlinearWindow seed time F output input)+
        NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input)) time := by
  have generated := (NativeWindowStressHeatSource.physical.hasFDerivAt.comp_hasDerivAt time
    (jet_hasDerivAt seed F output input 0 time)).neg
  have rate : -NativeWindowStressHeatSource.physical (jet seed F output input 1 time) =
      NativeWindowStressHeatSource.physical (nonlinearWindow seed time F output input)+
        NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input) := by
    rw [← map_neg,jet_generator seed time nonnegative F closed,map_add]
  unfold sigma
  simpa only [Function.comp_def,Pi.neg_apply,jet_zero,rate] using! generated

def energy (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) : ℝ :=
  ∑ output : Coordinate, ∑ input : Coordinate, (1/2 : ℝ)*‖sigma seed F output input time‖^2

def nonlinearWork (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : ℝ :=
  ∑ output : Coordinate, ∑ input : Coordinate, inner ℝ (sigma seed F output input time)
    (NativeWindowStressHeatSource.physical (nonlinearWindow seed time F output input))

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) :
    HasDerivAt (energy seed F) (nonlinearWork seed time F+NativeWindowStressHeatSource.heatWork seed time F) time := by
  have entry (output input : Coordinate) : HasDerivAt (fun actual => (1/2 : ℝ)*‖sigma seed F output input actual‖^2)
      (inner ℝ (sigma seed F output input time) (NativeWindowStressHeatSource.physical (nonlinearWindow seed time F output input))+
        inner ℝ (sigma seed F output input time)
          (NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input))) time := by
    convert! ((sigma_hasDerivAt seed time nonnegative F closed output input).norm_sq).const_mul (1/2 : ℝ) using 1
    rw [inner_add_right]
    ring
  have sum := HasDerivAt.sum (u := Finset.univ) fun output _ => HasDerivAt.sum (u := Finset.univ) fun input _ => entry output input
  simpa only [energy,nonlinearWork,NativeWindowStressHeatSource.heatWork,sigma,Finset.sum_fn,Finset.sum_add_distrib] using! sum

theorem cube_energy_balance (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) (radius : ℕ) :
    let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius
    deriv (energy seed F) time+nu.coeff*NativeWindowStressHeatSource.dirichlet seed time F+
      2*nu.coeff*(∫ point, NativeWindowStressHeatSource.interaction seed time F point) = nonlinearWork seed time F := by
  dsimp only
  rw [(energy_hasDerivAt seed time nonnegative _ (NativeWindowFiniteGramFourier.cube_closed radius)).deriv,
    (NativeWindowStressHeatSource.cube_heatWork seed time radius).1]
  ring

open SourceGeneratedNativeResponseDisposition ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem nonlinearWindow_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) :
    nonlinearWindow seed (step.2.clockAdvance+time) F = nonlinearWindow step.1 time F := by
  have heat := congrArg Prod.fst (NativeWindowStressHeatSource.whole_next seed step generated time nonnegative F)
  change NativeWindowStressHeatSource.heat seed (step.2.clockAdvance+time) F =
    NativeWindowStressHeatSource.heat step.1 time F at heat
  funext output input
  have before := jet_generator seed (step.2.clockAdvance+time) (add_nonneg step.2.clockAdvance_pos.le nonnegative)
    F closed output input
  have after := jet_generator step.1 time nonnegative F closed output input
  rw [NativeWindowStressHeatTime.jet_next seed F output input 1 step generated time nonnegative,heat] at before
  exact add_right_cancel (before.symm.trans after)

theorem whole_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) :
    ((fun output input => sigma seed F output input (step.2.clockAdvance+time)),energy seed F (step.2.clockAdvance+time),
      nonlinearWork seed (step.2.clockAdvance+time) F) =
    ((fun output input => sigma step.1 F output input time),energy step.1 F time,nonlinearWork step.1 time F) := by
  simp only [energy,nonlinearWork,sigma,NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative,
    nonlinearWindow_next seed step generated time nonnegative F closed]

end
end SaturationMonoid.NavierStokes.NativeWindowStressHeatBalance
