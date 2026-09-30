import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWindowAction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter (IntegerWavevector)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM include_inner restrict_include)
open NativeFiniteActionResolvent (pairing physicalSpace)
open NativeForwardWindowPairingReadout (averageMeasure density)
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

theorem rate_word_sample_ae (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    NativeWindowHistorySpatialWords.rate seed M directions time =ᵐ[averageMeasure]
      fun shift => includeCLM (modes M) (modes_closed M)
        (NativeWindowStageNineSource.coefficientRate seed M directions (time-shift)) := by
  have source : ∀ᵐ shift ∂averageMeasure,
      NativeWindowHistoryOseen.velocityRate seed M (time-shift)=
        includeCLM (modes M) (modes_closed M)
          (NativeWindowStageNineSource.lift (modes M)
            (NativeUnheatedGlobalNegativeOne.rate seed (time-shift))) :=
    (withDensity_absolutelyContinuous volume (fun shift => (density shift : ℝ≥0∞))).ae_le
      ((Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
        (NativeWindowHistoryOseen.velocityRate_original seed M))
  filter_upwards [(NativeWindowHistorySpatialWords.fiber M directions).coeFn_compLpL
      (NativeWindowHistoryOseen.rateHistory seed M time),
    NativeWindowHistoryOseen.rateHistory_ae seed M time,source]
      with shift applied sampled actual
  change NativeWindowHistorySpatialWords.rate seed M directions time shift=
    NativeWindowHistorySpatialWords.fiber M directions
      (NativeWindowHistoryOseen.rateHistory seed M time shift) at applied
  rw [applied,sampled,actual]
  exact NativeWindowHistoryOseen.lift_included M _ _

private theorem included_metric_pair (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ)
    (u v : NativeWindowTraceWholeHistory.H)
    (f g : ℝ → physicalSpace (modes M))
    (uf : u=ᵐ[averageMeasure] fun shift => includeCLM (modes M) (modes_closed M) (f shift))
    (vg : v=ᵐ[averageMeasure] fun shift => includeCLM (modes M) (modes_closed M) (g shift)) :
    inner ℝ u (fullMetricAction seed time M F radius v)=
      ∫shift,pairing (modes M) (f shift)
        (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius (g shift))
        ∂averageMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(fullMetricFiber seed time M F radius).coeFn_compLpL v,uf,vg]
    with shift applied left right
  change inner ℝ (u shift)
    (((fullMetricFiber seed time M F radius).compLpL 2 averageMeasure v) shift)=_
  rw [applied,left,right]
  dsimp only [fullMetricFiber]
  rw [NativeWindowHistoryOseen.lift_included]
  rw [include_inner (modes M) (modes_zero M) (modes_closed M),restrict_include]
  rfl

theorem history_word_rate_metric (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ)
    (F : Finset IntegerWavevector) (radius : ℕ) :
    inner ℝ (NativeWindowHistorySpatialWords.rate seed M directions time)
      (fullMetricAction seed time M F radius
        (NativeWindowHistorySpatialWords.history seed M directions time))=
      ∫shift,pairing (modes M)
        (NativeWindowStageNineSource.coefficientRate seed M directions (time-shift))
        (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
          (NativeWindowStageNineSource.coefficient seed M directions (time-shift)))
        ∂averageMeasure :=
  included_metric_pair seed M time F radius _ _ _ _
    (rate_word_sample_ae seed M directions time)
    (NativeWindowHistorySpatialWords.history_original seed M directions time)

theorem history_word_metric_rate (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ)
    (F : Finset IntegerWavevector) (radius : ℕ) :
    inner ℝ (NativeWindowHistorySpatialWords.history seed M directions time)
      (fullMetricAction seed time M F radius
        (NativeWindowHistorySpatialWords.rate seed M directions time))=
      ∫shift,pairing (modes M)
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift))
        (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
          (NativeWindowStageNineSource.coefficientRate seed M directions (time-shift)))
        ∂averageMeasure :=
  included_metric_pair seed M time F radius _ _ _ _
    (NativeWindowHistorySpatialWords.history_original seed M directions time)
    (rate_word_sample_ae seed M directions time)

private theorem included_metric_integrable (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ)
    (u v : NativeWindowTraceWholeHistory.H)
    (f g : ℝ → physicalSpace (modes M))
    (uf : u=ᵐ[averageMeasure] fun shift => includeCLM (modes M) (modes_closed M) (f shift))
    (vg : v=ᵐ[averageMeasure] fun shift => includeCLM (modes M) (modes_closed M) (g shift)) :
    Integrable (fun shift => pairing (modes M) (f shift)
      (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius (g shift)))
      averageMeasure := by
  have original := L2.integrable_inner (𝕜 := ℝ) u (fullMetricAction seed time M F radius v)
  apply original.congr
  filter_upwards [(fullMetricFiber seed time M F radius).coeFn_compLpL v,uf,vg]
    with shift applied left right
  change inner ℝ (u shift)
    (((fullMetricFiber seed time M F radius).compLpL 2 averageMeasure v) shift)=_
  rw [applied,left,right]
  dsimp only [fullMetricFiber]
  rw [NativeWindowHistoryOseen.lift_included]
  rw [include_inner (modes M) (modes_zero M) (modes_closed M),restrict_include]
  rfl

theorem spatialRate_lag (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWindowHierarchyWrite.spatialRate seed M order F radius 0 time=
      ∫shift,NativeWindowHierarchyWrite.sampleRate seed time M order F radius (time-shift)
        ∂averageMeasure := by
  rw [NativeWindowHierarchyWrite.spatialRate,
    NativeForwardWindowPairingReadout.density_integral]
  change (∫sample in time+1..time+2,
      NativeUnheatedStressPairEvolution.kernelWeight 0 time 0 sample •
        NativeWindowHierarchyWrite.sampleRate seed time M order F radius sample)=
    ∫shift,NativeForwardWindowJets.kernelJet 0 shift •
      NativeWindowHierarchyWrite.sampleRate seed time M order F radius (time-shift)
  exact (NativeWindowStressHeatTime.kernel_integral
    (NativeWindowHierarchyWrite.sampleRate seed time M order F radius) 0 time).symm

theorem spatialRate_full_metric (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWindowHierarchyWrite.spatialRate seed M order F radius 0 time=
      ∑index : FixedMatterSpatialWordIndex order,
        let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
        let r:=NativeWindowHistorySpatialWords.rate seed M index.toList time
        inner ℝ r (fullMetricAction seed time M F radius h)+
          inner ℝ h (fullMetricAction seed time M F radius r) := by
  let term (index : FixedMatterSpatialWordIndex order) (shift : ℝ) :=
    pairing (modes M)
      (NativeWindowStageNineSource.coefficientRate seed M index.toList (time-shift))
      (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
        (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift)))+
    pairing (modes M)
      (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift))
      (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
        (NativeWindowStageNineSource.coefficientRate seed M index.toList (time-shift)))
  have firstI (index : FixedMatterSpatialWordIndex order) : Integrable (fun shift =>
      pairing (modes M)
        (NativeWindowStageNineSource.coefficientRate seed M index.toList (time-shift))
        (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
          (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift))))
      averageMeasure :=
    included_metric_integrable seed M time F radius _ _ _ _
      (rate_word_sample_ae seed M index.toList time)
      (NativeWindowHistorySpatialWords.history_original seed M index.toList time)
  have lastI (index : FixedMatterSpatialWordIndex order) : Integrable (fun shift =>
      pairing (modes M)
        (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift))
        (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
          (NativeWindowStageNineSource.coefficientRate seed M index.toList (time-shift))))
      averageMeasure :=
    included_metric_integrable seed M time F radius _ _ _ _
      (NativeWindowHistorySpatialWords.history_original seed M index.toList time)
      (rate_word_sample_ae seed M index.toList time)
  have termI (index : FixedMatterSpatialWordIndex order) :
      Integrable (term index) averageMeasure := (firstI index).add (lastI index)
  have integrated : (∫shift,∑index : FixedMatterSpatialWordIndex order,
      term index shift ∂averageMeasure)=
      ∑index : FixedMatterSpatialWordIndex order,
        ∫shift,term index shift ∂averageMeasure :=
    integral_finsetSum Finset.univ (fun index _ => termI index)
  have row (index : FixedMatterSpatialWordIndex order) :
      (∫shift,term index shift ∂averageMeasure)=
      let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
      let r:=NativeWindowHistorySpatialWords.rate seed M index.toList time
      inner ℝ r (fullMetricAction seed time M F radius h)+
        inner ℝ h (fullMetricAction seed time M F radius r) := by
    dsimp only [term]
    rw [integral_add (firstI index) (lastI index),
      ← history_word_rate_metric seed M index.toList time F radius,
      ← history_word_metric_rate seed M index.toList time F radius]
  calc
    _=∫shift,NativeWindowHierarchyWrite.sampleRate seed time M order F radius (time-shift)
        ∂averageMeasure := spatialRate_lag seed M order time F radius
    _=∫shift,∑index : FixedMatterSpatialWordIndex order,
        term index shift ∂averageMeasure := rfl
    _=∑index : FixedMatterSpatialWordIndex order,
      ∫shift,term index shift ∂averageMeasure := integrated
    _=_ := Finset.sum_congr rfl (fun index _ => row index)
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
