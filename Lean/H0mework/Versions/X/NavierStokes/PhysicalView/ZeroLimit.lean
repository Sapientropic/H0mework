import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Mixed.Outputs
import H0mework.Versions.X.NavierStokes.PhysicalView.ZeroContract

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeMixedHeatConsumer
open Set Filter MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowRootCarrier NativeWindowRootControl NativeWindowSpacetimeFourier
open NativeFullOrderSynthesis NativeEndpointVelocityCarrier
noncomputable section
variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    {current : NativeTemporalCurrent initial} {occurrence : Occurrence initial current}

def velocity (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (x : Spacetime) : PhysicalSpace :=
  spatialField (wholeVelocity (carrier.view lag x.1).fst) x.2

def stress (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (x : Spacetime) : EuclideanSpace ℝ (Coordinate × Coordinate) :=
  WithLp.toLp 2 fun i => (∑' k,NativeCompleteStressCarrier.read (carrier.view lag x.1).snd k i.1 i.2*monomial k x.2).re

def residual (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (x : Spacetime) : EuclideanSpace ℝ (Coordinate × Coordinate) :=
  WithLp.toLp 2 fun i => (∑' k,NativeCompleteCorrectionRead.residual (carrier.view lag x.1) k i.1 i.2*monomial k x.2).re

def vorticity (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (x : Spacetime) : PhysicalSpace :=
  NativeViewPhysicalCurl.jointCurlRead (fderiv ℝ (velocity carrier lag) x)

def rate (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (x : Spacetime) : PhysicalSpace :=
  fderiv ℝ (velocity carrier lag) x (1,0)

def outputs (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (x : Spacetime) :=
  ((velocity carrier lag x,stress carrier lag x,residual carrier lag x),vorticity carrier lag x,rate carrier lag x)

theorem outputs_zero (carrier : CarrierAt initial occurrence) :
    outputs carrier 0=NativeWindowTailRootConsumer.outputs carrier := rfl

theorem velocity_generated (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) :
    velocity carrier lag=NativeWindowSpacetimeVelocity.jointField initial lag ∘ chart initial current := by
  funext x
  rw [velocity,CarrierAt.view_generated,Function.comp_apply,NativeWindowSpacetimeVelocity.jointField_source]
  rfl

theorem chart_translation (x : Spacetime) :
    chart initial current x=(clockAt initial current,0)+x := by
  ext <;> simp [chart]

theorem chart_jets {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Spacetime → F) (n : ℕ) (x : Spacetime) :
    iteratedFDeriv ℝ n (f ∘ chart initial current) x=
      iteratedFDeriv ℝ n f (chart initial current x) := by
  simpa only [Function.comp_def,chart_translation] using
    (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) n ((clockAt initial current,0) : Spacetime) x)

theorem velocity_derivative (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (x : Spacetime) :
    fderiv ℝ (velocity carrier lag) x=
      fderiv ℝ (NativeWindowSpacetimeVelocity.jointField initial lag) (chart initial current x) := by
  rw [velocity_generated]
  simpa only [Function.comp_def,chart_translation] using
    (fderiv_comp_add_left (𝕜 := ℝ) (f := NativeWindowSpacetimeVelocity.jointField initial lag)
      (x := x) ((clockAt initial current,0) : Spacetime))

theorem outputs_generated (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) :
    outputs carrier lag=NativeMixedHeatOutputs.outputs initial lag ∘ chart initial current := by
  have sigma : stress carrier lag=NativeWindowSpacetimeStress.jointField initial lag ∘ chart initial current := by
    funext x
    apply PiLp.ext
    intro i
    rw [Function.comp_apply,NativeWindowSpacetimeStress.jointField_source]
    change (∑' k,NativeCompleteStressCarrier.read (carrier.view lag x.1).snd k i.1 i.2*monomial k x.2).re=_
    rw [CarrierAt.view_generated]
    rfl
  have rem : residual carrier lag=NativeWindowSpacetimeResidual.jointField initial lag ∘ chart initial current := by
    funext x
    apply PiLp.ext
    intro i
    rw [Function.comp_apply,NativeWindowSpacetimeResidual.jointField_source]
    change (∑' k,NativeCompleteCorrectionRead.residual (carrier.view lag x.1) k i.1 i.2*monomial k x.2).re=_
    rw [CarrierAt.view_generated]
    rfl
  funext x
  simp only [outputs,NativeMixedHeatOutputs.outputs,vorticity,rate,NativeMixedHeatOutputs.vorticity,
    NativeMixedHeatOutputs.rate,Function.comp_apply,velocity_derivative]
  simp only [velocity_generated,sigma,rem,Function.comp_apply]

theorem outputs_smooth (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (outputs carrier lag) (NativeWindowTailRootConsumer.support initial current) := by
  rw [outputs_generated]
  intro x inside
  have member : chart initial current x ∈ NativeMixedHeatPhysical.domain initial ((chart initial current x).1+1) :=
    ⟨⟨inside.1,by linarith⟩,trivial⟩
  exact ((NativeMixedHeatOutputs.outputs_smooth initial _ lag).contDiffAt
    ((NativeMixedHeatPhysical.domain_open initial _).mem_nhds member)).comp_contDiffWithinAt x
      (chart_smooth initial current).contDiffAt.contDiffWithinAt

theorem compact_jets (carrier : CarrierAt initial occurrence) (n : ℕ) {K : Set Spacetime}
    (compact : IsCompact K) (contained : K⊆NativeWindowTailRootConsumer.support initial current) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (outputs carrier lag))
      (iteratedFDeriv ℝ n (NativeWindowTailRootConsumer.outputs carrier)) (𝓝 0) K := by
  have source := NativeMixedHeatOutputs.compact_outputs_jets initial n
    (compact.image (chart_smooth initial current).continuous)
    (by rintro _ ⟨x,inside,rfl⟩; exact contained inside)
  have pulled := (source.comp (chart initial current)).mono (subset_preimage_image _ _)
  have written (lag : ℝ≥0) : iteratedFDeriv ℝ n (outputs carrier lag)=
      iteratedFDeriv ℝ n (NativeMixedHeatOutputs.outputs initial lag) ∘ chart initial current := by
    funext x
    rw [outputs_generated,chart_jets]
    rfl
  rw [← outputs_zero carrier]
  simpa only [written] using! pulled

theorem compact_common_bound (carrier : CarrierAt initial occurrence) (n : ℕ) {K : Set Spacetime}
    (compact : IsCompact K) (contained : K⊆NativeWindowTailRootConsumer.support initial current) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ lag : ℝ≥0 in 𝓝 0,∀ x∈K,‖iteratedFDeriv ℝ n (outputs carrier lag) x‖≤B := by
  obtain ⟨B,B0,paid⟩ := NativeMixedHeatOutputs.compact_outputs_common_bound initial n
    (compact.image (chart_smooth initial current).continuous)
    (by rintro _ ⟨x,inside,rfl⟩; exact contained inside)
  refine ⟨B,B0,paid.mono fun lag bound x inside => ?_⟩
  rw [outputs_generated,chart_jets]
  exact bound _ ⟨x,inside,rfl⟩

theorem compact_continuous_jets (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (n : ℕ)
    {K : Set Spacetime} (contained : K⊆NativeWindowTailRootConsumer.support initial current) :
    ContinuousOn (iteratedFDeriv ℝ n (outputs carrier lag)) K :=
  (ContinuousOn.continuousOn_iteratedFDeriv (outputs_smooth carrier lag)
    (NativeWindowTailRootConsumer.support_open initial current)
    (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤))).mono contained

theorem all_Lp (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (n : ℕ) (p : ℝ≥0∞)
    {K : Set Spacetime} (compact : IsCompact K) (contained : K⊆NativeWindowTailRootConsumer.support initial current) :
    MemLp (iteratedFDeriv ℝ n (outputs carrier lag)) p (volume.restrict K) :=
  (NativeWindowLocalFourier.compact_all_order_Lp_on _ (outputs_smooth carrier lag)
    (NativeWindowTailRootConsumer.support_open initial current) n p compact contained).choose_spec.2.1

theorem all_Lp_common_bound (carrier : CarrierAt initial occurrence) (n : ℕ) {K : Set Spacetime}
    (compact : IsCompact K) (contained : K⊆NativeWindowTailRootConsumer.support initial current) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ lag : ℝ≥0 in 𝓝 0,∀ p : ℝ≥0∞,
      MemLp (iteratedFDeriv ℝ n (outputs carrier lag)) p (volume.restrict K) ∧
      eLpNorm (iteratedFDeriv ℝ n (outputs carrier lag)) p (volume.restrict K) ≤
        ENNReal.ofReal B*volume K^(1/p.toReal) := by
  obtain ⟨B,B0,paid⟩ := compact_common_bound carrier n compact contained
  refine ⟨B,B0,paid.mono fun lag bounded p => ⟨all_Lp carrier lag n p compact contained,?_⟩⟩
  have bound : ∀ᵐ x ∂volume.restrict K,‖iteratedFDeriv ℝ n (outputs carrier lag) x‖≤B := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with x inside
    exact bounded x inside
  simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := p) bound

theorem uniform_finite_Lp {Parameter F : Type*} [NormedAddCommGroup F]
    {filter : Filter Parameter} (f : Parameter → Spacetime → F) (target : Spacetime → F)
    {K : Set Spacetime} (compact : IsCompact K) (converges : TendstoUniformlyOn f target filter K)
    (p : ℝ≥0∞) : Tendsto (fun h => eLpNorm (fun x => f h x-target x) p (volume.restrict K)) filter (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro epsilon positive
  have finite : volume K^(1/p.toReal)≠(⊤ : ℝ≥0∞) :=
    (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr ENNReal.toReal_nonneg)
      (compact.measure_lt_top (μ := volume)).ne).ne
  obtain ⟨delta,delta0,small⟩ := ENNReal.exists_nnreal_pos_mul_lt finite positive.ne'
  have near := (Metric.tendstoUniformlyOn_iff.mp converges) delta (by exact_mod_cast delta0)
  filter_upwards [near] with h near
  have bounded : ∀ᵐ x ∂volume.restrict K,‖f h x-target x‖≤(delta : ℝ) := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with x inside
    simpa only [dist_eq_norm,norm_sub_rev] using (near x inside).le
  have paid := eLpNorm_le_of_ae_bound (p := p) bounded
  apply paid.trans
  simpa [mul_comm] using small.le

theorem all_Lp_converges (carrier : CarrierAt initial occurrence) (n : ℕ) (p : ℝ≥0∞)
    {K : Set Spacetime} (compact : IsCompact K) (contained : K⊆NativeWindowTailRootConsumer.support initial current) :
    Tendsto (fun lag : ℝ≥0 => eLpNorm (fun x => iteratedFDeriv ℝ n (outputs carrier lag) x-
      iteratedFDeriv ℝ n (NativeWindowTailRootConsumer.outputs carrier) x) p (volume.restrict K)) (𝓝 0) (𝓝 0) :=
  uniform_finite_Lp _ _ compact (compact_jets carrier n compact contained) p

open NativeViewRuntime NativeViewConsumerNext

def read (runtime : Runtime) (lag : ℝ≥0) := outputs (payload runtime) lag

theorem read_zero (runtime : Runtime) : read runtime 0=NativeWindowTailRootConsumer.read runtime := rfl

theorem measured_next (runtime : Runtime) (lag : ℝ≥0) (time : ℝ) :
    (payload runtime.tick.next).view lag time=(payload runtime).view lag (advance runtime+time) := by
  erw [CarrierAt.view_generated,CarrierAt.view_generated]
  simp only [index_next,visit_current]
  change NativeWindowHeatEvolution.source NativeViewRuntime.initial lag
    (elapsedTime NativeViewRuntime.initial (index runtime+1)+time)=_
  rw [elapsedTime_succ,add_assoc]
  rfl

theorem controller_limit (runtime : Runtime) (n : ℕ) (p : ℝ≥0∞) {K : Set Spacetime}
    (compact : IsCompact K) (contained : K⊆NativeWindowTailRootConsumer.support NativeViewRuntime.initial
      (visit (index runtime)).current) :
    HEq (facade.readoutAt runtime PUnit.unit)
      (runtime.tick.generated.projectionOutcome ((installation NativeViewRuntime.initial).embed resolution)) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      ((nativeTemporalRoot NativeViewRuntime.initial).generatedLedgerAt (visit runtime.state).current) ∧
    runtime.tick.nextCurrent=process.stateAt (process.successor runtime.state) ∧
    (∀ lag time,(payload runtime.tick.next).view lag time=(payload runtime).view lag (advance runtime+time)) ∧
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (read runtime lag))
      (iteratedFDeriv ℝ n (NativeWindowTailRootConsumer.read runtime)) (𝓝 0) K ∧
    Tendsto (fun lag : ℝ≥0 => eLpNorm (fun x => iteratedFDeriv ℝ n (read runtime lag) x-
      iteratedFDeriv ℝ n (NativeWindowTailRootConsumer.read runtime) x) p (volume.restrict K)) (𝓝 0) (𝓝 0) :=
  ⟨(activated_readout runtime).1,(activated_readout runtime).2.1,(activated_readout runtime).2.2,
    measured_next runtime,compact_jets (payload runtime) n compact contained,
    all_Lp_converges (payload runtime) n p compact contained⟩

end
end SaturationMonoid.NavierStokes.NativeMixedHeatConsumer
