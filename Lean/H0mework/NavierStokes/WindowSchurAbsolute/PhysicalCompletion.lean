import H0mework.NavierStokes.WindowSchurAbsolute.PhysicalLimit
import Mathlib.Analysis.Normed.Operator.Completeness

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalCompletion
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes)
open NativeWindowAbsoluteTimeSource (H history rate)
open NativeWindowAbsoluteTimeFourier (Fiber Space physical realize row)
open NativeWindowTraceWholeHistory (projection)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
local instance spaceSeminormed : SeminormedAddCommGroup Space :=
  (inferInstance : NormedAddCommGroup Space).toSeminormedAddCommGroup
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}

def project (M : ℕ) : H →L[ℝ] H := (projection M).compLpL 2 volume

private theorem project_error (M : ℕ) (v : wholePhysical) : ‖projection M v-v‖^2≤4*‖v‖^2 := by
  have bound:‖projection M v-v‖≤2*‖v‖ := calc
    _≤‖projection M v‖+‖v‖ := norm_sub_le _ _
    _≤‖v‖+‖v‖ := add_le_add (NativeWindowHistoryWholeRecovery.projection_norm M v) le_rfl
    _=_ := by ring
  exact (pow_le_pow_left₀ (norm_nonneg _) bound 2).trans_eq (by ring)

theorem project_tendsto (v : H) : Tendsto (fun M => project M v) atTop (𝓝 v) := by
  let F:=fun M s => ‖projection M (v s)-v s‖^2
  have measured (M : ℕ) : AEStronglyMeasurable (F M) (volume : Measure ℝ) :=
    (((projection M).continuous.comp_aestronglyMeasurable (Lp.memLp v).1).sub (Lp.memLp v).1).norm.pow 2
  have dominated (M : ℕ) : ∀ᵐ s : ℝ,‖F M s‖≤4*‖v s‖^2 := by
    filter_upwards with s
    simpa only [F,Real.norm_eq_abs,abs_sq] using project_error M (v s)
  have paid:Integrable (fun s : ℝ => 4*‖v s‖^2) :=
    ((Lp.memLp v).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul 4
  have limit:=tendsto_integral_of_dominated_convergence (μ := volume) (f := fun _ => (0:ℝ))
    (fun s => 4*‖v s‖^2) measured paid dominated
    (Eventually.of_forall fun s => NativeWindowHistoryWholeRecovery.projection_error_tendsto (v s))
  have read (M : ℕ) : ‖project M v-v‖^2=∫ s : ℝ,F M s := by
    rw [NativeWindowAbsoluteTimeIsometry.norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (project M v) v,(projection M).coeFn_compLpL v] with s difference actual
    rw [difference,Pi.sub_apply,show project M v s=projection M (v s) from actual]
  have squared:Tendsto (fun M => ‖project M v-v‖^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [read,integral_zero] using limit
  have normed:=Real.continuous_sqrt.continuousAt.tendsto.comp squared
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,@abs_norm H _,Real.sqrt_zero] using normed

theorem row_project (M : ℕ) (k : IntegerWavevector) (i : Coordinate) (v : H) :
    row k i (project M v)=if k∈modes M then row k i v else 0 := by
  apply Lp.ext
  filter_upwards [(NativeWindowAbsoluteTimeFourier.rowMap k i).coeFn_compLpL (project M v),
    (projection M).coeFn_compLpL v,(NativeWindowAbsoluteTimeFourier.rowMap k i).coeFn_compLpL v]
    with s outer projected original
  change row k i (project M v) s=_ at outer
  change project M v s=_ at projected
  change row k i v s=_ at original
  rw [outer,projected,NativeWindowAbsoluteTimeFourier.row_apply,
    NativeWindowAbsoluteTimePhysicalLimit.projection_velocity,complexSharpSupportProjection_apply]
  split_ifs with inside
  · exact original.symm
  · simp

theorem modes_mono {N M : ℕ} (le : N≤M) : modes N⊆modes M :=
  Finset.erase_subset_erase 0
    (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion.integerWaveFrequencyCube_mono le)

theorem physical_project (N M : ℕ) (le : N≤M) (i : Coordinate) (v : H) :
    physical (modes M) i (project N v)=physical (modes N) i v := by
  apply congrArg (ContinuousMap.toLp 2 volume ℂ)
  apply ContinuousMap.ext
  intro x
  change (∑ k∈modes M,UnitAddTorus.mFourier k x • row k i (project N v))=
    ∑ k∈modes N,UnitAddTorus.mFourier k x • row k i v
  rw [← Finset.sum_subset (modes_mono le) (by
    intro k _ outside
    simp only [row_project,if_neg outside,smul_zero])]
  exact Finset.sum_congr rfl fun k inside => by rw [row_project,if_pos inside]

theorem physical_norm (F : Finset IntegerWavevector) (i : Coordinate) (v : H) : ‖physical F i v‖≤‖v‖ := by
  have one:=(Finset.single_le_sum (s := Finset.univ) (fun j _ => sq_nonneg ‖physical F j v‖)
    (Finset.mem_univ i)).trans (NativeWindowAbsoluteTimeFourier.physical_mass F v)
  exact (sq_le_sq₀ (norm_nonneg (physical F i v)) (norm_nonneg v)).mp one

theorem physical_difference (N M : ℕ) (le : N≤M) (i : Coordinate) (v : H) :
    ‖physical (modes N) i v-physical (modes M) i v‖≤‖project N v-v‖ := by
  have same:physical (modes N) i v-physical (modes M) i v=
      realize (modes M) i (project N v-v) := by
    rw [map_sub]
    exact congrArg (fun u : Space => u-physical (modes M) i v) (physical_project N M le i v).symm
  rw [same]
  exact physical_norm (modes M) i (project N v-v)

theorem physical_cauchy (i : Coordinate) (v : H) : CauchySeq (fun M => physical (modes M) i v) :=
  cauchySeq_of_le_tendsto_0' (fun M => ‖project M v-v‖)
    (fun N M le => by simpa only [dist_eq_norm] using physical_difference N M le i v)
    (tendsto_iff_norm_sub_tendsto_zero.mp (project_tendsto v))

def value (i : Coordinate) (v : H) : Space :=
  Classical.choose (cauchySeq_tendsto_of_complete (physical_cauchy i v))

theorem value_tendsto (i : Coordinate) (v : H) :
    Tendsto (fun M => physical (modes M) i v) atTop (𝓝 (value i v)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (physical_cauchy i v))

theorem value_norm (i : Coordinate) (v : H) : ‖value i v‖≤‖v‖ :=
  le_of_tendsto (value_tendsto i v).norm (Eventually.of_forall fun M => physical_norm (modes M) i v)

theorem value_add (i : Coordinate) (u v : H) : value i (u+v)=value i u+value i v := by
  apply tendsto_nhds_unique (value_tendsto i (u+v))
  simpa only [NativeWindowAbsoluteTimeFourier.physical_add] using (value_tendsto i u).add (value_tendsto i v)

theorem value_smul (i : Coordinate) (a : ℝ) (v : H) : value i (a • v)=a • value i v := by
  apply tendsto_nhds_unique (value_tendsto i (a • v))
  simpa only [NativeWindowAbsoluteTimeFourier.physical_smul] using (value_tendsto i v).const_smul a

def synthesis (i : Coordinate) : H →L[ℝ] Space :=
  LinearMap.mkContinuous ({toFun := value i,map_add' := value_add i,map_smul' := value_smul i} : H →ₗ[ℝ] Space)
    1 (fun v => by simpa only [one_mul] using! value_norm i v)

theorem synthesis_project (M : ℕ) (i : Coordinate) (v : H) :
    synthesis i (project M v)=physical (modes M) i v := by
  apply tendsto_nhds_unique (value_tendsto i (project M v))
  apply tendsto_const_nhds.congr'
  exact eventually_atTop.mpr ⟨M,fun N le => (physical_project M N le i v).symm⟩

theorem mass (v : H) : (∑ i : Coordinate,‖synthesis i v‖^2)=‖v‖^2 := by
  have left:=tendsto_finsetSum Finset.univ fun i _ => (value_tendsto i v).norm.pow 2
  have right:=(project_tendsto v).norm.pow 2
  apply tendsto_nhds_unique left
  convert! right using 1
  funext M
  exact NativeWindowAbsoluteTimeFourier.physical_mass_exact M v

theorem pairing (u v : H) : (∑ i : Coordinate,inner ℝ (synthesis i u) (synthesis i v))=inner ℝ u v := by
  have plus:=mass (u+v)
  simp only [map_add,norm_add_sq_real,Finset.sum_add_distrib,← Finset.mul_sum] at plus
  linarith only [plus,mass u,mass v]

theorem source_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i : Coordinate) :
    Tendsto (fun M => physical (modes M) i (history seed time)) atTop
      (𝓝 (synthesis i (history seed time))) := value_tendsto i (history seed time)

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i : Coordinate) :
    HasDerivAt (fun t => synthesis i (history seed t)) (synthesis i (rate seed time)) time :=
  (synthesis i).hasFDerivAt.comp_hasDerivAt time (NativeWindowAbsoluteTimeSource.source_hasDerivAt seed time)

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i : Coordinate) :
    ‖synthesis i (history seed time)‖≤NativeUnifiedCompleteSource.budget seed := by
  apply (value_norm i _).trans
  rw [← NativeWindowAbsoluteTimeBridge.source_map,NativeWindowAbsoluteTimeIsometry.norm_map]
  exact NativeWindowTraceWholeHistory.history_bound seed time

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalCompletion
