import TrainingChartConsumer
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Independent source-coordinate, interval and full-source consumer audit for tc0001. -/
set_option autoImplicit false
open Lean Elab Command

private partial def chartDependencies (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then chartDependencies env rest seen
    else
      let children := match env.checked.get.find? name with
        | some info => info.getUsedConstantsAsSet.toArray.toList
        | none => []
      chartDependencies env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let inverse := chartDependencies env [``P23.ObservableClosure.TrainingChart.actual_means_recover_chart]
  let intervals := chartDependencies env [``P23.ObservableClosure.TrainingChart.single_membership_iff_polytope]
  let consumer := chartDependencies env [``P23.ObservableClosure.TrainingChart.Consumer.source_generates_full_training_chart]
  let recipe := chartDependencies env [``P23.ObservableClosure.TrainingChart.Consumer.chart_generates_full_training_source]
  let regular := chartDependencies env [``P23.ObservableClosure.TrainingChart.Consumer.full_interval_members_recover_regular_chart]
  let primitive := chartDependencies env [``P23.ObservableClosure.TrainingChart.MeanSeed,
    ``P23.ObservableClosure.TrainingChart.MeanIntervals]
  let actualBody := chartDependencies env [``P23.ObservableClosure.TrainingChart.actualSeed]
  let inverseBody := chartDependencies env [``P23.ObservableClosure.TrainingChart.recoveredRatio,
    ``P23.ObservableClosure.TrainingChart.recoveredZ,
    ``P23.ObservableClosure.TrainingChart.recoveredM,
    ``P23.ObservableClosure.TrainingChart.recoveredX]
  let declarations := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.TrainingChart.".isPrefixOf (privateToUserName name).toString
  let bundle := chartDependencies env (declarations.map Prod.fst)
  let inverseRequired := [``P23.ObservableClosure.TrainingChart.native_mirror_means,
    ``P23.ObservableClosure.TrainingChart.actualSeed,
    ``P23.ObservableClosure.TrainingChart.ratio_denominator_negative,
    ``P23.ObservableClosure.TrainingChart.source_ratio_relation,
    ``P23.ObservableClosure.TrainingChart.recovered_ratio_readback,
    ``P23.ObservableClosure.TrainingChart.recovered_U_readback]
  let intervalRequired := [``P23.ObservableClosure.TrainingChart.native_mean_A_covariance,
    ``P23.ObservableClosure.TrainingChart.mirror_beta_interval_iff,
    ``P23.ObservableClosure.ratio_pos]
  let consumerRequired := [``P23.ObservableClosure.TrainingChart.source_physical_covariance,
    ``P23.ObservableClosure.TrainingChart.single_membership_iff_polytope,
    ``P23.ObservableClosure.TrainingChart.Consumer.full_training_iff_chart,
    ``P23.ObservableClosure.TrainingChart.Consumer.phase_polytope_iff_baseline,
    ``P23.ObservableClosure.TrainingChart.Consumer.original_window_phase_readback,
    ``P23.ObservableClosure.PhaseFiber.with_phase_affine_readback,
    ``P23.ObservableClosure.PhaseFiber.training_qualified_iff_phase,
    ``P23.ObservableClosure.Consumer.generatedWindow,
    ``P23.ObservableClosure.Consumer.windowOutcomes]
  let recipeRequired := [``P23.ObservableClosure.PhaseFiber.generatedSnapshot,
    ``P23.ObservableClosure.PhaseFiber.generated_interference,
    ``P23.ObservableClosure.PhaseFiber.phase_recipe_bounds,
    ``P23.ObservableClosure.TrainingChart.Consumer.full_training_iff_chart]
  let regularRequired := [``P23.ObservableClosure.TrainingChart.interval_members_recover_chart,
    ``P23.ObservableClosure.TrainingChart.actual_means_recover_chart,
    ``P23.ObservableClosure.TrainingChart.training_intervals_exclude_equal_modes,
    ``P23.ObservableClosure.TrainingChart.both_mean_increases_force_z,
    ``P23.ObservableClosure.TrainingChart.both_mean_increases_force_radius]
  for (role, graph, required) in [("inverse", inverse, inverseRequired),
    ("intervals", intervals, intervalRequired), ("consumer", consumer, consumerRequired),
    ("recipe", recipe, recipeRequired), ("regular", regular, regularRequired)] do
    for name in required do
      unless graph.contains name do throwError "MISSING_TRAINING_CHART_DEPENDENCY {role}: {name}"
  let targets := [``P23.ObservableClosure.Snapshot,
    ``P23.ObservableClosure.PhaseFiber.covarianceM,
    ``P23.ObservableClosure.PhaseFiber.covarianceZ,
    ``P23.ObservableClosure.PhaseFiber.covarianceX,
    ``P23.ObservableClosure.PhaseFiber.covarianceR2,
    ``P23.ObservableClosure.TrainingChart.ChartReadback,
    ``P23.ObservableClosure.TrainingChart.SourcePolytope,
    ``P23.ObservableClosure.TrainingChart.PhysicalCovariance,
    ``P23.ObservableClosure.TrainingChart.Consumer.FullTrainingChart]
  for name in targets do
    if primitive.contains name || inverseBody.contains name then
      throwError "COMPLETED_SOURCE_COORDINATE_OR_CHART_IN_INVERSE_INPUT_OR_FORMULA {name}"
  for name in [``P23.ObservableClosure.PhaseFiber.covarianceM,
    ``P23.ObservableClosure.PhaseFiber.covarianceZ,
    ``P23.ObservableClosure.PhaseFiber.covarianceX,
    ``P23.ObservableClosure.TrainingChart.recoveredRatio,
    ``P23.ObservableClosure.TrainingChart.recoveredZ,
    ``P23.ObservableClosure.TrainingChart.ChartReadback,
    ``P23.ObservableClosure.pulse00, ``P23.ObservableClosure.Consumer.windowOutcomes] do
    if actualBody.contains name then throwError "CHART_OR_JOINT_TARGET_PRELOADED_IN_ACTUAL_MEANS {name}"
  for name in bundle.toArray do
    unless (env.checked.get.find? name).isSome do throwError "UNRESOLVED_CHART_DEPENDENCY {name}"
    let label := (privateToUserName name).toString
    if "SaturationMonoid.".isPrefixOf label || "ProbabilityTheory.".isPrefixOf label then
      throwError "ROOT_OR_STATISTICAL_AUTHORITY_IN_TRAINING_CHART {name}"
  for name in [``P23.GaussianWindow.fullBorn, ``P23.GaussianWindow.countPGF,
    ``P23.GaussianWindow.amplitude_normalized] do
    if bundle.contains name then throwError "NEW_INFINITE_BORN_SCOPE_IN_TRAINING_CHART {name}"
  let sourceDeclarations := env.constants.toList.filter fun (name, _) =>
    let label := (privateToUserName name).toString
    "P23.ObservableClosure.".isPrefixOf label || "P23.GaussianWindow.".isPrefixOf label
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in sourceDeclarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_CHART_SOURCE_AXIOMS {name}: {axioms}"
    logInfo m!"TRAINING_CHART_AXIOMS {name}|{axioms}"
  for (role, graph) in [("inverse", inverse), ("intervals", intervals), ("consumer", consumer),
    ("recipe", recipe), ("regular", regular), ("primitive", primitive),
    ("actual_body", actualBody), ("inverse_body", inverseBody), ("bundle", bundle)] do
    for name in graph.toArray do logInfo m!"TRAINING_CHART_DEP {role}|{name}"
    logInfo m!"TRAINING_CHART_GRAPH {role}|{graph.size}"
  logInfo m!"TRAINING_CHART_CERTIFIED declarations={declarations.length} source_declarations={sourceDeclarations.length}"

namespace P23.ObservableClosure.TrainingChart.IndependentCertification

open PhaseFiber
noncomputable section

private def pure : RawSource where
  nH := 2
  nV := 0
  etaA := 1/2
  etaB := 3/4
  delta := 0
  nH_nonneg := by norm_num
  nV_nonneg := by norm_num
  nV_le_nH := by norm_num
  etaA_pos := by norm_num
  etaA_le_one := by norm_num
  etaB_pos := by norm_num
  etaB_le_one := by norm_num

private def pureS : Snapshot := pure.withPhase (1/3) (by norm_num) (by norm_num)
private def a0 : ℝ := Real.pi/4
private def a1 : ℝ := -Real.pi/3
private def exactBounds : MeanIntervals := ⟨1/2,1/2,3/4,3/4,3/4,3/4,9/8,9/8⟩

theorem angle_values : sinDouble a0=1 ∧ sinDouble a1= -Real.sqrt 3/2 ∧
    cosDouble a0=0 ∧ cosDouble a1= -1/2 := by
  have ha : 2*a0=Real.pi/2 := by dsimp [a0]; ring
  have hb : 2*a1= -(2*(Real.pi/3)) := by dsimp [a1]; ring
  refine ⟨?_,?_,?_,?_⟩
  · rw [sinDouble,ha,Real.sin_pi_div_two]
  · rw [sinDouble,hb,Real.sin_neg,Real.sin_two_mul,Real.sin_pi_div_three,
      Real.cos_pi_div_three]
    ring
  · rw [cosDouble,ha,Real.cos_pi_div_two]
  · rw [cosDouble,hb,Real.cos_neg,Real.cos_two_mul,Real.cos_pi_div_three]
    norm_num

theorem regular_angles : 0 < sinDouble a0 ∧ sinDouble a1 < 0 ∧
    cosDouble a1 < cosDouble a0 := by
  rcases angle_values with ⟨hs0,hs1,hc0,hc1⟩
  rw [hs0,hs1,hc0,hc1]
  have ht : 0 < Real.sqrt 3 := by positivity
  constructor
  · norm_num
  constructor
  · nlinarith
  · norm_num

theorem pure_coordinates : covarianceM pureS=1/2 ∧ covarianceZ pureS=1/2 ∧
    covarianceX pureS=0 ∧ ratio pureS=2/3 := by
  norm_num [covarianceM,covarianceZ,covarianceX,covarianceC,h,v,ratio,
    pureS,pure,RawSource.withPhase]

theorem pure_actual_four_means : (actualSeed pureS a0 a1).alpha0=1/2 ∧
    (actualSeed pureS a0 a1).alpha1=3/4 ∧ (actualSeed pureS a0 a1).beta0=3/4 ∧
    (actualSeed pureS a0 a1).beta1=9/8 := by
  rcases pure_coordinates with ⟨hm,hz,hx,hr⟩
  rcases angle_values with ⟨_,_,hc0,hc1⟩
  have h0 := native_mirror_means pureS a0
  have h1 := native_mirror_means pureS a1
  rw [hm,hz,hx,hr,hc0] at h0
  rw [hm,hz,hx,hr,hc1] at h1
  dsimp only [actualSeed]
  constructor
  · nlinarith [h0.1]
  constructor
  · nlinarith [h1.1]
  constructor <;> nlinarith [h0.2,h1.2]

theorem pure_interval_membership : SingleMembership pureS a0 a1 exactBounds := by
  rcases pure_actual_four_means with ⟨h0,h1,h2,h3⟩
  change meanA pureS a0=1/2 at h0
  change meanA pureS a1=3/4 at h1
  change meanB pureS (-a0)=3/4 at h2
  change meanB pureS (-a1)=9/8 at h3
  refine ⟨?_,?_,?_,?_⟩ <;> dsimp [exactBounds] <;>
    simp [h0,h1,h2,h3]

theorem pure_psd_boundary : PhysicalCovariance pureS ∧
    covarianceR2 pureS=covarianceM pureS^2 ∧ pureS.nV=0 := by
  refine ⟨source_physical_covariance pureS,?_,rfl⟩
  rw [covariance_radius]
  norm_num [covarianceC,covarianceM,h,v,pureS,pure,RawSource.withPhase]

theorem pure_mode_regular_chart : Consumer.RegularTrainingReadout pureS a0 a1 := by
  rcases regular_angles with ⟨hs0,hs1,hc⟩
  have hx := training_intervals_exclude_equal_modes pureS a0 a1 exactBounds
    pure_interval_membership (by norm_num [exactBounds]) (by norm_num [exactBounds]) hc
  exact ⟨interval_members_recover_chart pureS a0 a1 exactBounds pure_interval_membership
    hs0 hs1 (by norm_num [exactBounds]) (by norm_num [exactBounds]) hc,hx.1,hx.2⟩

theorem pure_full_training :
    Consumer.FullTrainingMembership pure (1/3) (by norm_num) (by norm_num) a0 a1 exactBounds
      (pulse00 pureS (mirror a0)) (pulse00 pureS (mirror a0))
      (pulse00 pureS (mirror a1)) (pulse00 pureS (mirror a1)) := by
  refine ⟨pure_interval_membership,?_⟩
  exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩

theorem pure_source_full_chart_consumer :
    Consumer.SourceChartReadout pure (1/3) (by norm_num) (by norm_num) a0 a1 exactBounds
      (pulse00 pureS (mirror a0)) (pulse00 pureS (mirror a0))
      (pulse00 pureS (mirror a1)) (pulse00 pureS (mirror a1)) (1/100) (1/100) :=
  Consumer.source_generates_full_training_chart pure (1/3) (by norm_num) (by norm_num)
    a0 a1 exactBounds _ _ _ _ (1/100) (1/100) pure_full_training

theorem pure_chart_returns_training_source :
    ∃ (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1),
    Consumer.FullTrainingMembership pure lam h0 h1 a0 a1 exactBounds
      (pulse00 pureS (mirror a0)) (pulse00 pureS (mirror a0))
      (pulse00 pureS (mirror a1)) (pulse00 pureS (mirror a1)) := by
  let hc := pure_source_full_chart_consumer.chart
  exact ⟨_,_,_,Consumer.chart_generates_full_training_source pure a0 a1 exactBounds
    _ _ _ _ _ hc⟩

private def vacuum : RawSource :=
  { pure with
    nH := 0
    nH_nonneg := by norm_num
    nV_le_nH := by norm_num [pure] }

theorem zero_means_do_not_recover_ratio :
    recoveredRatio (actualSeed vacuum.baseline a0 a1) a0 a1=0 ∧
    ratio vacuum.baseline ≠ 0 := by
  norm_num [recoveredRatio,ratioDenominator,actualSeed,meanA,meanB,ratio,
    vacuum,pure,RawSource.baseline,RawSource.withPhase]

private def equalModes : RawSource :=
  { pure with
    nH := 1
    nV := 1
    nH_nonneg := by norm_num
    nV_nonneg := by norm_num
    nV_le_nH := by norm_num }

theorem equal_modes_keep_inverse_chart : ChartReadback equalModes.baseline a0 a1 ∧
    covarianceR2 equalModes.baseline=0 := by
  rcases regular_angles with ⟨hs0,hs1,hc⟩
  have hb : ∀ b, meanB equalModes.baseline b=3/4 := by
    intro b
    rw [native_mean_B_covariance]
    norm_num [covarianceMean,covarianceM,covarianceZ,covarianceX,covarianceC,h,v,ratio,
      equalModes,pure,RawSource.baseline,RawSource.withPhase]
  refine ⟨actual_means_recover_chart _ a0 a1 hs0 hs1 ?_ ?_ hc,?_⟩
  · rw [hb]; norm_num
  · rw [hb]; norm_num
  · rw [covariance_radius]
    norm_num [covarianceC,h,v,equalModes,pure,RawSource.baseline,RawSource.withPhase]

private def rotated : RawSource := { pure with delta := Real.pi/4 }

theorem rotated_coordinates : covarianceM rotated.baseline=1/2 ∧
    covarianceZ rotated.baseline=0 ∧ covarianceX rotated.baseline=1/2 ∧
    ratio rotated.baseline=2/3 := by
  have hd : 2*(Real.pi/4)=Real.pi/2 := by ring
  norm_num [covarianceM,covarianceZ,covarianceX,covarianceC,h,v,ratio,
    rotated,pure,RawSource.baseline,RawSource.withPhase,hd]

theorem rotated_inverse_recovers_nonzero_x :
    recoveredX (actualSeed rotated.baseline a0 a1) a0 a1=1/2 := by
  rcases regular_angles with ⟨hs0,hs1,hc⟩
  rcases angle_values with ⟨hv0,hv1,hc0,hc1⟩
  rcases rotated_coordinates with ⟨hm,hz,hx,hr⟩
  have h0 := (native_mirror_means rotated.baseline a0).2
  have h1 := (native_mirror_means rotated.baseline a1).2
  rw [hm,hz,hx,hr,hv0,hc0] at h0
  rw [hm,hz,hx,hr,hv1,hc1] at h1
  have ht : Real.sqrt 3 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hb0 : 0 < meanB rotated.baseline (-a0) := by nlinarith
  have hb1 : 0 < meanB rotated.baseline (-a1) := by nlinarith
  exact (actual_means_recover_chart _ a0 a1 hs0 hs1 hb0 hb1 hc).x_eq.trans hx

end
end P23.ObservableClosure.TrainingChart.IndependentCertification

run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.TrainingChart.IndependentCertification.".isPrefixOf
      (privateToUserName name).toString
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_INDEPENDENT_CHART_AXIOMS {name}: {axioms}"
    logInfo m!"TRAINING_CHART_INDEPENDENT_AXIOMS {name}|{axioms}"
  logInfo m!"TRAINING_CHART_INDEPENDENT_CERTIFIED declarations={declarations.length}"
