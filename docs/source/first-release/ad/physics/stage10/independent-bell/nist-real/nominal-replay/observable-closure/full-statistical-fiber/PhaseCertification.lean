import PhaseConsumer
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Independent exact-mouth, source-body and boundary audit for pf0001. -/
set_option autoImplicit false
open Lean Elab Command

private partial def phaseDependencies (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then phaseDependencies env rest seen
    else
      let children := match env.checked.get.find? name with
        | some info => info.getUsedConstantsAsSet.toArray.toList
        | none => []
      phaseDependencies env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let mouth := phaseDependencies env [``P23.ObservableClosure.PhaseFiber.complete_phase_fiber]
  let consumer := phaseDependencies env
    [``P23.ObservableClosure.PhaseFiber.Consumer.generates_training_and_all_windows]
  let primitive := phaseDependencies env [``P23.ObservableClosure.PhaseFiber.RawSource]
  let body := phaseDependencies env [``P23.ObservableClosure.PhaseFiber.generatedSnapshot]
  let declarations := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.PhaseFiber.".isPrefixOf (privateToUserName name).toString
  let bundle := phaseDependencies env (declarations.map Prod.fst)
  let mouthRequired := [``P23.ObservableClosure.PhaseFiber.RawSource.withPhase,
    ``P23.ObservableClosure.PhaseFiber.phaseRecipe,
    ``P23.ObservableClosure.PhaseFiber.phase_recipe_bounds,
    ``P23.ObservableClosure.PhaseFiber.generated_interference,
    ``P23.ObservableClosure.PhaseFiber.training_qualified_iff_phase,
    ``P23.ObservableClosure.PhaseFiber.with_phase_affine_readback,
    ``P23.ObservableClosure.E_pos, ``P23.ObservableClosure.source_H]
  let consumerRequired := [``P23.ObservableClosure.PhaseFiber.generatedSnapshot,
    ``P23.ObservableClosure.PhaseFiber.generated_all_cells,
    ``P23.ObservableClosure.PhaseFiber.generated_interference,
    ``P23.ObservableClosure.PhaseFiber.training_qualified_iff_phase,
    ``P23.ObservableClosure.PhaseFiber.Consumer.generated_window_readback,
    ``P23.ObservableClosure.PhaseFiber.Consumer.generated_marginals,
    ``P23.ObservableClosure.Consumer.generatedWindow,
    ``P23.ObservableClosure.Consumer.windowOutcomes]
  for name in mouthRequired do
    unless mouth.contains name do throwError "MISSING_PHASE_FIBER_MOUTH_DEPENDENCY {name}"
  for name in consumerRequired do
    unless consumer.contains name do throwError "MISSING_PHASE_FIBER_DIRECT_CONSUMER {name}"
  for name in [``P23.ObservableClosure.Snapshot, ``P23.ObservableClosure.Cell,
    ``P23.ObservableClosure.pulse00, ``P23.ObservableClosure.PhaseFiber.PhysicalPhase,
    ``P23.ObservableClosure.PhaseFiber.Slab, ``P23.ObservableClosure.PhaseFiber.TrainingQualified,
    ``P23.ObservableClosure.PhaseFiber.PhaseQualified,
    ``P23.ObservableClosure.PhaseFiber.generatedSnapshot] do
    if primitive.contains name then throwError "COMPLETED_TARGET_IN_RAW_PHASE_SOURCE {name}"
  for name in [``P23.ObservableClosure.Cell, ``P23.ObservableClosure.pulse00,
    ``P23.ObservableClosure.E, ``P23.ObservableClosure.L, ``P23.ObservableClosure.source_H,
    ``P23.ObservableClosure.PhaseFiber.Slab, ``P23.ObservableClosure.PhaseFiber.TrainingQualified,
    ``P23.ObservableClosure.PhaseFiber.PhaseQualified,
    ``P23.ObservableClosure.PhaseFiber.complete_phase_fiber,
    ``P23.ObservableClosure.Consumer.windowOutcomes,
    ``P23.ObservableClosure.PhaseFiber.Consumer.phaseWindow] do
    if body.contains name then throwError "WINDOW_OR_TRAINING_TARGET_PRELOADED_IN_PHASE_BODY {name}"
  for name in bundle.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "UNRESOLVED_PHASE_DEPENDENCY {name}"
    let label := (privateToUserName name).toString
    if "SaturationMonoid.".isPrefixOf label || "ProbabilityTheory.".isPrefixOf label then
      throwError "ROOT_OR_STATISTICAL_AUTHORITY_IN_PHASE_FIBER {name}"
  for name in [``P23.GaussianWindow.fullBorn, ``P23.GaussianWindow.countPGF,
    ``P23.GaussianWindow.amplitude_normalized] do
    if bundle.contains name then throwError "NEW_INFINITE_BORN_SCOPE_IN_PHASE_FIBER {name}"
  let sourceDeclarations := env.constants.toList.filter fun (name, _) =>
    let label := (privateToUserName name).toString
    "P23.ObservableClosure.".isPrefixOf label || "P23.GaussianWindow.".isPrefixOf label
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in sourceDeclarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_PHASE_SOURCE_AXIOMS {name}: {axioms}"
    logInfo m!"PHASE_FIBER_AXIOMS {name}|{axioms}"
  for (role, graph) in [("mouth", mouth), ("consumer", consumer),
    ("primitive", primitive), ("body", body), ("bundle", bundle)] do
    for name in graph.toArray do logInfo m!"PHASE_FIBER_DEP {role}|{name}"
  logInfo m!"PHASE_FIBER_CERTIFIED declarations={declarations.length} source_declarations={sourceDeclarations.length} mouth_nodes={mouth.size} consumer_nodes={consumer.size} primitive_nodes={primitive.size} body_nodes={body.size} bundle_nodes={bundle.size} required_mouth={mouthRequired.length} required_consumer={consumerRequired.length}"

namespace P23.ObservableClosure.PhaseFiber.IndependentCertification

noncomputable section

private def vacuum : RawSource where
  nH := 0
  nV := 0
  etaA := 1/2
  etaB := 3/4
  delta := 2/7
  nH_nonneg := by norm_num
  nV_nonneg := by norm_num
  nV_le_nH := by norm_num
  etaA_pos := by norm_num
  etaA_le_one := by norm_num
  etaB_pos := by norm_num
  etaB_le_one := by norm_num

private def mixed : RawSource where
  nH := 2
  nV := 1
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

theorem raw_source_nonempty : Nonempty RawSource := ⟨vacuum⟩

theorem mixed_T_positive : 0 < T mixed.baseline := by
  dsimp [T,ratio,kH,kV,RawSource.baseline,RawSource.withPhase,mixed]
  positivity

theorem mixed_endpoints_generated :
    phaseRecipe mixed (T mixed.baseline)=0 ∧
    phaseRecipe mixed (-T mixed.baseline)=1 := by
  have ht := ne_of_gt mixed_T_positive
  simp [phaseRecipe,ht]

theorem out_of_range_rejected (raw : RawSource) :
    ¬ PhysicalPhase raw (T raw.baseline+1) := by
  intro hk
  have hhi := hk.2
  linarith

theorem pure_mode_preserves_distinct_phases (raw : RawSource) (hv : raw.nV=0) :
    raw.withPhase 0 (by norm_num) (by norm_num) ≠
      raw.withPhase 1 (by norm_num) (by norm_num) ∧
    ∀ cell, pulse00 (raw.withPhase 0 (by norm_num) (by norm_num)) cell=
      pulse00 (raw.withPhase 1 (by norm_num) (by norm_num)) cell := by
  constructor
  · intro heq
    have h := congrArg Snapshot.lam heq
    norm_num [RawSource.withPhase] at h
  · exact zero_T_all_phases raw (pure_mode_zero_T raw hv) 0 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem source_axis_zero_g (raw : RawSource) (b : ℝ) :
    g raw.baseline ⟨raw.delta,b⟩=0 := by
  simp [g,U,RawSource.baseline,RawSource.withPhase]

theorem source_axis_slab_retained (raw : RawSource) (b lo hi k : ℝ) :
    Slab raw ⟨raw.delta,b⟩ lo hi k ↔
      lo*E raw.baseline ⟨raw.delta,b⟩ (e raw.baseline) ≤
        L raw.baseline ⟨raw.delta,b⟩ (e raw.baseline) ∧
      L raw.baseline ⟨raw.delta,b⟩ (e raw.baseline) ≤
        hi*E raw.baseline ⟨raw.delta,b⟩ (e raw.baseline) := by
  dsimp [Slab]
  rw [source_axis_zero_g,zero_mul]
  constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith

theorem vacuum_affine_one (cell : Cell) : affinePulse vacuum cell 0=1 := by
  norm_num [affinePulse,L,D,E,T2,meanA,meanB,h,v,e,ratio,
    RawSource.baseline,RawSource.withPhase,vacuum]

theorem degenerate_training_nonempty (cell0 cell1 : Cell) :
    PhaseQualified vacuum cell0 cell1 1 1 1 1 0 := by
  refine ⟨?_,?_,?_⟩
  · have ht : T vacuum.baseline=0 := pure_mode_zero_T vacuum (by rfl)
    exact (zero_T_physical_iff vacuum ht 0).2 rfl
  · apply (affine_interval_iff_slab vacuum cell0 1 1 0).1
    rw [vacuum_affine_one]
    exact ⟨le_rfl,le_rfl⟩
  · apply (affine_interval_iff_slab vacuum cell1 1 1 0).1
    rw [vacuum_affine_one]
    exact ⟨le_rfl,le_rfl⟩

theorem incompatible_training_rejected (cell0 cell1 : Cell) :
    ¬ PhaseQualified vacuum cell0 cell1 2 3 1 1 0 := by
  intro hq
  have hlo := ((affine_interval_iff_slab vacuum cell0 2 3 0).2 hq.first).1
  rw [vacuum_affine_one] at hlo
  norm_num at hlo

theorem mixed_covariance_chart_nonzero : covarianceR2 mixed.baseline ≠ 0 := by
  rw [covariance_radius]
  norm_num [covarianceC,h,v,RawSource.baseline,RawSource.withPhase,mixed]

theorem vacuum_covariance_chart_zero : covarianceR2 vacuum.baseline=0 := by
  rw [covariance_radius]
  norm_num [covarianceC,h,v,RawSource.baseline,RawSource.withPhase,vacuum]

end
end P23.ObservableClosure.PhaseFiber.IndependentCertification

run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.PhaseFiber.IndependentCertification.".isPrefixOf
      (privateToUserName name).toString
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_INDEPENDENT_PHASE_AXIOMS {name}: {axioms}"
    logInfo m!"PHASE_FIBER_INDEPENDENT_AXIOMS {name}|{axioms}"
  logInfo m!"PHASE_FIBER_INDEPENDENT_CERTIFIED declarations={declarations.length}"
