import ContrastConsumer
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Independent source-body, exact-mouth and boundary certification of ct0001. -/
set_option autoImplicit false
open Lean Elab Command

private partial def ctDependencies (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then ctDependencies env rest seen
    else
      let children := match env.checked.get.find? name with
        | some info => info.getUsedConstantsAsSet.toArray.toList
        | none => []
      ctDependencies env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.ContrastSource.".isPrefixOf (privateToUserName name).toString
  let roles := [("primitive",ctDependencies env [``P23.ObservableClosure.Snapshot]),
    ("background",ctDependencies env [``P23.ObservableClosure.ContrastSource.Background]),
    ("source",ctDependencies env [``P23.ObservableClosure.ContrastSource.sourceLaw]),
    ("contrast",ctDependencies env [``P23.ObservableClosure.ContrastSource.source_CH_readback,
      ``P23.ObservableClosure.ContrastSource.loss_outcome_readback]),
    ("consumer",ctDependencies env [``P23.ObservableClosure.ContrastSource.Consumer.source_nonpositive_CH_one_step]),
    ("success",ctDependencies env [``P23.ObservableClosure.ContrastSource.Consumer.relevant_success_bound]),
    ("local",ctDependencies env [``P23.ObservableClosure.ContrastSource.assignmentLaw,
      ``P23.ObservableClosure.ContrastSource.sixteen_assignments_CH_nonpositive,
      ``P23.ObservableClosure.ContrastSource.Consumer.local_assignment_one_step]),
    ("bundle",ctDependencies env (declarations.map Prod.fst))]
  let sourceRequired := [``P23.ObservableClosure.ContrastSource.window_positive,
    ``P23.ObservableClosure.ContrastSource.window_normalized,
    ``P23.ObservableClosure.ContrastSource.window_marginal_A,
    ``P23.ObservableClosure.ContrastSource.window_marginal_B,
    ``P23.ObservableClosure.ContrastSource.source_per_pulse_bounds,
    ``P23.ObservableClosure.ContrastSource.phase_cauchy_left,
    ``P23.ObservableClosure.phase_cauchy,``P23.ObservableClosure.phaseDen_pos,
    ``P23.ObservableClosure.pulse00]
  let consumerRequired := [``P23.ObservableClosure.ContrastSource.sourceLaw,
    ``P23.ObservableClosure.ContrastSource.source_CH_readback,
    ``P23.ObservableClosure.ContrastSource.contrast_CH_readback,
    ``P23.ObservableClosure.ContrastSource.loss_outcome_readback,
    ``P23.ObservableClosure.ContrastSource.Consumer.nonpositive_CH_one_step,
    ``P23.ObservableClosure.ContrastSource.Consumer.weighted_null_bound,
    ``P23.ObservableClosure.ContrastSource.Consumer.expectation_readback,
    ``P23.ObservableClosure.ContrastSource.Consumer.expectation_nonneg]
  for (role, graph) in roles do
    if role="source" then
      for name in sourceRequired do
        unless graph.contains name do throwError "CT_MISSING_SOURCE_PRODUCER {name}"
      for name in [``P23.ObservableClosure.ContrastSource.CH,
        ``P23.ObservableClosure.ContrastSource.win,``P23.ObservableClosure.ContrastSource.loss,
        ``P23.ObservableClosure.ContrastSource.Consumer.Settings,
        ``P23.ObservableClosure.ContrastSource.Consumer.oneStep,
        ``P23.ObservableClosure.ContrastSource.Consumer.qThreshold] do
        if graph.contains name then throwError "CT_STATISTIC_PRELOADED_IN_SOURCE {name}"
    if role="consumer" then
      for name in consumerRequired do
        unless graph.contains name do throwError "CT_MISSING_DIRECT_CONSUMER {name}"
    if role="primitive" || role="background" then
      for name in [``P23.ObservableClosure.ContrastSource.ProbabilityLaw,
        ``P23.ObservableClosure.ContrastSource.CH,
        ``P23.ObservableClosure.ContrastSource.sourceLaw,
        ``P23.ObservableClosure.ContrastSource.Consumer.oneStep,
        ``P23.ObservableClosure.Consumer.generatedWindow] do
        if graph.contains name then throwError "CT_TARGET_PRELOADED_IN_PRIMITIVE {name}"
    for name in graph.toArray do
      unless (env.checked.get.find? name).isSome do throwError "CT_UNRESOLVED_DEPENDENCY {name}"
      let label := (privateToUserName name).toString
      if "SaturationMonoid.".isPrefixOf label || "ProbabilityTheory.".isPrefixOf label then
        throwError "CT_ROOT_OR_STOCHASTIC_AUTHORITY {name}"
      logInfo m!"CT_DEP {role}|{name}"
    logInfo m!"CT_GRAPH {role}|{graph.size}"
  let sourceDeclarations := env.constants.toList.filter fun (name, _) =>
    let label := (privateToUserName name).toString
    "P23.ObservableClosure.".isPrefixOf label || "P23.GaussianWindow.".isPrefixOf label
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for (name, _) in sourceDeclarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "CT_UNAUTHORIZED_AXIOMS {name}: {axioms}"
    logInfo m!"CT_AXIOMS {name}|{axioms}"
  logInfo m!"CT_CERTIFIED declarations={declarations.length} source_declarations={sourceDeclarations.length}"

namespace P23.ObservableClosure.ContrastSource.IndependentCertification
open P23.ObservableClosure P23.ObservableClosure.Consumer
open P23.ObservableClosure.ContrastSource.Consumer
noncomputable section

private def vacuum : Snapshot where
  nH := 0
  nV := 0
  etaA := 1
  etaB := 1/2
  delta := 0
  lam := 1/2
  nH_nonneg := by norm_num
  nV_nonneg := by norm_num
  nV_le_nH := by norm_num
  etaA_pos := by norm_num
  etaA_le_one := by norm_num
  etaB_pos := by norm_num
  etaB_le_one := by norm_num
  lam_nonneg := by norm_num
  lam_le_one := by norm_num

private def balanced : Snapshot where
  nH := 1
  nV := 1
  etaA := 1
  etaB := 1/2
  delta := 0
  lam := 0
  nH_nonneg := by norm_num
  nV_nonneg := by norm_num
  nV_le_nH := by norm_num
  etaA_pos := by norm_num
  etaA_le_one := by norm_num
  etaB_pos := by norm_num
  etaB_le_one := by norm_num
  lam_nonneg := by norm_num
  lam_le_one := by norm_num

private def pure : Snapshot := { balanced with nV:=0,nV_nonneg:=by norm_num,nV_le_nH:=by norm_num [balanced],lam:=1,lam_nonneg:=by norm_num,lam_le_one:=by norm_num }
private def bg0 : Background := ⟨0,0,by norm_num,by norm_num,by norm_num,by norm_num⟩
private def bg1 : Background := ⟨1,1,by norm_num,by norm_num,by norm_num,by norm_num⟩
private def uniform : Settings 0 where
  probabilities := fun _ => 1/4
  eps_nonneg := by norm_num
  eps_lt_one := by norm_num
  bounds := by intro i; norm_num [pLower,pUpper]
  normalized := by norm_num

theorem physical_source_nonempty : Nonempty Snapshot := ⟨balanced⟩
theorem settings_nonempty : Nonempty (Settings 0) := ⟨uniform⟩

theorem zero_pulse_no_click (s : Snapshot) (bg : Background) (cell : Cell) :
    window s 0 bg cell=⟨0,0,0,1⟩ := by ext <;> simp [window]

theorem saturated_background_all_click (s : Snapshot) (cell : Cell) :
    window s 1 bg1 cell=⟨1,0,0,0⟩ := by
  ext <;> simp [window,perPulseA,perPulseB,perPulsePair,bg1]

theorem vacuum_zero_background (N : ℕ) (cell : Cell) :
    window vacuum N bg0 cell=⟨0,0,0,1⟩ := by
  ext <;> norm_num [window,perPulseA,perPulseB,perPulsePair,pulse00,phaseDen,D,kappa,kH,kV,U,V,meanA,meanB,vacuum,bg0]

theorem pure_mode_full_N_positive (N : ℕ) (bg : Background) (cell : Cell) :
    PositiveOutcomes (window pure N bg cell) := window_positive pure N bg cell

theorem full_lambda_domain_preserved (s : Snapshot) (N : ℕ) (bg : Background) (cell : Cell) :
    PositiveOutcomes (window s N bg cell) := window_positive s N bg cell

theorem exact_old_five_readback (s : Snapshot) (bg : Background) (cell : Cell) :
    window s 5 bg cell=generatedWindow s cell bg.alice bg.bob := rfl

theorem exact_source_cell (s : Snapshot) (N : ℕ) (bg : Background) (a0 a1 b0 b1 : ℝ) :
    (sourceLaw s N bg a0 a1 b0 b1).cells 2=window s N bg ⟨a1,b0⟩ := by
  simp [sourceLaw,fourCells]

theorem swapped_loss_labels_rejected :
    let q:=assignmentLaw ⟨true,false,true,false⟩
    loss q=2 ∧ (q.cells 1).onlyB+(q.cells 2).onlyA+(q.cells 3).both=0 := by
  norm_num [loss,assignmentLaw,assignmentCell,deterministicOutcomes,marginalA,marginalB,Fin.ext_iff]

theorem original_epsilon_threshold : qThreshold (3/1000)=1006009/2000018 := by
  rw [threshold_closed_form]
  norm_num

theorem zero_relevant_events :
    weightedWin uniform (assignmentLaw ⟨false,false,false,false⟩)+
      weightedLoss uniform (assignmentLaw ⟨false,false,false,false⟩)=0 := by
  norm_num [weightedWin,weightedLoss,uniform,assignmentLaw,assignmentCell,deterministicOutcomes]

theorem zero_relevant_step_one (p : ℝ) :
    oneStep uniform (assignmentLaw ⟨false,false,false,false⟩) p=1 := by
  norm_num [oneStep,expectation,cellExpectation,uniform,assignmentLaw,assignmentCell,deterministicOutcomes]

theorem null_allows_positive_win :
    CH (assignmentLaw ⟨true,true,true,true⟩)=0 ∧
      weightedWin uniform (assignmentLaw ⟨true,true,true,true⟩)=1/4 := by
  norm_num [CH,weightedWin,uniform,assignmentLaw,assignmentCell,deterministicOutcomes,marginalA,marginalB]

theorem maximum_fixed_bet_boundary :
    0 ≤ oneStep uniform (assignmentLaw ⟨true,true,true,true⟩) 1 ∧
      oneStep uniform (assignmentLaw ⟨true,true,true,true⟩) 1 ≤ 1 :=
  local_assignment_one_step uniform _ 1 (by norm_num [qThreshold,pUpper,pLower]) (by norm_num)

theorem all_sixteen_assignments_consumed (a : Assignment) (p : ℝ)
    (hp0 : 1/2 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ oneStep uniform (assignmentLaw a) p ∧ oneStep uniform (assignmentLaw a) p ≤ 1 := by
  apply local_assignment_one_step uniform a p
  · have ht : qThreshold (0 : ℝ)=1/2 := by norm_num [qThreshold,pUpper,pLower]
    rw [ht]
    exact hp0
  · exact hp1

theorem negative_Gaussian_source : nativeCH balanced 1 bg0 0 0 0 0= -(1/6) := by
  norm_num [nativeCH,window,perPulseA,perPulseB,perPulsePair,pulse00,phaseDen,D,kappa,kH,kV,U,V,meanA,meanB,balanced,bg0]

theorem negative_source_direct_step :
    0 ≤ oneStep uniform (sourceLaw balanced 1 bg0 0 0 0 0) 1 ∧
      oneStep uniform (sourceLaw balanced 1 bg0 0 0 0 0) 1 ≤ 1 := by
  apply source_nonpositive_CH_one_step balanced 1 bg0 0 0 0 0 0 1 uniform
  · norm_num [qThreshold,pUpper,pLower]
  · norm_num
  · rw [negative_Gaussian_source]
    norm_num

theorem balanced_source_other_mass_retained :
    (window balanced 1 bg0 ⟨0,0⟩).onlyA=1/6 := by
  norm_num [window,perPulseA,perPulseB,perPulsePair,pulse00,phaseDen,D,kappa,kH,kV,U,V,meanA,meanB,balanced,bg0]

end
end P23.ObservableClosure.ContrastSource.IndependentCertification

run_cmd do
  let env ← getEnv
  let rows := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.ContrastSource.IndependentCertification.".isPrefixOf
      (privateToUserName name).toString
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for (name, _) in rows do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "CT_UNAUTHORIZED_INDEPENDENT_AXIOMS {name}: {axioms}"
    logInfo m!"CT_INDEPENDENT_AXIOMS {name}|{axioms}"
  logInfo m!"CT_INDEPENDENT_CERTIFIED declarations={rows.length}"
