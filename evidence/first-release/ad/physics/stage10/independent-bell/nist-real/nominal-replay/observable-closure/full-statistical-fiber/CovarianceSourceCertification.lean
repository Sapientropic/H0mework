import CovarianceSourceConsumer
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Independent producer-body, source provenance and boundary audit for cs0001. -/
set_option autoImplicit false
open Lean Elab Command

private partial def covarianceDependencies (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then covarianceDependencies env rest seen
    else
      let children := match env.checked.get.find? name with
        | some info => info.getUsedConstantsAsSet.toArray.toList
        | none => []
      covarianceDependencies env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let primitive := covarianceDependencies env [``P23.ObservableClosure.CovarianceSource.Primitive]
  let axisBody := covarianceDependencies env [``P23.ObservableClosure.CovarianceSource.axis,
    ``P23.ObservableClosure.CovarianceSource.radius]
  let rawBody := covarianceDependencies env [``P23.ObservableClosure.CovarianceSource.rawSource]
  let phaseBody := covarianceDependencies env [``P23.ObservableClosure.CovarianceSource.generatedSnapshot]
  let baseline := covarianceDependencies env [``P23.ObservableClosure.CovarianceSource.baseline_coordinates]
  let consumer := covarianceDependencies env [``P23.ObservableClosure.CovarianceSource.Consumer.primitive_generates_source_and_readouts]
  let intervals := covarianceDependencies env [``P23.ObservableClosure.CovarianceSource.Consumer.generated_single_intervals_iff_tuple]
  let shared := covarianceDependencies env [``P23.ObservableClosure.CovarianceSource.Consumer.generated_shared_phase]
  let boundary := covarianceDependencies env [``P23.ObservableClosure.CovarianceSource.boundary_preserves_all_phases]
  let declarations := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.CovarianceSource.".isPrefixOf (privateToUserName name).toString
  let bundle := covarianceDependencies env (declarations.map Prod.fst)
  let baselineRequired := [``P23.ObservableClosure.CovarianceSource.rawSource,
    ``P23.ObservableClosure.CovarianceSource.axis,
    ``P23.ObservableClosure.CovarianceSource.axis_readback,
    ``P23.ObservableClosure.CovarianceSource.arctan_normalizer,
    ``P23.ObservableClosure.CovarianceSource.radius_sq,
    ``P23.ObservableClosure.CovarianceSource.radius_le_m,
    ``P23.ObservableClosure.CovarianceSource.baseline_hv,
    ``P23.ObservableClosure.PhaseFiber.RawSource.baseline]
  let consumerRequired := [``P23.ObservableClosure.CovarianceSource.generatedSnapshot,
    ``P23.ObservableClosure.CovarianceSource.generated_coordinates,
    ``P23.ObservableClosure.CovarianceSource.baseline_coordinates,
    ``P23.ObservableClosure.CovarianceSource.generated_interference,
    ``P23.ObservableClosure.CovarianceSource.generated_all_cells,
    ``P23.ObservableClosure.CovarianceSource.Consumer.generated_means,
    ``P23.ObservableClosure.CovarianceSource.Consumer.generated_window_readback,
    ``P23.ObservableClosure.PhaseFiber.generatedSnapshot,
    ``P23.ObservableClosure.PhaseFiber.phaseRecipe,
    ``P23.ObservableClosure.PhaseFiber.phase_recipe_bounds,
    ``P23.ObservableClosure.Consumer.generatedWindow,
    ``P23.ObservableClosure.Consumer.windowOutcomes]
  let phaseRequired := [``P23.ObservableClosure.CovarianceSource.rawSource,
    ``P23.ObservableClosure.CovarianceSource.generated_phase_physical,
    ``P23.ObservableClosure.CovarianceSource.baseline_T2,
    ``P23.ObservableClosure.PhaseFiber.physical_phase_iff_square,
    ``P23.ObservableClosure.PhaseFiber.generatedSnapshot]
  let intervalRequired := [``P23.ObservableClosure.TrainingChart.single_membership_iff_polytope,
    ``P23.ObservableClosure.CovarianceSource.Consumer.generated_polytope_iff_tuple,
    ``P23.ObservableClosure.CovarianceSource.generated_coordinates,
    ``P23.ObservableClosure.CovarianceSource.rawSource]
  let sharedRequired := [``P23.ObservableClosure.PhaseFiber.Consumer.shared_phase_relation,
    ``P23.ObservableClosure.CovarianceSource.generated_phase_physical,
    ``P23.ObservableClosure.CovarianceSource.rawSource]
  let boundaryRequired := [``P23.ObservableClosure.CovarianceSource.boundary_pure_mode,
    ``P23.ObservableClosure.CovarianceSource.boundary_zero_T,
    ``P23.ObservableClosure.PhaseFiber.pure_mode_zero_T,
    ``P23.ObservableClosure.PhaseFiber.zero_T_all_phases]
  for (role, graph, required) in [("baseline", baseline, baselineRequired),
    ("consumer", consumer, consumerRequired), ("phase_body", phaseBody, phaseRequired),
    ("intervals", intervals, intervalRequired), ("shared", shared, sharedRequired),
    ("boundary", boundary, boundaryRequired)] do
    for name in required do
      unless graph.contains name do throwError "MISSING_COVARIANCE_SOURCE_DEPENDENCY {role}: {name}"
  for name in [``P23.ObservableClosure.PhaseFiber.RawSource, ``P23.ObservableClosure.Snapshot,
    ``P23.ObservableClosure.Cell, ``P23.ObservableClosure.CovarianceSource.axis,
    ``P23.ObservableClosure.CovarianceSource.radius,
    ``P23.ObservableClosure.CovarianceSource.CoordinatesReadback,
    ``P23.ObservableClosure.CovarianceSource.rawSource,
    ``P23.ObservableClosure.CovarianceSource.generatedSnapshot,
    ``P23.ObservableClosure.TrainingChart.SourcePolytope] do
    if primitive.contains name then throwError "SOURCE_OR_TARGET_PRELOADED_IN_PRIMITIVE_COORDINATES {name}"
  for name in [``P23.ObservableClosure.PhaseFiber.RawSource, ``P23.ObservableClosure.Snapshot,
    ``P23.ObservableClosure.PhaseFiber.covarianceM, ``P23.ObservableClosure.PhaseFiber.covarianceZ,
    ``P23.ObservableClosure.PhaseFiber.covarianceX,
    ``P23.ObservableClosure.CovarianceSource.CoordinatesReadback,
    ``P23.ObservableClosure.CovarianceSource.baseline_coordinates] do
    if axisBody.contains name then throwError "SOURCE_ENDPOINT_OR_TARGET_IN_POLAR_AXIS_RECIPE {name}"
  for name in [``P23.ObservableClosure.Snapshot, ``P23.ObservableClosure.Cell,
    ``P23.ObservableClosure.CovarianceSource.axis_readback,
    ``P23.ObservableClosure.CovarianceSource.CoordinatesReadback,
    ``P23.ObservableClosure.CovarianceSource.baseline_coordinates,
    ``P23.ObservableClosure.CovarianceSource.generatedSnapshot,
    ``P23.ObservableClosure.PhaseFiber.covarianceM, ``P23.ObservableClosure.PhaseFiber.covarianceZ,
    ``P23.ObservableClosure.PhaseFiber.covarianceX,
    ``P23.ObservableClosure.pulse00, ``P23.ObservableClosure.Consumer.windowOutcomes,
    ``P23.ObservableClosure.TrainingChart.SingleMembership,
    ``P23.ObservableClosure.CovarianceSource.Consumer.TuplePolytope] do
    if rawBody.contains name then throwError "FINISHED_SOURCE_READBACK_OR_OBSERVATION_IN_RAW_PRODUCER {name}"
  for name in [``P23.ObservableClosure.Cell, ``P23.ObservableClosure.pulse00,
    ``P23.ObservableClosure.Consumer.windowOutcomes,
    ``P23.ObservableClosure.TrainingChart.SingleMembership,
    ``P23.ObservableClosure.CovarianceSource.Consumer.TuplePolytope] do
    if phaseBody.contains name then throwError "CELL_OR_TRAINING_PRELOADED_IN_PHASE_SOURCE {name}"
  for name in bundle.toArray do
    unless (env.checked.get.find? name).isSome do throwError "UNRESOLVED_COVARIANCE_SOURCE_DEPENDENCY {name}"
    let label := (privateToUserName name).toString
    if "SaturationMonoid.".isPrefixOf label || "ProbabilityTheory.".isPrefixOf label then
      throwError "ROOT_OR_STATISTICAL_AUTHORITY_IN_COVARIANCE_SOURCE {name}"
  for name in [``P23.GaussianWindow.fullBorn, ``P23.GaussianWindow.countPGF,
    ``P23.GaussianWindow.amplitude_normalized] do
    if bundle.contains name then throwError "NEW_INFINITE_BORN_SCOPE_IN_COVARIANCE_SOURCE {name}"
  let sourceDeclarations := env.constants.toList.filter fun (name, _) =>
    let label := (privateToUserName name).toString
    "P23.ObservableClosure.".isPrefixOf label || "P23.GaussianWindow.".isPrefixOf label
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in sourceDeclarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_COVARIANCE_SOURCE_AXIOMS {name}: {axioms}"
    logInfo m!"COVARIANCE_SOURCE_AXIOMS {name}|{axioms}"
  for (role, graph) in [("primitive", primitive), ("axis_body", axisBody), ("raw_body", rawBody),
    ("phase_body", phaseBody), ("baseline", baseline), ("consumer", consumer),
    ("intervals", intervals), ("shared", shared), ("boundary", boundary), ("bundle", bundle)] do
    for name in graph.toArray do logInfo m!"COVARIANCE_SOURCE_DEP {role}|{name}"
    logInfo m!"COVARIANCE_SOURCE_GRAPH {role}|{graph.size}"
  logInfo m!"COVARIANCE_SOURCE_CERTIFIED declarations={declarations.length} source_declarations={sourceDeclarations.length}"

namespace P23.ObservableClosure.CovarianceSource.IndependentCertification

open PhaseFiber TrainingChart
noncomputable section

private def positive : Primitive where
  m := 2
  z := 3/5
  x := 4/5
  r := 2/3
  loss := 1/2
  m_nonneg := by norm_num
  psd := by norm_num
  z_pos := by norm_num
  r_pos := by norm_num
  loss_pos := by norm_num
  loss_le_one := by norm_num
  loss_le_ratio := by norm_num

private def negative : Primitive :=
  { positive with
    x := -4/5
    psd := by norm_num [positive] }

private def pure : Primitive :=
  { positive with
    m := 1
    z := 1
    x := 0
    m_nonneg := by norm_num
    psd := by norm_num
    z_pos := by norm_num }

theorem regular_primitive_domain_nonempty : Nonempty Primitive := ⟨positive⟩

theorem signed_radii : radius positive=1 ∧ radius negative=1 := by
  norm_num [radius,positive,negative]

theorem original_loss_and_occupations : (rawSource positive).etaA=1/2 ∧
    (rawSource positive).etaB=3/4 ∧ (rawSource positive).nH=6 ∧
    (rawSource positive).nV=2 := by
  norm_num [rawSource,radius,positive]

theorem signed_axes_preserve_orientation :
    0 < Real.sin (2*(rawSource positive).delta) ∧
    Real.sin (2*(rawSource negative).delta) < 0 ∧
    0 < Real.cos (2*(rawSource positive).delta) ∧
    0 < Real.cos (2*(rawSource negative).delta) := by
  have hp := axis_readback positive
  have hn := axis_readback negative
  change 0 < Real.sin (2*axis positive) ∧ Real.sin (2*axis negative) < 0 ∧
    0 < Real.cos (2*axis positive) ∧ 0 < Real.cos (2*axis negative)
  rw [hp.1,hp.2,hn.1,hn.2,signed_radii.1,signed_radii.2]
  norm_num [positive,negative]

theorem signed_baseline_x_readback :
    covarianceX (rawSource positive).baseline=4/5 ∧
    covarianceX (rawSource negative).baseline= -4/5 := by
  exact ⟨by simpa [positive] using (baseline_coordinates positive).x_eq,
    by simpa [negative] using (baseline_coordinates negative).x_eq⟩

theorem unit_phases_legal : PhaseDomain positive 1 ∧ PhaseDomain negative (-1) := by
  norm_num [PhaseDomain,primitiveT2,positive,negative]

theorem unit_phases_generate_original_interference :
    interference (CovarianceSource.generatedSnapshot positive 1 unit_phases_legal.1)=1 ∧
    interference (CovarianceSource.generatedSnapshot negative (-1) unit_phases_legal.2)= -1 :=
  ⟨CovarianceSource.generated_interference positive 1 unit_phases_legal.1,
    CovarianceSource.generated_interference negative (-1) unit_phases_legal.2⟩

theorem generated_five_coordinates :
    let s := CovarianceSource.generatedSnapshot positive 1 unit_phases_legal.1
    covarianceM s=2 ∧ covarianceZ s=3/5 ∧ covarianceX s=4/5 ∧ ratio s=2/3 ∧ e s=1/2 := by
  have hc := generated_coordinates positive 1 unit_phases_legal.1
  exact ⟨hc.m_eq,hc.z_eq,hc.x_eq,hc.ratio_eq,hc.loss_eq⟩

theorem mixed_native_T_positive : 0 < T (rawSource positive).baseline := by
  have ht := T_nonneg (rawSource positive).baseline
  have he : T (rawSource positive).baseline^2=63/4 := by
    rw [T_sq,baseline_T2]
    norm_num [primitiveT2,positive]
  nlinarith

theorem signed_k_enters_internal_phase_recipe :
    (CovarianceSource.generatedSnapshot positive 1 unit_phases_legal.1).lam=
      (1-1/T (rawSource positive).baseline)/2 := by
  have ht := ne_of_gt mixed_native_T_positive
  change PhaseFiber.phaseRecipe (rawSource positive) 1=_
  simp [PhaseFiber.phaseRecipe,ht]

theorem pure_source_keeps_zero_V_and_T : (rawSource pure).nV=0 ∧
    T (rawSource pure).baseline=0 := by
  have hp : pure.m^2=pure.z^2+pure.x^2 := by norm_num [pure]
  exact ⟨boundary_pure_mode pure hp,boundary_zero_T pure hp⟩

theorem pure_coordinate_phase_is_zero (k : ℝ) : PhaseDomain pure k ↔ k=0 := by
  have hT : primitiveT2 pure=0 := by norm_num [primitiveT2,pure]
  simp only [PhaseDomain,hT]
  constructor
  · intro hk
    nlinarith [sq_nonneg k]
  · rintro rfl
    norm_num

theorem pure_preserves_every_lawful_lambda (lam mu : ℝ)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hm0 : 0 ≤ mu) (hm1 : mu ≤ 1) :
    ∀ cell, pulse00 ((rawSource pure).withPhase lam hl0 hl1) cell=
      pulse00 ((rawSource pure).withPhase mu hm0 hm1) cell := by
  have hp : pure.m^2=pure.z^2+pure.x^2 := by norm_num [pure]
  exact boundary_preserves_all_phases pure hp lam mu hl0 hl1 hm0 hm1

private def exactBounds : MeanIntervals := ⟨7/5,7/5,6/5,6/5,21/10,21/10,21/5,21/5⟩

theorem exact_tuple_eight_halfspaces :
    CovarianceSource.Consumer.TuplePolytope positive 0 (Real.pi/4) exactBounds := by
  have ha : 2*(Real.pi/4)=Real.pi/2 := by ring
  refine ⟨?_,?_,?_,?_⟩ <;>
    norm_num [CovarianceSource.Consumer.tupleMean,CovarianceSource.Consumer.tupleMirrorMean,
      exactBounds,positive,cosDouble,sinDouble,ha]

theorem original_four_single_intervals_generated :
    SingleMembership (CovarianceSource.generatedSnapshot positive 1 unit_phases_legal.1)
      0 (Real.pi/4) exactBounds :=
  (CovarianceSource.Consumer.generated_single_intervals_iff_tuple positive 1
    unit_phases_legal.1 0 (Real.pi/4) exactBounds).2 exact_tuple_eight_halfspaces

theorem native_mirror_means_keep_signed_x :
    meanA (CovarianceSource.generatedSnapshot positive 1 unit_phases_legal.1) (Real.pi/4)=6/5 ∧
    meanB (CovarianceSource.generatedSnapshot positive 1 unit_phases_legal.1) (-Real.pi/4)=21/5 ∧
    meanA (CovarianceSource.generatedSnapshot negative (-1) unit_phases_legal.2) (Real.pi/4)=14/5 ∧
    meanB (CovarianceSource.generatedSnapshot negative (-1) unit_phases_legal.2) (-Real.pi/4)=9/5 := by
  have hp := CovarianceSource.Consumer.generated_means positive 1 unit_phases_legal.1
    (Real.pi/4) (-Real.pi/4)
  have hn := CovarianceSource.Consumer.generated_means negative (-1) unit_phases_legal.2
    (Real.pi/4) (-Real.pi/4)
  rw [hp.1,hp.2,hn.1,hn.2]
  have ha : 2*(Real.pi/4)=Real.pi/2 := by ring
  have hb : 2*(-Real.pi/4)= -(Real.pi/2) := by ring
  norm_num [CovarianceSource.Consumer.tupleMean,positive,negative,cosDouble,sinDouble,ha,hb]

end
end P23.ObservableClosure.CovarianceSource.IndependentCertification

run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.CovarianceSource.IndependentCertification.".isPrefixOf
      (privateToUserName name).toString
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_INDEPENDENT_COVARIANCE_SOURCE_AXIOMS {name}: {axioms}"
    logInfo m!"COVARIANCE_SOURCE_INDEPENDENT_AXIOMS {name}|{axioms}"
  logInfo m!"COVARIANCE_SOURCE_INDEPENDENT_CERTIFIED declarations={declarations.length}"
