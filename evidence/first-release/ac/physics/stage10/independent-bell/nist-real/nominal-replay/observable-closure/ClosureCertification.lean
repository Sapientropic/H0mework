import ClosureConsumer
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Independent trust audit of source-forward arithmetic for the named pulse law. -/
set_option autoImplicit false

open Lean Elab Command

private partial def closureDependencies (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then closureDependencies env rest seen
    else
      let children := match env.checked.get.find? name with
        | some info => info.getUsedConstantsAsSet.toArray.toList
        | none => []
      closureDependencies env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let mouth := ``P23.ObservableClosure.Consumer.shared_training_root_and_heldout
  let main := closureDependencies env [mouth]
  let roots := [mouth, ``P23.ObservableClosure.native_mean_readback,
    ``P23.ObservableClosure.snapshot_scaled_readback,
    ``P23.ObservableClosure.Consumer.outcomes_sum_one]
  let bundle := closureDependencies env roots
  let required := [``P23.ObservableClosure.Snapshot, ``P23.ObservableClosure.Cell,
    ``P23.ObservableClosure.U, ``P23.ObservableClosure.V,
    ``P23.ObservableClosure.meanA, ``P23.ObservableClosure.meanB,
    ``P23.ObservableClosure.D, ``P23.ObservableClosure.kH, ``P23.ObservableClosure.kV,
    ``P23.ObservableClosure.kappa, ``P23.ObservableClosure.phaseDen,
    ``P23.ObservableClosure.pulse00, ``P23.ObservableClosure.two_term_cauchy,
    ``P23.ObservableClosure.phase_cauchy, ``P23.ObservableClosure.phaseDen_pos,
    ``P23.ObservableClosure.kH_scaled_sq, ``P23.ObservableClosure.kV_scaled_sq,
    ``P23.ObservableClosure.T, ``P23.ObservableClosure.T2, ``P23.ObservableClosure.T_sq,
    ``P23.ObservableClosure.g, ``P23.ObservableClosure.L, ``P23.ObservableClosure.E,
    ``P23.ObservableClosure.H, ``P23.ObservableClosure.phaseDen_scaled,
    ``P23.ObservableClosure.E_factor, ``P23.ObservableClosure.E_pos,
    ``P23.ObservableClosure.source_H, ``P23.ObservableClosure.L_affine,
    ``P23.ObservableClosure.Quadratic.polynomial,
    ``P23.ObservableClosure.Quadratic.degree_le,
    ``P23.ObservableClosure.hQuadratic, ``P23.ObservableClosure.hQuadratic_value,
    ``P23.ObservableClosure.linearCombination, ``P23.ObservableClosure.combination_value,
    ``P23.ObservableClosure.trainingF, ``P23.ObservableClosure.same_source_quadratic_root,
    ``P23.ObservableClosure.closurePulse, ``P23.ObservableClosure.same_source_cell_closure,
    ``P23.ObservableClosure.cellRelation, ``P23.ObservableClosure.same_source_cell_relation,
    ``P23.ObservableClosure.sylvester, ``P23.ObservableClosure.common_root_sylvester_zero,
    ``P23.ObservableClosure.source_resultant_necessary,
    ``Matrix.exists_mulVec_eq_zero_iff,
    ``P23.ObservableClosure.mirror_U, ``P23.ObservableClosure.mirror_V,
    ``P23.ObservableClosure.mirror_g, ``P23.ObservableClosure.mirror_training_informative,
    ``P23.ObservableClosure.Consumer.windowOutcomes,
    ``P23.ObservableClosure.Consumer.generatedWindow,
    ``P23.ObservableClosure.Consumer.predictedWindow,
    ``P23.ObservableClosure.Consumer.same_source_all_cells]
  for name in required do
    unless main.contains name do throwError "MISSING_NAMED_SOURCE_ELIMINATION_OR_COMMON_CONSUMER {name}"
  for name in [``P23.ObservableClosure.nativeKernel, ``P23.GaussianWindow.RawKernel,
    ``P23.GaussianWindow.meanNumber] do
    unless bundle.contains name do throwError "MISSING_SEPARATE_NATIVE_SOURCE_MAPPING {name}"
  let primitive := closureDependencies env [``P23.ObservableClosure.Snapshot,
    ``P23.ObservableClosure.Cell, ``P23.ObservableClosure.Quadratic,
    ``P23.ObservableClosure.Consumer.Outcomes]
  for name in [``P23.ObservableClosure.pulse00, ``P23.ObservableClosure.H,
    ``P23.ObservableClosure.trainingF, ``P23.ObservableClosure.source_H,
    ``P23.ObservableClosure.closurePulse, ``P23.ObservableClosure.same_source_quadratic_root,
    ``P23.ObservableClosure.Consumer.generatedWindow,
    ``P23.ObservableClosure.Consumer.shared_training_root_and_heldout] do
    if primitive.contains name then throwError "TARGET_READOUT_OR_ROOT_IN_SOURCE_PRIMITIVE {name}"
  for name in main.toArray do
    let label := (privateToUserName name).toString
    if "SaturationMonoid.".isPrefixOf label || "ProbabilityTheory.".isPrefixOf label then
      throwError "ROOT_OR_STATISTICAL_AUTHORITY_IN_NAMED_LAW_ARITHMETIC {name}"
  for name in [``P23.ObservableClosure.nativeKernel, ``P23.GaussianWindow.countPGF,
    ``P23.GaussianWindow.countPGF_eq, ``P23.GaussianWindow.fullBorn] do
    if main.contains name then throwError "UNEXPECTED_BORN_OR_NATIVE_MAPPING_SCOPE_CHANGE {name}"
  let declarations := env.constants.toList.filter fun (name, _) =>
    let label := (privateToUserName name).toString
    "P23.ObservableClosure.".isPrefixOf label || "P23.GaussianWindow.".isPrefixOf label
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_OBSERVABLE_CLOSURE_AXIOMS {name}: {axioms}"
  logInfo m!"OBSERVABLE_CLOSURE_CERTIFIED declarations={declarations.length} main_nodes={main.size} bundle_nodes={bundle.size} required={required.length} primitive={primitive.size}"
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"OBSERVABLE_CLOSURE_AXIOMS {root}: {axioms}"

namespace P23.ObservableClosure.IndependentCertification

noncomputable section

private def fixture : Snapshot where
  nH := 1/4
  nV := 1/9
  etaA := 3/4
  etaB := 2/3
  delta := 0
  lam := 3/5
  nH_nonneg := by norm_num
  nV_nonneg := by norm_num
  nV_le_nH := by norm_num
  etaA_pos := by norm_num
  etaA_le_one := by norm_num
  etaB_pos := by norm_num
  etaB_le_one := by norm_num
  lam_nonneg := by norm_num
  lam_le_one := by norm_num

theorem nonempty_native_kernel :
    (nativeKernel fixture).tH=1/5 ∧ (nativeKernel fixture).tV=1/10 := by
  norm_num [nativeKernel,fixture]

theorem legal_negative_coherence : coherence fixture= -1/5 ∧ 1/2 < fixture.lam := by
  norm_num [coherence,fixture]

theorem actual_scaled_root :
    e fixture=3/4 ∧ ratio fixture=9/8 ∧ h fixture=3/16 ∧ v fixture=1/12 := by
  norm_num [e,ratio,h,v,fixture]

theorem actual_coherence_square : T fixture^2=25/2048 := by
  rw [T_sq]
  norm_num [T2,h,v,e,fixture]

private theorem twiceQuarter : 2*(Real.pi/4)=Real.pi/2 := by ring

theorem raw_angle_contrast : Real.cos (2*(0:ℝ))^2 ≠ Real.cos (2*(Real.pi/4))^2 := by
  rw [twiceQuarter]
  norm_num

theorem first_mirror_seed_uninformative : g fixture (mirror 0)=0 := by
  norm_num [g,U,V,mirror,fixture]

theorem fallback_mirror_seed_informative : g fixture (mirror (Real.pi/4))= -4/9 := by
  rw [mirror_g,twiceQuarter]
  norm_num [fixture,ratio]

theorem nonempty_common_source_consumer :
    (trainingF fixture (mirror 0) (mirror (Real.pi/4))).polynomial.eval (e fixture)=0 ∧
    ∀ bgA bgB cell, Consumer.predictedWindow fixture (mirror (Real.pi/4)) cell bgA bgB=
      Consumer.generatedWindow fixture cell bgA bgB := by
  refine ⟨(same_source_quadratic_root fixture _ _).2,?_⟩
  intro bgA bgB
  apply Consumer.same_source_all_cells
  rw [fallback_mirror_seed_informative]
  norm_num

theorem coincident_training_keeps_zero_polynomial (s : Snapshot) (cell : Cell) :
    (trainingF s cell cell).polynomial=0 := by
  simp [trainingF,linearCombination,Quadratic.polynomial]

private def noRealRoot : Quadratic := ⟨1,0,1⟩

theorem necessary_resultant_is_not_sufficient :
    (sylvester noRealRoot noRealRoot).det=0 ∧ ¬ ∃ x : ℝ, noRealRoot.value x=0 := by
  constructor
  · apply Matrix.det_zero_of_row_eq (show (0:Fin 4) ≠ 2 by decide)
    rfl
  · rintro ⟨x,hx⟩
    dsimp [noRealRoot,Quadratic.value] at hx
    nlinarith [sq_nonneg x]

end
end P23.ObservableClosure.IndependentCertification

run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.IndependentCertification.".isPrefixOf (privateToUserName name).toString
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_INDEPENDENT_CLOSURE_AXIOMS {name}: {axioms}"
  logInfo m!"OBSERVABLE_CLOSURE_INDEPENDENT_AXIOMS declarations={declarations.length}"
