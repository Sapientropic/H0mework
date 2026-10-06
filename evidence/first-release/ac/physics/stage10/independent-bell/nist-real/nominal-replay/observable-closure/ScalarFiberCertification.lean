import ScalarFiberConsumer
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Independent certification of source generation from the scalar numerical domain. -/
set_option autoImplicit false
open Lean Elab Command

private partial def scalarDependencies (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then scalarDependencies env rest seen
    else
      let children := match env.checked.get.find? name with
        | some info => info.getUsedConstantsAsSet.toArray.toList
        | none => []
      scalarDependencies env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let mouth := ``P23.ObservableClosure.ScalarFiber.Consumer.source_fiber_generates_seed_and_windows
  let main := scalarDependencies env [mouth]
  let roots := [mouth, ``P23.ObservableClosure.ScalarFiber.generated_interval_readback]
  let bundle := scalarDependencies env roots
  let required := [``P23.ObservableClosure.ScalarFiber.ScaledSource,
    ``P23.ObservableClosure.ScalarFiber.LegalLoss,
    ``P23.ObservableClosure.ScalarFiber.lossSnapshot,
    ``P23.ObservableClosure.ScalarFiber.baseline,
    ``P23.ObservableClosure.ScalarFiber.lossSnapshot_scaled,
    ``P23.ObservableClosure.ScalarFiber.scaledMeanA,
    ``P23.ObservableClosure.ScalarFiber.scaledMeanB,
    ``P23.ObservableClosure.ScalarFiber.lossSnapshot_means,
    ``P23.ObservableClosure.ScalarFiber.baseline_T_pos,
    ``P23.ObservableClosure.ScalarFiber.observedH,
    ``P23.ObservableClosure.ScalarFiber.inferredCoherence,
    ``P23.ObservableClosure.ScalarFiber.PhaseDomain,
    ``P23.ObservableClosure.ScalarFiber.inferred_coherence_bounds,
    ``P23.ObservableClosure.ScalarFiber.inferredLambda,
    ``P23.ObservableClosure.ScalarFiber.inferred_lambda_bounds,
    ``P23.ObservableClosure.ScalarFiber.generatedSnapshot,
    ``P23.ObservableClosure.ScalarFiber.generated_coherence,
    ``P23.ObservableClosure.ScalarFiber.generated_seed_readback,
    ``P23.ObservableClosure.ScalarFiber.observedClosure,
    ``P23.ObservableClosure.ScalarFiber.generated_cell_readback,
    ``P23.ObservableClosure.ScalarFiber.Consumer.predictedFiberWindow,
    ``P23.ObservableClosure.ScalarFiber.Consumer.generated_window_readback,
    ``P23.ObservableClosure.Snapshot, ``P23.ObservableClosure.pulse00,
    ``P23.ObservableClosure.source_H, ``P23.ObservableClosure.E_pos,
    ``P23.ObservableClosure.phaseDen_pos, ``P23.ObservableClosure.phase_cauchy,
    ``P23.ObservableClosure.T_sq, ``P23.ObservableClosure.same_source_cell_closure,
    ``P23.ObservableClosure.Consumer.generatedWindow,
    ``P23.ObservableClosure.Consumer.windowOutcomes]
  for name in required do
    unless main.contains name do throwError "MISSING_SCALAR_DOMAIN_SOURCE_GENERATION_OR_SHARED_CONSUMER {name}"
  let primitive := scalarDependencies env [``P23.ObservableClosure.ScalarFiber.ScaledSource,
    ``P23.ObservableClosure.ScalarFiber.LegalLoss,
    ``P23.ObservableClosure.ScalarFiber.PhaseDomain,
    ``P23.ObservableClosure.ScalarFiber.observedH]
  for name in [``P23.ObservableClosure.pulse00, ``P23.ObservableClosure.source_H,
    ``P23.ObservableClosure.ScalarFiber.inferred_coherence_bounds,
    ``P23.ObservableClosure.ScalarFiber.inferred_lambda_bounds,
    ``P23.ObservableClosure.ScalarFiber.generatedSnapshot,
    ``P23.ObservableClosure.ScalarFiber.generated_seed_readback,
    ``P23.ObservableClosure.ScalarFiber.generated_cell_readback,
    ``P23.ObservableClosure.ScalarFiber.generated_interval_readback,
    ``P23.ObservableClosure.ScalarFiber.Consumer.source_fiber_generates_seed_and_windows] do
    if primitive.contains name then throwError "COMPLETED_SEED_ENDPOINT_OR_SOURCE_CERTIFICATE_IN_DOMAIN {name}"
  for name in bundle.toArray do
    let label := (privateToUserName name).toString
    if "SaturationMonoid.".isPrefixOf label || "ProbabilityTheory.".isPrefixOf label then
      throwError "ROOT_OR_PROBABILITY_AUTHORITY_IN_SCALAR_SOURCE_ALGEBRA {name}"
  for name in [``P23.GaussianWindow.countPGF, ``P23.GaussianWindow.countPGF_eq,
    ``P23.GaussianWindow.fullBorn, ``P23.ObservableClosure.nativeKernel] do
    if main.contains name then throwError "UNEXPECTED_FULL_BORN_OR_NATIVE_MAPPING_SCOPE {name}"
  let declarations := env.constants.toList.filter fun (name, _) =>
    let label := (privateToUserName name).toString
    "P23.ObservableClosure.".isPrefixOf label || "P23.GaussianWindow.".isPrefixOf label
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_SCALAR_SOURCE_AXIOMS {name}: {axioms}"
  logInfo m!"SCALAR_SOURCE_CERTIFIED declarations={declarations.length} main_nodes={main.size} bundle_nodes={bundle.size} required={required.length} primitive={primitive.size}"
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"SCALAR_SOURCE_AXIOMS {root}: {axioms}"

namespace P23.ObservableClosure.ScalarFiber.IndependentCertification
noncomputable section

private def scaled : ScaledSource where
  h := 3/16
  v := 1/12
  r := 9/8
  delta := 0
  v_pos := by norm_num
  v_lt_h := by norm_num
  r_pos := by norm_num

private theorem legal : LegalLoss scaled (3/4) := by
  constructor <;> norm_num [scaled]

private def seed : Cell := mirror (Real.pi/4)
private def base : Snapshot := baseline scaled (3/4) legal
private theorem twiceQuarter : 2*(Real.pi/4)=Real.pi/2 := by ring

theorem informative_seed : g base seed ≠ 0 := by
  rw [seed,mirror_g,twiceQuarter]
  norm_num [base,baseline,lossSnapshot,scaled,ratio]

private def middleObservation : ℝ := L base seed (3/4)/E base seed (3/4)

theorem middle_observed_H_zero : observedH scaled (3/4) legal seed middleObservation=0 := by
  change (L base seed (3/4)/E base seed (3/4))*E base seed (3/4)-L base seed (3/4)=0
  have he : E base seed (3/4) ≠ 0 := ne_of_gt (E_pos base seed)
  rw [div_mul_cancel₀ _ he]
  ring

theorem nonempty_phase_domain : PhaseDomain scaled (3/4) legal seed middleObservation := by
  dsimp only [PhaseDomain]
  rw [middle_observed_H_zero]
  simpa [base] using mul_nonneg (sq_nonneg (g base seed)) (sq_nonneg (T base))

theorem inferred_half_phase : inferredLambda scaled (3/4) legal seed middleObservation=1/2 := by
  rw [inferredLambda,inferredCoherence,middle_observed_H_zero]
  norm_num

theorem generated_physical_snapshot :
    let snap := generatedSnapshot scaled (3/4) legal seed middleObservation informative_seed nonempty_phase_domain
    snap.nH=1/4 ∧ snap.nV=1/9 ∧ snap.etaA=3/4 ∧ snap.etaB=2/3 ∧ snap.lam=1/2 := by
  change scaled.h/(3/4)=1/4 ∧ scaled.v/(3/4)=1/9 ∧ (3/4:ℝ)=3/4 ∧
    (3/4:ℝ)/scaled.r=2/3 ∧ inferredLambda scaled (3/4) legal seed middleObservation=1/2
  rw [inferred_half_phase]
  norm_num [scaled]

theorem generated_seed_and_all_windows :
    pulse00 (generatedSnapshot scaled (3/4) legal seed middleObservation informative_seed nonempty_phase_domain)
      seed=middleObservation ∧
    ∀ cell bgA bgB,
      P23.ObservableClosure.Consumer.generatedWindow
        (generatedSnapshot scaled (3/4) legal seed middleObservation informative_seed nonempty_phase_domain)
        cell bgA bgB=Consumer.predictedFiberWindow scaled (3/4) legal seed cell middleObservation bgA bgB :=
  ⟨generated_seed_readback scaled (3/4) legal seed middleObservation informative_seed nonempty_phase_domain,
    fun cell bgA bgB => Consumer.generated_window_readback scaled (3/4) legal seed middleObservation
      informative_seed nonempty_phase_domain cell bgA bgB⟩

theorem zero_loss_is_not_legal : ¬ LegalLoss scaled 0 := by
  intro h
  have hp := h.positive
  norm_num at hp

private theorem otherLegal : LegalLoss scaled (1/2) := by
  constructor <;> norm_num [scaled]

theorem distinct_loss_identical_means (a b : ℝ) :
    meanA base a=meanA (baseline scaled (1/2) otherLegal) a ∧
    meanB base b=meanB (baseline scaled (1/2) otherLegal) b := by
  have h0 := lossSnapshot_means scaled (3/4) legal 0 (by norm_num) (by norm_num) a b
  have h1 := lossSnapshot_means scaled (1/2) otherLegal 0 (by norm_num) (by norm_num) a b
  exact ⟨h0.1.trans h1.1.symm,h0.2.trans h1.2.symm⟩

private def outsideObservation : ℝ := (L base seed (3/4)+2*g base seed*T base)/E base seed (3/4)

theorem outside_observed_H : observedH scaled (3/4) legal seed outsideObservation=2*g base seed*T base := by
  change ((L base seed (3/4)+2*g base seed*T base)/E base seed (3/4))*
    E base seed (3/4)-L base seed (3/4)=2*g base seed*T base
  have he : E base seed (3/4) ≠ 0 := ne_of_gt (E_pos base seed)
  rw [div_mul_cancel₀ _ he]
  ring

theorem phase_violation_is_excluded : ¬ PhaseDomain scaled (3/4) legal seed outsideObservation := by
  intro hp
  have hd := mul_ne_zero informative_seed (ne_of_gt (baseline_T_pos scaled (3/4) legal))
  have hsq : 0 < (g base seed*T base)^2 := sq_pos_of_ne_zero hd
  dsimp only [PhaseDomain] at hp
  rw [outside_observed_H] at hp
  change (2*g base seed*T base)^2 ≤ g base seed^2*T base^2 at hp
  nlinarith

end
end P23.ObservableClosure.ScalarFiber.IndependentCertification

run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.ScalarFiber.IndependentCertification.".isPrefixOf (privateToUserName name).toString
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_INDEPENDENT_SCALAR_AXIOMS {name}: {axioms}"
  logInfo m!"SCALAR_SOURCE_INDEPENDENT_AXIOMS declarations={declarations.length}"
