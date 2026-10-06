import NormalizedSourceBet
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

set_option autoImplicit false
open Lean Elab Command

namespace P23.ObservableClosure.SourceCompression.Certification
open P23.ObservableClosure.ContrastSource
open P23.ObservableClosure.ContrastSource.Consumer

noncomputable section

theorem unbiased_support (q : ProbabilityLaw) : support 0 q=CH q/4 := by
  norm_num [support,pLower,settingExcess]
  ring

theorem first_grid : fixedScale 0=(1:ℝ)/2 := by norm_num [fixedScale]
theorem last_grid : fixedScale 19=(1:ℝ)/1048576 := by norm_num [fixedScale]

theorem original_predictability_vertex (q : ProbabilityLaw) :
    ∃ settings : Settings (3/1000:ℝ), drift settings q=support (3/1000) q :=
  support_attained (by norm_num) (by norm_num) q

theorem positive_cut_readback {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (cut : ℝ) (hcut : 0 < cut) (hsource : cut < support eps q) : 0 < CH q := by
  by_contra h
  have hs := nonpositive_CH_support settings.eps_nonneg settings.eps_lt_one q (le_of_not_gt h)
  linarith

theorem source_cut_consumes_generated_law (s : P23.ObservableClosure.Snapshot)
    (N : ℕ) (bg : Background) (a0 a1 b0 b1 eps cut : ℝ)
    (settings : Settings eps) (hcut : 0 < cut)
    (hsource : cut < support eps (sourceLaw s N bg a0 a1 b0 b1)) :
    0 < CH (sourceLaw s N bg a0 a1 b0 b1) :=
  positive_cut_readback settings _ cut hcut hsource

theorem both_feature (q : ProbabilityLaw) (i : Fin 4) :
    conditionalFeature q i 0=(q.cells i).both := by simp [conditionalFeature]
theorem only_A_feature (q : ProbabilityLaw) (i : Fin 4) :
    conditionalFeature q i 1=(q.cells i).onlyA := by norm_num [conditionalFeature]
theorem only_B_feature (q : ProbabilityLaw) (i : Fin 4) :
    conditionalFeature q i 2=(q.cells i).onlyB := by rfl
theorem neutral_feature (q : ProbabilityLaw) (i : Fin 4) :
    conditionalFeature q i 3=(q.cells i).neither := by rfl
theorem Alice_single_feature (q : ProbabilityLaw) (i : Fin 4) :
    conditionalFeature q i 4=(q.cells i).both+(q.cells i).onlyA := by rfl
theorem Bob_single_feature (q : ProbabilityLaw) (i : Fin 4) :
    conditionalFeature q i 5=(q.cells i).both+(q.cells i).onlyB := by rfl

theorem zero_sampling_bet (q : ProbabilityLaw) (i : Fin 4) (f : Fin 6) :
    conditionalPoissonStep q i f 0=1 := by simp [conditionalPoissonStep]

theorem all_N_full_trial_normalization (s : P23.ObservableClosure.Snapshot)
    (N : ℕ) (bg : Background) (a0 a1 b0 b1 eps : ℝ)
    (settings : Settings eps) (k : ℕ) :
    let q := sourceLaw s N bg a0 a1 b0 b1
    0 < normalizer eps q (fixedScale k) ∧
    expectation settings q (winFactor eps (fixedScale k)) (lossFactor (fixedScale k))/
      normalizer eps q (fixedScale k) ≤ 1 := by
  have h := source_normalized_fixed_bet s N bg a0 a1 b0 b1 eps settings k
  exact ⟨h.1,h.2.2⟩

end
end P23.ObservableClosure.SourceCompression.Certification

private partial def compressionDependencies (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then compressionDependencies env rest seen
    else
      let children := match env.checked.get.find? name with
        | some info => info.getUsedConstantsAsSet.toArray.toList
        | none => []
      compressionDependencies env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    "P23.ObservableClosure.SourceCompression.".isPrefixOf (privateToUserName name).toString
  let graph := compressionDependencies env (owned.map Prod.fst)
  for required in [``P23.ObservableClosure.ContrastSource.sourceLaw,
    ``P23.ObservableClosure.ContrastSource.Consumer.expectation_readback,
    ``P23.ObservableClosure.ContrastSource.window_positive,
    ``P23.ObservableClosure.SourceCompression.support_attained,
    ``P23.ObservableClosure.SourceCompression.normalized_one_step,
    ``P23.ObservableClosure.SourceCompression.source_selected_setting_one_step] do
    unless graph.contains required do throwError "SC_MISSING_SOURCE_CONSUMER {required}"
  for name in graph.toArray do
    unless (env.checked.get.find? name).isSome do throwError "SC_UNRESOLVED_DEPENDENCY {name}"
    let label := (privateToUserName name).toString
    if "SaturationMonoid.".isPrefixOf label || "ProbabilityTheory.".isPrefixOf label then
      throwError "SC_NEW_RUNTIME_OR_STOCHASTIC_AUTHORITY {name}"
    logInfo m!"SC_DEP {name}"
  logInfo m!"SC_GRAPH {graph.size}"
  for (name, _) in owned do
    let axioms ← liftCoreM <| Lean.collectAxioms name
    logInfo m!"SC_AXIOMS {name}|{axioms}"
  logInfo m!"SC_OWNED {owned.length}"
