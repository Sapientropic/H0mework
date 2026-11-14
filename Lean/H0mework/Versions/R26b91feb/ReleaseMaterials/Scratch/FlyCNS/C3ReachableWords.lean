import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ReachableSource

set_option autoImplicit false
namespace FlyCNS.C3Reachable
open C3Successful

def generatedPrefix (m : C3Macro.Material) (seed : Seed) (n : Nat) : Except String Current :=
  generate m (.ok seed.initial) n

theorem generatedPrefix_visit {m : C3Macro.Material} {seed : Seed} {n : Nat} {current : Current}
    (generated : generatedPrefix m seed n=.ok current) : current.original.visit=2+n := by
  have h:=reachable_visit (generate_reachable generated)
  simpa only [seed.visit] using h

theorem generatedPrefix_bound {m : C3Macro.Material} {seed : Seed} {n : Nat} {current : Current}
    (generated : generatedPrefix m seed n=.ok current) : n+2<stateBound := by
  have h:=reachable_visit_bound seed.clock seed.signed_bound (generate_reachable generated)
  have v:=generatedPrefix_visit generated
  unfold stateBound
  omega

theorem generatedPrefix_terminal (m : C3Macro.Material) (seed : Seed) :
    ∃ why,generatedPrefix m seed stateBound=.error why := by
  cases h:generatedPrefix m seed stateBound with
  | error why => exact ⟨why,rfl⟩
  | ok current => have b:=generatedPrefix_bound h;omega

/-- Accepted generatedPrefixes are computed from the original seed. The extra two
addresses retain the original first source error and the illegal-letter error. -/
def indexedState (m : C3Macro.Material) (seed : Seed) (index : Fin (stateBound+2)) : Except String Current :=
  if index.val<stateBound then generatedPrefix m seed index.val
  else if index.val=stateBound then generatedPrefix m seed stateBound
  else .error "operation not admitted at this source incidence"

theorem indexed_ok_below {m : C3Macro.Material} {seed : Seed}
    {index : Fin (stateBound+2)} {current : Current}
    (generated : indexedState m seed index=.ok current) : index.val<stateBound := by
  unfold indexedState at generated
  split at generated
  · assumption
  · split at generated
    · rcases generatedPrefix_terminal m seed with ⟨why,failed⟩
      rw [failed] at generated
      contradiction
    · contradiction

def indexedAction (m : C3Macro.Material) (seed : Seed) (operation : C3Native.Operation)
    (index : Fin (stateBound+2)) : Fin (stateBound+2) :=
  match occurred : indexedState m seed index with
  | .error _ => index
  | .ok current =>
    if C3Native.operationAt current.original.visit=operation then
      ⟨index.val+1,by have below:=indexed_ok_below occurred;omega⟩
    else ⟨stateBound+1,by omega⟩

def effect (m : C3Macro.Material) (operation : C3Native.Operation)
    (current : Except String Current) : Except String Current := do
  let before ← current
  let generated ← C3Successful.action m operation before
  return generated.current

theorem indexed_error_absorbed (m : C3Macro.Material) (seed : Seed)
    (operation : C3Native.Operation) (index : Fin (stateBound+2))
    {why : String} (failed : indexedState m seed index=.error why) :
    indexedState m seed (indexedAction m seed operation index)=effect m operation (indexedState m seed index) := by
  unfold indexedAction
  split
  · simp_all only [effect,bind,Except.bind]
  · simp_all

theorem indexed_ok_prefix {m : C3Macro.Material} {seed : Seed}
    {index : Fin (stateBound+2)} {current : Current}
    (generated : indexedState m seed index=.ok current) : generatedPrefix m seed index.val=.ok current := by
  have below:=indexed_ok_below generated
  simpa only [indexedState,if_pos below] using generated

theorem indexed_action_commutes (m : C3Macro.Material) (seed : Seed)
    (operation : C3Native.Operation) (index : Fin (stateBound+2)) :
    indexedState m seed (indexedAction m seed operation index)=effect m operation (indexedState m seed index) := by
  cases occurred:indexedState m seed index with
  | error why => simpa only [occurred] using indexed_error_absorbed m seed operation index occurred
  | ok before =>
    have original:=indexed_ok_prefix occurred
    have below:=indexed_ok_below occurred
    unfold indexedAction
    split
    next why failed => rw [occurred] at failed;contradiction
    next current accepted =>
      have equal : current=before := Except.ok.inj (accepted.symm.trans occurred)
      subst current
      split
      next legal =>
        have bound:=generatedPrefix_bound original
        have nextBelow:index.val+1≤stateBound := by omega
        by_cases last:index.val+1<stateBound
        · simp only [indexedState,if_pos last]
          simp only [generatedPrefix,generate,bind,pure,Except.bind,Except.pure]
          change (do
            let previous ← generatedPrefix m seed index.val
            let generated ← C3Successful.successor m previous
            pure generated.current)=_
          rw [original]
          simp only [effect,bind,Except.bind]
          rw [← legal]
          rfl
        · have atEnd:index.val+1=stateBound := by omega
          simp only [indexedState,if_neg last,if_pos atEnd]
          rw [← atEnd]
          simp only [generatedPrefix,generate,bind,pure,Except.bind,Except.pure]
          change (do
            let previous ← generatedPrefix m seed index.val
            let generated ← C3Successful.successor m previous
            pure generated.current)=_
          rw [original]
          simp only [effect,bind,Except.bind]
          rw [← legal]
          rfl
      next wrong =>
        have failed:=wrong_letter m before operation wrong
        simp only [indexedState,show ¬stateBound+1<stateBound by omega,
          show stateBound+1≠stateBound by omega,if_false,effect,bind,Except.bind,failed]

def execute (m : C3Macro.Material) : List C3Native.Operation → Except String Current → Except String Current
  | [],current => current
  | operation::rest,current => execute m rest (effect m operation current)

theorem indexed_all_words (m : C3Macro.Material) (seed : Seed) (word : List C3Native.Operation)
    (index : Fin (stateBound+2)) :
    indexedState m seed (SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.WholeRepresentation.runMap
      (indexedAction m seed) word index)=execute m word (indexedState m seed index) := by
  induction word generalizing index with
  | nil => rfl
  | cons operation rest previous =>
    simp only [SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.WholeRepresentation.runMap,execute]
    rw [previous,indexed_action_commutes]

theorem execute_error (m : C3Macro.Material) (word : List C3Native.Operation) (why : String) :
    execute m word (.error why)=.error why := by
  induction word with
  | nil => rfl
  | cons _ _ previous => simpa only [execute,effect,bind,Except.bind] using previous

theorem execute_original (m : C3Macro.Material) (word : List C3Native.Operation) (current : Current) :
    execute m word (.ok current)=C3Successful.word m word current := by
  induction word generalizing current with
  | nil => rfl
  | cons operation rest previous =>
    simp only [execute,effect,C3Successful.word,bind,pure,Except.bind,Except.pure]
    cases h:C3Successful.action m operation current with
    | error why => exact execute_error m rest why
    | ok generated => exact previous generated.current

end FlyCNS.C3Reachable
