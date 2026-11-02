import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Transport

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Transport

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Normalization Normalization.RawProfile

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input model.source.code) (cut : Nat)
  (raw nextRaw : List (Option model.source.code.Policy))
  (rival nextRival : Opponent model.source.code)
  (observed : ∀ ordinal < Cut.finish model.source input cut,
    ProgrammeSource.rawEvent (normalized model input cut nextRaw nextRival).source.input
      (ProgrammeHistory.visitAt (original model input cut raw rival).source.input ordinal).current =
    ProgrammeSource.rawEvent (original model input cut raw rival).source.input
      (ProgrammeHistory.visitAt (original model input cut raw rival).source.input ordinal).current)
  (terminalState : Residual.run model.source.code (Residual.scheduleAt model.source cut nextRaw)
      ⟨nextRival,input.budget⟩ (Residual.seed model.source input cut) (Cut.horizon model.source input cut) =
    Residual.run model.source.code (Residual.scheduleAt model.source cut raw)
      ⟨rival,input.budget⟩ (Residual.seed model.source input cut) (Cut.horizon model.source input cut))
  (active : model.source.feedback? = some input)

private def archiveIndex {candidate : Machine Party Good Port Technology Instrument}
    {index : Native.Slot candidate} {depth : Nat}
    {state : ResponsibilityLifecycle.ResponsibilityState (Native.V candidate)} : Native.Shape candidate index depth state → Option Nat
  | .live .. => none | .terminal first .. => some first

private def prefixIndex {candidate : Machine Party Good Port Technology Instrument}
    {index : Native.Slot candidate} {depth : Nat} (prior : Native.Prefix candidate index depth) : Option Nat :=
  archiveIndex prior.shape

private theorem first_service_is_prefix_index (candidate : Machine Party Good Port Technology Instrument)
    (index : Native.Slot candidate) (depth : Nat) :
    Identity.firstService candidate depth index = prefixIndex (Native.historyAt candidate index depth) := by
  cases shape : (Native.historyAt candidate index depth).shape <;>
    simp only [Identity.firstService, prefixIndex, shape, archiveIndex]

private theorem first_service_succ (candidate : Machine Party Good Port Technology Instrument)
    (index : Native.Slot candidate) (depth : Nat) :
    Identity.firstService candidate (depth + 1) index =
      match Identity.firstService candidate depth index with
      | some earlier => some earlier
      | none => if Native.Paid candidate depth index then some depth else none := by
  have rule (prior : Native.Prefix candidate index depth) :
      prefixIndex (Native.advance candidate index depth prior) =
      match prefixIndex prior with
      | some earlier => some earlier
      | none => if Native.Paid candidate depth index then some depth else none := by
    rcases prior with ⟨state, run, shape⟩
    cases shape with
    | live unpaid slots =>
      simp only [Native.advance]
      split_ifs <;> rfl
    | terminal first earlier paid slots => rfl
  rw [first_service_is_prefix_index, first_service_is_prefix_index, Native.historyAt]
  exact rule (Native.historyAt candidate index depth)


include observed in
theorem source_current (ordinal : Nat) (inside : ordinal ≤ Cut.finish model.source input cut) :
    (machine model.source input cut nextRival nextRaw).currentAt ordinal =
      (machine model.source input cut rival raw).currentAt ordinal := by
  have same := Machine.actual_prefix_from_events (machine model.source input cut rival raw).input
    (machine model.source input cut nextRival nextRaw).input rfl rfl
    (Cut.finish model.source input cut)
    (observed) ordinal inside
  change ProgrammeSource.rawCurrent _ _ = ProgrammeSource.rawCurrent _ _
  rw [same]
  cases (ProgrammeHistory.visitAt (machine model.source input cut rival raw).input ordinal).current <;> rfl

include observed in
theorem world (depth : Nat) (inside : depth+1 < Cut.finish model.source input cut) :
    let old := (machine model.source input cut rival raw).actualExecution depth
    let new := (machine model.source input cut nextRival nextRaw).actualExecution depth
    new.before = old.before ∧ new.submitted = old.submitted ∧ new.after = old.after ∧ new.interpreted.items = old.interpreted.items := by
  have before := current model input cut raw nextRaw rival nextRival observed depth (by
    dsimp only [last,finish,Cut.finish,Cut.start] at *;omega)
  have submitted := word model input cut raw nextRaw rival nextRival observed depth (by
    dsimp only [last,finish,Cut.finish,Cut.start] at *;omega)
  refine ⟨before,submitted,?_,?_⟩
  · exact congrArg₂ model.source.code.law.next before submitted
  · exact congrArg₂ model.source.code.law.rawItems before submitted

include observed in
theorem accounts (ordinal : Nat) (inside : ordinal ≤ Cut.finish model.source input cut) :
    Native.Coupling.Match model.source.code (machine model.source input cut rival raw).input
      (machine model.source input cut nextRival nextRaw).input
      (Financial.accountAt (machine model.source input cut rival raw).input ordinal)
      (Financial.accountAt (machine model.source input cut nextRival nextRaw).input ordinal) :=
  Native.Coupling.History.complete_accounts model.source.code
    (machine model.source input cut rival raw).input
    (machine model.source input cut nextRival nextRaw).input rfl rfl
    (Cut.finish model.source input cut) observed
    (machine model.source input cut rival raw).body (machine model.source input cut nextRival nextRaw).body
    rfl rfl ordinal inside


include observed in
theorem first_service (depth : Nat) (bounded : depth < RawProfile.finish model.source input cut)
    (index : Fin model.source.code.task.slots.length) :
    Identity.firstService (machine model.source input cut nextRival nextRaw) depth index =
      Identity.firstService (machine model.source input cut rival raw) depth index := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [first_service_succ, first_service_succ, ih (by omega)]
    have world := world model input cut raw nextRaw rival nextRival observed depth (by omega)
    have paid : Native.Paid (machine model.source input cut nextRival nextRaw) depth index ↔
        Native.Paid (machine model.source input cut rival raw) depth index := by
      dsimp only [Native.Paid]
      rw [world.1, world.2.1, world.2.2.1]
      rfl
    by_cases old : Native.Paid (machine model.source input cut rival raw) depth index
    · simp only [if_pos old, if_pos (paid.mpr old)]
    · simp only [if_neg old, if_neg (fun new => old (paid.mp new))]

include observed in
theorem holdings_preserved :
    holdings model.source input cut nextRival nextRaw = holdings model.source input cut rival raw := by
  have first := accounts model input cut raw nextRaw rival nextRival observed (RawProfile.start model.source cut) (by dsimp only [RawProfile.start,Cut.finish,Cut.start]; omega)
  have last := accounts model input cut raw nextRaw rival nextRival observed (RawProfile.finish model.source input cut) (Nat.le_refl _)
  apply List.ext_getElem
  · simpa only [holdings, List.length_ofFn, Identity.financeImage, List.length_map] using congrArg List.length first.slots
  · intro index newBound oldBound
    simp only [holdings, List.getElem_ofFn]
    let oldIndex : Fin (before model.source input cut rival raw).current.slots.length := ⟨index, by simpa only [holdings, List.length_ofFn] using oldBound⟩
    let newIndex : Fin (before model.source input cut nextRival nextRaw).current.slots.length := ⟨index, by simpa only [holdings, List.length_ofFn] using newBound⟩
    apply List.map_congr_left
    intro holder _
    have image := congrArg (fun images => images[index]?) last.slots
    change ((after model.source input cut nextRival nextRaw).current.slots.map
        (Identity.debtImage model.source.code (machine model.source input cut nextRival nextRaw).input))[index]? =
      ((after model.source input cut rival raw).current.slots.map (Identity.debtImage model.source.code (machine model.source input cut rival raw).input))[index]? at image
    rw [List.getElem?_map, List.getElem?_map, (migration model.source input cut nextRival nextRaw newIndex).present,
      (migration model.source input cut rival raw oldIndex).present] at image
    have balances := congrArg Identity.DebtImage.balance (Option.some.inj image)
    apply Prod.ext
    · exact congrArg (fun balance : Party →₀ ℚ => balance holder) balances
    · exact Native.Coupling.Realization.receivedBy model.source.code (machine model.source input cut rival raw).input
        (Financial.BalanceConservation.fromActualCut _ (RawProfile.start model.source cut) (RawProfile.horizon model.source input cut))
        (machine model.source input cut nextRival nextRaw).input
        (Financial.BalanceConservation.fromActualCut _ (RawProfile.start model.source cut) (RawProfile.horizon model.source input cut))
        first last index _ _ (migration model.source input cut rival raw oldIndex)
        (migration model.source input cut nextRival nextRaw newIndex) holder

include observed in
theorem profile_preserved :
    profile model.source input cut nextRival nextRaw = profile model.source input cut rival raw := by
  have first := accounts model input cut raw nextRaw rival nextRival observed (RawProfile.start model.source cut) (by dsimp only [RawProfile.start,Cut.finish,Cut.start]; omega)
  have last := accounts model input cut raw nextRaw rival nextRival observed (RawProfile.finish model.source input cut) (Nat.le_refl _)
  have slots := congrArg List.length first.slots
  simp only [Identity.financeImage, List.length_map] at slots
  have current := source_current model input cut raw nextRaw rival nextRival observed (RawProfile.finish model.source input cut) (Nat.le_refl _)
  dsimp only [profile]
  congr 1
  · exact first.slots
  · rw [last.slots, slots]
  · exact congrArg Settlement.rights (holdings_preserved model input cut raw nextRaw rival nextRival observed)
  · apply List.flatMap_congr
    intro instrument _
    apply List.flatMap_congr
    intro debtor _
    apply List.map_congr_left
    intro creditor _
    exact congrArg₂ Sub.sub (congrArg (fun current => current.claims instrument debtor creditor) current)
      (last.same_native_quota instrument debtor creditor)
  · apply List.map_congr_left
    intro index _
    exact first_service model input cut raw nextRaw rival nextRival observed (RawProfile.start model.source cut - 1) (by dsimp only [RawProfile.finish,RawProfile.start,Cut.finish,Cut.start]; omega) index
  · exact congrArg (fun current => (⟨current.technology, current.clock, current.round⟩ : Open.Control (Mandate.State Party Technology))) current

include observed terminalState in
theorem material_preserved (metric : Settlement.Material Party Good) :
    material model.source input cut nextRival nextRaw metric = material model.source input cut rival raw metric := by
  cases metric with
  | debit bearer material =>
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset inside
    have bound := List.mem_range.mp inside
    exact congrArg (fun items => model.source.code.law.totalDebit items bearer material)
      (world model input cut raw nextRaw rival nextRival observed (RawProfile.start model.source cut - 1 + offset) (by dsimp only [RawProfile.finish,RawProfile.start,RawProfile.horizon,Cut.finish,Cut.start,Cut.horizon] at *; omega)).2.2.2
  | credit bearer material =>
    apply congrArg Neg.neg
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset inside
    have bound := List.mem_range.mp inside
    exact congrArg (fun items => model.source.code.law.totalCredit items bearer material)
      (world model input cut raw nextRaw rival nextRival observed (RawProfile.start model.source cut - 1 + offset) (by dsimp only [RawProfile.finish,RawProfile.start,RawProfile.horizon,Cut.finish,Cut.start,Cut.horizon] at *; omega)).2.2.2
  | inventory bearer material =>
    exact congrArg (fun current => -current.stock bearer material) (source_current model input cut raw nextRaw rival nextRival observed (RawProfile.finish model.source input cut) (Nat.le_refl _))
  | clock =>
    exact congrArg (fun current => current.clock) (source_current model input cut raw nextRaw rival nextRival observed (RawProfile.finish model.source input cut) (Nat.le_refl _))
  | admissibility =>
    unfold material
    rw [terminalState]

include observed terminalState active in
/-- A source-event and actual-state relation transports the entire original evaluator. -/
theorem full_evaluation_congr :
    Normalization.evaluate model input cut active nextRival nextRaw =
      Normalization.evaluate model input cut active rival raw := by
  apply (Evaluation.mk.injEq ..).mpr
  refine ⟨congrArg (fun state : State model.source.code => state.frame.localLegal) terminalState,?_,
    profile_preserved model input cut raw nextRaw rival nextRival observed,
    the_complete_raw_native_manifest_is_preserved model input cut raw nextRaw rival nextRival observed active,?_⟩
  · apply List.all_congr rfl
    intro index
    exact congrArg Option.isSome (first_service model input cut raw nextRaw rival nextRival observed
      (Cut.finish model.source input cut-1) (by dsimp only [RawProfile.finish,RawProfile.start,RawProfile.horizon,Cut.finish,Cut.start,Cut.horizon];omega) index)
  · funext axis
    cases axis with
    | material metric => exact material_preserved model input cut raw nextRaw rival nextRival observed terminalState metric
    | unpaid index holder =>
      exact congrArg (fun matrix => (Settlement.holdingAt matrix index (model.source.code.parties.idxOf holder)).1)
        (holdings_preserved model input cut raw nextRaw rival nextRival observed)
    | service index =>
      exact congrArg (fun first : Option Nat => (first.getD (Cut.finish model.source input cut) : ℚ))
        (first_service model input cut raw nextRaw rival nextRival observed
          (Cut.finish model.source input cut-1) (by dsimp only [RawProfile.finish,RawProfile.start,RawProfile.horizon,Cut.finish,Cut.start,Cut.horizon];omega) index)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Transport
