import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Profile
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Realization

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut

open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code) (cut : Nat)
  (rival : Opponent source.code) (term : Term source input cut)
  (active : source.feedback? = some input) (empty : source.continuation = [])

abbrev finiteRival := Future.jointOpponent source input cut rival

include active empty in
theorem joint_world (depth : Nat) (bounded : depth + 1 < finish source input cut) :
    let original := (machine source input cut rival term).actualExecution depth
    let finite := (machine source input cut (finiteRival source input cut rival) term).actualExecution depth
    finite.before = original.before ∧ finite.submitted = original.submitted ∧
      finite.after = original.after ∧ finite.interpreted.items = original.interpreted.items := by
  have current := Future.joint_current source input cut rival term.val active empty term.property (depth + 1) (by dsimp only [finish, start, horizon] at bounded ⊢; omega)
  have words := (Future.joint_occurrences source input cut rival term.val active empty term.property (depth + 1) bounded).2
  have submitted : ((machine source input cut (finiteRival source input cut rival) term).actualExecution depth).submitted =
      ((machine source input cut rival term).actualExecution depth).submitted := words
  have before : ((machine source input cut (finiteRival source input cut rival) term).actualExecution depth).before =
      ((machine source input cut rival term).actualExecution depth).before := current
  refine ⟨before, submitted, ?_, ?_⟩
  · change source.code.law.next _ _ = source.code.law.next _ _
    exact congrArg₂ source.code.law.next before submitted
  · change source.code.law.rawItems _ _ = source.code.law.rawItems _ _
    exact congrArg₂ source.code.law.rawItems before submitted

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

include active empty in
theorem joint_first_service (depth : Nat) (bounded : depth < finish source input cut)
    (index : Fin source.code.task.slots.length) :
    Identity.firstService (machine source input cut (finiteRival source input cut rival) term) depth index =
      Identity.firstService (machine source input cut rival term) depth index := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [first_service_succ, first_service_succ, ih (by omega)]
    have world := joint_world source input cut rival term active empty depth (by omega)
    have paid : Native.Paid (machine source input cut (finiteRival source input cut rival) term) depth index ↔
        Native.Paid (machine source input cut rival term) depth index := by
      dsimp only [Native.Paid]
      rw [world.1, world.2.1, world.2.2.1]
      rfl
    by_cases old : Native.Paid (machine source input cut rival term) depth index
    · simp only [if_pos old, if_pos (paid.mpr old)]
    · simp only [if_neg old, if_neg (fun new => old (paid.mp new))]

include active empty in
theorem joint_holdings :
    holdings source input cut (finiteRival source input cut rival) term = holdings source input cut rival term := by
  have first := Future.joint_complete_finance source input cut rival term.val active empty term.property (start source cut) (by dsimp only [start]; omega)
  have last := Future.joint_complete_finance source input cut rival term.val active empty term.property (finish source input cut) (Nat.le_refl _)
  apply List.ext_getElem
  · simpa only [holdings, List.length_ofFn, Identity.financeImage, List.length_map] using congrArg List.length first.slots
  · intro index newBound oldBound
    simp only [holdings, List.getElem_ofFn]
    let oldIndex : Fin (before source input cut rival term).current.slots.length := ⟨index, by simpa only [holdings, List.length_ofFn] using oldBound⟩
    let newIndex : Fin (before source input cut (finiteRival source input cut rival) term).current.slots.length := ⟨index, by simpa only [holdings, List.length_ofFn] using newBound⟩
    apply List.map_congr_left
    intro holder _
    have image := congrArg (fun images => images[index]?) last.slots
    change ((after source input cut (finiteRival source input cut rival) term).current.slots.map
        (Identity.debtImage source.code (machine source input cut (finiteRival source input cut rival) term).input))[index]? =
      ((after source input cut rival term).current.slots.map (Identity.debtImage source.code (machine source input cut rival term).input))[index]? at image
    rw [List.getElem?_map, List.getElem?_map, (migration source input cut _ term newIndex).present,
      (migration source input cut rival term oldIndex).present] at image
    have balances := congrArg Identity.DebtImage.balance (Option.some.inj image)
    apply Prod.ext
    · exact congrArg (fun balance : Party →₀ ℚ => balance holder) balances
    · exact Native.Coupling.Realization.receivedBy source.code (machine source input cut rival term).input
        (Financial.BalanceConservation.fromActualCut _ (start source cut) (horizon source input cut))
        (machine source input cut (finiteRival source input cut rival) term).input
        (Financial.BalanceConservation.fromActualCut _ (start source cut) (horizon source input cut))
        first last index _ _ (migration source input cut rival term oldIndex)
        (migration source input cut _ term newIndex) holder

include active empty in
theorem joint_profile :
    profile source input cut (finiteRival source input cut rival) term = profile source input cut rival term := by
  have first := Future.joint_complete_finance source input cut rival term.val active empty term.property (start source cut) (by dsimp only [start]; omega)
  have last := Future.joint_complete_finance source input cut rival term.val active empty term.property (finish source input cut) (Nat.le_refl _)
  have slots := congrArg List.length first.slots
  simp only [Identity.financeImage, List.length_map] at slots
  have current := Future.joint_current source input cut rival term.val active empty term.property (finish source input cut) (Nat.le_refl _)
  dsimp only [profile]
  congr 1
  · exact first.slots
  · rw [last.slots, slots]
  · exact congrArg Settlement.rights (joint_holdings source input cut rival term active empty)
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
    exact joint_first_service source input cut rival term active empty (start source cut - 1) (by dsimp only [finish, start]; omega) index
  · exact congrArg (fun current => (⟨current.technology, current.clock, current.round⟩ : Open.Control Technology)) current

include active empty in
theorem joint_material (metric : Settlement.Material Party Good) :
    material source input cut (finiteRival source input cut rival) term metric = material source input cut rival term metric := by
  cases metric with
  | debit party good =>
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset inside
    have bound := List.mem_range.mp inside
    exact congrArg (fun items => source.code.law.totalDebit items party good)
      (joint_world source input cut rival term active empty (start source cut - 1 + offset) (by dsimp only [finish, start] at *; omega)).2.2.2
  | credit party good =>
    apply congrArg Neg.neg
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset inside
    have bound := List.mem_range.mp inside
    exact congrArg (fun items => source.code.law.totalCredit items party good)
      (joint_world source input cut rival term active empty (start source cut - 1 + offset) (by dsimp only [finish, start] at *; omega)).2.2.2
  | inventory party good =>
    exact congrArg (fun current => -current.stock party good) (Future.joint_current source input cut rival term.val active empty term.property (finish source input cut) (Nat.le_refl _))
  | clock =>
    exact congrArg (fun current => current.clock) (Future.joint_current source input cut rival term.val active empty term.property (finish source input cut) (Nat.le_refl _))
  | admissibility =>
    unfold material finiteRival Future.jointOpponent
    rw [Residual.one_restriction_preserves_the_whole_remaining_run source.code (Residual.seed source input cut)
      (Residual.schedules source input cut) _ (List.mem_map.mpr ⟨term.val, term.property, rfl⟩) ⟨rival, input.budget⟩
      (horizon source input cut) (Nat.le_refl _)]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut
