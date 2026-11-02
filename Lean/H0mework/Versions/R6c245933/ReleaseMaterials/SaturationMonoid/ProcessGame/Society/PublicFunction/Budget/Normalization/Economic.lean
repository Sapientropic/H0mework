import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Native
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.RawProfile
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Realization

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.NativeTransport

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RawProfile

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input model.source.code) (cut : Nat) (raw : List (Option model.source.code.Policy))
  (party : Party) (good : Good)
  (floor : Gross.Floor model.source.code.law party good model.source.code.actions) (budget : ℚ)
  (rival : Opponent model.source.code)
  (paid : Source.Paid model.source input cut raw (Cut.horizon model.source input cut) party good budget rival)
  (active : model.source.feedback? = some input) (empty : model.source.continuation = [])

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


include paid active empty in
theorem source_current (ordinal : Nat) (inside : ordinal ≤ Cut.finish model.source input cut) :
    (machine model.source input cut rival (representative model input cut raw party good floor budget)).currentAt ordinal =
      (machine model.source input cut rival raw).currentAt ordinal := by
  have same := Machine.actual_prefix_from_events (machine model.source input cut rival raw).input
    (machine model.source input cut rival (representative model input cut raw party good floor budget)).input rfl rfl
    (Cut.finish model.source input cut)
    (events model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty) ordinal inside
  change ProgrammeSource.rawCurrent _ _ = ProgrammeSource.rawCurrent _ _
  rw [same]
  cases (ProgrammeHistory.visitAt (machine model.source input cut rival raw).input ordinal).current <;> rfl

include paid active empty in
theorem world (depth : Nat) (inside : depth+1 < Cut.finish model.source input cut) :
    let old := (machine model.source input cut rival raw).actualExecution depth
    let new := (machine model.source input cut rival (representative model input cut raw party good floor budget)).actualExecution depth
    new.before = old.before ∧ new.submitted = old.submitted ∧ new.after = old.after ∧ new.interpreted.items = old.interpreted.items := by
  have before := current model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty depth (by
    dsimp only [last,finish,Cut.finish,Cut.start] at *;omega)
  have submitted := word model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty depth (by
    dsimp only [last,finish,Cut.finish,Cut.start] at *;omega)
  refine ⟨before,submitted,?_,?_⟩
  · exact congrArg₂ model.source.code.law.next before submitted
  · exact congrArg₂ model.source.code.law.rawItems before submitted

include paid active empty in
theorem accounts (ordinal : Nat) (inside : ordinal ≤ Cut.finish model.source input cut) :
    Native.Coupling.Match model.source.code (machine model.source input cut rival raw).input
      (machine model.source input cut rival (representative model input cut raw party good floor budget)).input
      (Financial.accountAt (machine model.source input cut rival raw).input ordinal)
      (Financial.accountAt (machine model.source input cut rival (representative model input cut raw party good floor budget)).input ordinal) :=
  Source.complete_native_financial_histories_are_transported model.source input cut raw (Cut.horizon model.source input cut)
    party good floor budget rival paid active empty ordinal inside

include paid active empty in
theorem first_service (depth : Nat) (bounded : depth < RawProfile.finish model.source input cut)
    (index : Fin model.source.code.task.slots.length) :
    Identity.firstService (machine model.source input cut rival (representative model input cut raw party good floor budget)) depth index =
      Identity.firstService (machine model.source input cut rival raw) depth index := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [first_service_succ, first_service_succ, ih (by omega)]
    have world := world model input cut raw party good floor budget rival paid active empty depth (by omega)
    have paid : Native.Paid (machine model.source input cut rival (representative model input cut raw party good floor budget)) depth index ↔
        Native.Paid (machine model.source input cut rival raw) depth index := by
      dsimp only [Native.Paid]
      rw [world.1, world.2.1, world.2.2.1]
      rfl
    by_cases old : Native.Paid (machine model.source input cut rival raw) depth index
    · simp only [if_pos old, if_pos (paid.mpr old)]
    · simp only [if_neg old, if_neg (fun new => old (paid.mp new))]

include paid active empty in
theorem holdings_preserved :
    holdings model.source input cut rival (representative model input cut raw party good floor budget) = holdings model.source input cut rival raw := by
  have first := accounts model input cut raw party good floor budget rival paid active empty (RawProfile.start model.source cut) (by dsimp only [RawProfile.start,Cut.finish,Cut.start]; omega)
  have last := accounts model input cut raw party good floor budget rival paid active empty (RawProfile.finish model.source input cut) (Nat.le_refl _)
  apply List.ext_getElem
  · simpa only [holdings, List.length_ofFn, Identity.financeImage, List.length_map] using congrArg List.length first.slots
  · intro index newBound oldBound
    simp only [holdings, List.getElem_ofFn]
    let oldIndex : Fin (before model.source input cut rival raw).current.slots.length := ⟨index, by simpa only [holdings, List.length_ofFn] using oldBound⟩
    let newIndex : Fin (before model.source input cut rival (representative model input cut raw party good floor budget)).current.slots.length := ⟨index, by simpa only [holdings, List.length_ofFn] using newBound⟩
    apply List.map_congr_left
    intro holder _
    have image := congrArg (fun images => images[index]?) last.slots
    change ((after model.source input cut rival (representative model input cut raw party good floor budget)).current.slots.map
        (Identity.debtImage model.source.code (machine model.source input cut rival (representative model input cut raw party good floor budget)).input))[index]? =
      ((after model.source input cut rival raw).current.slots.map (Identity.debtImage model.source.code (machine model.source input cut rival raw).input))[index]? at image
    rw [List.getElem?_map, List.getElem?_map, (migration model.source input cut rival (representative model input cut raw party good floor budget) newIndex).present,
      (migration model.source input cut rival raw oldIndex).present] at image
    have balances := congrArg Identity.DebtImage.balance (Option.some.inj image)
    apply Prod.ext
    · exact congrArg (fun balance : Party →₀ ℚ => balance holder) balances
    · exact Native.Coupling.Realization.receivedBy model.source.code (machine model.source input cut rival raw).input
        (Financial.BalanceConservation.fromActualCut _ (RawProfile.start model.source cut) (RawProfile.horizon model.source input cut))
        (machine model.source input cut rival (representative model input cut raw party good floor budget)).input
        (Financial.BalanceConservation.fromActualCut _ (RawProfile.start model.source cut) (RawProfile.horizon model.source input cut))
        first last index _ _ (migration model.source input cut rival raw oldIndex)
        (migration model.source input cut rival (representative model input cut raw party good floor budget) newIndex) holder

include paid active empty in
theorem profile_preserved :
    profile model.source input cut rival (representative model input cut raw party good floor budget) = profile model.source input cut rival raw := by
  have first := accounts model input cut raw party good floor budget rival paid active empty (RawProfile.start model.source cut) (by dsimp only [RawProfile.start,Cut.finish,Cut.start]; omega)
  have last := accounts model input cut raw party good floor budget rival paid active empty (RawProfile.finish model.source input cut) (Nat.le_refl _)
  have slots := congrArg List.length first.slots
  simp only [Identity.financeImage, List.length_map] at slots
  have current := source_current model input cut raw party good floor budget rival paid active empty (RawProfile.finish model.source input cut) (Nat.le_refl _)
  dsimp only [profile]
  congr 1
  · exact first.slots
  · rw [last.slots, slots]
  · exact congrArg Settlement.rights (holdings_preserved model input cut raw party good floor budget rival paid active empty)
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
    exact first_service model input cut raw party good floor budget rival paid active empty (RawProfile.start model.source cut - 1) (by dsimp only [RawProfile.finish,RawProfile.start,Cut.finish,Cut.start]; omega) index
  · exact congrArg (fun current => (⟨current.technology, current.clock, current.round⟩ : Open.Control (Mandate.State Party Technology))) current

include paid active empty in
theorem material_preserved (metric : Settlement.Material Party Good) :
    material model.source input cut rival (representative model input cut raw party good floor budget) metric = material model.source input cut rival raw metric := by
  cases metric with
  | debit bearer material =>
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset inside
    have bound := List.mem_range.mp inside
    exact congrArg (fun items => model.source.code.law.totalDebit items bearer material)
      (world model input cut raw party good floor budget rival paid active empty (RawProfile.start model.source cut - 1 + offset) (by dsimp only [RawProfile.finish,RawProfile.start,RawProfile.horizon,Cut.finish,Cut.start,Cut.horizon] at *; omega)).2.2.2
  | credit bearer material =>
    apply congrArg Neg.neg
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset inside
    have bound := List.mem_range.mp inside
    exact congrArg (fun items => model.source.code.law.totalCredit items bearer material)
      (world model input cut raw party good floor budget rival paid active empty (RawProfile.start model.source cut - 1 + offset) (by dsimp only [RawProfile.finish,RawProfile.start,RawProfile.horizon,Cut.finish,Cut.start,Cut.horizon] at *; omega)).2.2.2
  | inventory bearer material =>
    exact congrArg (fun current => -current.stock bearer material) (source_current model input cut raw party good floor budget rival paid active empty (RawProfile.finish model.source input cut) (Nat.le_refl _))
  | clock =>
    exact congrArg (fun current => current.clock) (source_current model input cut raw party good floor budget rival paid active empty (RawProfile.finish model.source input cut) (Nat.le_refl _))
  | admissibility =>
    have same := Source.one_public_normalization_preserves_each_rivals_actual_complete_prefix model.source input cut raw
      (Cut.horizon model.source input cut) party good floor budget rival paid
      (Cut.horizon model.source input cut) (Nat.le_refl _)
    rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state] at same
    unfold material
    rw [same]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.NativeTransport
