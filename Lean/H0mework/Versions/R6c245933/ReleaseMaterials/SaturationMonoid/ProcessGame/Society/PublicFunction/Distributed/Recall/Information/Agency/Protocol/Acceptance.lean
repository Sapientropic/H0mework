import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Migration

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Acceptance

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

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
    simp only [Identity.firstService,prefixIndex,shape,archiveIndex]

private theorem first_service_succ (candidate : Machine Party Good Port Technology Instrument)
    (index : Native.Slot candidate) (depth : Nat) :
    Identity.firstService candidate (depth+1) index =
      match Identity.firstService candidate depth index with
      | some earlier => some earlier
      | none => if Native.Paid candidate depth index then some depth else none := by
  have rule (prior : Native.Prefix candidate index depth) :
      prefixIndex (Native.advance candidate index depth prior) =
      match prefixIndex prior with
      | some earlier => some earlier
      | none => if Native.Paid candidate depth index then some depth else none := by
    rcases prior with ⟨state,run,shape⟩
    cases shape with
    | live unpaid slots => simp only [Native.advance];split_ifs <;> rfl
    | terminal first earlier paid slots => rfl
  rw [first_service_is_prefix_index,first_service_is_prefix_index,Native.historyAt]
  exact rule (Native.historyAt candidate index depth)

private def firstServiceInput (basis : Code Party Good Port Technology Instrument)
    (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (index : Fin basis.task.slots.length) : Nat → Option Nat
  | 0 => none
  | depth+1 => match firstServiceInput basis input index depth with
    | some earlier => some earlier
    | none =>
      let actual := (ProgrammeLiving.projectionLaw input).project .execution
        (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (depth+1)).current) ()
      if basis.task.earliest ≤ actual.before.clock ∧ actual.after.clock ≤ basis.task.deadline ∧
          Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid basis.law actual.before actual.submitted
            (basis.task.slots.get index).bearer (basis.task.slots.get index).goods (basis.task.slots.get index).purpose
        then some depth else none

private theorem first_service_factor (source : Machine Party Good Port Technology Instrument)
    (depth : Nat) (index : Native.Slot source) :
    Identity.firstService source depth index = firstServiceInput source.code source.input index depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => rw [first_service_succ,ih];rfl

private def holdingsInput (basis : Code Party Good Port Technology Instrument)
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (start count : Nat) : List (List (ℚ × ℚ)) :=
  List.ofFn fun index : Fin (Financial.accountAt input start).current.slots.length =>
    let actual := Financial.Migration.actual input start count index.val
      ((Financial.accountAt input start).current.slots.get index) (List.getElem?_eq_getElem index.isLt)
    basis.parties.map fun holder => (Financial.slotBalance input actual.slot holder,actual.path.receivedBy input holder)

private theorem holdings_factor (source : Machine Party Good Port Technology Instrument)
    (entry : Input source.code) (cut : Nat) (rival : Opponent source.code) (programme : Cut.Term source entry cut) :
    Cut.holdings source entry cut rival programme = holdingsInput source.code
      (Cut.machine source entry cut rival programme).input (Cut.start source cut) (Cut.horizon source entry cut) := rfl

private def profileInput (basis : Code Party Good Port Technology Instrument)
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (start count : Nat) :
    Settlement.Profile Party Good Port Technology Instrument :=
  let first := Financial.accountAt input start
  let last := Financial.accountAt input (start+count)
  let current := ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input (start+count)).current
  ⟨Identity.financeImage basis input first,
    (Identity.financeImage basis input last).drop first.current.slots.length,
    Settlement.rights (holdingsInput basis input start count),
    basis.instruments.flatMap fun instrument => basis.parties.flatMap fun debtor =>
      basis.parties.map fun creditor => current.claims instrument debtor creditor -
        Financial.BalanceConservation.ledgerClaims input last.current instrument debtor creditor,
    (List.finRange basis.task.slots.length).map (fun index => firstServiceInput basis input index (start-1)),
    ⟨current.technology,current.clock,current.round⟩⟩

private theorem profile_factor (source : Machine Party Good Port Technology Instrument)
    (entry : Input source.code) (cut : Nat) (rival : Opponent source.code) (programme : Cut.Term source entry cut) :
    Cut.profile source entry cut rival programme = profileInput source.code
      (Cut.machine source entry cut rival programme).input (Cut.start source cut) (Cut.horizon source entry cut) := by
  have services : Identity.firstService (Cut.machine source entry cut rival programme) (Cut.start source cut-1) =
      (fun index => firstServiceInput source.code (Cut.machine source entry cut rival programme).input index (Cut.start source cut-1)) := by
    funext index
    exact first_service_factor _ _ _
  simp only [Cut.profile,holdings_factor,profileInput,services]
  rfl

namespace Generated

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (first second : Cursor model.source.code) (matched : Aligned first second)
  (firstDriver secondDriver : Opponent model.source.code)
  (firstTerm : Cut.Term first.source first.entry first.cut)
  (secondTerm : Cut.Term second.source second.entry second.cut)
  (emitted : (Future.target first.source first.entry first.cut firstDriver firstTerm.val).input =
    (Future.target second.source second.entry second.cut secondDriver secondTerm.val).input)
  (states : ∀ n, Residual.run model.source.code
      (Residual.scheduleAt first.source first.cut firstTerm.val) ⟨firstDriver,first.entry.budget⟩
      (Residual.seed first.source first.entry first.cut) n =
    Residual.run model.source.code
      (Residual.scheduleAt second.source second.cut secondTerm.val) ⟨secondDriver,second.entry.budget⟩
      (Residual.seed second.source second.entry second.cut) n)

private abbrev leftMachine := Future.target first.source first.entry first.cut firstDriver firstTerm.val
private abbrev rightMachine := Future.target second.source second.entry second.cut secondDriver secondTerm.val

include matched firstDriver secondDriver firstTerm secondTerm emitted states

omit matched states in
theorem aligned_service_ordinal (depth : Nat) (index : Fin model.source.code.task.slots.length) :
    Identity.firstService (leftMachine model first firstDriver firstTerm) depth index =
      Identity.firstService (rightMachine model second secondDriver secondTerm) depth index := by
  rw [first_service_factor,first_service_factor]
  exact congrArg (fun input => firstServiceInput model.source.code input index depth)
    emitted

omit states in
theorem aligned_financial_profile :
    (Migration.Generated.evaluation model first firstDriver firstTerm).profile =
      (Migration.Generated.evaluation model second secondDriver secondTerm).profile := by
  change Cut.profile first.source first.entry first.cut
    firstDriver firstTerm =
    Cut.profile second.source second.entry second.cut
    secondDriver secondTerm
  rw [profile_factor,profile_factor,matched.horizon,matched.start]
  exact congrArg (fun input => profileInput model.source.code input
    (Cut.start second.source second.cut)
    (Cut.horizon second.source second.entry second.cut))
    emitted

private abbrev leftRun (n : Nat) := Residual.run model.source.code
  (Residual.scheduleAt first.source first.cut firstTerm.val)
  ⟨firstDriver,first.entry.budget⟩
  (Residual.seed first.source first.entry first.cut) n
private abbrev rightRun (n : Nat) := Residual.run model.source.code
  (Residual.scheduleAt second.source second.cut secondTerm.val)
  ⟨secondDriver,second.entry.budget⟩
  (Residual.seed second.source second.entry second.cut) n

omit matched emitted in
private theorem runs (n : Nat) :
    leftRun model first firstDriver firstTerm n = rightRun model second secondDriver secondTerm n := by
  exact states n

omit matched states in
private theorem currents (depth : Nat) :
    (leftMachine model first firstDriver firstTerm).currentAt depth =
      (rightMachine model second secondDriver secondTerm).currentAt depth :=
  congrArg (fun input => ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input depth).current)
    emitted

omit matched states in
private theorem items (depth : Nat) :
    ((leftMachine model first firstDriver firstTerm).actualExecution depth).interpreted.items =
      ((rightMachine model second secondDriver secondTerm).actualExecution depth).interpreted.items :=
  congrArg (fun input : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument =>
    ((ProgrammeLiving.projectionLaw input).project .execution
      (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (depth+1)).current) ()).interpreted.items)
    emitted

theorem aligned_material_coordinate (metric : Settlement.Material Party Good) :
    Cut.material first.source first.entry first.cut
      firstDriver firstTerm metric =
    Cut.material second.source second.entry second.cut
      secondDriver secondTerm metric := by
  cases metric with
  | debit party good =>
    simp only [Cut.material]
    rw [matched.horizon,matched.start]
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset _
    exact congrArg (fun items => model.source.code.law.totalDebit items party good)
      (items model first second firstDriver secondDriver firstTerm secondTerm emitted _)
  | credit party good =>
    simp only [Cut.material]
    rw [matched.horizon,matched.start]
    apply congrArg Neg.neg
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset _
    exact congrArg (fun items => model.source.code.law.totalCredit items party good)
      (items model first second firstDriver secondDriver firstTerm secondTerm emitted _)
  | inventory party good =>
    change -((leftMachine model first firstDriver firstTerm).currentAt _).stock party good = _
    rw [matched.finish]
    exact congrArg (fun current => -current.stock party good) (currents model first second firstDriver secondDriver firstTerm secondTerm emitted _)
  | clock =>
    change ((leftMachine model first firstDriver firstTerm).currentAt _).clock = _
    rw [matched.finish]
    exact congrArg (fun current => current.clock) (currents model first second firstDriver secondDriver firstTerm secondTerm emitted _)
  | admissibility =>
    change (if model.source.code.eligible (leftRun model first firstDriver firstTerm _).past then 0 else 1) = _
    rw [matched.horizon]
    exact congrArg (fun state : State model.source.code => if model.source.code.eligible state.past then (0 : ℚ) else 1)
      (runs model first second firstDriver secondDriver firstTerm secondTerm states _)

theorem aligned_evaluation :
    Migration.Generated.evaluation model first firstDriver firstTerm =
      Migration.Generated.evaluation model second secondDriver secondTerm := by
  apply (Evaluation.mk.injEq ..).mpr
  refine ⟨?_,?_,aligned_financial_profile model first second matched firstDriver secondDriver firstTerm secondTerm emitted,
    Migration.Generated.aligned_native_manifest model first second matched firstDriver secondDriver firstTerm secondTerm emitted,?_⟩
  · change (leftRun model first firstDriver firstTerm
      (Cut.horizon first.source first.entry first.cut)).frame.localLegal = _
    rw [matched.horizon]
    exact congrArg (fun state : State model.source.code => state.frame.localLegal)
      (runs model first second firstDriver secondDriver firstTerm secondTerm states _)
  · change (List.finRange model.source.code.task.slots.length).all (fun index =>
      (Identity.firstService (leftMachine model first firstDriver firstTerm)
        (Cut.finish first.source first.entry first.cut-1) index).isSome) = _
    rw [matched.finish]
    apply List.all_congr rfl
    intro index
    exact congrArg Option.isSome (aligned_service_ordinal model first second firstDriver secondDriver firstTerm secondTerm emitted _ index)
  · funext axis
    cases axis with
    | material metric => exact aligned_material_coordinate model first second matched firstDriver secondDriver firstTerm secondTerm emitted states metric
    | unpaid index holder =>
      change (Settlement.holdingAt (Cut.holdings first.source
        first.entry first.cut
        firstDriver firstTerm)
        index (model.source.code.parties.idxOf holder)).1 =
        (Settlement.holdingAt (Cut.holdings second.source
        second.entry second.cut
        secondDriver secondTerm)
        index (model.source.code.parties.idxOf holder)).1
      rw [holdings_factor,holdings_factor,matched.horizon,matched.start]
      exact congrArg (fun input => (Settlement.holdingAt (holdingsInput model.source.code input
        (Cut.start second.source second.cut)
        (Cut.horizon second.source second.entry second.cut))
        index (model.source.code.parties.idxOf holder)).1)
        emitted
    | service index =>
      change ((Identity.firstService (leftMachine model first firstDriver firstTerm)
        (Cut.finish first.source first.entry first.cut-1) index).getD
        (Cut.finish first.source first.entry first.cut) : ℚ) = _
      rw [matched.finish]
      exact congrArg (fun first : Option Nat => (first.getD
        (Cut.finish second.source second.entry second.cut) : ℚ))
        (aligned_service_ordinal model first second firstDriver secondDriver firstTerm secondTerm emitted _ index)

end Generated

section

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (first second : Cursor model.source.code) (matched : Aligned first second)
  (new : Rule model.source.code) (futureRival : Opponent model.source.code)

include matched

theorem aligned_service_ordinal (depth : Nat) (index : Fin model.source.code.task.slots.length) :
    Identity.firstService (Cursor.target first new futureRival) depth index =
      Identity.firstService (Cursor.target second new futureRival) depth index := by
  exact Generated.aligned_service_ordinal model first second
    (Cursor.controller first new futureRival) (Cursor.controller second new futureRival)
    (term first.source first.entry first.cut new) (term second.source second.entry second.cut new)
    (matched.after new futureRival).input depth index

theorem aligned_financial_profile :
    (Replanning.actualEvaluation model first new futureRival).profile =
      (Replanning.actualEvaluation model second new futureRival).profile := by
  exact Generated.aligned_financial_profile model first second matched
    (Cursor.controller first new futureRival) (Cursor.controller second new futureRival)
    (term first.source first.entry first.cut new) (term second.source second.entry second.cut new)
    (matched.after new futureRival).input

theorem aligned_material_coordinate (metric : Settlement.Material Party Good) :
    Cut.material first.source first.entry first.cut
      (Cursor.controller first new futureRival) (term first.source first.entry first.cut new) metric =
    Cut.material second.source second.entry second.cut
      (Cursor.controller second new futureRival) (term second.source second.entry second.cut new) metric := by
  apply Generated.aligned_material_coordinate model first second matched
    (Cursor.controller first new futureRival) (Cursor.controller second new futureRival)
    (term first.source first.entry first.cut new) (term second.source second.entry second.cut new)
    (matched.after new futureRival).input
  intro n
  have same := matched.after_states new futureRival n
  rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state] at same
  exact same

theorem aligned_evaluation :
    Replanning.actualEvaluation model first new futureRival =
      Replanning.actualEvaluation model second new futureRival := by
  apply Generated.aligned_evaluation model first second matched
    (Cursor.controller first new futureRival) (Cursor.controller second new futureRival)
    (term first.source first.entry first.cut new) (term second.source second.entry second.cut new)
    (matched.after new futureRival).input
  intro n
  have same := matched.after_states new futureRival n
  rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state] at same
  exact same

theorem aligned_economic_axes :
    economicAxes first.source first.cut =
      economicAxes second.source second.cut := by
  have slots : Cut.originalSlots first.source first.cut =
      Cut.originalSlots second.source second.cut := by
    change (Financial.accountAt first.source.input (Cut.start first.source first.cut)).current.slots.length = _
    rw [matched.start]
    exact congrArg (fun input => (Financial.accountAt input
      (Cut.start second.source second.cut)).current.slots.length)
      (matched.input)
  change (Settlement.materials model.source.code).map EconomicAxis.material ++
    (List.range (Cut.originalSlots first.source first.cut)).flatMap
      (fun index => model.source.code.parties.map (.unpaid index)) ++
    (List.finRange model.source.code.task.slots.length).map EconomicAxis.service = _
  rw [slots]
  rfl

theorem aligned_acceptance
    (alternative reference : Rule model.source.code) :
    Synthesis.accepts model.source.code (economicAxes first.source first.cut)
      (Replanning.actualEvaluation model first alternative futureRival)
      (Replanning.actualEvaluation model first reference futureRival) ↔
    Synthesis.accepts model.source.code (economicAxes second.source second.cut)
      (Replanning.actualEvaluation model second alternative futureRival)
      (Replanning.actualEvaluation model second reference futureRival) := by
  rw [aligned_economic_axes model first second matched,
    aligned_evaluation model first second matched alternative futureRival,
    aligned_evaluation model first second matched reference futureRival]


end

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (old new : Rule model.source.code)
  (pastRival futureRival : Opponent model.source.code)

private abbrev finite := Transport.representative point old pastRival
private abbrev actual := Transport.actual point old pastRival
private abbrev finiteTerm := term (finite model point old pastRival).source (finite model point old pastRival).entry (point.cut+1) new
private abbrev actualTerm := term (actual model point old pastRival).source (actual model point old pastRival).entry (point.cut+1) new
private abbrev finiteMachine := Cursor.target (finite model point old pastRival) new futureRival
private abbrev actualMachine := Cursor.target (actual model point old pastRival) new futureRival


theorem every_actual_service_keeps_its_first_paid_ordinal (depth : Nat) (index : Fin model.source.code.task.slots.length) :
    Identity.firstService (finiteMachine model point old new pastRival futureRival) depth index =
      Identity.firstService (actualMachine model point old new pastRival futureRival) depth index :=
  aligned_service_ordinal model _ _ (Aligned.representative point old pastRival) new futureRival depth index

theorem every_original_debt_keeps_its_complete_financial_profile :
    (Replanning.actualEvaluation model (finite model point old pastRival) new futureRival).profile =
      (Replanning.actualEvaluation model (actual model point old pastRival) new futureRival).profile :=
  aligned_financial_profile model _ _ (Aligned.representative point old pastRival) new futureRival

theorem every_actual_material_coordinate_is_preserved (metric : Settlement.Material Party Good) :
    Cut.material (finite model point old pastRival).source (finite model point old pastRival).entry (point.cut+1)
      (Cursor.controller (finite model point old pastRival) new futureRival) (finiteTerm model point old new pastRival) metric =
    Cut.material (actual model point old pastRival).source (actual model point old pastRival).entry (point.cut+1)
      (Cursor.controller (actual model point old pastRival) new futureRival) (actualTerm model point old new pastRival) metric :=
  aligned_material_coordinate model _ _ (Aligned.representative point old pastRival) new futureRival metric

theorem the_new_rule_preserves_the_complete_actual_evaluation :
    Replanning.actualEvaluation model (finite model point old pastRival) new futureRival =
      Replanning.actualEvaluation model (actual model point old pastRival) new futureRival :=
  aligned_evaluation model _ _ (Aligned.representative point old pastRival) new futureRival

theorem the_original_responsibility_axis_inventory_is_preserved :
    economicAxes (finite model point old pastRival).source (point.cut+1) =
      economicAxes (actual model point old pastRival).source (point.cut+1) :=
  aligned_economic_axes model _ _ (Aligned.representative point old pastRival)

theorem complete_acceptance_is_preserved_for_the_same_actual_rival
    (alternative reference : Rule model.source.code) :
    Synthesis.accepts model.source.code (economicAxes (finite model point old pastRival).source (point.cut+1))
      (Replanning.actualEvaluation model (finite model point old pastRival) alternative futureRival)
      (Replanning.actualEvaluation model (finite model point old pastRival) reference futureRival) ↔
    Synthesis.accepts model.source.code (economicAxes (actual model point old pastRival).source (point.cut+1))
      (Replanning.actualEvaluation model (actual model point old pastRival) alternative futureRival)
      (Replanning.actualEvaluation model (actual model point old pastRival) reference futureRival) :=
  aligned_acceptance model _ _ (Aligned.representative point old pastRival) futureRival alternative reference

structure SourceMatch (installed : Rule model.source.code) (environment : Opponent model.source.code)
    (next : Cursor model.source.code) : Prop extends toNativeMatch : Migration.SourceMatch model point installed environment next where
  renewed_evaluation : ∀ (rule : Rule model.source.code) (rival : Opponent model.source.code),
    Replanning.actualEvaluation model next rule rival =
      Replanning.actualEvaluation model (Transport.actual point installed environment) rule rival
  axes : economicAxes next.source next.cut =
    economicAxes (Transport.actual point installed environment).source (Transport.actual point installed environment).cut

theorem one_public_successor_preserves_every_complete_evaluation
    (domain : List (Cursor model.source.code)) (inside : point ∈ domain) :
    ∃ next ∈ advance model.source.code domain old, SourceMatch model point old pastRival next := by
  refine ⟨Transport.representative point old pastRival,
    every_generated_table_produces_its_own_successor model.source.code domain old point inside
      (externalTable point pastRival) (Residual.restriction_is_generated _ _ _ pastRival),?_⟩
  exact {
    toNativeMatch := Migration.the_public_representative_preserves_every_original_and_new_native_responsibility model point old pastRival
    renewed_evaluation := fun rule rival => the_new_rule_preserves_the_complete_actual_evaluation model point old rule pastRival rival
    axes := the_original_responsibility_axis_inventory_is_preserved model point old pastRival }

theorem every_selected_rule_protects_its_actual_successor
    (domain : List (Cursor model.source.code))
    (sources : ∃ next ∈ domain, SourceMatch model point old pastRival next)
    (choice : Replanning.Choice model domain old) (rival : Opponent model.source.code) :
    Synthesis.accepts model.source.code
      (economicAxes (Transport.actual point old pastRival).source (Transport.actual point old pastRival).cut)
      (Replanning.actualEvaluation model (Transport.actual point old pastRival) choice.policy.protocol rival)
      (Replanning.actualEvaluation model (Transport.actual point old pastRival) old rival) := by
  obtain ⟨next,inside,matched⟩ := sources
  have protection := Replanning.every_verified_protocol_protects_its_own_actual_full_responsibility model domain
    old choice.policy.protocol (Replanning.independently_replayed_choice_is_accepted model domain old choice) ⟨next,inside⟩ rival
  rw [matched.axes,matched.renewed_evaluation,matched.renewed_evaluation] at protection
  exact protection

theorem the_selected_successor_rule_protects_the_actual_full_responsibility
    (domain : List (Cursor model.source.code)) (inside : point ∈ domain)
    (choice : Replanning.Choice model (advance model.source.code domain old) old)
    (rival : Opponent model.source.code) :
    Synthesis.accepts model.source.code
      (economicAxes (Transport.actual point old pastRival).source (point.cut+1))
      (Replanning.actualEvaluation model (Transport.actual point old pastRival) choice.policy.protocol rival)
      (Replanning.actualEvaluation model (Transport.actual point old pastRival) old rival) :=
  every_selected_rule_protects_its_actual_successor model point old pastRival _
    (one_public_successor_preserves_every_complete_evaluation model point old pastRival domain inside) choice rival

def ActualProtection (domain : List (Cursor model.source.code)) : Replanning.Outcome model domain old → Prop
  | .selected choice => ∀ rival : Opponent model.source.code,
      Synthesis.accepts model.source.code
        (economicAxes (Transport.actual point old pastRival).source (Transport.actual point old pastRival).cut)
        (Replanning.actualEvaluation model (Transport.actual point old pastRival) choice.policy.protocol rival)
        (Replanning.actualEvaluation model (Transport.actual point old pastRival) old rival)
  | .blocked _ => True

theorem every_public_outcome_transports_its_selected_actual_protection
    (domain : List (Cursor model.source.code))
    (sources : ∃ next ∈ domain, SourceMatch model point old pastRival next)
    (outcome : Replanning.Outcome model domain old) : ActualProtection model point old pastRival domain outcome := by
  cases outcome with
  | selected choice => exact every_selected_rule_protects_its_actual_successor model point old pastRival domain sources choice
  | blocked rejected => exact True.intro

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Acceptance
