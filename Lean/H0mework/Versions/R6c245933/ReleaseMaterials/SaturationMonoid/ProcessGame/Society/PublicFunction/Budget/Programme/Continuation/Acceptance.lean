import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Continuation.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Successor.Acceptance

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
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
    (entry : Input source.code) (cut : Nat) (rival : Opponent source.code) (programme : List (Option source.code.Policy)) :
    Normalization.RawProfile.holdings source entry cut rival programme = holdingsInput source.code
      (Normalization.RawProfile.machine source entry cut rival programme).input (Cut.start source cut) (Cut.horizon source entry cut) := rfl

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
    (entry : Input source.code) (cut : Nat) (rival : Opponent source.code) (programme : List (Option source.code.Policy)) :
    Normalization.RawProfile.profile source entry cut rival programme = profileInput source.code
      (Normalization.RawProfile.machine source entry cut rival programme).input (Cut.start source cut) (Cut.horizon source entry cut) := by
  have services : Identity.firstService (Normalization.RawProfile.machine source entry cut rival programme) (Cut.start source cut-1) =
      (fun index => firstServiceInput source.code (Normalization.RawProfile.machine source entry cut rival programme).input index (Cut.start source cut-1)) := by
    funext index
    exact first_service_factor _ _ _
  simp only [Normalization.RawProfile.profile,holdings_factor,profileInput,services]
  rfl

section

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (first second : Cursor model.source.code) (matched : Aligned first second)
  (fallback : Rule model.source.code) (new : Program model.source.code) (futureRival : Opponent model.source.code)

private abbrev leftTerm := schedule first fallback new
private abbrev rightTerm := schedule second fallback new
private abbrev leftMachine := source first fallback new futureRival
private abbrev rightMachine := source second fallback new futureRival

include matched

theorem aligned_service_ordinal (depth : Nat) (index : Fin model.source.code.task.slots.length) :
    Identity.firstService (leftMachine model first fallback new futureRival) depth index =
      Identity.firstService (rightMachine model second fallback new futureRival) depth index := by
  rw [first_service_factor,first_service_factor]
  exact congrArg (fun input => firstServiceInput model.source.code input index depth)
    ((aligned_after matched fallback new futureRival 1).input)

theorem aligned_financial_profile :
    (Finite.actualEvaluation model first fallback new futureRival).profile =
      (Finite.actualEvaluation model second fallback new futureRival).profile := by
  change Normalization.RawProfile.profile first.source first.entry first.cut
    (controller first fallback new futureRival) (leftTerm model first fallback new) =
    Normalization.RawProfile.profile second.source second.entry second.cut
    (controller second fallback new futureRival) (rightTerm model second fallback new)
  rw [profile_factor,profile_factor,matched.horizon,matched.start]
  exact congrArg (fun input => profileInput model.source.code input
    (Cut.start second.source second.cut)
    (Cut.horizon second.source second.entry second.cut))
    ((aligned_after matched fallback new futureRival 1).input)

private abbrev leftRun (n : Nat) := Residual.run model.source.code
  (Residual.scheduleAt first.source first.cut (leftTerm model first fallback new))
  ⟨controller first fallback new futureRival,first.entry.budget⟩
  (Residual.seed first.source first.entry first.cut) n
private abbrev rightRun (n : Nat) := Residual.run model.source.code
  (Residual.scheduleAt second.source second.cut (rightTerm model second fallback new))
  ⟨controller second fallback new futureRival,second.entry.budget⟩
  (Residual.seed second.source second.entry second.cut) n

private theorem runs (n : Nat) :
    leftRun model first fallback new futureRival n = rightRun model second fallback new futureRival n := by
  exact Programme.Successor.runs matched fallback new futureRival n

private theorem currents (depth : Nat) :
    (leftMachine model first fallback new futureRival).currentAt depth =
      (rightMachine model second fallback new futureRival).currentAt depth :=
  congrArg (fun input => ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input depth).current)
    ((aligned_after matched fallback new futureRival 1).input)

private theorem items (depth : Nat) :
    ((leftMachine model first fallback new futureRival).actualExecution depth).interpreted.items =
      ((rightMachine model second fallback new futureRival).actualExecution depth).interpreted.items :=
  congrArg (fun input : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument =>
    ((ProgrammeLiving.projectionLaw input).project .execution
      (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (depth+1)).current) ()).interpreted.items)
    ((aligned_after matched fallback new futureRival 1).input)

theorem aligned_material_coordinate (metric : Settlement.Material Party Good) :
    Normalization.RawProfile.material first.source first.entry first.cut
      (controller first fallback new futureRival) (leftTerm model first fallback new) metric =
    Normalization.RawProfile.material second.source second.entry second.cut
      (controller second fallback new futureRival) (rightTerm model second fallback new) metric := by
  have raw_horizon : Normalization.RawProfile.horizon first.source first.entry first.cut =
      Normalization.RawProfile.horizon second.source second.entry second.cut := matched.horizon
  have raw_start : Normalization.RawProfile.start first.source first.cut =
      Normalization.RawProfile.start second.source second.cut := matched.start
  have raw_finish : Normalization.RawProfile.finish first.source first.entry first.cut =
      Normalization.RawProfile.finish second.source second.entry second.cut := matched.finish
  cases metric with
  | debit party good =>
    simp only [Normalization.RawProfile.material]
    rw [raw_horizon,raw_start]
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset _
    exact congrArg (fun items => model.source.code.law.totalDebit items party good)
      (items model first second matched fallback new futureRival _)
  | credit party good =>
    simp only [Normalization.RawProfile.material]
    rw [raw_horizon,raw_start]
    apply congrArg Neg.neg
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset _
    exact congrArg (fun items => model.source.code.law.totalCredit items party good)
      (items model first second matched fallback new futureRival _)
  | inventory party good =>
    change -((leftMachine model first fallback new futureRival).currentAt _).stock party good = _
    rw [raw_finish]
    exact congrArg (fun current => -current.stock party good) (currents model first second matched fallback new futureRival _)
  | clock =>
    change ((leftMachine model first fallback new futureRival).currentAt _).clock = _
    rw [raw_finish]
    exact congrArg (fun current => current.clock) (currents model first second matched fallback new futureRival _)
  | admissibility =>
    change (if model.source.code.eligible (leftRun model first fallback new futureRival _).past then 0 else 1) = _
    rw [raw_horizon]
    exact congrArg (fun state : State model.source.code => if model.source.code.eligible state.past then (0 : ℚ) else 1)
      (runs model first second matched fallback new futureRival _)

theorem aligned_evaluation :
    Finite.actualEvaluation model first fallback new futureRival =
      Finite.actualEvaluation model second fallback new futureRival := by
  apply (Evaluation.mk.injEq ..).mpr
  refine ⟨?_,?_,aligned_financial_profile model first second matched fallback new futureRival,
    NativeTransport.aligned_native_manifest model first second matched fallback new futureRival,?_⟩
  · change (leftRun model first fallback new futureRival
      (Cut.horizon first.source first.entry first.cut)).frame.localLegal = _
    rw [matched.horizon]
    exact congrArg (fun state : State model.source.code => state.frame.localLegal)
      (runs model first second matched fallback new futureRival _)
  · change (List.finRange model.source.code.task.slots.length).all (fun index =>
      (Identity.firstService (leftMachine model first fallback new futureRival)
        (Cut.finish first.source first.entry first.cut-1) index).isSome) = _
    rw [matched.finish]
    apply List.all_congr rfl
    intro index
    exact congrArg Option.isSome (aligned_service_ordinal model first second matched fallback new futureRival _ index)
  · funext axis
    cases axis with
    | material metric => exact aligned_material_coordinate model first second matched fallback new futureRival metric
    | unpaid index holder =>
      change (Settlement.holdingAt (Normalization.RawProfile.holdings first.source
        first.entry first.cut
        (controller first fallback new futureRival) (leftTerm model first fallback new))
        index (model.source.code.parties.idxOf holder)).1 =
        (Settlement.holdingAt (Normalization.RawProfile.holdings second.source
        second.entry second.cut
        (controller second fallback new futureRival) (rightTerm model second fallback new))
        index (model.source.code.parties.idxOf holder)).1
      rw [holdings_factor,holdings_factor,matched.horizon,matched.start]
      exact congrArg (fun input => (Settlement.holdingAt (holdingsInput model.source.code input
        (Cut.start second.source second.cut)
        (Cut.horizon second.source second.entry second.cut))
        index (model.source.code.parties.idxOf holder)).1)
        ((aligned_after matched fallback new futureRival 1).input)
    | service index =>
      change ((Identity.firstService (leftMachine model first fallback new futureRival)
        (Cut.finish first.source first.entry first.cut-1) index).getD
        (Cut.finish first.source first.entry first.cut) : ℚ) = _
      rw [matched.finish]
      exact congrArg (fun first : Option Nat => (first.getD
        (Cut.finish second.source second.entry second.cut) : ℚ))
        (aligned_service_ordinal model first second matched fallback new futureRival _ index)

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
    (fallback : Rule model.source.code) (alternative reference : Program model.source.code) :
    Synthesis.accepts model.source.code (economicAxes first.source first.cut)
      (Finite.actualEvaluation model first fallback alternative futureRival)
      (Finite.actualEvaluation model first fallback reference futureRival) ↔
    Synthesis.accepts model.source.code (economicAxes second.source second.cut)
      (Finite.actualEvaluation model second fallback alternative futureRival)
      (Finite.actualEvaluation model second fallback reference futureRival) := by
  rw [aligned_economic_axes model first second matched,
    aligned_evaluation model first second matched fallback alternative futureRival,
    aligned_evaluation model first second matched fallback reference futureRival]


end

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Successor.Acceptance
