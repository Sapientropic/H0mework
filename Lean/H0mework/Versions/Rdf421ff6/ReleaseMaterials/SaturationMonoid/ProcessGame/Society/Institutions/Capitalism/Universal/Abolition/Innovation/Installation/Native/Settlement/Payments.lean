import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Bindings

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Bindings

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

private theorem the_original_two_payment_folds_compose
    {P G Port T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq Port] [DecidableEq I]
    {source : ProgrammeSource.Input P G Port T I} {depth count prefixLimit renewalLimit : Nat}
    (oldPast prior : List (Compile.RawInput P G Port T I))
    (before : (Epoch.Finance.process source depth count).GeneratedState)
    (firstRequest lastRequest : Source.Program.Request P G Port T I)
    (first last : Epoch.Finance.ActualItem source depth count)
    (firstEffect : Epoch.Finance.PublicPast.foldFrom source depth count prefixLimit renewalLimit oldPast prior
      [.primitive firstRequest] before = (Epoch.Finance.consume source depth count first before).next source depth count)
    (lastEffect : Epoch.Finance.PublicPast.foldFrom source depth count prefixLimit renewalLimit oldPast
      (prior ++ [.primitive firstRequest]) [.primitive lastRequest]
      ((Epoch.Finance.consume source depth count first before).next source depth count) =
      (Epoch.Finance.consume source depth count last
        ((Epoch.Finance.consume source depth count first before).next source depth count)).next source depth count) :
    Epoch.Finance.PublicPast.foldFrom source depth count prefixLimit renewalLimit oldPast prior
      [.primitive firstRequest,.primitive lastRequest] before =
      (Epoch.Finance.consume source depth count last
        ((Epoch.Finance.consume source depth count first before).next source depth count)).next source depth count := by
  have split := the_original_public_fold_splits_at_its_actual_source_cut
    (input := source) (depth := depth) (count := count) (prefixLimit := prefixLimit) (renewalLimit := renewalLimit)
    oldPast prior [.primitive firstRequest] [.primitive lastRequest] before
  have lifted := congrArg (fun account : (Epoch.Finance.process source depth count).GeneratedState =>
    Epoch.Finance.PublicPast.foldFrom source depth count prefixLimit renewalLimit oldPast
      (prior ++ [.primitive firstRequest]) [.primitive lastRequest] account) firstEffect
  apply Eq.trans split
  exact Eq.trans lifted lastEffect

private theorem the_actual_payment_tail_is_its_same_original_source_fold
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (actualPublicVisit (Control.Scenario.discovery version) 11).account =
      Epoch.Finance.PublicPast.foldFrom input 0 count 0 0
        (firstOrigin (Control.Scenario.discovery version)).germ.snapshot.past (beforePayments version)
        [.primitive (firstSettlement version),.primitive (lastSettlement version)]
        (actualPublicVisit (Control.Scenario.discovery version) 9).account := by
  let nature := Control.Scenario.discovery version
  let oldPast := (firstOrigin nature).germ.snapshot.past
  let prior := beforePayments version
  have original9 := every_actual_public_visit_is_its_original_source_account nature 9
  have original11 := every_actual_public_visit_is_its_original_source_account nature 11
  have source9 : (actualPublicVisit nature 9).snapshot = Physical.Prefix.cursor prior :=
    the_original_actual_trial_executes_its_real_all_member_work version tested
  have source11 : (actualPublicVisit nature 11).snapshot =
      Physical.Prefix.cursor (prior ++ [.primitive (firstSettlement version),.primitive (lastSettlement version)]) := by
    have original := the_same_actual_trial_completes_its_four_original_performance_attempts version tested
    have layout : submittedInputs (firstRaw nature).germ.snapshot.past nature ++ performanceInputs version =
        prior ++ [.primitive (firstSettlement version),.primitive (lastSettlement version)] := by
      simp only [prior,beforePayments,performanceInputs,List.append_assoc]
      rfl
    exact original.trans (congrArg Physical.Prefix.cursor layout)
  have at9 := (congrArg (fun cursor : CursorAt => Epoch.Finance.PublicPast.account input 0 count 0 0 oldPast cursor.past base) source9).trans
    (congrArg (fun past : List InputAt => Epoch.Finance.PublicPast.account input 0 count 0 0 oldPast past base) (Physical.Prefix.past_readback prior))
  have at11 := (congrArg (fun cursor : CursorAt => Epoch.Finance.PublicPast.account input 0 count 0 0 oldPast cursor.past base) source11).trans
    (congrArg (fun past : List InputAt => Epoch.Finance.PublicPast.account input 0 count 0 0 oldPast past base) (Physical.Prefix.past_readback _))
  have suffix := the_original_public_fold_splits_at_its_actual_source_cut
    (input := input) (depth := 0) (count := count) (prefixLimit := 0) (renewalLimit := 0)
    oldPast [] prior [.primitive (firstSettlement version),.primitive (lastSettlement version)] base
  exact original11.trans (at11.trans (suffix.trans
    (congrArg (fun account : Account => Epoch.Finance.PublicPast.foldFrom input 0 count 0 0 oldPast prior
      [.primitive (firstSettlement version),.primitive (lastSettlement version)] account) (original9.trans at9).symm)))

theorem the_actual_terminal_account_consumes_its_two_original_accepted_payments
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    ∃ first last : Item,
      (first.instruction input 0 count).request.operation = (firstSettlement version).operation ∧
      (first.interpreter input 0 count).Valid (first.instruction input 0 count).before
        (first.instruction input 0 count).request ∧
      (last.instruction input 0 count).request.operation = (lastSettlement version).operation ∧
      (last.interpreter input 0 count).Valid (last.instruction input 0 count).before
        (last.instruction input 0 count).request ∧
      (actualPublicVisit (Control.Scenario.discovery version) 11).account =
        (Epoch.Finance.consume input 0 count last
          ((Epoch.Finance.consume input 0 count first (actualPublicVisit (Control.Scenario.discovery version) 9).account).next input 0 count)).next input 0 count := by
  let nature := Control.Scenario.discovery version
  let actualOrigin := firstOrigin nature
  have contextReflexive : actualOrigin = actualOrigin := rfl
  generalize contextEq : actualOrigin = origin at contextReflexive
  have stateReflexive : (actualPublicVisit nature 9).account = (actualPublicVisit nature 9).account := rfl
  generalize stateEq : (actualPublicVisit nature 9).account = state at stateReflexive
  let priorAt (context : Functions.Revision.Context (input := input) (review := none) 0 count 0 0 0 count) :=
    submittedInputs context.germ.snapshot.past nature ++ [.primitive (riskLiability version),.execute Control.Scenario.commonWork]
  let firstValue (context : Functions.Revision.Context (input := input) (review := none) 0 count 0 0 0 count) :=
    (Physical.Public.resultAt input 0 count 0 0 context.germ.snapshot.past
      (Epoch.Interface.ActualOccurrence.eventCursor (priorAt context) (.primitive (firstSettlement version)))).isAccepted
  let lastValue (context : Functions.Revision.Context (input := input) (review := none) 0 count 0 0 0 count) :=
    (Physical.Public.resultAt input 0 count 0 0 context.germ.snapshot.past
      (Epoch.Interface.ActualOccurrence.eventCursor (priorAt context ++ [.primitive (firstSettlement version)])
        (.primitive (lastSettlement version)))).isAccepted
  have starts := both_actual_settlements_have_their_literal_original_singleton_start version tested
  have accepted := both_settlements_on_the_original_actual_root_are_really_accepted version tested
  have actualFirst : firstValue actualOrigin = true :=
    (congrArg (fun cursor : CursorAt => (Physical.Public.resultAt input 0 count 0 0
      actualOrigin.germ.snapshot.past cursor).isAccepted) starts.1).symm.trans accepted.1
  have lastStart : (actualPublicVisit nature 11).start =
      Epoch.Interface.ActualOccurrence.eventCursor (priorAt actualOrigin ++ [.primitive (firstSettlement version)])
        (.primitive (lastSettlement version)) :=
    starts.2.trans (congrArg (fun past : List InputAt => Physical.receive (Physical.Prefix.cursor past)
      (.primitive (lastSettlement version)))
        (List.append_assoc (submittedInputs (firstRaw nature).germ.snapshot.past nature)
          [.primitive (riskLiability version),.execute Control.Scenario.commonWork]
          [.primitive (firstSettlement version)]).symm)
  have actualLast : lastValue actualOrigin = true :=
    (congrArg (fun cursor : CursorAt => (Physical.Public.resultAt input 0 count 0 0
      actualOrigin.germ.snapshot.past cursor).isAccepted) lastStart).symm.trans accepted.2
  have firstPaid : firstValue origin = true := (congrArg firstValue contextEq).symm.trans actualFirst
  have lastPaid : lastValue origin = true := (congrArg lastValue contextEq).symm.trans actualLast
  obtain ⟨first,firstOperation,firstValid,firstEffect⟩ :=
    Events.an_accepted_original_primitive_has_its_original_native_consumption
      (origin := origin) (priorAt origin) state (firstSettlement version) firstPaid
  obtain ⟨last,lastOperation,lastValid,lastEffect⟩ :=
    Events.an_accepted_original_primitive_has_its_original_native_consumption
      (origin := origin) (priorAt origin ++ [.primitive (firstSettlement version)])
      ((Epoch.Finance.consume input 0 count first state).next input 0 count) (lastSettlement version) lastPaid
  let suffixAt (context : Functions.Revision.Context (input := input) (review := none) 0 count 0 0 0 count) (account : Account) :=
    Epoch.Finance.PublicPast.foldFrom input 0 count 0 0 context.germ.snapshot.past (priorAt context)
      [.primitive (firstSettlement version),.primitive (lastSettlement version)] account
  have suffix : (actualPublicVisit nature 11).account = suffixAt origin state :=
    (the_actual_payment_tail_is_its_same_original_source_fold version tested).trans
      (congrArg₂ suffixAt contextEq stateEq)
  have paid := the_original_two_payment_folds_compose
    (source := input) (depth := 0) (count := count) (prefixLimit := 0) (renewalLimit := 0)
    origin.germ.snapshot.past (priorAt origin) state (firstSettlement version) (lastSettlement version)
    first last firstEffect lastEffect
  refine ⟨first,last,firstOperation,firstValid,lastOperation,lastValid,?_⟩
  exact suffix.trans paid

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Bindings
