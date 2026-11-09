import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.State
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.FinanceShape
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Admission.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Root.Registered.Macro
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Quantities.Execution (query next)
open Transport (NativeWork registrationAt sourceSupport structuralTarget)
open Transport.Admission (Registration financialStep finance original_birth_support)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Proposal" => Input Party Good Port Technology Instrument

section

variable (state : StateAt seed community cut) (registered : Registration cut.native)

def financeFirst : First state.world where
  before := state.stack.support (sourceSupport cut.native)
  after := state.stack.support (structuralTarget cut.native)
  whole := (Stack.Move.wait state.stack).lift
    (History.nativeWrite (input := cut.native.input) cut.native.frame cut.native.visit.current)
    (cut.native.frame.entry cut.native.visit.current)
  beforeFinite := state.stack.finite _ (cut.native.frame.entries_finite cut.native.visit.current)
  afterFinite := state.stack.finite _
    (cut.native.frame.entries_finite (cut.native.frame.successor cut.native.visit.current).targetCurrent)
  openFibres := state.stack.fibres cut.native.frame.family.open_fibres
  writes := History.hasWrite cut.native.frame cut.native.visit.current

abbrev financeDraft := (financeFirst state).prepare state.resident state.exactSupport.symm

def financePrepared :
    Prepared seed community (cut.birth registered).native.frame.N
      (sourceSupport (cut.birth registered).native) := by
  let draft := financeDraft state
  let admission := financialStep registered
  let stack := Stack.under (finance registered) state.stack
  refine ⟨_, stack, draft.extended admission, ?_⟩
  refine (draft.the_joint_first_support_is_the_original_successor_with_the_new_row admission).trans ?_
  refine (congrArg (fun support => (support, some admission.target)) (financeFirst state).first_support).trans ?_
  refine (Stack.under_support (finance registered) state.stack _ _).symm.trans ?_
  exact congrArg stack.support (original_birth_support registered).symm

def financeBorn : StateAt seed community (cut.birth registered) :=
  StateAt.fromPrepared (financePrepared state registered) rfl rfl

theorem financeBorn_balances : (financeBorn state registered).stack.balances = state.stack.balances := by
  unfold financeBorn
  rw [StateAt.fromPrepared_balances]
  exact Stack.under_balances (finance registered) state.stack

end

theorem selected_birth_is_the_original_cut (input : Proposal) (work : NativeWork (query cut input))
    {registered : Registration (query cut input).native}
    (selected : registrationAt (query cut input) = some registered) :
    next cut input = (query cut input).birth registered := by
  unfold registrationAt at selected
  unfold next Evolving.Epoch.Current.advance
  rw [dif_pos work, selected]

def financeNext (state : StateAt seed community cut) (input : Proposal)
    (work : NativeWork (query cut input))
    (registered : Registration (query cut input).native)
    (selected : registrationAt (query cut input) = some registered) :
    StateAt seed community (next cut input) :=
  (financeBorn (state.atQuery input) registered).rebase (selected_birth_is_the_original_cut input work selected).symm

theorem financeNext_balances (state : StateAt seed community cut) (input : Proposal)
    (work : NativeWork (query cut input))
    {registered : Registration (query cut input).native}
    (selected : registrationAt (query cut input) = some registered) :
    (financeNext state input work registered selected).stack.balances = state.stack.balances := by
  unfold financeNext
  rw [StateAt.rebase_balances, financeBorn_balances, StateAt.query_balances]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
