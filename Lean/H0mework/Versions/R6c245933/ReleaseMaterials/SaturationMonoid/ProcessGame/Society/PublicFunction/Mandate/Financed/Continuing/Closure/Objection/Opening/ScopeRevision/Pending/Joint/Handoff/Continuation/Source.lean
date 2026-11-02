import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Inventory

/-! Pending native Challenges choose the next authority attempt. Otherwise
the existing service planner acts; the resulting debt matrix emits its own
portfolio response. Both actual words advance the same saved joint inventory. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} {authority : ScopeRevision.Ready old}
  {originInputs : List (List Action)} {inventory : Pending.Joint.Inventory authority originInputs}
  {fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs}
  (saved : Inventory authority inventory fresh)

structure Request where
  private mk ::
  resident : Mandate.Challenge.Cross.Resident (newBound fresh) saved.inputs
  recorded : resident ∈ saved.objections
  pending : resident.history.isPending = true

def Request.target (request : Request saved) :
    Mandate.Challenge.Cross.Target (Mandate.Challenge.fromHistory (newBound fresh)) request.resident.original saved.inputs := by
  cases history : request.resident.history with
  | pending target state slots => exact target
  | closed state archive slots => have impossible := request.pending; rw [history] at impossible; cases impossible

def request? : Option (Request saved) :=
  match selected : saved.objections.find? (fun resident : Mandate.Challenge.Cross.Resident (newBound fresh) saved.inputs => resident.history.isPending) with
  | some resident => some ⟨resident,List.mem_of_find?_eq_some selected,
      List.find?_some (p := fun resident : Mandate.Challenge.Cross.Resident (newBound fresh) saved.inputs => resident.history.isPending) selected⟩
  | none => none

def preamble (request : Request saved) : List Action :=
  if (currentAt fresh saved.inputs).technology = (request.target saved).snapshot (Mandate.Challenge.fromHistory (newBound fresh)) then []
  else [⟨(request.target saved).claim.signer (Mandate.Challenge.fromHistory (newBound fresh)) saved.inputs,
    [],fresh.scope.challenge,[fresh.scope.challenge],.present⟩]

def reply (request : Request saved) :=
  Mandate.Response.produce base fresh.scope ((law fresh).execute (currentAt fresh saved.inputs) 0 (preamble saved request)).final

inductive ServiceOutcome where
  | private paid (payment : Handoff.Paid fresh (currentAt fresh saved.inputs))
      (selected : Handoff.select fresh (currentAt fresh saved.inputs) = some payment)
  | private blocked (absent : Handoff.select fresh (currentAt fresh saved.inputs) = none)
      (failed : ∀ method ∈ Handoff.methods, ¬ Handoff.Pass fresh (currentAt fresh saved.inputs) method)

def serviceOutcome : ServiceOutcome saved :=
  match selected : Handoff.select fresh (currentAt fresh saved.inputs) with
  | some payment => .paid payment selected
  | none => .blocked selected (Handoff.blocked_menu_has_actual_failed_checks fresh _ selected)

def emit : List Action :=
  match request? saved with
  | some request => preamble saved request ++ (reply saved request).word
  | none => Handoff.emitAt fresh (currentAt fresh saved.inputs)

theorem pending_native_request_drives_the_actual_attempt (request : Request saved) (selected : request? saved = some request) :
    request.resident ∈ saved.objections ∧ request.resident.history.isPending = true ∧
    emit saved = preamble saved request ++ (reply saved request).word := by
  exact ⟨request.recorded,request.pending,by simp only [emit,selected]⟩

def staged := submit saved (emit saved)
def responseWord := Repayment.Portfolio.word (law fresh) (Handoff.debtPositions (currentAt fresh (staged saved).inputs))
  (currentAt fresh (staged saved).inputs)
def advance := submit (staged saved) (responseWord saved)
abbrev I := inputAt fresh (advance saved).inputs

theorem inputs_exact : (advance saved).inputs = saved.inputs ++ [emit saved,responseWord saved] := by
  change (saved.inputs ++ [emit saved]) ++ [responseWord saved] = _
  rw [List.append_assoc]
  rfl

def execution := OutstandingSource.History.actualExecution (source fresh) (advance saved).inputs (saved.inputs.length + 1)
def responseExecution := OutstandingSource.History.actualExecution (source fresh) (advance saved).inputs ((staged saved).inputs.length + 1)

theorem actual_first_word_and_cut : (execution saved).submitted = emit saved ∧
    (execution saved).before = currentAt fresh saved.inputs := by
  constructor
  · have member : saved.inputs.length < (advance saved).inputs.length := by rw [inputs_exact]; simp
    have actual := OutstandingSource.History.scheduled_input_is_actual (source fresh) (advance saved).inputs saved.inputs.length member
    have same : (advance saved).inputs[saved.inputs.length] = emit saved := by
      simp only [inputs_exact,List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]
    exact actual.trans same
  · have common := OutstandingSource.History.extending_inputs_preserves_its_executed_prefix (source fresh) saved.inputs
      [emit saved,responseWord saved] (saved.inputs.length + 2) (Nat.le_refl _)
    change OutstandingSource.History.currentAt (source fresh) (advance saved).inputs (saved.inputs.length + 2) = _
    rw [(OutstandingSource.History.actual_frame _ _ _).1,inputs_exact,common]
    exact (OutstandingSource.History.actual_frame _ _ _).1.symm

theorem actual_response_word_and_cut : (responseExecution saved).submitted = responseWord saved ∧
    (responseExecution saved).before = currentAt fresh (staged saved).inputs := actual_word_and_cut _ _

def advanceFinanceRun : (Financial.Family.process Pending.Joint.Finance.sources).Run
    saved.finance.current (advance saved).finance.current :=
  (financialRun saved (emit saved)).concatRuns _ (financialRun (staged saved) (responseWord saved))

def advanceServiceRun (index : (source fresh).Slot) :
    (OutstandingSource.History.NativeService.threadProcess (source fresh) (epochInputs fresh)).Run
      (saved.services index).state.current ((advance saved).services index).state.current :=
  ((saved.services index).actualRun (source fresh) (emit saved)).concatRuns _
    (((staged saved).services index).actualRun (source fresh) (responseWord saved))

def evolve (saved : Inventory authority inventory fresh) : Nat → Inventory authority inventory fresh
  | 0 => saved
  | count + 1 => evolve (advance saved) count

def evolutionFinanceRun (saved : Inventory authority inventory fresh) : (count : Nat) →
    (Financial.Family.process Pending.Joint.Finance.sources).Run saved.finance.current (evolve saved count).finance.current
  | 0 => .nil
  | count + 1 => (advanceFinanceRun saved).concatRuns _ (evolutionFinanceRun (advance saved) count)

def evolutionServiceRun (saved : Inventory authority inventory fresh) (index : (source fresh).Slot) : (count : Nat) →
    (OutstandingSource.History.NativeService.threadProcess (source fresh) (epochInputs fresh)).Run
      (saved.services index).state.current ((evolve saved count).services index).state.current
  | 0 => .nil
  | count + 1 => (advanceServiceRun saved index).concatRuns _ (evolutionServiceRun (advance saved) index count)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation
