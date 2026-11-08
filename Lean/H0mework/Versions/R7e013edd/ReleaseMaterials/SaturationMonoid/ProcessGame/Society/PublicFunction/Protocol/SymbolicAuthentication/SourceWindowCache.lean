import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredProductiveConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceWindowCache
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
 (terms : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))

-- The retained state is a computational cache; the source cursor still owns every event.
def rowAt {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
 (cursor : Cursor code) (before : Feedback.State code) (protocol : Rule code) (rival : Opponent code) :
 StageTrace.Record (code := code) :=
 let call := StageTrace.capture cursor protocol rival before
 let selected : Input code := ⟨fun _ _ _ => ControlExecution.admitted code call,cursor.entry.budget⟩
 ⟨cursor,protocol,before,call,word code (some protocol.work.val) selected before,
  Reaction.Feedback.advance code (some protocol.work.val) selected before⟩

theorem rowAt_is_the_actual_row {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
 (cursor : Cursor code) (before : Feedback.State code) (same : before=EventStep.seed cursor)
 (protocol : Rule code) (rival : Opponent code) :
 rowAt cursor before protocol rival=StageTrace.material cursor protocol rival := by subst before;rfl

variable (saved : Cursor old) (before : Feedback.State old) (enabled accept : Bool)

def lifted := Extension.state old (CatalogueHandoffSource.supply old (PaidInvocationSource.catalogue old terms)) before
def payment := rowAt (PaidInvocationSource.start old terms saved) (lifted old terms before)
 (PaidInvocationSource.protocol old terms enabled) (EventStep.fixed none)
def delivery := rowAt ((PaidInvocationSource.start old terms saved).after
 (PaidInvocationSource.protocol old terms enabled) (EventStep.fixed none))
 (payment old terms saved before enabled).after SilentWindow.quiet (PaidInvocationSource.supplier old terms accept)
def paid := ((PaidInvocationSource.start old terms saved).after
 (PaidInvocationSource.protocol old terms enabled) (EventStep.fixed none)).after
 SilentWindow.quiet (PaidInvocationSource.supplier old terms accept)

def Full : Prop :=
 (payment old terms saved before enabled).submitted=[terms.payment] ∧
 (delivery old terms saved before enabled accept).submitted=[terms.acceptance] ∧
 terms.payment.signer=terms.payer ∧ terms.acceptance.signer=terms.provider ∧
 (∀ item∈StageTrace.items (payment old terms saved before enabled),old.law.Valid item.before item.request) ∧
 (∀ item∈StageTrace.items (delivery old terms saved before enabled accept),old.law.Valid item.before item.request) ∧
 0<terms.units ∧ 0<terms.steps ∧
 flowAt (old.law.actualDebit (payment old terms saved before enabled).before.current terms.payment) terms.payer terms.unit=terms.units ∧
 flowAt (old.law.actualCredit (payment old terms saved before enabled).before.current terms.payment) terms.provider terms.unit=terms.units ∧
 (paid old terms saved enabled accept).cut≤(paid old terms saved enabled accept).entry.budget
instance : Decidable (Full old terms saved before enabled accept) := by unfold Full;infer_instance
def admitted : Bool := decide (Full old terms saved before enabled accept)
def point := if admitted old terms saved before enabled accept then
 PaidInvocationRebase.cursor (paid old terms saved enabled accept) terms.steps else paid old terms saved enabled accept
def after : Feedback.State (PaidInvocationSource.code old terms) :=
 if admitted old terms saved before enabled accept then
 PaidInvocationRebase.credit (delivery old terms saved before enabled accept).after terms.steps
 else (delivery old terms saved before enabled accept).after

variable (same : before=EventStep.seed saved) (original : saved.side=.original)
include same original

theorem payment_is_the_original_actual_row :
 payment old terms saved before enabled=PaidInvocationSource.paymentRow old terms saved enabled := by
 apply rowAt_is_the_actual_row
 exact (congrArg (Extension.state old (CatalogueHandoffSource.supply old (PaidInvocationSource.catalogue old terms))) same).trans
  (CatalogueHandoffSource.seed old (PaidInvocationSource.catalogue old terms) saved original).symm

theorem delivery_is_the_original_actual_row :
 delivery old terms saved before enabled accept=PaidInvocationSource.acceptanceRow old terms saved enabled accept := by
 apply rowAt_is_the_actual_row
 rw [payment_is_the_original_actual_row old terms saved before enabled same original]
 exact (StageTrace.material_is_the_actual_step _ _ _).1

theorem admission_is_the_original_source_guard :
 admitted old terms saved before enabled accept=PaidInvocationSource.admitted old terms saved enabled accept := by
 unfold admitted PaidInvocationSource.admitted
 apply decide_eq_decide.mpr
 unfold Full PaidInvocationSource.Full
 rw [payment_is_the_original_actual_row old terms saved before enabled same original,
  delivery_is_the_original_actual_row old terms saved before enabled accept same original]
 rfl

theorem after_is_the_entire_actual_endpoint :
 after old terms saved before enabled accept=EventStep.seed (point old terms saved before enabled accept) := by
 have endState : (delivery old terms saved before enabled accept).after=EventStep.seed (paid old terms saved enabled accept) := by
  rw [delivery_is_the_original_actual_row old terms saved before enabled accept same original]
  exact (StageTrace.material_is_the_actual_step _ _ _).1
 by_cases accepted : admitted old terms saved before enabled accept=true
 · have endpoint : point old terms saved before enabled accept=
    PaidInvocationRebase.cursor (paid old terms saved enabled accept) terms.steps := if_pos accepted
   rw [endpoint]
   change (if admitted old terms saved before enabled accept then
    PaidInvocationRebase.credit (delivery old terms saved before enabled accept).after terms.steps
    else (delivery old terms saved before enabled accept).after)=_
   rw [if_pos accepted]
   rw [endState]
   apply (PaidInvocationRebase.seed_credit _ _ ?_).symm
   exact (of_decide_eq_true accepted : Full old terms saved before enabled accept).2.2.2.2.2.2.2.2.2.2
 · have endpoint : point old terms saved before enabled accept=paid old terms saved enabled accept := if_neg accepted
   rw [endpoint]
   exact (if_neg accepted).trans endState

theorem point_is_the_original_generated_window :
 point old terms saved before enabled accept=
 (match PaidInvocationSource.produce old terms saved enabled accept with
  | .opened account => account.point | .blocked _ account => account.point) := by
 unfold point
 split
 · rename_i accepted
   have actual := (admission_is_the_original_source_guard old terms saved before enabled accept same original).symm.trans accepted
   rw [PaidInvocationSource.actual_admission_generates_the_paid_window old terms saved enabled accept actual]
   rfl
 · rename_i refused
   have actual : PaidInvocationSource.admitted old terms saved enabled accept=false := by
    rw [← admission_is_the_original_source_guard old terms saved before enabled accept same original]
    exact Bool.eq_false_iff.mpr refused
   rw [PaidInvocationSource.absent_payment_or_acceptance_cannot_open_the_window old terms saved enabled accept actual]
   rfl

omit same original in
theorem cached_point_keeps_the_source_side :
 (point old terms saved before enabled accept).side=saved.side := by
 unfold point
 split <;> rfl

omit same original
section Physical
variable (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (cursor : Cursor model.source.code) (retained : Feedback.State model.source.code)

def modelAfter : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument) :=
 ⟨model.base,model.scope,(point model.source.code terms cursor retained enabled accept).source,
  model.law_exact,model.task_exact⟩

def output : FreshSigningReplay.Physical (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument) :=
 ⟨modelAfter terms enabled accept model cursor retained,point model.source.code terms cursor retained enabled accept⟩

omit old saved before same original in
theorem output_is_the_original_renewal
 (state : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (retained : Feedback.State state.model.source.code)
 (same : retained=EventStep.seed state.point) (original : state.point.side=.original) :
 output terms enabled accept state.model state.point retained=
 FreshSigningReplay.physical (RenewableArchiveSource.renew terms state enabled accept) := by
 have samePoint : point state.model.source.code terms state.point retained enabled accept=
   (RenewableArchiveSource.window terms state enabled accept).point := by
  have admission := admission_is_the_original_source_guard state.model.source.code terms state.point retained enabled accept same original
  unfold point
  split
  · rename_i accepted
    have opened := PaidInvocationSource.actual_admission_generates_the_paid_window state.model.source.code terms state.point enabled accept (admission.symm.trans accepted)
    simp only [RenewableArchiveSource.Window.point,RenewableArchiveSource.Window.result,
     RenewableArchiveSource.window,opened,PaidInvocationSource.opened]
    rfl
  · rename_i refused
    have unpaid : PaidInvocationSource.admitted state.model.source.code terms state.point enabled accept=false :=
     Bool.eq_false_iff.mpr (fun accepted => refused (admission.trans accepted))
    have blocked := PaidInvocationSource.absent_payment_or_acceptance_cannot_open_the_window state.model.source.code terms state.point enabled accept unpaid
    simp only [RenewableArchiveSource.Window.point,RenewableArchiveSource.Window.result,
     RenewableArchiveSource.window,blocked,PaidInvocationSource.initial]
    rfl
 exact congrArg (fun point : Cursor (PaidInvocationSource.code state.model.source.code terms) =>
  (⟨⟨state.model.base,state.model.scope,point.source,state.model.law_exact,state.model.task_exact⟩,point⟩ :
   FreshSigningReplay.Physical (Party := Party) (Good := Good) (Port := Port)
   (Technology := Technology) (Instrument := Instrument))) samePoint

end Physical

section Transport
variable (terms : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (enabled accept : Bool)
 (state : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (cursor : Cursor model.source.code) (retained : Feedback.State model.source.code)

theorem renewal_at_the_same_complete_cached_occurrence
 (physical : FreshSigningReplay.physical state=⟨model,cursor⟩)
 (same : retained=EventStep.seed cursor) (original : cursor.side=.original) :
 FreshSigningReplay.physical (RenewableArchiveSource.renew terms state enabled accept)=
 output terms enabled accept model cursor retained := by
 cases state
 cases physical
 exact (output_is_the_original_renewal terms enabled accept _ retained same original).symm

theorem admission_at_the_same_complete_cached_occurrence
 (physical : FreshSigningReplay.physical state=⟨model,cursor⟩)
 (same : retained=EventStep.seed cursor) (original : cursor.side=.original) :
 PaidInvocationSource.admitted state.model.source.code terms state.point enabled accept=
 admitted model.source.code terms cursor retained enabled accept := by
 cases state
 cases physical
 exact (admission_is_the_original_source_guard _ terms _ retained enabled accept same original).symm

end Transport

section FreshCycle
variable {root : RenewableCodeLineage.Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}
 (terms : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (laws : (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) → StageReception.Law model.source.code)
 (state : JointReceptionSource.State root)
 (request : FreshSigningSource.Request (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))

theorem a_zero_repair_cycle_has_the_complete_cached_occurrence (zero : request.depth=0) :
 FreshSigningReplay.physical (FreshSigningSource.cycle terms base laws state request).actual=
 ⟨(FreshSigningSource.prepared terms state request).actual.model,
  (SourceDynamicCache.Fresh.generated base laws (FreshSigningSource.prepared terms state request) request).cursor⟩ :=
 SourceDynamicCache.Fresh.zero_repair_keeps_the_entire_original_model_and_cached_cursor
  base laws (FreshSigningSource.prepared terms state request) request terms zero

end FreshCycle

section Side
variable (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (origin : Cursor model.source.code) (baseline : Nat)
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (law : StageReception.Law model.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument))

theorem cached_stream_keeps_the_source_side (count : Nat) :
 (SourceDynamicCache.stream model origin baseline base law work count).cursor.side=origin.side := by
 induction count with
 | zero => rfl
 | succ count ih =>
  change (SourceDynamicCache.stream model origin baseline base law work count).cursor.side=origin.side
  exact ih

theorem actual_window_keeps_the_source_side
 (window : RenewableArchiveSource.Window (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) : window.point.side=window.before.side := by
 unfold RenewableArchiveSource.Window.point RenewableArchiveSource.Window.result
 unfold PaidInvocationSource.produce PaidInvocationSource.redeem
 split_ifs <;> rfl

end Side
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceWindowCache
