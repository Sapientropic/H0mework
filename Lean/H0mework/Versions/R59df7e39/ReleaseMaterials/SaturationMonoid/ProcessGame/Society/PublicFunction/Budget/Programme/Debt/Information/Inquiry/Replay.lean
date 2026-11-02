import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Deployment
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Continuation

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

abbrev Word := RawEvent Party Good Port (Mandate.State Party Technology) Instrument

variable (worker : Fin code.sites) (requested : Word (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

def policy : code.Policy := fun key _ => if key.1 = worker then requested else []
def events : EventTable code := fun key _ =>
  if key.1 = worker then choose key.1 (activations key.1) else waiting key.1

def protocol (supported : requested ∈ words code.actions code.actionLimit) :
    Distributed.Recall.Information.Agency.Protocol.Rule code :=
  ⟨⟨policy worker requested,code.every_local_policy_is_enumerated _ (by
      intro key _
      by_cases owned : key.1 = worker
      · simpa only [policy,if_pos owned] using supported
      · simp only [policy,if_neg owned]
        exact (mem_words_iff _ _ _).mpr ⟨Nat.zero_le _,by simp⟩)⟩,events worker⟩

variable (point : View (code := code)) (rival : Opponent code)

abbrev submitted (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) :=
  ((point.point.target rule rival).actualExecution (depth point.point)).submitted
abbrev before (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) :=
  ((point.point.target rule rival).actualExecution (depth point.point)).before

inductive Attempt where
  | unsupported (outside : requested ∉ words code.actions code.actionLimit)
  | withheld (supported : requested ∈ words code.actions code.actionLimit)
      (different : submitted point rival (protocol worker requested supported) ≠ requested)
  | refused (supported : requested ∈ words code.actions code.actionLimit)
      (emitted : submitted point rival (protocol worker requested supported) = requested)
      (illegal : ¬ Open.Legal code.law (before point rival (protocol worker requested supported)) requested)
  | paid (supported : requested ∈ words code.actions code.actionLimit)
      (emitted : submitted point rival (protocol worker requested supported) = requested)
      (legal : Open.Legal code.law (before point rival (protocol worker requested supported)) requested)

def inspect : Attempt worker requested point rival :=
  if supported : requested ∈ words code.actions code.actionLimit then
    if emitted : submitted point rival (protocol worker requested supported) = requested then
      if legal : Open.Legal code.law (before point rival (protocol worker requested supported)) requested then
        .paid supported emitted legal
      else .refused supported emitted legal
    else .withheld supported emitted
  else .unsupported supported

variable {worker requested point rival}

def Attempt.rule : Attempt worker requested point rival → Option (Distributed.Recall.Information.Agency.Protocol.Rule code)
  | .unsupported _ => none
  | .withheld supported _ | .refused supported _ _ | .paid supported _ _ => some (protocol worker requested supported)

def Attempt.next (attempt : Attempt worker requested point rival) : View (code := code) :=
  match attempt.rule with
  | none => point
  | some rule => Evidence.after point rule rival

def Attempt.views (attempt : Attempt worker requested point rival) (views : List (View (code := code))) :=
  match attempt.rule with
  | none => views
  | some rule => successors rule views

theorem every_attempt_keeps_an_actual_original_debt_representative
    (attempt : Attempt worker requested point rival) (views : List (View (code := code)))
    (covered : Knowledge.Contains views point) : Knowledge.Contains (attempt.views views) attempt.next := by
  cases attempt <;> first | exact covered | exact Knowledge.after views point covered _ rival

namespace PublicDomain
open Distributed.Recall.Information.Agency

def quiet : Bool := (moves code).all fun move => (externalChoice code move).isNone

def silent : Opponent code := fun _ _ _ => none

omit [DecidableEq Port] [DecidableEq Technology] in
theorem quiet_filters_every_actual_move (checked : quiet (code := code) = true) (move : Move code) :
    externalChoice code move = none := by
  have clean := (List.all_eq_true.mp checked) move (every_move_is_generated code move)
  exact Option.isNone_iff_eq_none.mp clean

omit [DecidableEq Port] [DecidableEq Technology] in
theorem quiet_controllers_are_identical (checked : quiet (code := code) = true)
    (point : Cursor code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : Cursor.controller point rule rival = Cursor.controller point rule silent := by
  funext history past frame
  simp only [Cursor.controller,Distributed.Recall.Information.Agency.Protocol.driver]
  cases ownerAt code point.ownerStart history.length with
  | some site => rfl
  | none =>
    change externalChoice code (rival history past frame) = externalChoice code (silent history past frame)
    rw [quiet_filters_every_actual_move checked (rival history past frame),
      quiet_filters_every_actual_move checked (silent history past frame)]

theorem quiet_after_is_the_same_actual_source (checked : quiet (code := code) = true)
    (point : Cursor code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : point.after rule rival = point.after rule silent := by
  have identical := quiet_controllers_are_identical checked point rule rival
  unfold Cursor.after Cursor.target Cursor.targetInput
  rw [identical]

def next (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) (views : List (View (code := code))) :=
  if quiet (code := code) then views.map (fun view => Evidence.after view rule silent) else successors rule views

theorem after (views : List (View (code := code))) (actual : View (code := code))
    (covered : Knowledge.Contains views actual) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : Knowledge.Contains (next rule views) (Evidence.after actual rule rival) := by
  unfold next
  split
  · rename_i checked
    obtain ⟨representative,inside,matched⟩ := covered
    refine ⟨Evidence.after representative rule silent,List.mem_map.mpr ⟨representative,inside,rfl⟩,?_,matched.origin⟩
    change Aligned (representative.point.after rule silent) (actual.point.after rule rival)
    rw [←quiet_after_is_the_same_actual_source checked representative.point rule rival]
    exact matched.cursor.after rule rival
  · exact Knowledge.after views actual covered rule rival

end PublicDomain

variable (worker)

inductive Path (worker : Fin code.sites) : List (View (code := code)) → View (code := code) →
    List (Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) →
      Opponent code → Type where
  | complete {views point rival} : Path worker views point [] rival
  | unsupported {views point requested rest rival}
      (outside : requested ∉ words code.actions code.actionLimit) : Path worker views point (requested::rest) rival
  | withheld {views point requested rest rival}
      (supported : requested ∈ words code.actions code.actionLimit)
      (different : submitted point rival (protocol worker requested supported) ≠ requested) :
      Path worker views point (requested::rest) rival
  | refused {views point requested rest rival}
      (supported : requested ∈ words code.actions code.actionLimit)
      (emitted : submitted point rival (protocol worker requested supported) = requested)
      (illegal : ¬ Open.Legal code.law (before point rival (protocol worker requested supported)) requested) :
      Path worker views point (requested::rest) rival
  | paid {views point requested rest rival}
      (supported : requested ∈ words code.actions code.actionLimit)
      (emitted : submitted point rival (protocol worker requested supported) = requested)
      (legal : Open.Legal code.law (before point rival (protocol worker requested supported)) requested)
      (tail : Path worker (PublicDomain.next (protocol worker requested supported) views)
        (Evidence.after point (protocol worker requested supported) rival) rest rival) :
      Path worker views point (requested::rest) rival

def generate (views : List (View (code := code))) (point : View (code := code)) :
    (requested : List (Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) →
      (rival : Opponent code) → Path worker views point requested rival
  | [],_ => .complete
  | requested::rest,rival => match inspect worker requested point rival with
    | .unsupported outside => .unsupported outside
    | .withheld supported different => .withheld supported different
    | .refused supported emitted illegal => .refused supported emitted illegal
    | .paid supported emitted legal => .paid supported emitted legal
        (generate (PublicDomain.next (protocol worker requested supported) views)
          (Evidence.after point (protocol worker requested supported) rival) rest rival)

namespace Path
variable {worker} {views : List (View (code := code))} {point : View (code := code)}
  {requested : List (Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))}
  {rival : Opponent code}

def rules : {views : List (View (code := code))} → {point : View (code := code)} →
    {requested : List (Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))} →
    {rival : Opponent code} → Path worker views point requested rival → List (Distributed.Recall.Information.Agency.Protocol.Rule code)
  | _,_,_,_,.complete | _,_,_,_,.unsupported _ => []
  | _,_,_,_,.withheld supported _ | _,_,_,_,.refused supported _ _ => [protocol worker _ supported]
  | _,_,_,_,.paid supported _ _ tail => protocol worker _ supported :: tail.rules

def successful : {views : List (View (code := code))} → {point : View (code := code)} →
    {requested : List (Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))} →
    {rival : Opponent code} → Path worker views point requested rival → Nat
  | _,_,_,_,.complete | _,_,_,_,.unsupported _ | _,_,_,_,.withheld _ _ | _,_,_,_,.refused _ _ _ => 0
  | _,_,_,_,.paid _ _ _ tail => tail.successful+1

def final (path : Path worker views point requested rival) :=
  path.rules.foldl (fun current rule => Evidence.after current rule rival) point
def finalViews (path : Path worker views point requested rival) :=
  path.rules.foldl (fun current rule => PublicDomain.next rule current) views

theorem final_keeps_the_actual_original_debt (path : Path worker views point requested rival)
    (covered : Knowledge.Contains views point) : Knowledge.Contains path.finalViews path.final := by
  unfold finalViews final
  generalize path.rules = rules
  clear path
  induction rules generalizing views point with
  | nil => exact covered
  | cons rule rest ih => exact ih (PublicDomain.after views point covered rule rival)

theorem stops_at_the_first_unsuccessful_requested_word (path : Path worker views point requested rival) :
    path.successful ≤ requested.length ∧ path.rules.length ≤ path.successful+1 := by
  induction path with
  | complete => exact ⟨Nat.le_refl _,Nat.zero_le _⟩
  | unsupported => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | withheld => exact ⟨Nat.zero_le _,Nat.le_refl _⟩
  | refused => exact ⟨Nat.zero_le _,Nat.le_refl _⟩
  | paid supported emitted legal tail ih => exact ⟨Nat.succ_le_succ ih.1,Nat.succ_le_succ ih.2⟩

end Path
end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay
