import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Material
import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Runtime

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure Seed where
  private mk ::
  basis : State
  original : Stream.Runtime.Result basis (Requests.finite 3) 9
  originalExact : original=Stream.Runtime.consume basis (Requests.finite 3) 9
  current : Frame basis
  currentExact : current=original.frame
  role : Option (Requests.Role basis)
  roleExact : role=Requests.role? basis

/-- One sealed old activation supplies its protocol, inventories and native archives. -/
@[noinline] def start (basis : State) : Seed :=
  let original := Stream.Runtime.consume basis (Requests.finite 3) 9
  let frame := original.frame
  ⟨basis,original,rfl,{frame with raw:=Supply.initialMemo frame.raw},by rw [Supply.initialMemo_exact],Requests.role? basis,rfl⟩

def initial (seed : Seed) := seed.current

theorem initial_is_the_actual_inherited_frame (seed : Seed) : initial seed=seed.original.frame := seed.currentExact

def due (seed : Seed) (requests : Requests.Source) (ordinal : Nat) (frame : Frame seed.basis) : Bool :=
  ordinal != 0 && decide (frame.raw.stock customer .feed<1 ∧ frame.raw.stock supplier .feed<1 ∧
    (frame.raw.stock receiver .energy<3 ∨ frame.raw.stock supplier .labor<2)) &&
  match frame.protocol.pending with
  | some window => decide (frame.raw.clock≤window.task.deadline)
  | none => match requests frame.protocol.received frame.raw.round with
    | none => false
    | some submission => decide (Requests.Shape submission frame.raw) && seed.role.isSome

theorem due_exact (seed : Seed) (requests : Requests.Source) (ordinal : Nat) (frame : Frame seed.basis) :
    due seed requests ordinal frame=Material.due seed.basis requests ordinal frame := by
  unfold due Material.due
  rw [seed.roleExact]
  cases pending : frame.protocol.pending with
  | some window => rfl
  | none =>
    cases received : requests frame.protocol.received frame.raw.round <;> rfl

def requestWord (seed : Seed) (before : Current) (submission : Requests.Submission) : List JointAction :=
  if Requests.Shape submission before ∧ seed.role.isSome then
    Requests.prepare seed.basis.origin.scope before ++ [submission.registration,submission.payment] else []

theorem requestWord_exact (seed : Seed) (before : Current) (submission : Requests.Submission) :
    requestWord seed before submission=Requests.word seed.basis seed.basis.origin.scope before submission := by
  simp only [requestWord,Requests.word,seed.roleExact]

def word (seed : Seed) (requests : Requests.Source) (mode : Material.Mode) (ordinal : Nat)
    (frame : Frame seed.basis) : List JointAction :=
  if due seed requests ordinal frame then Material.offer mode
  else if ordinal=0 then [] else
    match frame.protocol.pending with
    | some window =>
      if frame.raw.clock<window.task.earliest ∨ window.task.deadline<frame.raw.clock then []
      else (Stream.search seed.basis window frame.raw).word
    | none => match requests frame.protocol.received frame.raw.round with
      | none => []
      | some submission => requestWord seed frame.raw submission

theorem word_exact (seed : Seed) (requests : Requests.Source) (mode : Material.Mode) (ordinal : Nat)
    (frame : Frame seed.basis) : word seed requests mode ordinal frame=Material.word seed.basis requests mode ordinal frame := by
  unfold word Material.word
  rw [due_exact]
  by_cases supplying : Material.due seed.basis requests ordinal frame=true
  · simp only [if_pos supplying]
  · simp only [if_neg supplying]
    unfold Stream.word
    by_cases boot : ordinal=0
    · simp only [if_pos boot]
    · simp only [if_neg boot]
      cases pending : frame.protocol.pending with
      | some window => rfl
      | none =>
        cases received : requests frame.protocol.received frame.raw.round with
        | none => rfl
        | some submission => exact requestWord_exact _ _ _

def requestReceipt (seed : Seed) (before : Current) (submission : Requests.Submission) (actions : List JointAction) :=
  Requests.receipt? seed.basis seed.basis.origin.scope before submission actions

theorem requestReceipt_exact (seed : Seed) (before : Current) (submission : Requests.Submission) (actions : List JointAction) :
    requestReceipt seed before submission actions=Requests.receipt? seed.basis seed.basis.origin.scope before submission actions := rfl

def update (seed : Seed) (requests : Requests.Source) (mode : Material.Mode) (ordinal : Nat)
    (frame : Frame seed.basis) : Protocol seed.basis :=
  if ordinal=0 then frame.protocol else if due seed requests ordinal frame then frame.protocol else
  match frame.protocol.pending with
  | some _ => Stream.update seed.basis requests ordinal frame
  | none => match requests frame.protocol.received frame.raw.round with
    | none => {frame.protocol with event:=.idle}
    | some submission =>
      let actions := word seed requests mode ordinal frame
      match requestReceipt seed frame.raw submission actions with
      | none => {frame.protocol with received:=frame.protocol.received+1,event:=.refusedRequest}
      | some receipt =>
        ⟨frame.protocol.received+1,some (Requests.openWindow seed.basis frame.protocol.received frame.raw submission actions receipt),
          frame.protocol.expired,frame.protocol.completed,.admitted⟩

theorem update_exact (seed : Seed) (requests : Requests.Source) (mode : Material.Mode) (ordinal : Nat)
    (frame : Frame seed.basis) : update seed requests mode ordinal frame=
      if ordinal=0 then frame.protocol else Material.update seed.basis requests mode ordinal frame := by
  by_cases zero : ordinal=0
  · simp only [update,zero,if_pos]
  · simp only [update,if_neg zero,Material.update]
    rw [due_exact]
    split
    · rfl
    · rename_i absent
      cases pending : frame.protocol.pending with
      | some window => rfl
      | none =>
        have sameWord : word seed requests mode ordinal frame=Stream.word seed.basis requests ordinal frame := by
          rw [word_exact]
          exact if_neg absent
        rw [sameWord]
        unfold Stream.update
        simp only [if_neg zero,pending]
        cases received : requests frame.protocol.received frame.raw.round with
        | none => rfl
        | some submission =>
          simp only [requestReceipt]
          cases granted : Requests.receipt? seed.basis seed.basis.origin.scope frame.raw submission
              (Stream.word seed.basis requests ordinal frame) <;> rfl


def step (seed : Seed) (requests : Requests.Source) (mode : Material.Mode) (ordinal : Nat)
    (frame : Frame seed.basis) : Frame seed.basis :=
  ⟨Supply.initialMemo ((law seed.basis.origin.scope).next frame.raw (word seed requests mode ordinal frame)),
    update seed requests mode ordinal frame⟩

def run (seed : Seed) (requests : Requests.Source) (mode : Material.Mode) : Nat → Frame seed.basis
  | 0 => initial seed
  | ordinal+1 => step seed requests mode ordinal (run seed requests mode ordinal)

theorem run_round (seed : Seed) (requests : Requests.Source) (mode : Material.Mode) (ordinal : Nat) :
    (run seed requests mode ordinal).raw.round=(initial seed).raw.round+ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change (Supply.initialMemo _).round=_
    rw [Supply.initialMemo_exact]
    change (run seed requests mode ordinal).raw.round+1=_
    rw [ih];omega

def input (seed : Seed) (requests : Requests.Source) (mode : Material.Mode) : Finance.Input :=
  {law:=law seed.basis.origin.scope,initial:=(initial seed).raw,instructions:=[],
   emission?:=some fun current =>
     let ordinal := current.round-(initial seed).raw.round
     word seed requests mode ordinal (run seed requests mode ordinal)}

theorem own_current (seed : Seed) (requests : Requests.Source) (mode : Material.Mode) (ordinal : Nat) :
    ProgrammeSource.rawCurrent (input seed requests mode)
      (ProgrammeHistory.visitAt (input seed requests mode) ordinal).current=(run seed requests mode ordinal).raw := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change ProgrammeSource.rawCurrent (input seed requests mode)
      (ProgrammeSource.next (input seed requests mode)
        (ProgrammeHistory.visitAt (input seed requests mode) ordinal).current)=_
    rw [ProgrammeSource.actual_raw_next,ih]
    change (law seed.basis.origin.scope).next (run seed requests mode ordinal).raw _=(Supply.initialMemo _ )
    rw [Supply.initialMemo_exact]
    cases ordinal with
    | zero => rfl
    | succ ordinal =>
      congr 1
      have emitted : ProgrammeSource.rawEvent (input seed requests mode)
          (ProgrammeHistory.visitAt (input seed requests mode) (ordinal+1)).current=
          ProgrammeSource.wordAt (input seed requests mode)
            (ProgrammeSource.rawCurrent (input seed requests mode)
              (ProgrammeHistory.visitAt (input seed requests mode) (ordinal+1)).current) := by
        change ProgrammeSource.rawEvent (input seed requests mode)
          (ProgrammeSource.next (input seed requests mode)
            (ProgrammeHistory.visitAt (input seed requests mode) ordinal).current)=
          ProgrammeSource.wordAt (input seed requests mode)
            (ProgrammeSource.rawCurrent (input seed requests mode)
              (ProgrammeSource.next (input seed requests mode)
                (ProgrammeHistory.visitAt (input seed requests mode) ordinal).current))
        generalize (ProgrammeHistory.visitAt (input seed requests mode) ordinal).current=previous
        cases previous <;> rfl
      rw [emitted,ih]
      change word seed requests mode ((run seed requests mode (ordinal+1)).raw.round-(initial seed).raw.round)
          (run seed requests mode ((run seed requests mode (ordinal+1)).raw.round-(initial seed).raw.round))=_
      rw [run_round]
      simp

theorem all_due_responsibilities_survive (seed : Seed) (requests : Requests.Source) (mode : Material.Mode)
    (ordinal : Nat) :
    (initial seed).protocol.expired <+: (run seed requests mode ordinal).protocol.expired := by
  induction ordinal with
  | zero => exact List.prefix_rfl
  | succ ordinal ih =>
    apply ih.trans
    change _ <+: (update seed requests mode ordinal _).expired
    rw [update_exact]
    split
    · exact List.prefix_rfl
    · unfold Material.update
      split
      · exact List.prefix_rfl
      · exact Stream.due_responsibilities_are_never_dropped seed.basis requests ordinal _

open private Stream.safe_execution from H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream

theorem all_future_old_financial_positions (seed : Seed) (requests : Requests.Source) (mode : Material.Mode)
    (ordinal : Nat) (instrument : Instrument) (old : instrument≠.delivery) :
    (run seed requests mode ordinal).raw.claims instrument=(initial seed).raw.claims instrument := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change (Supply.initialMemo _).claims instrument=_
    rw [Supply.initialMemo_exact]
    rw [word_exact]
    exact (Stream.safe_execution _ _ _ 0 (Material.every_action_keeps_old_instruments seed.basis requests mode ordinal _)
      instrument old).trans ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume
