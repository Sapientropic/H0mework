import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.DonorRelease

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Material
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

inductive Mode where | normal | withheld | wrongSigner
  deriving DecidableEq
inductive Refusal where | withheld | signer | stock | sourceLaw
  deriving DecidableEq
inductive SupplyStatus where | supplied | blocked (reason : Refusal)
  deriving DecidableEq

def quantity : ℚ := 6
def offer (mode : Mode) : List JointAction :=
  match mode with
  | .normal => [DonorRelease.request quantity]
  | .withheld => []
  | .wrongSigner => [{DonorRelease.request quantity with signer:=supplier}]

/-- Material is requested only for a real current request or a still-live service. -/
def due (basis : State) (requests : Requests.Source) (ordinal : Nat) (frame : Frame basis) : Bool :=
  ordinal != 0 && decide (frame.raw.stock customer .feed<1 ∧ frame.raw.stock supplier .feed<1 ∧
    (frame.raw.stock receiver .energy<3 ∨ frame.raw.stock supplier .labor<2)) &&
  match frame.protocol.pending with
  | some window => decide (frame.raw.clock≤window.task.deadline)
  | none => match requests frame.protocol.received frame.raw.round with
    | none => false
    | some submission => decide (Requests.Shape submission frame.raw) && (Requests.role? basis).isSome

def status (scope : Scope) (before : Current) (mode : Mode) : SupplyStatus :=
  if mode=.withheld then .blocked .withheld
  else if mode=.wrongSigner then .blocked .signer
  else if before.stock receiver .feed<quantity then .blocked .stock
  else if (law scope).Valid before (DonorRelease.request quantity) then .supplied
  else .blocked .sourceLaw

def word (basis : State) (requests : Requests.Source) (mode : Mode) (ordinal : Nat)
    (frame : Frame basis) : List JointAction :=
  if due basis requests ordinal frame then offer mode else Stream.word basis requests ordinal frame

def update (basis : State) (requests : Requests.Source) (_mode : Mode) (ordinal : Nat)
    (frame : Frame basis) : Protocol basis :=
  if due basis requests ordinal frame then frame.protocol else Stream.update basis requests ordinal frame

def step (basis : State) (requests : Requests.Source) (mode : Mode) (ordinal : Nat)
    (frame : Frame basis) : Frame basis :=
  ⟨(law basis.origin.scope).next frame.raw (word basis requests mode ordinal frame),
    update basis requests mode ordinal frame⟩

def run (basis : State) (requests : Requests.Source) (mode : Mode) : Nat → Frame basis
  | 0 => Stream.initial basis
  | ordinal+1 => step basis requests mode ordinal (run basis requests mode ordinal)

theorem no_material_tick_is_exactly_the_original_stream_step (basis : State) (requests : Requests.Source)
    (mode : Mode) (ordinal : Nat) (frame : Frame basis) (absent : due basis requests ordinal frame=false) :
    step basis requests mode ordinal frame=Stream.step basis requests ordinal frame := by
  simp only [step,word,update,absent,Bool.false_eq_true,if_false,Stream.step]

theorem replenishment_keeps_the_entire_request_protocol (basis : State) (requests : Requests.Source)
    (mode : Mode) (ordinal : Nat) (frame : Frame basis) (needed : due basis requests ordinal frame=true) :
    (step basis requests mode ordinal frame).protocol=frame.protocol := by
  simp only [step,update,needed,if_true]

theorem supplied_stock_is_the_original_donor_debit (scope : Scope) (before : Current)
    (service : scope.service≠native .common) (challenge : scope.challenge≠native .common)
    (accepted : status scope before .normal=.supplied) :
    ((law scope).step before (DonorRelease.request quantity)).stock receiver .feed=before.stock receiver .feed-quantity ∧
    ((law scope).step before (DonorRelease.request quantity)).stock customer .feed=before.stock customer .feed+quantity ∧
    ((law scope).step before (DonorRelease.request quantity)).claims=before.claims := by
  have enough : quantity≤before.stock receiver .feed := by
    by_contra short
    simp [status,lt_of_not_ge short] at accepted
  exact DonorRelease.actual_stock scope before quantity service challenge (by norm_num [quantity]) enough

theorem wrong_supplier_cannot_release_material (scope : Scope) (before : Current) :
    ¬(law scope).Valid before {DonorRelease.request quantity with signer:=supplier} :=
  DonorRelease.wrong_provider_signer_is_rejected scope before quantity

theorem run_round (basis : State) (requests : Requests.Source) (mode : Mode) (ordinal : Nat) :
    (run basis requests mode ordinal).raw.round=basis.raw.round+ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => change (run basis requests mode ordinal).raw.round+1=_;rw [ih];omega

def input (basis : State) (requests : Requests.Source) (mode : Mode) : Finance.Input :=
  {law:=law basis.origin.scope,initial:=basis.raw,instructions:=[],
   emission?:=some fun current =>
     let ordinal := current.round-basis.raw.round
     word basis requests mode ordinal (run basis requests mode ordinal)}

theorem own_current (basis : State) (requests : Requests.Source) (mode : Mode) (ordinal : Nat) :
    ProgrammeSource.rawCurrent (input basis requests mode)
      (ProgrammeHistory.visitAt (input basis requests mode) ordinal).current=(run basis requests mode ordinal).raw := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change ProgrammeSource.rawCurrent (input basis requests mode)
      (ProgrammeSource.next (input basis requests mode)
        (ProgrammeHistory.visitAt (input basis requests mode) ordinal).current)=_
    rw [ProgrammeSource.actual_raw_next,ih]
    change (law basis.origin.scope).next (run basis requests mode ordinal).raw _=_
    cases ordinal with
    | zero => rfl
    | succ ordinal =>
      congr 1
      have emitted : ProgrammeSource.rawEvent (input basis requests mode)
          (ProgrammeHistory.visitAt (input basis requests mode) (ordinal+1)).current=
          ProgrammeSource.wordAt (input basis requests mode)
            (ProgrammeSource.rawCurrent (input basis requests mode)
              (ProgrammeHistory.visitAt (input basis requests mode) (ordinal+1)).current) := by
        change ProgrammeSource.rawEvent (input basis requests mode)
          (ProgrammeSource.next (input basis requests mode)
            (ProgrammeHistory.visitAt (input basis requests mode) ordinal).current)=
          ProgrammeSource.wordAt (input basis requests mode)
            (ProgrammeSource.rawCurrent (input basis requests mode)
              (ProgrammeSource.next (input basis requests mode)
                (ProgrammeHistory.visitAt (input basis requests mode) ordinal).current))
        generalize (ProgrammeHistory.visitAt (input basis requests mode) ordinal).current=previous
        cases previous <;> rfl
      rw [emitted,ih]
      change word basis requests mode ((run basis requests mode (ordinal+1)).raw.round-basis.raw.round)
          (run basis requests mode ((run basis requests mode (ordinal+1)).raw.round-basis.raw.round))=_
      rw [run_round]
      simp

theorem all_due_responsibilities_survive (basis : State) (requests : Requests.Source) (mode : Mode)
    (ordinal : Nat) :
    (Stream.initial basis).protocol.expired <+: (run basis requests mode ordinal).protocol.expired := by
  induction ordinal with
  | zero => exact List.prefix_rfl
  | succ ordinal ih =>
    apply ih.trans
    change _ <+: (update basis requests mode ordinal _).expired
    unfold update
    split
    · exact List.prefix_rfl
    · exact Stream.due_responsibilities_are_never_dropped basis requests ordinal _

theorem every_action_keeps_old_instruments (basis : State) (requests : Requests.Source) (mode : Mode)
    (ordinal : Nat) (frame : Frame basis) :
    ∀ action∈word basis requests mode ordinal frame,Historical action := by
  unfold word
  split
  · cases mode <;> simp [offer,DonorRelease.request,Historical]
  · exact Stream.every_submitted_action_keeps_old_claims basis requests ordinal frame

open private Stream.safe_execution from H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream
theorem all_future_old_financial_positions (basis : State) (requests : Requests.Source) (mode : Mode)
    (ordinal : Nat) (instrument : Instrument) (old : instrument≠.delivery) :
    (run basis requests mode ordinal).raw.claims instrument=basis.raw.claims instrument := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    exact (Stream.safe_execution _ _ _ 0 (every_action_keeps_old_instruments basis requests mode ordinal _)
      instrument old).trans ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Material
