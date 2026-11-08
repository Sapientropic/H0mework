import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime.Schedule
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime.Payment
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.ProtectedSettlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ordered : List TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Service.Ordinal source past)}
  {receipt : Network.Certificate (Service.network source past ordered.toFinset task reserved)}
  {sign : Service.Need ordered.toFinset task → Source.Program.Request Party Good Port Technology Instrument}

local notation "Now" => Execution.endAt source past
local notation "Snapshot" => Service.Floor.Runtime.Snapshot source past
local notation "Word" => RawEvent Party Good Port Technology Instrument

def CheckAt (read : Snapshot) (authority : LawRead Now) (input : ScheduleRead receipt sign) :
    ScheduleDecision receipt sign input → Type
  | .window _ _ _ => Unit
  | .ready word _ _ => PaymentInspection read authority word

/-- Compile the literal due word and check its stock and policy using
only authenticated numeric readings and executable native law data. -/
def inspectDue (input : ScheduleRead receipt sign) (read : Snapshot) (authority : LawRead Now)
    (opening : ∀ party good, 0 ≤ read.current.stock party good) :
    (proposal : ScheduleDecision receipt sign input) × CheckAt read authority input proposal :=
  match schedule input with
  | .window row original failure => ⟨.window row original failure, ()⟩
  | .ready word exactWord timely =>
    ⟨.ready word exactWord timely, inspectPayment read authority word opening⟩

theorem an_accepted_runtime_word_settles_its_original_due_or_names_the_retained_floor
    (input : ScheduleRead receipt sign) (read : Snapshot) (authority : LawRead Now)
    (word : Word) (exactWord : word = residualWord receipt input.clock sign)
    (timely : ∀ line ∈ residualRows receipt input.clock, InWindow (Now).raw.clock line)
    (opening : ∀ party good, 0 ≤ read.current.stock party good)
    (ready : Ready Now) (review : ReviewAvailable Now)
    (funded : ∀ key, read.charge word key ≤ read.current.stock key.1 key.2)
    (permitted : Every authority.law read.current 0 word (Permitted authority.law)) :
    Nonempty (ProtectedOutcome receipt input.clock sign) := by
  subst word
  obtain ⟨⟨payment⟩, _⟩ := the_runtime_payment_is_admitted_by_the_original_root read authority _
    (residual_word_is_service receipt input.clock sign) (residual_word_has_no_old_controller_consents receipt input.clock sign)
    opening ready review funded permitted
  have stock (key : Party × Good) : floorCharge source past (residualWord receipt input.clock sign) key ≤
      (Now).raw.stock key.1 key.2 := by
    rw [← read.current_exact, ← read.charge_exact]
    exact funded key
  exact ⟨settleProtected payment timely stock⟩

def OriginalDisposition (input : ScheduleRead receipt sign) (read : Snapshot) (authority : LawRead Now) :
    ((proposal : ScheduleDecision receipt sign input) × CheckAt read authority input proposal) → Prop
  | ⟨.window _ _ _, _⟩ => Recorded source past
  | ⟨.ready word _ _, .stock issue⟩ =>
      Recorded source past ∧ (Now).raw.stock issue.address.1 issue.address.2 <
        floorCharge source past word issue.address
  | ⟨.ready word _ _, .refused issue⟩ =>
      Recorded source past ∧
        issue.original ∈ ((interpreter Now).execute (Now).raw 0 word).items ∧
        ¬ Permitted (interpreter Now) issue.original.before issue.original.request
  | ⟨.ready _ _ _, .ready _ _⟩ => Nonempty (ProtectedOutcome receipt input.clock sign)

theorem the_runtime_inspection_disposes_its_original_attempt
    (input : ScheduleRead receipt sign) (read : Snapshot) (authority : LawRead Now)
    (opening : ∀ party good, 0 ≤ read.current.stock party good)
    (ready : Ready Now) (review : ReviewAvailable Now) :
    OriginalDisposition input read authority (inspectDue input read authority opening) := by
  unfold inspectDue
  split
  · exact record source past
  · rename_i word exactWord timely _
    cases inspectPayment read authority word opening with
    | stock issue =>
      refine ⟨record source past, ?_⟩
      exact (congrArg (fun state => state.stock issue.address.1 issue.address.2)
        read.current_exact.symm).trans_lt (issue.short.trans_eq (read.charge_exact word issue.address))
    | refused issue =>
      refine ⟨record source past, ?_, ?_⟩
      · rw [← authority.exactLaw, ← read.current_exact]
        exact issue.occurs
      · rw [← authority.exactLaw]
        exact issue.refused
    | ready funds permit =>
      exact an_accepted_runtime_word_settles_its_original_due_or_names_the_retained_floor
        input read authority word exactWord timely opening ready review funds permit

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime
