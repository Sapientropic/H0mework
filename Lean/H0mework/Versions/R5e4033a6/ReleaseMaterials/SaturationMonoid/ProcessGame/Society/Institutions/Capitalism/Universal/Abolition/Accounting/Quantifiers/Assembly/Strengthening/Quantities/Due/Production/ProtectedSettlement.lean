import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Admission
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Completion

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ordered : List TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Service.Ordinal source past)}
  {receipt : Network.Certificate (Service.network source past ordered.toFinset task reserved)}
  {dueBy : ℚ}
  {sign : Service.Need ordered.toFinset task → Source.Program.Request Party Good Port Technology Instrument}

local notation "Now" => Execution.endAt source past
local notation "Word" => residualWord receipt dueBy sign
local notation "Suffix" => Execution.primitiveScript Word

private def dueSuffix
    (chosen : Network.Certificate (Service.network source past ordered.toFinset task reserved))
    (timeLimit : ℚ) (signed : Service.Need ordered.toFinset task → Source.Program.Request Party Good Port Technology Instrument) :=
  Execution.primitiveScript (residualWord chosen timeLimit signed)

inductive ProtectedOutcome (receipt : Network.Certificate (Service.network source past ordered.toFinset task reserved))
    (dueBy : ℚ) (sign : Service.Need ordered.toFinset task → Source.Program.Request Party Good Port Technology Instrument)
  | remainingFloor (original : Demand.Deficit source (past ++ (dueSuffix receipt dueBy sign)))
      (whole : Recorded source (past ++ (dueSuffix receipt dueBy sign)))
      (served : Deadline.ServedThrough (Service.network source (past ++ (dueSuffix receipt dueBy sign)) ordered.toFinset task
        (Service.carryReservations source past (dueSuffix receipt dueBy sign) reserved)) Settlement.deadline dueBy)
      (remaining : ∀ key, Service.Floor.holding source (past ++ (dueSuffix receipt dueBy sign)) key ≤
        (Execution.endAt source (past ++ (dueSuffix receipt dueBy sign))).raw.stock key.1 key.2)
  | paid (settled : Settled source (past ++ (dueSuffix receipt dueBy sign)))
      (served : Deadline.ServedThrough (Service.network source (past ++ (dueSuffix receipt dueBy sign)) ordered.toFinset task
        (Service.carryReservations source past (dueSuffix receipt dueBy sign) reserved)) Settlement.deadline dueBy)
      (next : Execution.endAt source (past ++ (dueSuffix receipt dueBy sign)) = Execution.endAt Now (dueSuffix receipt dueBy sign))

/-- One admitted continuation can pay the floor together with the due use.
Any remaining floor stays at its own address with actual stock and account. -/
def settleProtected (payment : PaymentAt Now Word [])
    (timely : ∀ line ∈ residualRows receipt dueBy, InWindow (Now).raw.clock line)
    (funded : ∀ key, floorCharge source past Word key ≤ (Now).raw.stock key.1 key.2) :
    ProtectedOutcome receipt dueBy sign :=
  match Demand.inspect source (past ++ Suffix) with
  | .deficit original =>
    .remainingFloor original (record source _)
      (Service.paying_the_residual_pays_the_same_original_due_prefix receipt Settlement.deadline dueBy
        (the_original_suffix_pays_every_requested_unpaid_due_row payment timely)) fun key =>
      (original_floor_protection_is_exact_for_a_paid_word source past Word
        (residual_word_is_service receipt dueBy sign) payment key).mp (funded key)
  | .covered floorPaid =>
    let complete := the_prepared_service_word_pays_after_joint_original_floors payment timely floorPaid
    .paid complete.1 complete.2.1 complete.2.2

/-- The first component preserves the actual source disposition even
when no continuation was admitted. A paid continuation adds its floor and
due disposition on that very suffix. -/
def resolveLiveDue
    (receipt : Network.Certificate (Service.network source past ordered.toFinset task reserved))
    (sign : Service.Need ordered.toFinset task → Source.Program.Request Party Good Port Technology Instrument)
    (opening : ∀ party good, 0 ≤ (Now).raw.stock party good) :
    LiveEntry receipt sign × Option (ProtectedOutcome receipt (Now).raw.clock sign) :=
  let entry := submitDue receipt sign opening
  ⟨entry, match entry with
    | .proceed funds (.checked timely (.paid payment)) => some (settleProtected payment timely funds)
    | _ => none⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
