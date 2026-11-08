import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Residual
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.FloorGuard

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable Ready)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ordered : List TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Service.Ordinal source past)}

local notation "Receipt" => Network.Certificate (Service.network source past ordered.toFinset task reserved)
local notation "Rows" => Service.Need ordered.toFinset task
local notation "Request" => Source.Program.Request Party Good Port Technology Instrument
local notation "Now" => Execution.endAt source past

def dueNowWord (receipt : Receipt) (sign : Rows → Request) :
    RawEvent Party Good Port Technology Instrument :=
  residualWord receipt (Now).raw.clock sign

inductive LiveEntry (receipt : Receipt) (sign : Rows → Request)
  | pending (original : NativeObstruction Now)
  | review (closed : ¬ ReviewAvailable Now)
  | short (issue : AddressShortage (Now).raw (floorCharge source past (dueNowWord receipt sign))
      (floorSupport source (dueNowWord receipt sign)))
  | proceed (funded : ∀ key, floorCharge source past (dueNowWord receipt sign) key ≤
      (Now).raw.stock key.1 key.2)
      (continuation : Continuation receipt (Now).raw.clock sign [])

/-- Keep the old, unpaid floor before submitting any new debit. Amounts
that this word actually pays toward the floor reduce the required holding. -/
def submitDue (receipt : Receipt) (sign : Rows → Request)
    (opening : ∀ party good, 0 ≤ (Now).raw.stock party good) : LiveEntry receipt sign :=
  match observed : inspectNative Now with
  | some original => .pending original
  | none => if available : ReviewAvailable Now then
      match inspectFloorStock source past (dueNowWord receipt sign) opening with
      | .short issue => .short issue
      | .funded funds =>
        .proceed funds (prepare receipt (Now).raw.clock sign [] (by simp) opening
          (native_is_finished_without_a_pending_item _ observed) available)
    else .review available

theorem live_entry_produces_its_actual_due_proposal
    (receipt : Receipt) (sign : Rows → Request)
    (opening : ∀ party good, 0 ≤ (Now).raw.stock party good)
    (ready : Ready Now) (review : ReviewAvailable Now)
    (funds : ∀ key, floorCharge source past (dueNowWord receipt sign) key ≤ (Now).raw.stock key.1 key.2) :
    submitDue receipt sign opening =
      .proceed funds (prepare receipt (Now).raw.clock sign [] (by simp) opening ready review) := by
  unfold submitDue
  split
  · rename_i original _
    exact (ready original.pending).elim
  · rw [dif_pos review]
    split
    · rename_i issue _
      exact (not_lt_of_ge (funds issue.address) issue.short).elim
    · rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
