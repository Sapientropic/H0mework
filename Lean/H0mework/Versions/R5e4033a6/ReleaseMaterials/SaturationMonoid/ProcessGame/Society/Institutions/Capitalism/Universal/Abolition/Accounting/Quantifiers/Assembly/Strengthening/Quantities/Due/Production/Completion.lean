import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Allocation
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Advance
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.CarryJoin.Allocation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)

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
  {held : RawEvent Party Good Port Technology Instrument}

local notation "Now" => Execution.endAt source past
local notation "Word" => residualWord receipt dueBy sign
local notation "Suffix" => Execution.primitiveScript Word

theorem the_prepared_service_word_pays_after_joint_original_floors
    (paid : PaymentAt Now Word held)
    (timely : ∀ line ∈ residualRows receipt dueBy, InWindow (Now).raw.clock line)
    (floorPaid : Demand.Covers source (past ++ Suffix)) :
    Settled source (past ++ Suffix) ∧
      Deadline.ServedThrough
        (Service.network source (past ++ Suffix) ordered.toFinset task
          (Service.carryReservations source past Suffix reserved)) Settlement.deadline dueBy ∧
      Execution.endAt source (past ++ Suffix) = Execution.endAt Now Suffix := by
  have next := Execution.endAt_append source past Suffix
  have ready : ¬ Pending (Execution.endAt source (past ++ Suffix)) := by
    rw [next]
    exact paid.ready
  exact ⟨settle source _ ⟨floorPaid, ready⟩,
    Service.paying_the_residual_pays_the_same_original_due_prefix receipt Settlement.deadline dueBy
      (the_original_suffix_pays_every_requested_unpaid_due_row paid timely), next⟩

theorem the_prepared_service_word_pays_the_original_due_and_whole_account
    (paid : PaymentAt Now Word held)
    (timely : ∀ line ∈ residualRows receipt dueBy, InWindow (Now).raw.clock line)
    (floorPaid : Demand.Covers source past) :
    Settled source (past ++ Suffix) ∧
      Deadline.ServedThrough
        (Service.network source (past ++ Suffix) ordered.toFinset task
          (Service.carryReservations source past Suffix reserved)) Settlement.deadline dueBy ∧
      Execution.endAt source (past ++ Suffix) = Execution.endAt Now Suffix :=
  the_prepared_service_word_pays_after_joint_original_floors paid timely
    (paid.advance_the_original_settlement floorPaid).1.paid

theorem sufficient_original_funding_and_permission_execute_the_compiled_continuation
    (reserve : ∀ request ∈ held, IsService request)
    (opening : ∀ party good, 0 ≤ (Now).raw.stock party good)
    (ready : Ready Now) (review : ReviewAvailable Now)
    (timely : ∀ line ∈ residualRows receipt dueBy, InWindow (Now).raw.clock line)
    (funds : ∀ party good, required Word party good + required held party good ≤ (Now).raw.stock party good)
    (authorized : Every (interpreter Now) (Now).raw 0 Word (Permitted (interpreter Now))) :
    ∃ (windows : ∀ line ∈ residualRows receipt dueBy, InWindow (Now).raw.clock line)
      (paid : PaymentAt Now Word held),
      prepare receipt dueBy sign held reserve opening ready review = .checked windows (.paid paid) := by
  cases prepare receipt dueBy sign held reserve opening ready review with
  | window line original blocked => exact (blocked (timely line original)).elim
  | checked windows actual =>
    cases actual with
    | paid paid => exact ⟨windows, paid, rfl⟩
    | short issue => exact (not_lt_of_ge (funds issue.address.1 issue.address.2) issue.short).elim
    | refused issue => exact (issue.refused (authorized issue.original issue.occurs)).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
