import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Joint
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Enumerate
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.MaterialSupport
import Mathlib.Order.WithBot

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

def watched (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task) :
    List (Party × Good) :=
  (((Service.needList ordered.toFinset task ordered rfl).map address ++
      Execution.materialAddresses source script) ++
    ((Demand.requirements source).map fun cell => (cell.1, cell.2.2.1))).dedup

theorem every_due_address_is_watched (source : C) (script : Script)
    (ordered : List TaskId) (task : TaskId → Task) (line : Service.Need ordered.toFinset task) :
    address line ∈ watched source script ordered task := by
  apply List.mem_dedup.mpr
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨line, Service.needList_covers _ _ _ _ line, rfl⟩

def serviceFrontier (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) :=
  Deadline.inspect (Service.network source script ordered.toFinset task reserved) deadline
    (Service.needList ordered.toFinset task ordered rfl)
    (Service.supplyList source script ordered.toFinset task ordered rfl)
    (Service.needList_covers _ _ _ rfl) (Service.supplyList_covers _ _ _ _ _ rfl)

def stockFrontier (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (additional : Party × Good → ℚ) :=
  (stockView source script ordered.toFinset task).inspectProtected
    (Liquidity.beforeStock source script) (watched source script ordered task) additional

def serviceTime {Row Item : Type*} [Fintype Row] [Fintype Item]
    (network : Network Row Item) (due : Row → ℚ) : Deadline.Frontier network due → WithTop ℚ
  | .clear _ => ⊤
  | .short first => first.time

theorem serviceTime_exact {Row Item : Type*} [Fintype Row] [Fintype Item] [DecidableEq Row]
    (network : Network Row Item) (due : Row → ℚ) (frontier : Deadline.Frontier network due) (time : ℚ) :
    Deadline.ServedThrough network due time ↔ (time : WithTop ℚ) < serviceTime network due frontier := by
  cases frontier with
  | clear all => simp [serviceTime, all time]
  | short first => simpa only [serviceTime, WithTop.coe_lt_coe] using first.safe_iff time

def stockTime {Addr Row Item : Type*} [Fintype Row] [Fintype Item]
    (view : Liquidity.Profile Addr Row Item) (score : ℚ → Addr → ℚ) (keys : List Addr)
    (additional : Addr → ℚ) : view.DecisionAt score keys additional → WithTop ℚ
  | .noFailure _ => ⊤
  | .blocked first => first.time

theorem stockTime_exact {Addr Row Item : Type*} [Fintype Row] [Fintype Item]
    (view : Liquidity.Profile Addr Row Item) (score : ℚ → Addr → ℚ) (keys : List Addr)
    (additional : Addr → ℚ) (frontier : view.DecisionAt score keys additional) (time : ℚ) :
    view.SafeThroughAt score keys additional time ↔ (time : WithTop ℚ) < stockTime view score keys additional frontier := by
  cases frontier with
  | noFailure all => simp [stockTime, all time]
  | blocked first => simpa only [stockTime, WithTop.coe_lt_coe] using first.safeThrough_iff time

/-- The first unsafe clock of this original agenda. Its finite endpoint
is an original shortage, so waiting up to that endpoint is strict. -/
def renewalBoundary (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) (additional : Party × Good → ℚ) : WithTop ℚ :=
  min (serviceTime _ _ (serviceFrontier source script ordered task reserved))
    (stockTime _ _ _ _ (stockFrontier source script ordered task additional))

theorem the_latest_safe_renewal_cut_is_tight_for_the_joint_original_agenda
    (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) (additional : Party × Good → ℚ)
    (horizon : ℚ) (started : source.raw.clock ≤ horizon) :
    JointThrough source script ordered.toFinset task reserved
      (watched source script ordered task) additional horizon ↔
      (horizon : WithTop ℚ) < renewalBoundary source script ordered task reserved additional := by
  let stock := stockView source script ordered.toFinset task
  let before := Liquidity.beforeStock source script
  let keys := watched source script ordered task
  have stockDomain := stock.protected_safe_iff_tight_rolling_reserve before keys additional horizon started
  rw [the_joint_due_domain_is_exactly_the_original_service_and_stock_domain, renewalBoundary, lt_min_iff]
  exact (serviceTime_exact _ _ (serviceFrontier source script ordered task reserved) horizon).and
    (stockDomain.symm.trans (stockTime_exact stock _ keys additional (stockFrontier source script ordered task additional) horizon))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement
