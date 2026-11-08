import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Deadline.Frontier
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.ByAddress.Restricted
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Frontier

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def watchedAddresses (agenda : Agenda Party Good TaskId) (source : C) (script : Script) : List (Party × Good) :=
  Settlement.watched source script (agenda.atomic ++ agenda.fragments) agenda.task

abbrev stockProfile (agenda : Agenda Party Good TaskId) (source : C) (script : Script) :=
  Settlement.stockView source script agenda.fragments.toFinset agenda.task

def stockDecision (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ) :=
  (stockProfile agenda source script).inspectProtected (Liquidity.beforeStock source script)
    (watchedAddresses agenda source script) additional

def JointThrough (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ) (horizon : ℚ) : Prop :=
  ∃ choice : ChoiceAt agenda source script horizon,
    Settlement.JointThrough source script agenda.fragments.toFinset agenda.task choice.reserved
      (watchedAddresses agenda source script) additional horizon

theorem the_mixed_service_and_stock_conditions_share_one_original_execution
    (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ) (horizon : ℚ) :
    JointThrough agenda source script additional horizon ↔ ServedThrough agenda source script horizon ∧
      ∀ key ∈ watchedAddresses agenda source script, (stockProfile agenda source script).rollingReserveThrough
        (Liquidity.beforeStock source script) horizon key ≤ additional key := by
  constructor
  · rintro ⟨choice, jointly⟩
    have fit := (Settlement.the_joint_due_domain_is_exactly_the_original_service_and_stock_domain
      source script agenda.fragments.toFinset agenda.task choice.reserved
      (watchedAddresses agenda source script) additional horizon).mp jointly
    exact ⟨⟨choice, fit.1⟩, fit.2⟩
  · rintro ⟨⟨choice, service⟩, stock⟩
    exact ⟨choice, (Settlement.the_joint_due_domain_is_exactly_the_original_service_and_stock_domain
      source script agenda.fragments.toFinset agenda.task choice.reserved
      (watchedAddresses agenda source script) additional horizon).mpr ⟨service, stock⟩⟩

/-- Earliest unsafe maturity or physical reserve cut on one actual script. -/
def jointRenewalBoundary (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ) : WithTop ℚ :=
  min (serviceBoundary agenda source script (inspectFrontier agenda source script))
    (Settlement.stockTime _ _ _ _ (stockDecision agenda source script additional))

theorem the_mixed_renewal_boundary_is_the_exact_joint_original_cut
    (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ) (horizon : ℚ) (started : source.raw.clock ≤ horizon) :
    JointThrough agenda source script additional horizon ↔
      (horizon : WithTop ℚ) < jointRenewalBoundary agenda source script additional := by
  let stock := stockProfile agenda source script
  let keys := watchedAddresses agenda source script
  let before := Liquidity.beforeStock source script
  have stockDomain := stock.protected_safe_iff_tight_rolling_reserve before keys additional horizon started
  rw [the_mixed_service_and_stock_conditions_share_one_original_execution, jointRenewalBoundary, lt_min_iff]
  exact (serviceBoundary_exact agenda source script (inspectFrontier agenda source script) horizon).and
    (stockDomain.symm.trans (Settlement.stockTime_exact stock _ keys additional
      (stockDecision agenda source script additional) horizon))

theorem a_named_fragment_cut_keeps_the_original_due_bearer_and_material_bound
    (agenda : Agenda Party Good TaskId) (source : C) (script : Script) (horizon : ℚ)
    (choice : ChoiceAt agenda source script horizon) (named : NamedCut (networkAt agenda source script horizon choice))
    (key : Party × Good) :
    let net := base agenda source script choice.reserved
    let active := keepAt agenda horizon
    let rows := (linesAtAddress (ids := agenda.fragments.toFinset) (task := agenda.task) Finset.univ key).filter
      fun line => active line = true
    let group := (linesAtAddress (ids := agenda.fragments.toFinset) (task := agenda.task) named.receipt.group key).filter
      fun line => active line = true
    (∑ line ∈ rows, (net.need line - Network.rowTotal named.receipt.allocation line)) = net.gap group :=
  (each_original_address_has_its_exact_due_cut (keepAt agenda horizon) named.receipt key).1

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
