import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Domain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort

open Abolition.Root Abolition.Root.Registered
open Bounds System

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

inductive BudgetIssue (origin : C) (meter : Meter.{u} origin) (exposure : Script)
    (limit : Address origin meter exposure → EReal) (repair : Script)
  | accounting (issue : Obstruction (Execution.endAt origin exposure) repair)
  | shortage (loss : Loss origin exposure repair)
  | excess (address : Address origin meter exposure) (short : limit address < profile origin meter exposure repair address)

theorem BudgetIssue.refutes {origin : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)}
    {meter : Meter.{u} origin} {exposure repair : Script} {limit : Address origin meter exposure → EReal}
    (issue : BudgetIssue origin meter exposure limit repair) :
    ¬ (PaidRecovery origin exposure repair ∧ profile origin meter exposure repair ≤ limit) := by
  rintro ⟨paid, fits⟩
  cases issue with
  | accounting original => exact original.refutes paid.settled.toFeasible
  | shortage loss => exact (not_le_of_gt loss.unpaid) (paid.restored loss.address.1 loss.address.2)
  | excess address short => exact (not_le_of_gt short) (fits address)

inductive BudgetDecision (origin : C) (meter : Meter.{u} origin) (exposure : Script)
    (limit : Address origin meter exposure → EReal)
  | paid (repair : Script) (settled : PaidRecovery origin exposure repair)
      (fits : profile origin meter exposure repair ≤ limit)
  | blocked (every : ∀ repair, Recorded origin (exposure ++ repair) ∧
      Nonempty (BudgetIssue origin meter exposure limit repair))

/-- One repair pays the simultaneous allowances. Each rejected word
keeps its whole original ledger and a concrete accounting, material or
personal time obstruction. -/
def decideBudget (origin : C) (meter : Meter.{u} origin) (exposure : Script)
    (limit : Address origin meter exposure → EReal) :
    BudgetDecision origin meter exposure limit :=
  match System.decideBox (Execution.endAt origin exposure) id (repairCheck origin exposure)
      (profile origin meter exposure) limit with
  | .paid repair paid restored fits =>
    .paid repair ⟨paid, (repair_passes_iff_original_stock_is_restored origin exposure repair).mp restored,
      record origin _⟩ fits
  | .blocked every => .blocked fun repair => ⟨record origin _, by
    obtain ⟨issue⟩ := (every repair).2
    cases issue with
    | original missing => exact ⟨.accounting missing⟩
    | requirement issue => exact ⟨.shortage issue.2.1⟩
    | address address short => exact ⟨.excess address short⟩⟩

theorem simultaneous_budget_iff_one_actual_repair_pays_every_cap
    (origin : C) (meter : Meter.{u} origin) (exposure : Script)
    (limit : Address origin meter exposure → EReal) :
    (∃ values ∈ domain origin meter exposure, values ≤ limit) ↔
      ∃ repair, PaidRecovery origin exposure repair ∧ profile origin meter exposure repair ≤ limit := by
  constructor
  · rintro ⟨values, admitted, fits⟩
    obtain ⟨repair, paid, rfl⟩ := (mem_domain_iff_one_original_paid_repair origin meter exposure values).mp admitted
    exact ⟨repair, paid, fits⟩
  · rintro ⟨repair, paid, fits⟩
    exact ⟨_, (mem_domain_iff_one_original_paid_repair origin meter exposure _).mpr ⟨repair, paid, rfl⟩, fits⟩

theorem incomparable_cohort_repairs_name_each_bearer_and_keep_both_whole_accounts
    (origin : C) (meter : Meter.{u} origin) (exposure left right : Script)
    (leftPaid : PaidRecovery origin exposure left) (rightPaid : PaidRecovery origin exposure right)
    (crossed : ¬ profile origin meter exposure left ≤ profile origin meter exposure right ∧
      ¬ profile origin meter exposure right ≤ profile origin meter exposure left) :
    Nonempty (Bounds.Tradeoff (Execution.endAt origin exposure) (profile origin meter exposure) left right) ∧
      Recorded origin (exposure ++ left) ∧ Recorded origin (exposure ++ right) := by
  refine ⟨?_, leftPaid.whole, rightPaid.whole⟩
  rcases Bounds.compare_paid (Execution.endAt origin exposure) (profile origin meter exposure)
      left right leftPaid.settled rightPaid.settled with le | le | witnesses
  · exact (crossed.1 le).elim
  · exact (crossed.2 le).elim
  · exact witnesses

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort
