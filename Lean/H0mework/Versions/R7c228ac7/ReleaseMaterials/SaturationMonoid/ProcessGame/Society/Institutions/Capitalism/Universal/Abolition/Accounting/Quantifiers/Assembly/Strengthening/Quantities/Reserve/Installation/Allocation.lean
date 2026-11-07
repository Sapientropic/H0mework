import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation.Share
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Retention

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction.Financing
open Innovation.Contribution.Pricing.Root.Runtime (normalise)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

structure Allocation (Party Good Port Technology Instrument : Type) where
  reserve : List (Option (Compile.RawInput Party Good Port Technology Instrument))
  install : List (Option (Compile.RawInput Party Good Port Technology Instrument))

local notation "Plan" => Allocation Party Good Port Technology Instrument

def financeScript (funding : Word) : Script := Execution.primitiveScript (normalise funding)

abbrev LoanAt (source : C) (funding : Word) (terms : Terms Party Instrument) :=
  Disbursement (Physical.Public.interpreter source.native.input) source.raw (normalise funding) terms

def compileAllocation (funding : Word) (plan : Plan) : Script :=
  (financeScript funding ++ plan.reserve) ++ plan.install

def installationStart (source : C) (funding : Word) (plan : Plan) :=
  Execution.endAt source (financeScript funding ++ plan.reserve)

/-- Net available capacity is measured at the actual construction start in
the original disbursed unit. Any amount above the original advance stays in
the whole stock account instead of inflating its retained fraction. -/
def available (source : C) (funding : Word) (terms : Terms Party Instrument)
    (loan : LoanAt source funding terms) (plan : Plan) : ℚ :=
  let unit := (Physical.Public.interpreter source.native.input).settlementUnit terms.instrument
  (installationStart source funding plan).raw.stock terms.borrower unit -
    (reserveBaseline loan).stock terms.borrower unit

def actualShare (source : C) (funding : Word) (terms : Terms Party Instrument)
    (loan : LoanAt source funding terms) (plan : Plan) : ℚ :=
  min (funds loan) (max 0 (available source funding terms loan plan)) / funds loan

omit [DecidableEq Technology] in
theorem available_divides_into_retained_extra_and_spent_original_capacity
    (source : C) (funding : Word) (terms : Terms Party Instrument)
    (loan : LoanAt source funding terms) (plan : Plan) :
    0 ≤ actualShare source funding terms loan plan ∧ actualShare source funding terms loan plan ≤ 1 ∧
      available source funding terms loan plan =
        actualShare source funding terms loan plan * funds loan +
          max 0 (available source funding terms loan plan - funds loan) -
          max 0 (-available source funding terms loan plan) := by
  let amount := available source funding terms loan plan
  let principal := funds loan
  have positive : 0 < principal := funds_positive loan
  change 0 ≤ min principal (max 0 amount) / principal ∧ min principal (max 0 amount) / principal ≤ 1 ∧
    amount = (min principal (max 0 amount) / principal) * principal +
      max 0 (amount - principal) - max 0 (-amount)
  refine ⟨div_nonneg (le_min positive.le (le_max_left _ _)) positive.le,
    (div_le_iff₀ positive).mpr (by simpa only [one_mul] using min_le_left principal (max 0 amount)), ?_⟩
  rw [div_mul_cancel₀ _ positive.ne']
  by_cases nonnegative : 0 ≤ amount
  · rw [max_eq_right nonnegative, max_eq_left (neg_nonpos.mpr nonnegative), sub_zero]
    by_cases within : amount ≤ principal
    · rw [min_eq_right within, max_eq_left (sub_nonpos.mpr within), add_zero]
    · have over := le_of_not_ge within
      rw [min_eq_left over, max_eq_right (sub_nonneg.mpr over)]
      ring
  · have negative := le_of_not_ge nonnegative
    rw [max_eq_left negative, min_eq_right positive.le, max_eq_left (sub_nonpos.mpr (negative.trans positive.le)),
      max_eq_right (neg_nonneg.mpr negative)]
    ring

def InstallationItem (law : RawLaw Party Good Port Technology Instrument)
    (builder : Party) (technology : Technology) (item : ExecutionItem Party Good Port Technology Instrument) : Prop :=
  match item.request.operation with
  | .revise operator target =>
      operator = builder ∧ item.request.signer = builder ∧ target = technology ∧
        item.before.technology ≠ target ∧ law.Valid item.before item.request
  | _ => False

instance (law : RawLaw Party Good Port Technology Instrument)
    (builder : Party) (technology : Technology) (item : ExecutionItem Party Good Port Technology Instrument) :
    Decidable (InstallationItem law builder technology item) := by
  unfold InstallationItem
  cases item.request.operation <;> infer_instance

def PerformedInstallation (source : C) (funding : Word) (builder : Party)
    (technology : Technology) (plan : Plan) : Prop :=
  let before := installationStart source funding plan
  ∃ item ∈ Execution.inventory before plan.install,
    InstallationItem (Physical.Public.interpreter before.native.input) builder technology item

def PaysInstallation (source : C) (funding : Word) (builder : Party)
    (technology : Technology) (plan : Plan) : Prop :=
  PerformedInstallation source funding builder technology plan ∧
    (Execution.endAt source (compileAllocation funding plan)).raw.technology = technology

inductive Uninstalled (source : C) (funding : Word) (builder : Party)
    (technology : Technology) (plan : Plan)
  | missing (absent : ¬ PerformedInstallation source funding builder technology plan)
  | superseded (actual : (Execution.endAt source (compileAllocation funding plan)).raw.technology ≠ technology)

def inspectInstallation (source : C) (funding : Word) (builder : Party)
    (technology : Technology) (plan : Plan) : Option (Uninstalled source funding builder technology plan) :=
  letI : Decidable (PerformedInstallation source funding builder technology plan) := by
    unfold PerformedInstallation
    infer_instance
  if installed : PerformedInstallation source funding builder technology plan then
    if current : (Execution.endAt source (compileAllocation funding plan)).raw.technology = technology then none
    else some (.superseded current)
  else some (.missing installed)

theorem installation_passes_iff_real_reconfiguration (source : C) (funding : Word)
    (builder : Party) (technology : Technology) (plan : Plan) :
    inspectInstallation source funding builder technology plan = none ↔
      PaysInstallation source funding builder technology plan := by
  unfold inspectInstallation PaysInstallation
  split
  · split <;> simp_all
  · simp_all

theorem a_paid_advance_without_construction_leaves_the_original_builder_unserved
    (source : C) (funding : Word) (builder : Party) (technology : Technology) (reserve : Script) :
    Recorded source (compileAllocation funding ⟨reserve, []⟩) ∧
      ∃ issue : Uninstalled source funding builder technology ⟨reserve, []⟩,
        inspectInstallation source funding builder technology ⟨reserve, []⟩ = some issue := by
  refine ⟨record source _, ?_⟩
  cases selected : inspectInstallation source funding builder technology ⟨reserve, []⟩ with
  | some issue => exact ⟨issue, rfl⟩
  | none =>
    have installed := (installation_passes_iff_real_reconfiguration _ _ _ _ _).mp selected
    obtain ⟨item, inside, _⟩ := installed.1
    exact (List.not_mem_nil inside).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation
