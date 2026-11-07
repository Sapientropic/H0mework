import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation.Allocation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Compiled
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction.Financing
open Innovation.Contribution.Pricing.Root.Runtime (Trace normalise)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Plan" => Allocation Party Good Port Technology Instrument

def shareValue (source : C) (funding : Word) (terms : Terms Party Instrument)
    (loan : LoanAt source funding terms) (plan : Plan) : EReal :=
  ((actualShare source funding terms loan plan : ℝ) : EReal)

theorem exact_actual_installation_shares (source : C) (funding : Word) (terms : Terms Party Instrument)
    (loan : LoanAt source funding terms) (builder : Party) (technology : Technology) (amount : EReal) :
    amount ∈ Bounds.Compiled.values source (compileAllocation funding)
      (inspectInstallation source funding builder technology) (shareValue source funding terms loan) ↔
      ∃ plan, Settled source (compileAllocation funding plan) ∧
        PaysInstallation source funding builder technology plan ∧ shareValue source funding terms loan plan = amount := by
  change (∃ plan, Settled source (compileAllocation funding plan) ∧
    inspectInstallation source funding builder technology plan = none ∧ shareValue source funding terms loan plan = amount) ↔ _
  simp only [installation_passes_iff_real_reconfiguration]

def IndexedFinancing (source : C) (funding : Word) (terms : Terms Party Instrument)
    (loan : LoanAt source funding terms) : Prop :=
  let inventory := Execution.inventory source (financeScript funding)
  inventory[loan.issue.index]? = some {loan.issue with index := 0} ∧
    inventory[loan.payout.index]? = some {loan.payout with index := 0} ∧
    loan.issue.index < loan.payout.index

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem execute_item_at_its_index
    (law : RawLaw Party Good Port Technology Instrument) (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (word : Word) (item : ExecutionItem Party Good Port Technology Instrument)
    (present : item ∈ (law.execute current index word).items) :
    ∃ offset, index + offset = item.index ∧ (law.execute current index word).items[offset]? = some item := by
  induction word generalizing current index with
  | nil => simp [RawLaw.execute] at present
  | cons request tail rest =>
      simp only [RawLaw.execute, List.mem_cons] at present
      rcases present with rfl | present
      · exact ⟨0, Nat.add_zero _, rfl⟩
      · obtain ⟨offset, position, exactItem⟩ := rest _ _ present
        exact ⟨offset + 1, by omega, exactItem⟩

omit [DecidableEq Technology] in
theorem the_financing_items_are_at_their_original_native_positions
    (source : C) (funding : Word) (terms : Terms Party Instrument) (loan : LoanAt source funding terms)
    (trace : Trace source (normalise funding) (Execution.endAt source (financeScript funding))) :
    IndexedFinancing source funding terms loan := by
  have actualItem (item : ExecutionItem Party Good Port Technology Instrument)
      (present : item ∈ (Physical.Public.interpreter source.native.input).rawItems source.raw (normalise funding)) :
      (Execution.inventory source (financeScript funding))[item.index]? = some {item with index := 0} := by
    obtain ⟨offset, position, exactItem⟩ := execute_item_at_its_index
      (Physical.Public.interpreter source.native.input) source.raw 0 (normalise funding) item present
    unfold financeScript
    rw [Execution.primitive_inventory trace 0, ← position, Nat.zero_add, List.getElem?_map, exactItem]
    rfl
  exact ⟨actualItem loan.issue loan.issue_mem, actualItem loan.payout loan.payout_mem, loan.ordered⟩

omit [DecidableEq Technology] in
theorem every_completed_installation_carries_the_funded_account_into_its_actual_next
    (source : C) (funding : Word) (plan : Plan) :
    Recorded (Execution.endAt source (financeScript funding)) (plan.reserve ++ plan.install) ∧
      Execution.endAt source (compileAllocation funding plan) =
        Execution.endAt (installationStart source funding plan) plan.install := by
  refine ⟨record _ _, ?_⟩
  exact Execution.endAt_append source (financeScript funding ++ plan.reserve) plan.install

/-- Every original allocation and construction suffix participates. The
tight domain distinguishes real installation from a booked advance, and an
attained or approximating share includes the full original settlement. -/
theorem the_original_root_resolves_every_actual_installation_share
    (source : C) (funding : Word) (terms : Terms Party Instrument)
    (loan : LoanAt source funding terms) (builder : Party) (technology : Technology)
    (actualFunding : Trace source (normalise funding) (Execution.endAt source (financeScript funding))) :
    let values := Bounds.Compiled.values source (compileAllocation funding)
      (inspectInstallation source funding builder technology) (shareValue source funding terms loan)
    IsGLB values (sInf values) ∧
      Bounds.Compiled.Minimum source (compileAllocation funding)
        (inspectInstallation source funding builder technology) (shareValue source funding terms loan) ∧
      IndexedFinancing source funding terms loan :=
  ⟨isGLB_sInf _, Bounds.Compiled.resolve _ _ _ _,
    the_financing_items_are_at_their_original_native_positions source funding terms loan actualFunding⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation
