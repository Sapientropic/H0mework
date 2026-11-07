import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Contract
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort

open Source.Program Abolition.Root Abolition.Root.Registered
open Redemption (sourceLaw sourceOrigin essentials)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Proposal" => Plan Party Good Port Technology Instrument
local notation "Address" => Party × Good

def grossReceived (source : C) (plan : Proposal) (address : Address) : ℚ :=
  let start := fundingStart source plan
  (sourceLaw start).totalCredit (Execution.inventory start (allTenders source plan)) address.1 address.2

def fundingOutflow (source : C) (plan : Proposal) (address : Address) : ℚ :=
  let start := fundingStart source plan
  (sourceLaw start).totalDebit (Execution.inventory start (allTenders source plan)) address.1 address.2

def afterFunding (source : C) (plan : Proposal) := Execution.endAt source (paidPrefix source plan)

def actualCharges (source : C) (plan : Proposal) (count : Nat) :=
  Execution.originalResponses source (paidPrefix source plan) count

def captureNet (source : C) (plan : Proposal) (count : Nat) (address : Address) : ℚ :=
  Capture.netTaken (afterFunding source plan) (actualCharges source plan count) address.1 address.2

theorem tender_amounts_are_the_gross_original_credits (source : C) (plan : Proposal) (address : Address) :
    tenderAmounts source plan address = ((grossReceived source plan address : ℝ) : EReal) := rfl

theorem the_entire_population_shares_one_post_charge_material_balance
    (source : C) (plan : Proposal) (count : Nat) (address : Address) :
    (exitStart source count plan).raw.stock address.1 address.2 =
      (fundingStart source plan).raw.stock address.1 address.2 + grossReceived source plan address -
        fundingOutflow source plan address - captureNet source plan count address := by
  let start := fundingStart source plan
  let issued := afterFunding source plan
  have funded : issued = Execution.endAt start (allTenders source plan) :=
    Execution.endAt_append _ _ _
  have exposed : exitStart source count plan = Execution.endAt issued (actualCharges source plan count) :=
    Execution.endAt_append _ _ _
  have first := (record start (allTenders source plan)).actualBalance address.1 address.2
  change (Execution.endAt start (allTenders source plan)).raw.stock address.1 address.2 +
    fundingOutflow source plan address = start.raw.stock address.1 address.2 + grossReceived source plan address at first
  rw [← funded] at first
  have later := (record issued (actualCharges source plan count)).actualBalance address.1 address.2
  change (Execution.endAt issued (actualCharges source plan count)).raw.stock address.1 address.2 +
    (sourceLaw issued).totalDebit (Execution.inventory issued (actualCharges source plan count)) address.1 address.2 =
    issued.raw.stock address.1 address.2 +
      (sourceLaw issued).totalCredit (Execution.inventory issued (actualCharges source plan count)) address.1 address.2 at later
  rw [exposed]
  unfold captureNet Capture.netTaken
  linarith only [first, later]

def originalFloor (source : C) (plan : Proposal) (address : Address) : ℚ :=
  let start := fundingStart source plan
  essentials (sourceLaw start) (sourceOrigin start) address.1 address.2

def grossFloor (source : C) (plan : Proposal) (count : Nat) (address : Address) : ℚ :=
  max 0 (originalFloor source plan address - (fundingStart source plan).raw.stock address.1 address.2 +
    fundingOutflow source plan address + captureNet source plan count address)

private theorem gross_nonnegative (source : C) (plan : Proposal) (address : Address) :
    0 ≤ grossReceived source plan address := by
  unfold grossReceived RawLaw.totalCredit
  apply List.sum_nonneg
  intro value present
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp present
  unfold RawLaw.actualCredit
  split
  · rename_i paid
    exact amount_nonnegative _ paid.2.2.2.2.1 _
  · exact le_rfl

theorem the_post_charge_floor_is_exact_at_every_original_material_address
    (source : C) (plan : Proposal) (count : Nat) (address : Address) :
    originalFloor source plan address ≤ (exitStart source count plan).raw.stock address.1 address.2 ↔
      grossFloor source plan count address ≤ grossReceived source plan address := by
  rw [the_entire_population_shares_one_post_charge_material_balance]
  unfold grossFloor
  rw [max_le_iff]
  constructor
  · intro enough
    exact ⟨gross_nonnegative source plan address, by linarith⟩
  · rintro ⟨_, fits⟩
    linarith

theorem a_missing_post_charge_address_keeps_the_original_bearer_and_the_whole_root
    (source : C) (plan : Proposal) (count : Nat) (address : Address)
    (gap : grossReceived source plan address < grossFloor source plan count address) :
    (exitStart source count plan).raw.stock address.1 address.2 < originalFloor source plan address ∧
      Recorded source (compile source count plan) :=
  ⟨lt_of_not_ge fun paid => (not_le_of_gt gap)
    ((the_post_charge_floor_is_exact_at_every_original_material_address _ _ _ _).mp paid), record source _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort
