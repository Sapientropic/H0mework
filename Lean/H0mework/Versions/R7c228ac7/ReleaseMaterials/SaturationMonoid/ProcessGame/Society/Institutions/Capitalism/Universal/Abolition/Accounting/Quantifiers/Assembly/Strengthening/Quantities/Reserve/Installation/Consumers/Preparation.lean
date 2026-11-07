import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation.Share
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.PreRead
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Checks.Work

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation.Consumers

open Source.Program PublicFunction.Financing
open Abolition.Root.Registered
open Innovation.Installation

noncomputable section

abbrev law := Physical.Public.interpreter input
abbrev issue := Innovation.Control.Scenario.issue
abbrev payout := Innovation.Control.Scenario.payout
abbrev commonWork := Innovation.Control.Scenario.commonWork
abbrev terms := quotedMechanism.terms

def commonBefore (raw : Raw) : PhysicalState :=
  (Physical.Public.compile input ⟨raw, .seeking, []⟩ (.execute commonWork)).next

def receipt? (raw : Raw) := readDisbursement? law (commonBefore raw).raw [issue, payout] terms

private theorem the_original_inventory_has_signed_funding :
    firstRawVariants.all (fun raw => (receipt? raw).isSome) = true := by
  decide +kernel

def oldPast (nature : RequestAt) := (firstOrigin nature).germ.snapshot.past
def originalRaw (nature : RequestAt) := (Physical.stateAt input 0 count 0 0 (oldPast nature)).raw

theorem originalRaw_mem (nature : RequestAt) : originalRaw nature ∈ firstRawVariants := by
  exact the_first_actual_raw_is_in_its_actual_source_inventory nature

def originalReceipt (nature : RequestAt) :
    Disbursement law (commonBefore (originalRaw nature)).raw [issue, payout] terms :=
  (receipt? (originalRaw nature)).get (List.all_eq_true.mp the_original_inventory_has_signed_funding
    _ (originalRaw_mem nature))

def actualCut (nature : RequestAt) (visit : Nat) :=
  (Physical.Public.stateAt input 0 count 0 0 (oldPast nature) (actualPublicVisit nature visit).snapshot.past).raw

theorem actualCut_prefix (nature : RequestAt) (visit : Nat) (within : visit ≤ 5) :
    actualCut nature visit = (Physical.Public.stateAt input 0 count 0 0 (oldPast nature)
      ((beforeReadInputs nature).take (visit + 1))).raw := by
  unfold actualCut
  rw [every_pre_read_request_is_consumed_on_the_original_actual_root nature visit within,
    Physical.Prefix.past_readback]

private theorem issue_is_original (raw : Raw)
    (paid : Disbursement law (commonBefore raw).raw [issue, payout] terms) :
    paid.issue = ⟨0, (commonBefore raw).raw, issue⟩ := by
  have present := paid.issue_mem
  simp only [RawLaw.rawItems, RawLaw.execute, List.mem_cons, List.mem_nil_iff, or_false] at present
  rcases present with selected | impossible
  · exact selected
  · have kind := paid.issue_kind
    rw [impossible] at kind
    cases kind

private theorem payout_is_original (raw : Raw)
    (paid : Disbursement law (commonBefore raw).raw [issue, payout] terms) :
    paid.payout = ⟨1, law.step (commonBefore raw).raw issue, payout⟩ := by
  have present := paid.payout_mem
  simp only [RawLaw.rawItems, RawLaw.execute, List.mem_cons, List.mem_nil_iff, or_false] at present
  rcases present with impossible | selected
  · have kind := paid.payout_kind
    rw [impossible] at kind
    cases kind
  · exact selected

theorem the_signed_loan_preserves_its_original_principal_and_delivers_six (nature : RequestAt) :
    (originalReceipt nature).issue.request = issue ∧
    (originalReceipt nature).payout.request = payout ∧
    funds (originalReceipt nature) = 6 := by
  rw [issue_is_original _ (originalReceipt nature), payout_is_original _ (originalReceipt nature)]
  refine ⟨rfl, rfl, ?_⟩
  change (3 : ℚ) * 2 = 6
  norm_num

theorem a_checked_primitive_is_its_raw_step
    (before : PhysicalState) (request : RequestAt)
    (signed : request.resign request.signer = request) (accepted : law.Valid before.raw request) :
    (Physical.Public.compile input before (.primitive request)).next.raw = law.step before.raw request := by
  unfold Physical.Public.compile
  simp only [Physical.Public.wordAt]
  cases inspected : Material.inspectList (fun item : ExecutionItem Party Good Bool Nat Unit =>
      law.Valid item.before item.request) (law.rawItems before.raw [request.resign request.signer]) with
  | clear checked =>
      change (law.execute before.raw 0 [request.resign request.signer]).final = law.step before.raw request
      rw [signed]
      rfl
  | failure item member failed =>
      have exactItem : item = ⟨0, before.raw, request.resign request.signer⟩ := by
        simpa only [RawLaw.rawItems, RawLaw.execute, List.mem_singleton] using member
      subst item
      rw [signed] at failed
      exact (failed accepted).elim

theorem the_full_retention_is_the_original_actual_payout_cut (nature : RequestAt) :
    actualCut nature 2 = retaining (originalReceipt nature) 1 := by
  let seed := Physical.stateAt input 0 count 0 0 (oldPast nature)
  let first := (Physical.Public.compile input seed (.execute commonWork)).next
  let issued := (Physical.Public.compile input first (.primitive issue)).next
  let paid := originalReceipt nature
  have firstRaw : first.raw = (commonBefore (originalRaw nature)).raw :=
    an_explicit_physical_step_reads_its_original_raw seed ⟨seed.raw, .seeking, []⟩ rfl _
      (by intro impossible; cases impossible)
  have issueLegal := paid.issue_accepted
  rw [issue_is_original _ paid] at issueLegal
  have issuedRaw : issued.raw = law.step (commonBefore (originalRaw nature)).raw issue := by
    change (Physical.Public.compile input first (.primitive issue)).next.raw = _
    rw [a_checked_primitive_is_its_raw_step first issue rfl (firstRaw.symm ▸ issueLegal), firstRaw]
  have payoutLegal := paid.payout_accepted
  rw [payout_is_original _ paid] at payoutLegal
  rw [actualCut_prefix nature 2 (by decide),
    the_pre_read_source_inventory_is_the_original_five_requests]
  change (Physical.Public.compile input issued (.primitive payout)).next.raw = retaining paid 1
  rw [a_checked_primitive_is_its_raw_step issued payout rfl (issuedRaw.symm ▸ payoutLegal),
    issuedRaw, the_full_share_is_the_literal_original_payout, payoutAfter, payout_is_original _ paid]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation.Consumers
