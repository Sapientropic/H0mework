import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Runtime
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.InstrumentProjection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle
open Financial.Family.InstrumentProjection

variable {seed : Seed} {oldRequests : Requests.Source} {permission : Material.Mode} {baseCut : Nat}
  {source : Inherited seed oldRequests permission baseCut}
  {requests : Requests.Source} {authority : Authority} {index : Nat}
  (cut : Cut source requests authority index)

local notation "startAt" => handoff (baseCut := baseCut) index
local notation "prog" => input cut

variable (offset : Nat)

local notation "permit" => permissionAt seed requests permission (index + 1 + (offset + 1)) (run cut offset)

def priorAccount : Finance.Account :=
  Financial.Family.continueVisits Finance.sources prog startAt offset cut.after.account

theorem actual_repayment_preserves_the_request
    (ready : OpeningAt cut)
    (choice : OptionAt seed.basis.origin.scope permit (run cut offset).raw)
    (selected : selection seed permit (run cut offset) = .repay choice) :
    owed (execution cut offset).after = 0 ∧ (after cut offset).protocol = (run cut offset).protocol := by
  rw [actual_after]
  change owed (admittedStep cut offset (run cut offset)).raw = 0 ∧
    (admittedStep cut offset (run cut offset)).protocol = (run cut offset).protocol
  rw [admitted_step_when_ready cut ready]
  exact repayment_retires_the_original_principal_and_keeps_the_request seed requests authority permission
    (index + 1 + (offset + 1)) (run cut offset) choice selected

private theorem original_word_has_no_issue
    (ready : OpeningAt cut)
    (choice : OptionAt seed.basis.origin.scope permit (run cut offset).raw)
    (selected : selection seed permit (run cut offset) = .repay choice) :
    let current := (ProgrammeHistory.visitAt prog (startAt + offset)).current
    ((prog).law.rawItems (ProgrammeSource.rawCurrent prog current) (ProgrammeSource.rawEvent prog current)).countP
      (acceptedIssue (prog).law) = 0 := by
  dsimp only
  rw [List.countP_eq_zero]
  intro row member
  have present : row.request ∈ ProgrammeSource.rawEvent prog (ProgrammeHistory.visitAt prog (startAt + offset)).current := by
    rw [← (prog).law.inventory_requests_exact (ProgrammeSource.rawCurrent prog
      (ProgrammeHistory.visitAt prog (startAt + offset)).current) 0
      (ProgrammeSource.rawEvent prog (ProgrammeHistory.visitAt prog (startAt + offset)).current)]
    exact List.mem_map.mpr ⟨row, member, rfl⟩
  rw [selected_word cut offset, admitted_word_when_ready cut ready, word, selected] at present
  have retained := choice.property.2.2.2.1 row.request present
  cases operation : row.request.operation <;> simp [RetainsClaims, acceptedIssue, operation] at retained ⊢

/-- The live principal is retired in its existing account. This step adds
no admission, even when the recipe includes several physical operations. -/
theorem repayment_preserves_exactly_the_original_claim_slots
    (ready : OpeningAt cut)
    (choice : OptionAt seed.basis.origin.scope permit (run cut offset).raw)
    (selected : selection seed permit (run cut offset) = .repay choice) :
    (account cut offset).current.slots.map (Financial.Family.slotClaim Finance.sources) =
      (priorAccount cut offset).current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  have count := actual_visit_generates_its_own_slot_count Finance.sources prog (startAt + offset) (priorAccount cut offset)
  change (account cut offset).current.slots.length =
    (priorAccount cut offset).current.slots.length +
      ((prog).law.rawItems
        (ProgrammeSource.rawCurrent prog (ProgrammeHistory.visitAt prog (startAt + offset)).current)
        (ProgrammeSource.rawEvent prog (ProgrammeHistory.visitAt prog (startAt + offset)).current)).countP
        (acceptedIssue (prog).law) at count
  rw [original_word_has_no_issue cut offset ready choice selected, Nat.add_zero] at count
  have ordered := Financial.Family.consumeOrigins_preserves_original_claims Finance.sources
    (Financial.Family.visitOrigins Finance.sources prog (startAt + offset)) (priorAccount cut offset)
  change _ <+: (account cut offset).current.slots.map (Financial.Family.slotClaim Finance.sources) at ordered
  exact (ordered.eq_of_length (by simpa only [List.length_map] using count.symm)).symm

theorem actual_exhaustion_keeps_the_original_input_and_claim_matrix
    (ready : OpeningAt cut)
    (blocked : select? seed.basis.origin.scope permit (run cut offset).raw = none)
    (selected : selection seed permit (run cut offset) = .blocked blocked) :
    (execution cut offset).submitted = [] ∧
      (execution cut offset).after.stock = (run cut offset).raw.stock ∧
      (execution cut offset).after.claims = (run cut offset).raw.claims ∧
      (after cut offset).protocol = (run cut offset).protocol ∧
      ∀ route, Nonempty (Obstruction seed.basis.origin.scope permit (run cut offset).raw route) := by
  rw [actual_submitted, admitted_word_when_ready cut ready, word, selected, actual_after]
  change [] = [] ∧
    (admittedStep cut offset (run cut offset)).raw.stock = (run cut offset).raw.stock ∧
    (admittedStep cut offset (run cut offset)).raw.claims = (run cut offset).raw.claims ∧
    (admittedStep cut offset (run cut offset)).protocol = (run cut offset).protocol ∧ _
  rw [admitted_step_when_ready cut ready]
  obtain ⟨stock, claims, protocol⟩ :=
    exhaustion_retains_the_entire_original_stock_claims_and_protocol seed requests authority permission
      (index + 1 + (offset + 1)) (run cut offset) blocked selected
  exact ⟨rfl, stock, claims, protocol, no_choice_has_a_named_obstruction_for_each_route _ _ _ blocked⟩

private theorem preserve_undecoded_rows (origins : List (Financial.InstructionOrigin prog))
    (previous : Finance.Account)
    (empty : origins.filterMap (Financial.InstructionOrigin.instruction? prog) = []) :
    Financial.Family.consumeOrigins Finance.sources (origins.map (Sigma.mk prog)) previous = previous := by
  induction origins generalizing previous with
  | nil => rfl
  | cons head tail later =>
    cases decoded : head.instruction? prog with
    | some row => simp [decoded] at empty
    | none =>
      simp only [List.filterMap_cons, decoded] at empty
      change Financial.Family.consumeOrigins Finance.sources (tail.map (Sigma.mk prog))
        ((Financial.Family.consume Finance.sources ⟨prog, head⟩ previous).next Finance.sources) = previous
      rw [Financial.Family.BalanceConservation.consume_without_instruction Finance.sources ⟨prog, head⟩ previous decoded]
      exact later previous empty

private theorem native_account_after_empty_word
    (emptyWord : admittedWord cut offset (run cut offset) = []) :
    account cut offset = priorAccount cut offset := by
  have original := Financial.inventoryAt_instructions_exact prog (ProgrammeHistory.visitAt prog (startAt + offset))
  rw [selected_word cut offset, emptyWord] at original
  exact preserve_undecoded_rows cut _ _ original

theorem actual_exhaustion_keeps_the_entire_native_account
    (ready : OpeningAt cut)
    (blocked : select? seed.basis.origin.scope permit (run cut offset).raw = none)
    (selected : selection seed permit (run cut offset) = .blocked blocked) :
    account cut offset = priorAccount cut offset := by
  apply native_account_after_empty_word cut offset
  rw [admitted_word_when_ready cut ready]
  simp only [word, selected]

theorem an_opening_obstruction_keeps_the_original_account_stock_and_protocol
    (reason : OpeningObstruction seed.basis.origin.scope cut.after.frame.raw cut.after.account)
    (refused : opening cut = .inr reason) :
    (execution cut offset).submitted = [] ∧ account cut offset = priorAccount cut offset ∧
      (execution cut offset).after.stock = (run cut offset).raw.stock ∧
      (execution cut offset).after.claims = (run cut offset).raw.claims ∧
      (after cut offset).protocol = (run cut offset).protocol := by
  have empty : admittedWord cut offset (run cut offset) = [] := by simp only [admittedWord, refused]
  rw [actual_submitted, actual_after]
  change admittedWord cut offset (run cut offset) = [] ∧ account cut offset = priorAccount cut offset ∧
    (admittedStep cut offset (run cut offset)).raw.stock = (run cut offset).raw.stock ∧
    (admittedStep cut offset (run cut offset)).raw.claims = (run cut offset).raw.claims ∧
    (admittedStep cut offset (run cut offset)).protocol = (run cut offset).protocol
  refine ⟨empty, native_account_after_empty_word cut offset empty, ?_⟩
  simp only [admittedStep, refused, Supply.initialMemo_exact]
  exact ⟨rfl, rfl, trivial⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Runtime
