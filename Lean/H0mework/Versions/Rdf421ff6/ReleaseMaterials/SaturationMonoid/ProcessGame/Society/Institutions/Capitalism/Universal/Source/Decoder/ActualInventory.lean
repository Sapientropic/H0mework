import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Trace

/-! Complete finite reads of an actually executed source instruction.
Authorization, material receipts and financial rights are computed from the
raw execution.  A later classifier cannot delete a required port or convert
a repaid principal into a newly acquired financial right. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder

open Program ProgrammeFace

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

def recipient : Operation Party Good Technology Instrument → Option Party
  | .produce operator => some operator
  | .transfer _ beneficiary _ | .settle _ _ beneficiary _ => some beneficiary
  | _ => none

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem recipient_mem_operationParties
    (operation : Operation Party Good Technology Instrument) (party : Party)
    (selected : recipient operation = some party) : party ∈ operationParties operation := by
  cases operation <;> simp_all [recipient, operationParties]

omit [DecidableEq Port] in
theorem recipient_mem_itemParties (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (selected : recipient item.request.operation = some party) :
    party ∈ itemParties law item := by
  exact operation_party_mem_itemParties law item party
    (recipient_mem_operationParties item.request.operation party selected)

def acquired (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) : ℚ :=
  flowAt (law.actualCredit item.before item.request) party good

def paid (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) : ℚ :=
  flowAt (law.actualDebit item.before item.request) party good

def produced (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) : ℚ :=
  match item.request.operation with
  | .produce _ => acquired law item party good
  | _ => 0

def consumedFor (purpose : Use) (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) : ℚ :=
  match item.request.operation with
  | .use _ _ actualPurpose => if actualPurpose = purpose then paid law item party good else 0
  | _ => 0

def acquiredClaim (item : ExecutionItem Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor creditor : Party) : ℚ :=
  max 0 ((law.step item.before item.request).claims instrument debtor creditor -
    item.before.claims instrument debtor creditor)

def dischargedClaim (item : ExecutionItem Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor creditor : Party) : ℚ :=
  max 0 (item.before.claims instrument debtor creditor -
    (law.step item.before item.request).claims instrument debtor creditor)

def authorizingAction (item : ExecutionItem Party Good Port Technology Instrument)
    (port : Port) : ActionSeed Party :=
  if law.controller item.before.technology port ∈ item.request.consents then
    ⟨item.index, .consent, law.controller item.before.technology port⟩
  else ⟨item.index, .execution, item.request.signer⟩

def actualAuthorizations (item : ExecutionItem Party Good Port Technology Instrument) :
    List (Port × ActionSeed Party) :=
  if law.Valid item.before item.request then
    (law.requiredPorts item.before item.request).map
      (fun port => (port, authorizingAction law item port))
  else []

def recipientDependentAuthorizations (item : ExecutionItem Party Good Port Technology Instrument)
    (beneficiary : Party) : List (Port × ActionSeed Party) :=
  (actualAuthorizations law item).filter
    (fun entry => !(law.allowed item.before.technology entry.1 beneficiary))

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem every_required_port_has_exact_authorization
    (item : ExecutionItem Party Good Port Technology Instrument)
    (accepted : law.Valid item.before item.request) (port : Port)
    (required : port ∈ law.requiredPorts item.before item.request) :
    (port, authorizingAction law item port) ∈ actualAuthorizations law item := by
  simp only [actualAuthorizations, if_pos accepted]
  exact List.mem_map.mpr ⟨port, required, rfl⟩

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem recipient_gate_complete
    (item : ExecutionItem Party Good Port Technology Instrument)
    (accepted : law.Valid item.before item.request) (beneficiary : Party) (port : Port)
    (required : port ∈ law.requiredPorts item.before item.request) :
    law.allowed item.before.technology port beneficiary = true ∨
      (port, authorizingAction law item port) ∈
        recipientDependentAuthorizations law item beneficiary := by
  by_cases independent : law.allowed item.before.technology port beneficiary = true
  · exact Or.inl independent
  · right
    apply List.mem_filter.mpr
    refine ⟨every_required_port_has_exact_authorization law item accepted port required, ?_⟩
    simpa using independent

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem authorizingAction_is_actual
    (item : ExecutionItem Party Good Port Technology Instrument)
    (accepted : law.Valid item.before item.request) (port : Port) :
    authorizingAction law item port ∈ itemActions law item := by
  by_cases consent : law.controller item.before.technology port ∈ item.request.consents
  · simp only [authorizingAction, if_pos consent, itemActions, if_pos accepted]
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨_, consent, rfl⟩
  · simp only [authorizingAction, if_neg consent, itemActions, if_pos accepted]
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    exact List.mem_cons_self

omit [DecidableEq Port] in
theorem authorizingAction_in_original_occurrence
    (origin : Origin Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (present : item ∈ law.rawItems origin.1 origin.2)
    (accepted : law.Valid item.before item.request) (port : Port) :
    authorizingAction law item port ∈ actions law origin :=
  List.mem_flatMap.mpr ⟨item, present, authorizingAction_is_actual law item accepted port⟩

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem generated_authorizer_has_permission_or_consent
    (item : ExecutionItem Party Good Port Technology Instrument)
    (accepted : law.Valid item.before item.request) (port : Port)
    (required : port ∈ law.requiredPorts item.before item.request) :
    ((authorizingAction law item port).kind = .consent ∧
      (authorizingAction law item port).party = law.controller item.before.technology port ∧
      law.controller item.before.technology port ∈ item.request.consents) ∨
    ((authorizingAction law item port).kind = .execution ∧
      (authorizingAction law item port).party = item.request.signer ∧
      law.allowed item.before.technology port item.request.signer = true) := by
  unfold authorizingAction
  split
  next consent => exact Or.inl ⟨rfl, rfl, consent⟩
  next noConsent =>
    exact Or.inr ⟨rfl, rfl, (accepted.2.1 port required).resolve_right noConsent⟩

omit [DecidableEq Port] in
theorem material_effect_is_original_balance
    (item : ExecutionItem Party Good Port Technology Instrument) (party : Party) (good : Good) :
    (law.step item.before item.request).stock party good + paid law item party good =
      item.before.stock party good + acquired law item party good :=
  law.material_step_balance item.before item.request party good

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem rejection_has_no_material_or_authorization
    (item : ExecutionItem Party Good Port Technology Instrument)
    (refused : ¬ law.Valid item.before item.request) (party : Party) (good : Good) :
    acquired law item party good = 0 ∧ paid law item party good = 0 ∧
      actualAuthorizations law item = [] := by
  simp [acquired, paid, RawLaw.actualCredit, RawLaw.actualDebit, actualAuthorizations,
    refused, flowAt, amount]

omit [DecidableEq Port] in
theorem repaid_principal_is_not_new_claim
    (item : ExecutionItem Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor creditor : Party) (quantity : ℚ)
    (kind : item.request.operation = .settle instrument debtor creditor quantity)
    (accepted : law.Valid item.before item.request) :
    acquiredClaim law item instrument debtor creditor = 0 ∧
      dischargedClaim law item instrument debtor creditor = quantity := by
  have nonnegative : 0 ≤ quantity := by
    have guard := accepted.2.2.1
    simp only [RawLaw.ClaimGuard, kind] at guard
    exact guard.1
  simp only [acquiredClaim, dischargedClaim, RawLaw.step, if_pos accepted,
    RawLaw.paidStep, RawLaw.nextClaims, kind, ↓reduceIte]
  constructor <;> simp only [sub_sub_cancel_left, sub_sub_cancel]
  · exact max_eq_left (neg_nonpos.mpr nonnegative)
  · exact max_eq_right nonnegative

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem necessary_use_is_source_computed
    (item : ExecutionItem Party Good Port Technology Instrument)
    (bearer : Party) (goods : Bundle Good)
    (kind : item.request.operation = .use bearer goods .necessity)
    (accepted : law.Valid item.before item.request) :
    goods = law.necessities item.before bearer := by
  simpa only [RawLaw.ClaimGuard, kind] using accepted.2.2.1

#print axioms recipient_gate_complete
#print axioms repaid_principal_is_not_new_claim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder
