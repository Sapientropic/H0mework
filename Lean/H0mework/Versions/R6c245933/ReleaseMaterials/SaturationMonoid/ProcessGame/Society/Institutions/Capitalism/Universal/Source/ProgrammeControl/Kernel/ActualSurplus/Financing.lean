import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Payments

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Financing

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

inductive Role | advance | issuance deriving DecidableEq

def index (role : Role) (witness : Witness law current word) : Option Nat :=
  match witness.evidence with
  | .financialReturn path => some (match role with
      | .advance => witness.dependency.proposal.access.access.val.index
      | .issuance => path.issuance.val.index)
  | _ => none

/-- Select original positions once; one advance may support several distinct claims. -/
def markedBy (witnesses : List (Witness law current word)) (role : Role) (position : Nat) : Bool :=
  witnesses.any fun witness => index law current word role witness == some position

def marked := markedBy law current word (Payments.financialWitnesses law current word)

omit [DecidableEq Port] in
theorem markedBy_exact (witnesses : List (Witness law current word)) (role : Role) (position : Nat) :
    markedBy law current word witnesses role position = true ↔
      ∃ witness ∈ witnesses, ∃ path : Financial.ReturnPath law current word,
        witness.evidence = .financialReturn path ∧
        (match role with
        | .advance => witness.dependency.proposal.access.access.val.index
        | .issuance => path.issuance.val.index) = position := by
  constructor
  · intro selected
    obtain ⟨witness, member, found⟩ := List.any_eq_true.mp selected
    have key := beq_iff_eq.mp found
    cases evidence : witness.evidence with
    | financialReturn path => exact ⟨witness, member, path, evidence, Option.some.inj (by simpa only [index, evidence] using key)⟩
    | _ => simp only [index, evidence, reduceCtorEq] at key
  · rintro ⟨witness, member, path, evidence, same⟩
    exact List.any_eq_true.mpr ⟨witness, member, beq_iff_eq.mpr (by simp only [index, evidence, same])⟩

theorem marked_issuance_is_the_original_checked_claim (position : OriginalItem law current word)
    (selected : marked law current word .issuance position.val.index = true) :
    ∃ witness ∈ Payments.financialWitnesses law current word, ∃ path : Financial.ReturnPath law current word,
      witness.evidence = .financialReturn path ∧ path.issuance = position ∧
      Financial.ReturnPath.Checks law current word witness.dependency.proposal.access path := by
  obtain ⟨witness, member, path, evidence, same⟩ := (markedBy_exact law current word _ _ _).mp selected
  have checked := witness.checked.2.2.1
  simp only [evidence, evidenceChecks] at checked
  exact ⟨witness, member, path, evidence, Financial.original_index_injective law current word same, checked⟩

theorem marked_advance_is_the_original_checked_access (position : OriginalItem law current word)
    (selected : marked law current word .advance position.val.index = true) :
    ∃ witness ∈ Payments.financialWitnesses law current word, ∃ path : Financial.ReturnPath law current word,
      witness.evidence = .financialReturn path ∧ witness.dependency.proposal.access.access = position ∧
      Financial.ReturnPath.Checks law current word witness.dependency.proposal.access path := by
  obtain ⟨witness, member, path, evidence, same⟩ := (markedBy_exact law current word _ _ _).mp selected
  have checked := witness.checked.2.2.1
  simp only [evidence, evidenceChecks] at checked
  exact ⟨witness, member, path, evidence, Financial.original_index_injective law current word same, checked⟩

omit [DecidableEq Port] in
theorem duplicate_evidence_preserves_every_selected_position
    (witnesses : List (Witness law current word)) (role : Role) (position : Nat) :
    markedBy law current word (witnesses ++ witnesses) role position = markedBy law current word witnesses role position := by
  simp only [markedBy, List.any_append, Bool.or_self]

/-- Independent complementary folds retain every actual operating debit and
non-settlement credit. Refunds and compensation stay in the complementary account. -/
def cashBy (witnesses : List (Witness law current word)) (selected credit : Bool) (party : Party) (good : Good) : ℚ :=
  ((law.rawItems current word).map fun item =>
    if markedBy law current word witnesses .advance item.index = selected then
      if PublicFunction.Costs.isDebtPayment item.request then 0 else
        flowAt (if credit then law.actualCredit item.before item.request else law.actualDebit item.before item.request) party good
    else 0).sum

def cash := cashBy law current word (Payments.financialWitnesses law current word)

omit [DecidableEq Port] in
theorem duplicate_evidence_preserves_actual_cash (witnesses : List (Witness law current word))
    (selected credit : Bool) (party : Party) (good : Good) :
    cashBy law current word (witnesses ++ witnesses) selected credit party good =
      cashBy law current word witnesses selected credit party good := by
  simp only [cashBy, duplicate_evidence_preserves_every_selected_position]

theorem cash_partition (credit : Bool) (party : Party) (good : Good) :
    cash law current word true credit party good + cash law current word false credit party good =
      ((law.rawItems current word).map fun item =>
        if PublicFunction.Costs.isDebtPayment item.request then 0 else
          flowAt (if credit then law.actualCredit item.before item.request else law.actualDebit item.before item.request) party good).sum := by
  unfold cash cashBy
  induction law.rawItems current word with
  | nil => simp only [List.map_nil, List.sum_nil, add_zero]
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons]
      cases markedBy law current word (Payments.financialWitnesses law current word) .advance item.index <;>
        simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true] <;> linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Financing
