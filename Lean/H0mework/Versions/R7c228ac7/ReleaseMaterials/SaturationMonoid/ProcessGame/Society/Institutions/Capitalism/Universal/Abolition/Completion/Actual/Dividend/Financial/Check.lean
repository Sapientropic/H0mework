import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

local notation "first" => Dividend.seed input depth count prefixLimit renewalLimit oldPast
local notation "actual" => Dividend.publicCurrent input depth count prefixLimit renewalLimit oldPast current
local notation "reference" => Dividend.oldEndpoint input depth count prefixLimit renewalLimit oldPast current
local notation "gain" => delta input depth count prefixLimit renewalLimit oldPast current
local notation "support" => cells input depth count prefixLimit renewalLimit oldPast current
local notation "claims" => quotedClaims input depth count prefixLimit renewalLimit oldPast current

def Checks : Prop :=
  (∀ key ∈ claims, 0 < input.law.settlementRate key.1) ∧
    (first).raw.clock < (actual).raw.clock ∧ (actual).raw.clock = (reference).clock ∧
    (∀ cell ∈ support, 0 ≤ gain cell.1 cell.2) ∧ ∃ cell ∈ support, 0 < gain cell.1 cell.2

instance : Decidable (Checks input depth count prefixLimit renewalLimit oldPast current) := by
  unfold Checks
  infer_instance

inductive Issue : Type
  | unquotedOriginalClaim (key : ClaimKey (Party := Party) (Instrument := Instrument))
      (affected : key ∈ claims) (rate : input.law.settlementRate key.1 ≤ 0)
  | noPositiveActualWindow (zero : (actual).raw.clock ≤ (first).raw.clock)
  | differentActualWindow (different : (actual).raw.clock ≠ (reference).clock)
  | originalBearerLoses (cell : Party × Good) (affected : cell ∈ support) (loss : gain cell.1 cell.2 < 0)
  | noStrictFullAccountIncrease (nonpositive : ∀ cell ∈ support, gain cell.1 cell.2 ≤ 0)

theorem Issue.refutes (issue : Issue input depth count prefixLimit renewalLimit oldPast current) :
    ¬ Checks input depth count prefixLimit renewalLimit oldPast current := by
  intro checked
  cases issue with
  | unquotedOriginalClaim key affected rate => exact (not_lt_of_ge rate) (checked.1 key affected)
  | noPositiveActualWindow zero => exact (not_lt_of_ge zero) checked.2.1
  | differentActualWindow different => exact different checked.2.2.1
  | originalBearerLoses cell affected loss => exact (not_le_of_gt loss) (checked.2.2.2.1 cell affected)
  | noStrictFullAccountIncrease nonpositive =>
      obtain ⟨cell, affected, positive⟩ := checked.2.2.2.2
      exact (not_lt_of_ge (nonpositive cell affected)) positive

inductive Decision : Type
  | accepted (checked : Checks input depth count prefixLimit renewalLimit oldPast current)
  | rejected (issue : Issue input depth count prefixLimit renewalLimit oldPast current)

/-- The same actual source now values financial movements. A settlement is
not a missing-valuation branch; failed dominance identifies its real bearer. -/
def check : Decision input depth count prefixLimit renewalLimit oldPast current :=
  match Material.inspectList (fun key : ClaimKey (Party := Party) (Instrument := Instrument) =>
      0 < input.law.settlementRate key.1) claims with
  | .failure key affected invalid => .rejected (.unquotedOriginalClaim key affected (le_of_not_gt invalid))
  | .clear quoted =>
      if positive : (first).raw.clock < (actual).raw.clock then
        if same : (actual).raw.clock = (reference).clock then
          match Material.inspectList (fun cell : Party × Good => 0 ≤ gain cell.1 cell.2) support with
          | .failure cell affected loss => .rejected (.originalBearerLoses cell affected (lt_of_not_ge loss))
          | .clear noLoss =>
              match Material.inspectList (fun cell : Party × Good => gain cell.1 cell.2 ≤ 0) support with
              | .clear noGain => .rejected (.noStrictFullAccountIncrease noGain)
              | .failure cell affected strict => .accepted ⟨quoted, positive, same, noLoss, cell, affected, lt_of_not_ge strict⟩
        else .rejected (.differentActualWindow same)
      else .rejected (.noPositiveActualWindow (le_of_not_gt positive))

theorem all_original_bearers_and_goods_keep_their_full_account_share
    (checked : Checks input depth count prefixLimit renewalLimit oldPast current) (person : Party) (good : Good) :
    0 ≤ gain person good := by
  by_cases present : (person, good) ∈ support
  · exact checked.2.2.2.1 (person, good) present
  · rw [no_unlisted_bearer_or_good_has_a_hidden_full_account_change input depth count prefixLimit renewalLimit oldPast current
      person good present]

theorem one_original_bearer_and_unit_has_strict_full_account_gain
    (checked : Checks input depth count prefixLimit renewalLimit oldPast current) :
    ∃ person good, 0 < gain person good := by
  obtain ⟨cell, _affected, positive⟩ := checked.2.2.2.2
  exact ⟨cell.1, cell.2, positive⟩

theorem a_real_full_account_gain_is_accepted
    (checked : Checks input depth count prefixLimit renewalLimit oldPast current) :
    ∃ proof, check input depth count prefixLimit renewalLimit oldPast current = .accepted proof := by
  cases generated : check input depth count prefixLimit renewalLimit oldPast current with
  | accepted proof => exact ⟨proof, rfl⟩
  | rejected issue => exact (issue.refutes _ _ _ _ _ _ _ checked).elim

#print axioms check
#print axioms Issue.refutes
#print axioms all_original_bearers_and_goods_keep_their_full_account_share
#print axioms one_original_bearer_and_unit_has_strict_full_account_gain

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial
