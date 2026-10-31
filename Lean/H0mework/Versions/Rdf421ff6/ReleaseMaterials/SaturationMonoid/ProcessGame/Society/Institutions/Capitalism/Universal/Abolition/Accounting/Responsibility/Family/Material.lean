import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.Scope
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Reparation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family

open Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Actual law supplies enforcement authority. Every material transfer debits the
original joint controller cohort and credits an originally harmed cell. -/
def materialOperation (cohort : List Party) (victims : List (Party × Good))
    (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .transfer sender recipient goods => sender ∈ cohort ∧ ∀ entry ∈ goods, (recipient,entry.1) ∈ victims
  | .produce operator | .revise operator _ => operator ∈ cohort
  | .use bearer _ purpose => bearer ∈ cohort ∨ purpose = .necessity ∨ purpose = .maintenance
  | .present => True
  | .issue .. | .assign .. | .settle .. => False

instance (cohort : List Party) (victims : List (Party × Good))
    (request : Request Party Good Port Technology Instrument) : Decidable (materialOperation cohort victims request) := by
  unfold materialOperation
  cases request.operation <;> infer_instance

inductive SourceAdmission (cohort : List Party) (victims : List (Party × Good))
    (word : RawEvent Party Good Port Technology Instrument) : Type
  | accepted (source : ∀ request ∈ word, materialOperation cohort victims request)
  | rejected (request : Request Party Good Port Technology Instrument) (member : request ∈ word)
      (foreign : ¬ materialOperation cohort victims request)

def inspectSource (cohort : List Party) (victims : List (Party × Good)) :
    (word : RawEvent Party Good Port Technology Instrument) → SourceAdmission cohort victims word
  | [] => .accepted (by simp)
  | request :: rest =>
    if source : materialOperation cohort victims request then
      match inspectSource cohort victims rest with
      | .accepted later => .accepted (by
          intro next member
          rcases List.mem_cons.mp member with same | old
          · exact same ▸ source
          · exact later next old)
      | .rejected next member foreign => .rejected next (List.mem_cons_of_mem request member) foreign
    else .rejected request List.mem_cons_self source

inductive Attempt (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (cohort : List Party) (victims : List (Party × Good))
    (word : RawEvent Party Good Port Technology Instrument) : Type
  | accepted (valid : ∀ item ∈ law.rawItems before word, law.Valid item.before item.request)
      (source : ∀ request ∈ word, materialOperation cohort victims request)
  | rejected (item : ExecutionItem Party Good Port Technology Instrument)
      (member : item ∈ law.rawItems before word) (invalid : ¬ law.Valid item.before item.request)
      (source : ∀ request ∈ word, materialOperation cohort victims request)
  | foreign (request : Request Party Good Port Technology Instrument) (member : request ∈ word)
      (outside : ¬ materialOperation cohort victims request)

def inspectAttempt (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (cohort : List Party) (victims : List (Party × Good))
    (word : RawEvent Party Good Port Technology Instrument) : Attempt law before cohort victims word :=
  match inspectSource cohort victims word with
  | .rejected request member foreign => .foreign request member foreign
  | .accepted source => match inspectMaterial law (law.rawItems before word) with
    | .accepted valid => .accepted valid source
    | .rejected item member invalid => .rejected item member invalid source

/-- This is the beneficiary's real net stock gain after every cost and transfer,
so paying one victim never also credits the payer's retained stock. -/
def Attempt.credit
    {law : RawLaw Party Good Port Technology Instrument} {before : RawCurrent Party Good Technology Instrument}
    {cohort : List Party} {victims : List (Party × Good)} {word : RawEvent Party Good Port Technology Instrument} :
    Attempt law before cohort victims word → (Party × Good) → ℚ
  | .accepted .., key | .rejected .., key =>
      max 0 ((law.next before word).stock key.1 key.2 - before.stock key.1 key.2)
  | .foreign .., _ => 0

theorem Attempt.credit_nonnegative
    {law : RawLaw Party Good Port Technology Instrument} {before : RawCurrent Party Good Technology Instrument}
    {cohort : List Party} {victims : List (Party × Good)} {word : RawEvent Party Good Port Technology Instrument}
    (attempt : Attempt law before cohort victims word) (key : Party × Good) : 0 ≤ attempt.credit key := by
  cases attempt with
  | accepted valid source => exact le_max_left _ _
  | rejected item member invalid source => exact le_max_left _ _
  | foreign request member outside => exact le_rfl

def Attempt.cursor
    {law : RawLaw Party Good Port Technology Instrument} {before : RawCurrent Party Good Technology Instrument}
    {cohort : List Party} {victims : List (Party × Good)} {word : RawEvent Party Good Port Technology Instrument} :
    Attempt law before cohort victims word → RawCurrent Party Good Technology Instrument
  | .accepted .. | .rejected .. => law.next before word
  | .foreign .. => before

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem a_source_material_operation_never_writes_a_financial_claim
    (cohort : List Party) (victims : List (Party × Good))
    (request : Request Party Good Port Technology Instrument) (source : materialOperation cohort victims request) :
    NonFinancialOperation request.operation := by
  cases operation : request.operation <;> simp_all [materialOperation,NonFinancialOperation]

theorem actual_family_reparation_preserves_every_original_financial_claim
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (cohort : List Party) (victims : List (Party × Good)) (word : RawEvent Party Good Port Technology Instrument)
    (source : ∀ request ∈ word, materialOperation cohort victims request) :
    (law.next before word).claims = before.claims :=
  nonfinancial_word_keeps_every_original_claim law before word (fun request member =>
    a_source_material_operation_never_writes_a_financial_claim cohort victims request (source request member))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family
