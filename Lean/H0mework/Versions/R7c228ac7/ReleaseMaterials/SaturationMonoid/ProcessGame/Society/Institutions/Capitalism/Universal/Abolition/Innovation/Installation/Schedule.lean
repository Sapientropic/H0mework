import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Observation.Reader
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

abbrev InputAt := Compile.RawInput Party Good Bool Nat Unit
abbrev CursorAt := Physical.Cursor Party Good Bool Nat Unit
abbrev count := Macro.Ingress.cut input 0 0

def rule : Observation.Rule Party Good Bool Nat Unit where
  code := Control.Scenario.code false
  site := 0
  cost := [(.message,1)]
  cost_nonnegative := by decide +kernel
  cost_positive := ⟨.message, by decide +kernel⟩
  port := false

def beforePublic : InputAt → Bool
  | .execute _ => false
  | _ => true

/-- The first completed source execution marks the public body. The cut is
read from this actual prefix, rather than passed in as an endpoint. -/
def sourceCut (past : List InputAt) := past.takeWhile beforePublic
def publicPast (past : List InputAt) := past.drop (sourceCut past).length

def localProposal (past : List InputAt) : InputAt :=
  Observation.scheduledProposal input 0 count 0 0 (sourceCut past) rule
    (Observation.programmeFromSensor rule programme) (publicPast past)

def isIssue (request : RequestAt) : Bool :=
  match request.operation with | .issue .. => true | _ => false

def isNonFinancial (request : RequestAt) : Bool :=
  decide (Settlement.NonFinancialRequest request)

/-- Liability births and financial movements remain separate original
microsteps. Only the intervening nonfinancial word is a guarded period. -/
def executionInputs (word : RawEvent Party Good Bool Nat Unit) : List InputAt :=
  let births := word.takeWhile isIssue
  let rest := word.drop births.length
  let work := rest.takeWhile isNonFinancial
  births.map Compile.RawInput.primitive ++ [.execute work] ++
    (rest.drop work.length).map Compile.RawInput.primitive

def codeProgressFromReverse : List InputAt → Option (RawEvent Party Good Bool Nat Unit × Nat)
  | [] => none
  | .code submitted :: _ => some (submitted.requests,0)
  | _ :: prior => (codeProgressFromReverse prior).map fun progress => (progress.1, progress.2 + 1)

def codeProgress (past : List InputAt) := codeProgressFromReverse past.reverse

def codeAttempt (word : RawEvent Party Good Bool Nat Unit) : InputAt :=
  ((executionInputs word)[0]?).getD (.execute Control.Scenario.commonWork)

/-- Progress counts completed attempts after the actual submitted code.
Refusal never rewinds it or removes the liability born before fulfillment. -/
def afterPreparationWith (localRead : List InputAt → InputAt) (past : List InputAt) : InputAt :=
  match codeProgress past with
  | some (word, spent) => ((executionInputs word)[spent]?).getD (.execute Control.Scenario.commonWork)
  | none => localRead past

def afterPreparation := afterPreparationWith localProposal

def selectedWith (localRead : List InputAt → InputAt) (nature : RequestAt) (past : List InputAt) : InputAt :=
  if offerAccepted then
    match publicPast past with
    | [] => .execute Control.Scenario.commonWork
    | _baseline :: completed =>
        if completed.length < preparation.length then
          match preparation[completed.length]? with
          | some request => .primitive request
          | none => .stopReview
        else if completed.length = preparation.length then .primitive nature
        else if completed.length = preparation.length + 1 then .primitive (Control.Scenario.production 0)
        else afterPreparationWith localRead past
  else .stopReview

def selected := selectedWith localProposal

def reader (nature : RequestAt) : Macro.Raw.Reader input 0 count :=
  fun cursor _ => selected nature cursor.past

theorem the_programme_consults_no_financial_or_hidden_global_state
    (nature : RequestAt) (cursor : CursorAt)
    (first second : (Epoch.Finance.process input 0 count).GeneratedState) :
    reader nature cursor first = reader nature cursor second := rfl

theorem every_financing_choice_is_independent_of_the_later_nature
    (first second : RequestAt) (past : List InputAt)
    (preparing : (publicPast past).length ≤ preparation.length) :
    selected first past = selected second past := by
  unfold selected selectedWith
  split
  · cases splitPast : publicPast past with
    | nil => rfl
    | cons initial rest =>
        have bound : rest.length < preparation.length := by
          rw [splitPast, List.length_cons] at preparing
          omega
        simp only [if_pos bound]
  · rfl

theorem a_generated_code_is_the_literal_next_execution_attempt
    (past : List InputAt) (submitted : Actual.Submission Party Good Bool Nat Unit) :
    afterPreparation (past ++ [.code submitted]) = codeAttempt submitted.requests := by
  simp only [afterPreparation, afterPreparationWith, codeProgress, List.reverse_append, List.reverse_singleton,
    List.singleton_append, codeProgressFromReverse]
  rfl

theorem native_risk_begins_before_the_guarded_work_and_primitive_payments :
    executionInputs (programme 1) = [.primitive Control.Scenario.successLiability,
      .execute Control.Scenario.commonWork,.primitive Control.Scenario.repay,.primitive Control.Scenario.successPayment] ∧
    executionInputs (programme 0) = [.primitive Control.Scenario.failureLiability,
      .execute Control.Scenario.commonWork,.primitive Control.Scenario.failureCoverage,.primitive Control.Scenario.repay] := by
  constructor <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
