import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Batch.Payments
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Admission.Datum input (Admission.frame input depth count)) (limit : Nat)

def selectedWord (current : Current input depth count datum) : Option (RawEvent Party Good Port Technology Instrument) :=
  match current.first with
  | true => (Batch.completed input depth count datum limit).selectedWord
  | false => (Review.Guarded.complete input (Batch.origin input depth count)
      (Batch.code input depth count datum).request (Batch.code input depth count datum).scope
      (Batch.cohort input depth count) current.raw (laterCandidates input limit current.raw)).selectedWord

def reviewed (current : Current input depth count datum) : Raw (Party := Party) (Good := Good)
    (Technology := Technology) (Instrument := Instrument) :=
  match current.first with
  | true => (Batch.completed input depth count datum limit).current
  | false => (Review.Guarded.complete input (Batch.origin input depth count)
      (Batch.code input depth count datum).request (Batch.code input depth count datum).scope
      (Batch.cohort input depth count) current.raw (laterCandidates input limit current.raw)).current

/-- These are actual period records only. Counterfactual candidate traces
remain in the review result and do not acquire execution or birth authority. -/
def executedPeriod (current : Current input depth count datum) :
    Option (ExecutionResult Party Good Port Technology Instrument) :=
  (selectedWord input depth count datum limit current).map
    (fun word => input.law.execute (reviewed input depth count datum limit current) 0 word)

def firstActualExecution : ExecutionResult Party Good Port Technology Instrument :=
  match paid_eq : Admission.result input depth count datum with
  | .inl paid => (Batch.completed input depth count datum limit).actualExecution
      (Batch.paymentsAfterOriginalFee input depth count datum limit paid paid_eq)
  | .inr _ => ⟨Batch.atFee input depth count datum, []⟩

def actualExecution (current : Current input depth count datum) :
    ExecutionResult Party Good Port Technology Instrument :=
  match current.first with
  | true => firstActualExecution input depth count datum limit
  | false =>
      let report := Review.Guarded.complete input (Batch.origin input depth count)
        (Batch.code input depth count datum).request (Batch.code input depth count datum).scope
        (Batch.cohort input depth count) current.raw (laterCandidates input limit current.raw)
      report.actualExecution report.payments

theorem selected_effect_is_actual (current : Current input depth count datum)
    (word : RawEvent Party Good Port Technology Instrument)
    (selected : selectedWord input depth count datum limit current = some word) :
    (next input depth count datum limit current).raw = input.law.next
        (reviewed input depth count datum limit current) word ∧
      Review.Guarded.Checks input (Batch.origin input depth count)
        (reviewed input depth count datum limit current) (Batch.cohort input depth count) word := by
  cases phase : current.first <;>
    simp only [selectedWord, reviewed, next, effect, phase] at selected ⊢
  · exact (Review.Guarded.complete input (Batch.origin input depth count)
      (Batch.code input depth count datum).request (Batch.code input depth count datum).scope
      (Batch.cohort input depth count) current.raw (laterCandidates input limit current.raw)).selected_effect_is_the_actual_period word selected
  · exact (Batch.completed input depth count datum limit).selected_effect_is_the_actual_period word selected

theorem next_preserves_original_financial_claims (current : Current input depth count datum) :
    (next input depth count datum limit current).raw.claims = current.raw.claims := by
  cases phase : current.first
  · change (effect input depth count datum limit current).claims = _
    simp only [effect, phase]
    exact (Review.Guarded.complete input (Batch.origin input depth count)
      (Batch.code input depth count datum).request (Batch.code input depth count datum).scope
      (Batch.cohort input depth count) current.raw (laterCandidates input limit current.raw)).effect_preserves_original_claims
  · have same := current.original_fee_target phase
    have safe : Settlement.NonFinancialRequest (Batch.code input depth count datum).request := by
      simp only [Settlement.NonFinancialRequest, (Batch.code input depth count datum).scope.operation]
    have paidClaims := safe.step_claims input.law (Batch.origin input depth count) (Batch.code input depth count datum).request
    change (effect input depth count datum limit current).claims = _
    simp only [effect, phase]
    exact (Batch.completed input depth count datum limit).effect_preserves_original_claims.trans
      (paidClaims.symm.trans (congrArg RawCurrent.claims same.symm))

def entryAt {current : Current input depth count datum}
    (occurrence : (source input depth count datum limit).toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt (N input depth count) occurrence.1 := by
  cases occurrence_eq_emitted input depth count datum limit occurrence
  exact (Admission.frame input depth count).native.entrySupport
    (Continuation.oldSupport input (Admission.frame input depth count))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller
