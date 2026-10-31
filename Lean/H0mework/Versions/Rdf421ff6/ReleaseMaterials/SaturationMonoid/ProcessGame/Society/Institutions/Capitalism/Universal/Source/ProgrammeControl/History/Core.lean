import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Reciprocity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Disposal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Checks
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.ControlledFlow

/-! A constitutive certificate spans original occurrences.  A source title
quotation or original actual surplus supplies the asset witness; title
mutability is not required. The current private phase can change holder. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History

open Program
open Kernel.AssetAuthority
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)

abbrev SourceQuote (access : Access input endpoint) :=
  { request : Request Party Good Port Technology Instrument //
    request ∈ input.localAttempts (access.access.raw input).before }

def titleProposal (access : Access input endpoint) (quote : SourceQuote input endpoint access) :
    TransferProposal input.law
      (Root.ProgrammeSource.rawCurrent input (access.access.address input).1.current)
      (Root.ProgrammeSource.rawEvent input (access.access.address input).1.current) :=
  ⟨(access.access.address input).2, access.port, some quote.val⟩

abbrev TitleAt (access : Access input endpoint) := AssetControlTransport input.law
  (Root.ProgrammeSource.rawCurrent input (access.access.address input).1.current)
  (Root.ProgrammeSource.rawEvent input (access.access.address input).1.current)

def retainedOutput (access : Access input endpoint) : Prop :=
  access.mode = .acquired ∧ access.accessHolder = access.controller input endpoint ∧
  (match (access.access.raw input).request.operation with
    | .produce operator => operator = access.accessHolder
    | _ => False) ∧
  input.law.controller (target input endpoint).technology access.port = access.accessHolder ∧
  input.law.totalDebit (((entries input endpoint).filter
    (fun entry => decide (access.access.position input ≤ entry.position input))).map (Entry.raw input))
      access.accessHolder access.accessGood <
    flowAt (input.law.actualCredit (access.access.raw input).before (access.access.raw input).request)
      access.accessHolder access.accessGood ∧
  (access.access.raw input).before.stock access.accessHolder access.accessGood <
    (target input endpoint).stock access.accessHolder access.accessGood

instance (access : Access input endpoint) : Decidable (retainedOutput input endpoint access) := by
  unfold retainedOutput
  cases (access.access.raw input).request.operation <;> infer_instance

inductive Evidence (access : Access input endpoint)
  | title (quote : SourceQuote input endpoint access)
  | retention
  | consumption (position : Entry input endpoint) (good : Good)
      (route : List (RouteLeg input endpoint))
  | investment (position : Entry input endpoint) (paidGood growthGood : Good)
      (route : List (RouteLeg input endpoint))

namespace Evidence
variable (access : Access input endpoint)

def Checks : Evidence input endpoint access → Prop
  | .title quote => (compileTransfer input.law _ _ (titleProposal input endpoint access quote)).isSome
  | .retention => retainedOutput input endpoint access
  | .consumption position good route =>
      access.mode = .acquired ∧
      Follows input endpoint (access.accessHolder, access.accessGood) (access.access.position input + 1)
        route (input.law.controller (position.raw input).before.technology access.port, good)
        (position.position input) ∧
      controlAlong input endpoint access.port access.recipient (access.accessHolder, access.accessGood) route ∧
      Kernel.ActualSurplus.performedAt input.law (position.raw input) access.port
        (input.law.controller (position.raw input).before.technology access.port) good
  | .investment position paidGood growthGood route =>
      access.mode = .acquired ∧
      Follows input endpoint (access.accessHolder, access.accessGood) (access.access.position input + 1)
        route (input.law.controller (position.raw input).before.technology access.port, paidGood)
        (position.position input) ∧
      controlAlong input endpoint access.port access.recipient (access.accessHolder, access.accessGood) route ∧
      Kernel.ActualSurplus.investedAt input.law (position.raw input) access.port
        (input.law.controller (position.raw input).before.technology access.port) paidGood growthGood

instance (evidence : Evidence input endpoint access) : Decidable (Checks input endpoint access evidence) := by
  cases evidence <;> unfold Checks <;> infer_instance

def actualPosition : Evidence input endpoint access → Option (Entry input endpoint)
  | .title _ => none
  | .retention => some access.access
  | .consumption position _ _ | .investment position _ _ _ => some position
end Evidence

structure Capital where
  private mk ::
  access : Access input endpoint
  reciprocity : Reciprocity input endpoint
  disposal : Disposal input endpoint
  checked : access.Checks input endpoint ∧ reciprocity.Checks input endpoint access ∧ disposal.Checks input endpoint access
  evidence : Evidence input endpoint access
  evidence_checked : evidence.Checks input endpoint access

def compile (access : Access input endpoint) (reciprocity : Reciprocity input endpoint)
    (disposal : Disposal input endpoint) (evidence : Evidence input endpoint access) : Option (Capital input endpoint) :=
  if checked : access.Checks input endpoint ∧ reciprocity.Checks input endpoint access ∧ disposal.Checks input endpoint access then
    if support : evidence.Checks input endpoint access then
      some ⟨access, reciprocity, disposal, checked, evidence, support⟩
    else none
  else none

namespace Capital
variable (capital : Capital input endpoint)

def accessOrigin := capital.access.access.origin input
def needOrigin := capital.access.need.origin input
def financialOrigin := capital.reciprocity.financialOrigin input endpoint

theorem original_origins_and_actual_before :
    (capital.accessOrigin input endpoint).instruction? input = some (capital.access.access.raw input) ∧
    (capital.needOrigin input endpoint).instruction? input = some (capital.access.need.raw input) ∧
    input.law.Valid (capital.access.access.raw input).before (capital.access.access.raw input).request :=
  ⟨(capital.access.access.original_visit_and_local_index input).2.2,
    (capital.access.need.original_visit_and_local_index input).2.2, capital.checked.1.1⟩

theorem private_relation_at_current_phase :
    input.law.allowed (target input endpoint).technology capital.access.port
      (input.law.controller (target input endpoint).technology capital.access.port) = true ∧
    ∃ person ∈ parties input endpoint,
      input.law.allowed (target input endpoint).technology capital.access.port person = false :=
  capital.checked.1.2.2.2.2.2

theorem source_generated_title_or_actual_surplus :
    (∃ quote : SourceQuote input endpoint capital.access,
      (compileTransfer input.law _ _ (titleProposal input endpoint capital.access quote)).isSome) ∨
    (∃ (position : Entry input endpoint) (good : Good),
      Kernel.ActualSurplus.performedAt input.law (position.raw input) capital.access.port
        (input.law.controller (position.raw input).before.technology capital.access.port) good) ∨
    (∃ (position : Entry input endpoint) (paidGood growthGood : Good),
      Kernel.ActualSurplus.investedAt input.law (position.raw input) capital.access.port
        (input.law.controller (position.raw input).before.technology capital.access.port) paidGood growthGood) ∨
    retainedOutput input endpoint capital.access := by
  have paid := capital.evidence_checked
  cases eq : capital.evidence with
  | title quote =>
      rw [eq] at paid
      exact Or.inl ⟨quote, paid⟩
  | retention =>
      rw [eq] at paid
      exact Or.inr (Or.inr (Or.inr paid))
  | consumption position good route =>
      rw [eq] at paid
      exact Or.inr (Or.inl ⟨position, good, paid.2.2.2⟩)
  | investment position paidGood growthGood route =>
      rw [eq] at paid
      exact Or.inr (Or.inr (Or.inl ⟨position, paidGood, growthGood, paid.2.2.2⟩))

end Capital

#print axioms compile
#print axioms Capital.original_origins_and_actual_before
#print axioms Capital.private_relation_at_current_phase
#print axioms Capital.source_generated_title_or_actual_surplus

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History
