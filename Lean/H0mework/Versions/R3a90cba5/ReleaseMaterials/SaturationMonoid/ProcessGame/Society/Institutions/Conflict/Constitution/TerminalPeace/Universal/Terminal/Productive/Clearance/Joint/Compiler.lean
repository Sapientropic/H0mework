import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Domain
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Production
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Receipt

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt primitiveScript)
open Reparation.Actual (ReceiptAnswers Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)

local notation "Word" => Script Party Good Port Technology Instrument
local notation "RawWord" => RawEvent Party Good Port Technology Instrument

def openingDrain : Word := Quantities.Execution.drain (endAt seed (Occurrence.history loss))

def firstProduction (body : RawWord) : Word :=
  openingDrain loss ++ primitiveScript body

/-- Production credit is read from the actual registered inventory after
the native queue is drained. A proposed output alone has no material effect. -/
def ProducesAtFirstWrite (body : RawWord) : Prop :=
  let cut := endAt seed (Occurrence.history loss ++ openingDrain loss)
  ∃ item ∈ Quantities.Execution.inventory cut (primitiveScript body),
    ∃ person good, item.request.operation = .produce person ∧
      0 < flowAt ((Boundary.Actual.materialLaw cut).actualCredit item.before item.request) person good

variable (reserve : Party → Good → ℚ) (body : RawEvent Party Good Port Technology Instrument)
  (offers : ProductionMenu Party Good Port Technology Instrument)

local notation "First" => firstProduction loss body
local notation "Candidate" => Feasible loss answers reserve First offers
local notation "Anchor" => Occurrence.history loss

inductive CandidateIssue (word : Word) where
  | beforePilot (missing : ¬ List.IsPrefix First word)
  | sourceRefusal (failed : ProductionInputFailure (community := community) answers Anchor Anchor word)
  | material (failed : InventoryShortage loss reserve word)
  | residual (origin : Reparation.Actual.Occurrence seed community) (balance : Reparation.Actual.Balance)
      (row : (origin, balance) ∈ prefixRows loss answers word) (unpaid : 0 < balance.remaining)
  | continuation (failed : ¬ Nonempty (Realization loss answers (fun _ => True) word offers))

theorem CandidateIssue.refutes {word : Word}
    (issue : CandidateIssue loss answers reserve body offers word) : ¬ Candidate word := by
  intro paid
  cases issue with
  | beforePilot missing => exact missing paid.first
  | sourceRefusal failed =>
    exact (ProductionInputFailure.refutes answers Anchor failed) paid.living.1.2
  | material failed => exact (failed.refutes loss) paid.inventory
  | residual origin balance row unpaid => exact (ne_of_gt unpaid) (paid.payable (origin, balance) row)
  | continuation failed => exact failed ⟨realize paid.living⟩

def inspectCandidate (word : Word) :
    CandidateIssue loss answers reserve body offers word ⊕ PLift (Candidate word) := by
  classical
  by_cases first : List.IsPrefix First word
  · match inspectInputs (community := community) answers Anchor Anchor word with
    | .inl failed => exact .inl (.sourceRefusal failed)
    | .inr _ =>
      match inspectInventory loss reserve word with
      | .inl failed => exact .inl (.material failed)
      | .inr stocked =>
        by_cases all : WholeCleared loss answers word
        · by_cases living : ViableEntry loss answers (fun _ => True) word offers
          · exact .inr ⟨⟨first, stocked.down, all, living⟩⟩
          · exact .inl (.continuation (fun ⟨run⟩ => living (realization_has_an_exactly_viable_source run)))
        · have missing : ∃ row ∈ prefixRows loss answers word, 0 < row.2.remaining := by
            by_contra! none
            exact all fun row listed => (none row listed).antisymm row.2.nonnegative
          let row := Classical.choose missing
          have exactRow := Classical.choose_spec missing
          exact .inl (.residual row.1 row.2 exactRow.1 exactRow.2)
  · exact .inl (.beforePilot first)

theorem inspectCandidate_passes_iff (word : Word) :
    (∃ accepted, inspectCandidate loss answers reserve body offers word = .inr accepted) ↔ Candidate word := by
  constructor
  · rintro ⟨accepted, _⟩
    exact accepted.down
  · intro fits
    cases inspectCandidate loss answers reserve body offers word with
    | inl failure => exact ((failure.refutes loss answers reserve body offers) fits).elim
    | inr accepted => exact ⟨accepted, rfl⟩

inductive JointOutcome where
  | pilotRefused (original : ProductionDecision answers loss (openingDrain loss) body)
      (refutes : ¬ ProductionWrite answers loss (openingDrain loss) body)
  | idlePilot (original : ProductionWrite answers loss (openingDrain loss) body)
      (noCredit : ¬ ProducesAtFirstWrite loss body)
  | exhausted (original : ProductionWrite answers loss (openingDrain loss) body)
      (growth : ProducesAtFirstWrite loss body)
      (explain : ∀ word, CandidateIssue loss answers reserve body offers word)
  | paid (original : ProductionWrite answers loss (openingDrain loss) body)
      (growth : ProducesAtFirstWrite loss body)
      (result : PaidFrontier loss answers reserve First offers)

/-- The only submitted word is the new production instruction. The
repayment order, amounts and cofinal run are selected on the native ledger. -/
def compileJoint : JointOutcome loss answers reserve body offers := by
  classical
  let original := inspectProduction answers loss (openingDrain loss) body
  cases chosen : original with
  | written write =>
    by_cases growth : ProducesAtFirstWrite loss body
    · by_cases canPay : ∃ word, Candidate word
      · exact .paid write growth (selectFirstPaid loss answers reserve First offers canPay)
      · refine .exhausted write growth fun word => ?_
        cases inspectCandidate loss answers reserve body offers word with
        | inl failure => exact failure
        | inr fits => exact (canPay ⟨word, fits.down⟩).elim
    · exact .idlePilot write growth
  | authority item listed failed =>
    exact .pilotRefused original (fun write => failed (write.authorized item listed))
  | native _ failed => exact .pilotRefused original (fun write => failed write.trace)
  | rejected failed =>
    exact .pilotRefused original (fun write => (ProductionInputFailure.refutes answers Anchor failed) write.eligible)

theorem compileJoint_pays_iff :
    (∃ original growth result, compileJoint loss answers reserve body offers = .paid original growth result) ↔
      ProductionWrite answers loss (openingDrain loss) body ∧ ProducesAtFirstWrite loss body ∧
        ∃ word : Word, Candidate word := by
  constructor
  · rintro ⟨original, growth, result, _⟩
    exact ⟨original, growth, result.word, result.feasible⟩
  · rintro ⟨write, grows, word, possible⟩
    cases compileJoint loss answers reserve body offers with
    | pilotRefused _ failed => exact (failed write).elim
    | idlePilot _ noCredit => exact (noCredit grows).elim
    | exhausted _ _ every => exact ((every word).refutes loss answers reserve body offers possible).elim
    | paid original growth result => exact ⟨original, growth, result, rfl⟩

theorem firstProduction_is_a_real_original_write
    (original : ProductionWrite answers loss (openingDrain loss) body) :
    Occurrence.Unbounded.ActualWrite answers loss First := by
  have empty := (Quantities.Execution.the_first_exhausted_native_cut_is_the_original_paid_drain
    (endAt seed (Occurrence.history loss))).2.2.1
  have eligible := Funding.empty_inventory_is_eligible (community := community)
    answers Anchor Anchor (openingDrain loss) empty
  exact Occurrence.Unbounded.an_eligible_word_has_its_actual_whole_write answers loss First
    (original.eligibility eligible)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint
