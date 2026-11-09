import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Recipe
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.FirstWrite
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Portfolio

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Material (inspectList)
open Reparation.Actual (ReceiptAnswers Occurrence Script)
open Quantities.Execution (primitiveScript)
open Clearance
open Joint.SourceReserve

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  [DecidableEq (Request Party Good Port Technology Instrument)]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (loss : Occurrence seed community) (answers : ReceiptAnswers seed)
  (body : RawEvent Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (offers : ProductionMenu Party Good Port Technology Instrument)
  (addresses : List (Party × Good)) (covered : ∀ address, address ∈ addresses)

local notation "Word" => Script Party Good Port Technology Instrument
local notation "First" => Joint.firstProduction loss body
local notation "Reserve" => openingReserve loss

/-- The finite scan uses original visit and item positions. The address
enumeration is supplied by the source's inventory decoder. -/
structure StockIssue (word : Word) where
  cut : Joint.InventoryRead Party Good Technology Instrument
  actual : cut ∈ Joint.inventoryTrace loss word
  address : Party × Good
  missing : cut.raw.stock address.1 address.2 <
    atRaw seed.native.input.law (originalRaw loss) cut.raw address.1 address.2

omit [DecidableEq (Request Party Good Port Technology Instrument)] in
theorem StockIssue.refutes {word : Word} (issue : StockIssue loss word) :
    ¬ ProtectsNeeds loss word :=
  fun fits => issue.missing.not_ge (fits issue.cut issue.actual issue.address.1 issue.address.2)

def inspectSourceStock (word : Word) :
    StockIssue loss word ⊕ PLift (ProtectsNeeds loss word) := by
  let fits (read : Joint.InventoryRead Party Good Technology Instrument) (address : Party × Good) :=
    atRaw seed.native.input.law (originalRaw loss) read.raw address.1 address.2 ≤
      read.raw.stock address.1 address.2
  let good (read : Joint.InventoryRead Party Good Technology Instrument) := ∀ address ∈ addresses, fits read address
  cases inspectList good (Joint.inventoryTrace loss word) with
  | failure cut actual failed =>
    cases inspectList (fits cut) addresses with
    | failure address _ missing => exact .inl ⟨cut, actual, address, lt_of_not_ge missing⟩
    | clear checks => exact (failed checks).elim
  | clear good =>
    exact .inr ⟨fun cut actual person commodity => good cut actual (person, commodity) (covered _)⟩

inductive OpeningResult
  | empty (noProductionWord : body = [])
  | unproductive (noActualOutput : ¬ Joint.ProducesAtFirstWrite loss body)
  | drained (failure : Joint.ProductionInputFailure (community := community) answers
      (Occurrence.history loss) (Occurrence.history loss) (Joint.openingDrain loss))
  | refused (failure : ProductionObstruction loss answers (Joint.openingDrain loss) body)
  | debt (landed : Endpoint loss answers First) (key : Reparation.Key Party Good)
      (failure : Block loss answers landed.word key)
  | stock (landed : Endpoint loss answers First) (failure : StockIssue loss landed.word)
  | unapproved (landed : Endpoint loss answers First) (choice : ProductionChoice offers)
      (refused : ¬ ProductionApproved seed loss landed.word choice)
  | pilot (landed : Endpoint loss answers First) (choice : ProductionChoice offers)
      (production : RawEvent Party Good Port Technology Instrument)
      (wrong : ¬ ProductionStartsWith choice production)
  | recipe (landed : Endpoint loss answers First) (choice : ProductionChoice offers)
      (code : RepeatCode (productionInput seed loss landed.word choice) (prefixRaw loss landed.word))
      (failure : RecipeIssue (productionInput seed loss landed.word choice)
        (originalRaw loss) (prefixRaw loss landed.word) (productionRoster seed loss landed.word choice) code)
  | opened (opening : SettledOpening loss answers Reserve body offers replies)

private instance producesDecidable (request : Request Party Good Port Technology Instrument) :
    Decidable (∃ person, request.operation = .produce person) := by
  cases request.operation <;> simp <;> infer_instance

def pilotCheck (choice : ProductionChoice offers)
    (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (ProductionStartsWith choice word) := by
  cases choice <;> unfold ProductionStartsWith <;> infer_instance

def approvalCheck (word : Word) (choice : ProductionChoice offers) :
    Decidable (ProductionApproved seed loss word choice) := by
  cases choice <;> unfold ProductionApproved <;> infer_instance

/-- Consume the selected original production and generate its portfolio
payment before checking the registered recurring recipe. The compiler
accepts no payment plan or completed productive trajectory. -/
def compileWithMenu
    (choiceAt : Word → ProductionChoice offers)
    (codeAt : ∀ word, RepeatCode (productionInput seed loss word (choiceAt word)) (prefixRaw loss word)) :
    OpeningResult loss answers body replies offers := by
  letI := firstProductionCheck loss addresses covered body
  exact
  if nonempty : body = [] then .empty nonempty
  else if produces : Joint.ProducesAtFirstWrite loss body then
    match Joint.inspectInputs (community := community) answers (Occurrence.history loss)
      (Occurrence.history loss) (Joint.openingDrain loss) with
    | .inl failure => .drained failure
    | .inr safe =>
      match clearAfterProduction loss answers (Joint.openingDrain loss) body safe.down nonempty with
      | .inl failure => .refused failure
      | .inr begun =>
        match begun.clearance with
        | .stopped landed key _ failure => .debt landed key failure
        | .complete landed closed =>
          match inspectSourceStock loss addresses covered landed.word with
          | .inl failure => .stock landed failure
          | .inr stocked => Id.run do
            let choice := choiceAt landed.word
            let code := codeAt landed.word
            letI := approvalCheck loss offers landed.word choice
            letI := pilotCheck offers choice code.production
            if approved : ProductionApproved seed loss landed.word choice then
              if starts : ProductionStartsWith choice code.production then
                let input := productionInput seed loss landed.word choice
                let roster := productionRoster seed loss landed.word choice
                match checkRecipe input (originalRaw loss) (prefixRaw loss landed.word) roster code with
                | .inl failure => return .recipe landed choice code failure
                | .inr recipe =>
                  return .opened (settleOpening loss answers Reserve body offers replies landed.word
                    ⟨landed.prefixWord, stocked.down.retains_opening_reserve loss, landed.safe, landed.ready,
                      a_completed_portfolio_clears_every_original_row loss answers landed closed,
                      choice, approved, _, recipe.val, recipe.property.symm ▸ starts⟩)
              else return .pilot landed choice code.production starts
            else return .unapproved landed choice approved
  else .unproductive produces

def compileNative
    (codeAt : (word : Word) → RepeatCode seed.native.input (prefixRaw loss word)) :
    OpeningResult loss answers body replies ProductionMenu.empty :=
  compileWithMenu loss answers body replies ProductionMenu.empty addresses covered (fun _ => none) codeAt

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational
