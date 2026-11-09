import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Opening

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Capitalism.Universal.Abolition.Material (inspectList)
open Reparation.Actual (ReceiptAnswers Occurrence Script)
open Quantities.Execution (endAt primitiveScript)
open Clearance Joint.SourceReserve
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  [DecidableEq (Request Party Good Port Technology Instrument)]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Occurrence seed community) (answers : ReceiptAnswers seed)
  (body : RawEvent Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (offers : ProductionMenu Party Good Port Technology Instrument)
  (addresses : List (Party × Good)) (covered : ∀ address, address ∈ addresses)

local notation "Word" => Script Party Good Port Technology Instrument
local notation "Front" => Joint.openingDrain loss
local notation "First" => Joint.firstProduction loss body
local notation "Reserve" => openingReserve loss

/-- A proposed word is evidence only after the source checks every original
visit, both signatures, the inventory and the separate personal exits. -/
inductive CertificateIssue (tail : Word) (choice : ProductionChoice offers)
    (code : RepeatCode (productionInput seed loss (First ++ tail) choice) (prefixRaw loss (First ++ tail))) : Type where
  | empty (missing : body = [])
  | unproductive (missing : ¬ Joint.ProducesAtFirstWrite loss body)
  | authority (item : ExecutionItem Party Good Port Technology Instrument)
      (refutes : ¬ Joint.ProductionWrite answers loss Front body)
  | native (position : Option (Nat × Request Party Good Port Technology Instrument))
      (refutes : ¬ Joint.ProductionWrite answers loss Front body)
  | firstInput (issue : Joint.ProductionInputFailure (community := community) answers
      (Occurrence.history loss) (Occurrence.history loss ++ Front) (primitiveScript body))
  | input (issue : Joint.ProductionInputFailure (community := community) answers
      (Occurrence.history loss) (Occurrence.history loss) (First ++ tail))
  | stock (issue : StockIssue loss (First ++ tail))
  | work (pending : ¬ Ready (endAt seed (Occurrence.history loss ++ (First ++ tail))))
  | review (closed : ¬ ReviewAvailable (endAt seed (Occurrence.history loss ++ (First ++ tail))))
  | debt (origin : Occurrence seed community) (due : Reparation.Actual.Balance)
      (actual : (origin, due) ∈ prefixRows loss answers (First ++ tail)) (openDebt : due.remaining ≠ 0)
  | unapproved (refused : ¬ ProductionApproved seed loss (First ++ tail) choice)
  | pilot (wrong : ¬ ProductionStartsWith choice code.production)
  | recipe (failed : RecipeIssue (productionInput seed loss (First ++ tail) choice) (originalRaw loss)
      (prefixRaw loss (First ++ tail)) (productionRoster seed loss (First ++ tail) choice) code)

structure CheckedCertificate (tail : Word) where
  opening : SettledOpening loss answers Reserve body offers replies
  usesOriginalWord : opening.word = First ++ tail
  firstWrite : Joint.ProductionWrite answers loss Front body
  firstProductive : Joint.ProducesAtFirstWrite loss body
  protects : ProtectsNeeds loss (First ++ tail)

variable (tail : Script Party Good Port Technology Instrument) (choice : ProductionChoice offers)

local notation "Candidate" => (First ++ tail)
local notation "Input" => productionInput seed loss Candidate choice
local notation "Roster" => productionRoster seed loss Candidate choice
local notation "Landing" => endAt seed (Occurrence.history loss ++ Candidate)

variable (code : RepeatCode
  (productionInput seed loss (Joint.firstProduction loss body ++ tail) choice)
  (prefixRaw loss (Joint.firstProduction loss body ++ tail)))

/-- Replay any submitted order and quantity of transfers. This consumes
no success flag or clearance proof and makes no greedy choice. -/
def verifyPrepared :
    Except (CertificateIssue loss answers body offers tail choice code)
      (CheckedCertificate loss answers body replies offers tail) := by
  letI := firstProductionCheck loss addresses covered body
  letI := approvalCheck loss offers Candidate choice
  letI := pilotCheck offers choice code.production
  exact do
    if empty : body = [] then
      throw (.empty empty)
    else pure ()
    let growth ← if paid : Joint.ProducesAtFirstWrite loss body then pure (PLift.up paid)
      else throw (.unproductive paid)
    let first ← match Joint.inspectProduction answers loss Front body with
      | .authority item actual refused => throw (.authority item
          (fun first => refused (first.authorized item actual)))
      | .native failure denied => throw (.native (match failure with
          | .authority item _ _ => some (item.index, item.request)
          | .body earlier _ request _ _ _ _ => some (earlier.length, request)
          | .accounts _ _ _ => none) (fun first => denied first.trace))
      | .rejected issue => throw (.firstInput issue)
      | .written first => pure (PLift.up first)
    let safe ← match Joint.inspectInputs (community := community) answers (Occurrence.history loss)
        (Occurrence.history loss) Candidate with
      | .inl issue => throw (.input issue)
      | .inr checked => pure checked
    let kept ← match inspectSourceStock loss addresses covered Candidate with
      | .inl issue => throw (.stock issue)
      | .inr checked => pure checked
    let ready ← if ready : Ready Landing then pure (PLift.up ready) else throw (.work ready)
    let review ← if review : ReviewAvailable Landing then pure (PLift.up review) else throw (.review review)
    let zero ← match inspectList (fun row => row.2.remaining = 0) (prefixRows loss answers Candidate) with
      | .failure row actual unpaid => throw (.debt row.1 row.2 actual unpaid)
      | .clear zero => pure (PLift.up zero)
    let approved ← if approved : ProductionApproved seed loss Candidate choice then pure (PLift.up approved)
      else throw (.unapproved approved)
    let starts ← if starts : ProductionStartsWith choice code.production then pure (PLift.up starts)
      else throw (.pilot starts)
    let recipe ← match checkRecipe Input (originalRaw loss) (prefixRaw loss Candidate) Roster code with
      | .inl issue => throw (.recipe issue)
      | .inr recipe => pure recipe
    let entry : OpeningAt loss answers Reserve body offers Candidate :=
      ⟨List.prefix_append _ _, kept.down.retains_opening_reserve loss, safe.down,
        ⟨ready.down, review.down⟩, zero.down, choice, approved.down, _, recipe.val, recipe.property.symm ▸ starts.down⟩
    return ⟨settleOpening loss answers Reserve body offers replies Candidate entry,
      rfl, first.down, growth.down, kept.down⟩


/-- Publish a failed preflight on the original occurrence. An invalid
word has no authority to advance the material position. -/
def writeCertificateIssue (issue : CertificateIssue loss answers body offers tail choice code) :
    Installation.Core.Landed seed community (endAt seed (Occurrence.history loss))
      (CertificateIssue loss answers body offers tail choice code) :=
  Installation.Core.publish (Occurrence.originState loss) issue true

omit [DecidableEq (Request Party Good Port Technology Instrument)] in
theorem a_failed_preflight_keeps_the_original_ledger_and_generates_next
    (issue : CertificateIssue loss answers body offers tail choice code) :
    let before := Occurrence.originState loss
    let next := writeCertificateIssue loss answers body offers tail choice code issue
    next.state.stack = before.stack ∧
      (⟨before.world, (Installation.Core.action before issue true).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = next.state.resident.erase :=
  ⟨rfl, Installation.Core.the_canonical_write_is_the_published_whole_state _ _ _⟩

structure PreparedChecks : Prop where
  nonempty : body ≠ []
  production : Joint.ProductionWrite answers loss Front body
  credit : Joint.ProducesAtFirstWrite loss body
  admissible : Occurrence.Eligible answers loss Candidate
  inventory : ProtectsNeeds loss Candidate
  ready : ReadyEntry loss Candidate
  debt : WholeCleared loss answers Candidate
  authorization : ProductionApproved seed loss Candidate choice
  pilot : ProductionStartsWith choice code.production
  recurring : RecipeConditions Input (originalRaw loss) (prefixRaw loss Candidate) Roster code

omit [DecidableEq (Request Party Good Port Technology Instrument)] in
theorem CertificateIssue.refutes (issue : CertificateIssue loss answers body offers tail choice code) :
    ¬ PreparedChecks loss answers body offers tail choice code := by
  intro checked
  cases issue with
  | empty missing => exact checked.nonempty missing
  | unproductive missing => exact missing checked.credit
  | authority _ denied => exact denied checked.production
  | native _ denied => exact denied checked.production
  | firstInput issue => exact (issue.refutes answers (Occurrence.history loss)) checked.production.eligible
  | input issue => exact (issue.refutes answers (Occurrence.history loss)) checked.admissible
  | stock issue => exact issue.refutes loss checked.inventory
  | work pending => exact pending checked.ready.1
  | review closed => exact closed checked.ready.2
  | debt _ _ actual unpaid => exact unpaid (checked.debt _ actual)
  | unapproved denied => exact denied checked.authorization
  | pilot wrong => exact wrong checked.pilot
  | recipe failure => exact failure.refutes _ _ _ _ _ checked.recurring

/-- There is no cap on the length, order or rational quantities of a
submitted certificate. Every word that meets the original checks lands. -/
theorem verifyPrepared_accepts_every_admissible_word
    (checked : PreparedChecks loss answers body offers tail choice code) :
    ∃ proof, verifyPrepared loss answers body replies offers addresses covered tail choice code = .ok proof := by
  cases verifyPrepared loss answers body replies offers addresses covered tail choice code with
  | error issue => exact (issue.refutes loss answers body offers tail choice code checked).elim
  | ok certified => exact ⟨certified, rfl⟩

omit [DecidableEq (Request Party Good Port Technology Instrument)] in
theorem CheckedCertificate.the_word_has_the_original_whole_write
    (verified : CheckedCertificate loss answers body replies offers tail) :
    Occurrence.Unbounded.ActualWrite answers loss Candidate ∧
    verified.opening.entry.current.ledger.stack.balances.map Prod.fst =
      (Occurrence.originState loss).stack.balances.map Prod.fst := by
  have eligible : Occurrence.Eligible answers loss Candidate :=
    verified.usesOriginalWord ▸ verified.opening.entry.eligible
  exact ⟨Occurrence.Unbounded.an_eligible_word_has_its_actual_whole_write answers loss _ eligible,
    verified.opening.entry.every_old_address_is_retained⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational
