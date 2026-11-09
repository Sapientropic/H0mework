import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Run
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Protected

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt primitiveScript)
open Reparation (Key)
open Reparation.Actual (ReceiptAnswers Occurrence Script StateAt)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Occurrence seed community) (answers : ReceiptAnswers seed)

local notation "Word" => Script Party Good Port Technology Instrument
local notation "Address" => Key Party Good
abbrev liveDue (word : Word) (key : Address) := dueFor key (prefixRows loss answers word)

def deliveryPort (word : Word) (key : Address) : Port :=
  seed.native.input.law.stockPort (prefixRaw loss word).technology key.2.1 key.2.2

abbrev afterDebit (word : Word) (key : Address) : Word :=
  word ++ installment (deliveryPort loss word key) key (maximumInstallment loss answers word key)

abbrev generatedPaid (word : Word) (key : Address) :=
  PaidInstallment loss answers (reserveAt loss word) word (deliveryPort loss word key) key
    (maximumInstallment loss answers word key)

abbrev generatedIssue (word : Word) (key : Address) :=
  ProtectedIssue loss answers word key (deliveryPort loss word key)
    (maximumInstallment loss answers word key)

structure Endpoint (front : Word) where
  word : Word
  prefixWord : front.IsPrefix word
  safe : Occurrence.Eligible answers loss word
  keepsNeeds : ProtectsNeeds loss word
  ready : ReadyEntry loss word
  dueNotIncreased : ∀ key, liveDue loss answers word key ≤ liveDue loss answers front key

private def Endpoint.at (front : Word) (safe : Occurrence.Eligible answers loss front)
    (keepsNeeds : ProtectsNeeds loss front)
    (ready : ReadyEntry loss front) : Endpoint loss answers front :=
  ⟨front, List.prefix_rfl, safe, keepsNeeds, ready, fun _ => le_rfl⟩

private def Endpoint.after (front : Word) (key : Address) (paid : generatedPaid loss answers front key)
    (keepsNeeds : ProtectsNeeds loss (afterDebit loss answers front key)) :
    Endpoint loss answers front where
  word := afterDebit loss answers front key
  prefixWord := List.prefix_append _ _
  safe := paid.eligible
  keepsNeeds := keepsNeeds
  ready := paid.ready
  dueNotIncreased other := by
    rw [liveDue, paid.debts]
    apply sub_le_self
    split
    · exact maximumInstallment_nonnegative _ _ _ _
    · exact le_rfl

private def Endpoint.trans {before : Word} (left : Endpoint loss answers before)
    (right : Endpoint loss answers left.word) : Endpoint loss answers before where
  word := right.word
  prefixWord := left.prefixWord.trans right.prefixWord
  safe := right.safe
  keepsNeeds := right.keepsNeeds
  ready := right.ready
  dueNotIncreased key := (right.dueNotIncreased key).trans (left.dueNotIncreased key)

inductive Block : Word → Address → Type _
  | refused (word : Word) (key : Address) (owing : 0 < liveDue loss answers word key)
      (issue : generatedIssue loss answers word key) : Block word key
  | partlyPaid {word : Word} (key : Address) (paid : generatedPaid loss answers word key)
      (remaining : 0 < liveDue loss answers (afterDebit loss answers word key) key) :
      Block (afterDebit loss answers word key) key

def Block.next {word : Word} {key : Address} (block : Block loss answers word key) :
    StateAt seed community (endAt seed (Occurrence.history loss ++ word)) :=
  match block with
  | .refused word key _ issue =>
    (writeProtectedRefusal loss answers word key (deliveryPort loss word key)
      (maximumInstallment loss answers word key) issue).state
  | .partlyPaid (word := before) key _ _ =>
    Occurrence.reached answers loss (afterDebit loss answers before key)

theorem Block.keeps_the_actual_rows {word : Word} {key : Address} (block : Block loss answers word key) :
    (block.next loss answers).stack.balances = prefixRows loss answers word := by
  cases block <;> rfl

inductive PortfolioResult (front : Word) (pending : List Address)
  | complete (landed : Endpoint loss answers front)
      (closed : ∀ key ∈ pending, liveDue loss answers landed.word key = 0)
  | stopped (landed : Endpoint loss answers front)
      (key : Address) (original : key ∈ pending) (failure : Block loss answers landed.word key)

def PortfolioResult.endpoint {front : Word} {pending : List Address}
    (result : PortfolioResult loss answers front pending) : Endpoint loss answers front :=
  match result with
  | .complete landed _ | .stopped landed _ _ _ => landed

def PortfolioResult.next {front : Word} {pending : List Address}
    (result : PortfolioResult loss answers front pending) :
    StateAt seed community (endAt seed (Occurrence.history loss ++ (result.endpoint loss answers).word)) :=
  match result with
  | .complete landed _ => Occurrence.reached answers loss landed.word
  | .stopped _ _ _ failure => failure.next loss answers

theorem PortfolioResult.next_reads_the_exact_original_balances {front : Word} {pending : List Address}
    (result : PortfolioResult loss answers front pending) :
    (result.next loss answers).stack.balances = prefixRows loss answers (result.endpoint loss answers).word := by
  cases result with
  | complete => rfl
  | stopped _ _ _ failure => exact failure.keeps_the_actual_rows loss answers

theorem PortfolioResult.has_original_whole_write {front : Word} {pending : List Address}
    (result : PortfolioResult loss answers front pending) :
    Occurrence.Unbounded.ActualWrite answers loss (result.endpoint loss answers).word :=
  Occurrence.Unbounded.an_eligible_word_has_its_actual_whole_write answers loss _
    (result.endpoint loss answers).safe

private def prependCleared {front : Word} {key : Address} {rest : List Address}
    (earlier : Endpoint loss answers front) (zero : liveDue loss answers earlier.word key = 0)
    (later : PortfolioResult loss answers earlier.word rest) :
    PortfolioResult loss answers front (key :: rest) :=
  match later with
  | .complete landed closed =>
    .complete (earlier.trans loss answers landed) fun other listed =>
      (List.mem_cons.mp listed).elim
        (fun same => same.symm ▸ le_antisymm ((landed.dueNotIncreased key).trans_eq zero) (dueFor_nonnegative _ _))
        (closed other)
  | .stopped landed other listed failure =>
    .stopped (earlier.trans loss answers landed) other (List.mem_cons_of_mem _ listed) failure

set_option maxHeartbeats 1200000 in
/-- The scan reads the current rows and the current protective material
floor before each posted transfer. A partial write returns the residual
at its actual successor, and no signed position is reused. -/
def scanOriginalKeys : (pending : List Address) → (front : Word) →
    (safe : Occurrence.Eligible answers loss front) → (keepsNeeds : ProtectsNeeds loss front) →
    (ready : ReadyEntry loss front) →
    PortfolioResult loss answers front pending
  | [], front, safe, keepsNeeds, ready => .complete (Endpoint.at loss answers front safe keepsNeeds ready) (by simp)
  | key :: rest, front, safe, keepsNeeds, ready =>
    if zero : liveDue loss answers front key = 0 then
      prependCleared loss answers (Endpoint.at loss answers front safe keepsNeeds ready)
        zero (scanOriginalKeys rest front safe keepsNeeds ready)
    else
      let owing := lt_of_le_of_ne (dueFor_nonnegative key (prefixRows loss answers front)) (Ne.symm zero)
      match compileProtectedPayment loss answers front key (deliveryPort loss front key) safe ready with
      | .refused issue _ _ =>
        .stopped (Endpoint.at loss answers front safe keepsNeeds ready) key List.mem_cons_self (.refused _ _ owing issue)
      | .written paid kept =>
        let middle := Endpoint.after loss answers front key paid kept
        if remains : liveDue loss answers middle.word key = 0 then
          prependCleared loss answers middle remains
            (scanOriginalKeys rest middle.word middle.safe middle.keepsNeeds middle.ready)
        else
          .stopped middle key List.mem_cons_self
            (.partlyPaid key paid (lt_of_le_of_ne (dueFor_nonnegative _ _) (Ne.symm remains)))
termination_by structural pending => pending

def clearOriginalPortfolio (front : Word) (safe : Occurrence.Eligible answers loss front)
    (keepsNeeds : ProtectsNeeds loss front) (ready : ReadyEntry loss front) :
    PortfolioResult loss answers front (originalKeys loss) :=
  scanOriginalKeys loss answers (originalKeys loss) front safe keepsNeeds ready

theorem a_completed_portfolio_clears_every_original_row {front : Word}
    (landed : Endpoint loss answers front)
    (closed : ∀ key ∈ originalKeys loss, liveDue loss answers landed.word key = 0) :
    WholeCleared loss answers landed.word := by
  intro row listed
  have keyListed : row.1.key ∈ originalKeys loss :=
    (eligible_prefix_has_the_original_keys loss answers landed.word landed.safe) ▸
      List.mem_dedup.mpr (List.mem_map_of_mem listed)
  exact every_original_row_is_cleared_when_its_key_has_zero_due _ _ (closed _ keyListed) _ listed rfl

theorem every_portfolio_endpoint_keeps_the_literal_original_addresses {front : Word}
    (landed : Endpoint loss answers front) :
    (prefixRows loss answers landed.word).map Prod.fst = (Occurrence.originState loss).stack.balances.map Prod.fst := by
  rw [Occurrence.reached_origins, Occurrence.originState_origins]
  exact Occurrence.eligible_preserves_the_literal_original_loss_inventory community answers _ _ _ landed.safe

abbrev ProductionObstruction (front : Word) (body : RawEvent Party Good Port Technology Instrument) :=
  (ProductionDecision answers loss front body × PLift (¬ ProductionWrite answers loss front body)) ⊕
    NeedShortage loss (front ++ primitiveScript body)

def writeProductionNeedShortage {front : Word} {body : RawEvent Party Good Port Technology Instrument}
    (issue : NeedShortage loss (front ++ primitiveScript body)) :=
  Installation.Core.publish (Occurrence.reached answers loss front) issue true

theorem the_production_need_shortage_retains_the_whole_original_ledger
    {front : Word} {body : RawEvent Party Good Port Technology Instrument}
    (issue : NeedShortage loss (front ++ primitiveScript body)) :
    let before := Occurrence.reached answers loss front
    let next := writeProductionNeedShortage loss answers (front := front) (body := body) issue
    next.state.stack = before.stack ∧
      (⟨before.world, (Installation.Core.action before issue true).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = next.state.resident.erase :=
  ⟨rfl, Installation.Core.the_canonical_write_is_the_published_whole_state _ _ _⟩

structure StartedPortfolio (front : Word) (body : RawEvent Party Good Port Technology Instrument) where
  production : ProductionWrite answers loss front body
  clearance : PortfolioResult loss answers (front ++ primitiveScript body) (originalKeys loss)

/-- Prepare the recipe and verify its actual stock trajectory before using
its credit. Each payment repeats this check at its own current. -/
def clearAfterProduction (front : Word) (body : RawEvent Party Good Port Technology Instrument)
    (earlier : Occurrence.Eligible answers loss front) (nonempty : body ≠ []) :
    ProductionObstruction loss answers front body ⊕ StartedPortfolio loss answers front body :=
  match inspectProduction answers loss front body with
  | .written actual =>
    match inspectNeeds loss (front ++ primitiveScript body) with
    | .inl short => .inl (.inr short)
    | .inr keepsNeeds =>
      .inr ⟨actual, clearOriginalPortfolio loss answers _ (actual.eligibility earlier) keepsNeeds.down (actual.ready nonempty)⟩
  | .authority item listed refused =>
    .inl (.inl ⟨.authority item listed refused, ⟨fun actual => refused (actual.authorized item listed)⟩⟩)
  | .native failure refutes => .inl (.inl ⟨.native failure refutes, ⟨fun actual => refutes actual.trace⟩⟩)
  | .rejected issue =>
    .inl (.inl ⟨.rejected issue, ⟨fun actual =>
      (issue.refutes answers (Occurrence.history loss)) actual.eligible⟩⟩)

theorem a_material_shortage_is_rejected_before_the_recipe_write
    (front : Word) (body : RawEvent Party Good Port Technology Instrument)
    (earlier : Occurrence.Eligible answers loss front) (nonempty : body ≠ [])
    (actual : ProductionWrite answers loss front body)
    (admitted : inspectProduction answers loss front body = .written actual)
    (shortage : NeedShortage loss (front ++ primitiveScript body))
    (found : inspectNeeds loss (front ++ primitiveScript body) = .inl shortage) :
    clearAfterProduction loss answers front body earlier nonempty = .inl (.inr shortage) := by
  simp only [clearAfterProduction, admitted, found]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve
