import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Scheduled.Due

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.Scheduled

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material (inspectList)
open Reparation (Key)
open Reparation.Actual (Script)
open FixedPoint (Recipe InReserve RevisionAnswers reviseProgramme)
open FixedPoint.OpenPeace.Operational (RecipeMenu RepeatCode RejectedRecipes RecipeConditions chooseRecipe)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}
  {quantum : ℚ}

abbrev MenuAt (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] :=
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) →
    (raw : RawCurrent Party Good Technology Instrument) → RecipeMenu input raw

variable (before : State loss front quantum)

structure Motion where
  event : Option (Event before.current)
  next : State loss front quantum
  actual : next.current = (event.map Event.next).getD before.current
  clock : before.current.physical.raw.clock ≤ next.current.physical.raw.clock

def hold : Motion before := ⟨none, before, rfl, le_rfl⟩

def deny {Issue : Type} (reason : Issue) : Motion before :=
  let refused := refuse before.current reason
  ⟨some (.refused refused), afterRefusal before refused, rfl, le_rfl⟩

variable (answers : DeliveryAnswers Party Good Port Technology Instrument)
  (key : Key Party Good) (quantity : ℚ)

local notation "Delivered" => deliveredRaw before.current.physical.raw key quantity

structure StockGap where
  person : Party
  good : Good
  short : (Delivered).stock person good < before.base.stock person good

private structure PaymentBacking where
  base : RawCurrent Party Good Technology Instrument
  recipe : Recipe before.current.programme (originalRaw loss) (people loss front) base quantum
  reserve : InReserve base Delivered

variable [DecidableEq (Request Party Good Port Technology Instrument)]
  (catalogue : MenuAt Party Good Port Technology Instrument)
  (addresses : List (Party × Good)) (covered : ∀ address, address ∈ addresses)

inductive PaymentContinuationIssue
  | slow (gap : StockGap before key quantity)
      (short : before.current.programme.law.duration Delivered < quantum)
  | noRecipe (gap : StockGap before key quantity)
      (failed : RejectedRecipes before.current.programme (originalRaw loss) Delivered (people loss front)
        (catalogue before.current.programme Delivered))

private def retainOrFind : Except (PaymentContinuationIssue before key quantity catalogue)
    (PaymentBacking before key quantity) :=
  let fits (cell : Party × Good) := before.base.stock cell.1 cell.2 ≤ (Delivered).stock cell.1 cell.2
  match inspectList fits addresses with
  | .clear all =>
    .ok ⟨before.base, before.recipe, ⟨fun p g => all (p, g) (covered _), before.reserve.claims, before.reserve.technology⟩⟩
  | .failure cell _ missing =>
    let gap : StockGap before key quantity := ⟨cell.1, cell.2, lt_of_not_ge missing⟩
    if bound : quantum ≤ before.current.programme.law.duration Delivered then
      match chooseRecipe before.current.programme (originalRaw loss) Delivered (people loss front)
          (catalogue before.current.programme Delivered) with
      | .inl rejected => .error (.noRecipe gap rejected)
      | .inr selected => .ok ⟨Delivered, selected.recipe.atMinimum before.recipe.law.positive bound,
          ⟨fun _ _ => le_rfl, rfl, rfl⟩⟩
    else .error (.slow gap (lt_of_not_ge bound))

private def postPayment (funded : Funding before.current answers key quantity)
    (backed : PaymentBacking before key quantity) : Motion before := by
  let actual := writeFunded before.current answers key quantity funded
  let next : State loss front quantum :=
    ⟨actual.next, backed.base, actual.sameProgramme.symm ▸ backed.recipe, actual.stock.symm ▸ backed.reserve⟩
  refine ⟨some (.paid actual), next, rfl, ?_⟩
  change before.current.physical.raw.clock ≤ actual.next.physical.raw.clock
  rw [actual.stock]
  exact le_rfl

/-- A debt transfer is emitted only after both its original signatures
and its actual post-transfer continuation pass. -/
def tryPayment : Motion before :=
  match checkFunding before.current answers key quantity addresses covered with
  | .error issue => deny before issue
  | .ok funded =>
    match retainOrFind before key quantity catalogue addresses covered with
    | .error issue => deny before issue
    | .ok backed => postPayment before answers key quantity funded.down backed

theorem refused_funding_keeps_the_paid_due_state (notFunded : ¬ Funding before.current answers key quantity) :
    (tryPayment before answers key quantity catalogue addresses covered).next.current.physical = before.current.physical ∧
    (tryPayment before answers key quantity catalogue addresses covered).next.current.ledger.stack.balances =
      before.current.ledger.stack.balances := by
  unfold tryPayment
  cases checkFunding before.current answers key quantity addresses covered with
  | error => exact ⟨rfl, rfl⟩
  | ok funded => exact (notFunded funded.down).elim

theorem tryPayment_writes_when_funded_and_continued
    (funded : Funding before.current answers key quantity)
    (continued : InReserve before.base Delivered ∨
      (quantum ≤ before.current.programme.law.duration Delivered ∧
        ∃ i : Fin (catalogue before.current.programme Delivered).length,
          RecipeConditions before.current.programme (originalRaw loss) Delivered (people loss front)
            (catalogue before.current.programme Delivered)[i])) :
    ∃ actual : PaidWrite before.current answers key quantity,
      (tryPayment before answers key quantity catalogue addresses covered).event = some (.paid actual) ∧
      (tryPayment before answers key quantity catalogue addresses covered).next.current = actual.next := by
  unfold tryPayment
  cases checkFunding before.current answers key quantity addresses covered with
  | error issue => exact (issue.refutes _ _ _ _ funded).elim
  | ok paid =>
    cases retainOrFind before key quantity catalogue addresses covered with
    | ok backed => exact ⟨writeFunded _ _ _ _ paid.down, rfl, rfl⟩
    | error issue =>
      rcases continued with kept | ⟨clock, i, viable⟩
      · cases issue with
        | slow gap _ | noRecipe gap _ => exact (gap.short.not_ge (kept.stock gap.person gap.good)).elim
      · cases issue with
        | slow _ tooFast => exact (tooFast.not_ge clock).elim
        | noRecipe _ failed => exact ((failed i).refutes _ _ _ _ _ viable).elim

variable (approvals : RevisionAnswers Party Good Port Technology Instrument)
  (offer : ProductionOffer Party Good Port Technology Instrument)
  (code : RepeatCode (reviseProgramme before.current.programme offer) before.current.physical.raw)

def tryProduction : Motion before :=
  match inspectTrial before.current approvals offer code with
  | .error issue => deny before issue
  | .ok approved =>
    if bound : quantum ≤ (reviseProgramme before.current.programme offer).law.duration before.current.physical.raw then
      let recipe := approved.recipe.atMinimum before.recipe.law.positive bound
      let self : InReserve before.current.physical.raw before.current.physical.raw := ⟨fun _ _ => le_rfl, rfl, rfl⟩
      let move := recipe.moveAt _ self
      let period := writePeriod before.current _ (FixedPoint.reviseProgramme_keeps_public_terms _ _) move
      let actual : TrialWrite before.current approvals offer :=
        ⟨period, approved.approved, (recipe.moveAt_word _ self).trans approved.pilot⟩
      let next : State loss front quantum := ⟨period.next, before.current.physical.raw,
        period.programmeNext.symm ▸ recipe, period.exactStock.symm ▸ recipe.next_reserved _ self⟩
      ⟨some (.revised actual), next, rfl,
        (le_add_of_nonneg_right recipe.law.positive.le).trans (period.exactStock.symm ▸ recipe.next_clock _ self)⟩
    else deny before (PLift.up (lt_of_not_ge bound))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.Scheduled
