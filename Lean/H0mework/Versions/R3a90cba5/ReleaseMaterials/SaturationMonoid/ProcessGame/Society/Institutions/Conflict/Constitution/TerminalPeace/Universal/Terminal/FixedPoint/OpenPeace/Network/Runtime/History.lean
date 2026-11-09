import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Advance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Transport (sourceSupport)
open NoFreeProbe
open private actual_stack_kept from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.History

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

local notation "St" => State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)
local notation "Request" => Input Party Good Port Technology Instrument
local notation "Alphabet" => Language (RawEvent Party Good Port Technology Instrument)
  (Effect Party Good Port Technology Instrument)

variable (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)

def transition (state : St) (command : ℚ → Terms Party Good Port Technology Instrument → Alphabet → Request) :
    St × AdaptivePeace.Observation :=
  let input := command state.current.physical.raw.clock (Prepayment.registeredTerms state.current) state.base.language
  ((advance home replies state input).next, (source home replies state input).observe)

variable (initial : State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
  (policy : Policy Party Good Port Technology Instrument)

/-- Policies may choose every proposal and due-slot interleaving from
the full public transcript and the currently generated language. -/
def history : Nat → St × List AdaptivePeace.Observation :=
  Erasure.run (transition home replies) initial policy

local notation "Reached" => history home replies initial policy
local notation "At" n => Prod.fst (Reached n)

def inputAt (n : Nat) : Request :=
  let past := Reached n
  policy n past.2 past.1.current.physical.raw.clock (Prepayment.registeredTerms past.1.current) past.1.base.language

local notation "InputAt" n => inputAt home replies initial policy n
local notation "Visit" n => source home replies (At n) (InputAt n)
local notation "Effects" n => scope home replies (At n) (InputAt n)

theorem history_succ (n : Nat) :
    (At (n + 1)) = (advance home replies (At n) (InputAt n)).next := rfl

theorem history_keeps_the_stack (n : Nat) :
    HEq (At n).current.ledger.stack initial.current.ledger.stack := by
  induction n with
  | zero => rfl
  | succ n earlier =>
    rw [history_succ]
    let current := At n
    let request := InputAt n
    exact (same_stack home replies current request).trans
      ((actual_stack_kept current.lanes.tariff.read home
        (request.orders current.lanes.payment.read current.lanes.openPayment.read)
        (request.replies replies) current.base.adaptive request.due).trans earlier)

theorem history_keeps_rows (n : Nat) :
    (At n).current.ledger.stack.balances = initial.current.ledger.stack.balances := by
  induction n with
  | zero => rfl
  | succ n earlier =>
    rw [history_succ, same_rows]
    let step := Visit n
    have exactRows : step.next.native.ledger.stack.balances = step.source.next.ledger.stack.balances := by
      cases step <;> rfl
    exact exactRows.trans (step.source.rows.trans earlier)

theorem history_reads_the_original_rows (n : Nat)
    (balance : Reparation.Actual.Occurrence seed community × Reparation.Actual.Balance)
    (original : balance ∈ initial.current.ledger.stack.balances) :
    let ledger := (At n).current.ledger
    ∃ row, ledger.stack.read (sourceSupport cut.native) row = .inr balance ∧
      ∃ live : OpenResponsibilityAt ledger.world ledger.resident.support,
        live = ledger.originalRow row ∧ live.progressBudget = row.progressBudget := by
  exact (At n).current.ledger.every_balance_has_a_live_row balance
    ((history_keeps_rows home replies initial policy n).symm ▸ original)

theorem history_keeps_original_signatures (n : Nat) :
    (At n).lanes.tariff.read = initial.lanes.tariff.read ∧
    (At n).lanes.payment.read = initial.lanes.payment.read ∧
    (At n).lanes.openPayment.read = initial.lanes.openPayment.read := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n earlier =>
    rw [history_succ]
    have exactReads := next_keeps_original_signatures home replies (At n) (InputAt n)
    exact ⟨exactReads.1.trans earlier.1, exactReads.2.1.trans earlier.2.1, exactReads.2.2.trans earlier.2.2⟩

theorem history_keeps_public_terms (n : Nat) :
    KeepsPublicTerms initial.current.programme (At n).current.programme := by
  induction n with
  | zero => exact .refl _
  | succ n earlier =>
    rw [history_succ, same_programme]
    exact earlier.trans (Visit n).keeps_public_terms

theorem history_clock_bound (start elapsed : Nat) :
    (At start).current.physical.raw.clock + (elapsed : ℚ) * quantum ≤
      (At (start + elapsed)).current.physical.raw.clock := by
  induction elapsed with
  | zero => simp
  | succ elapsed earlier =>
    let index := start + elapsed
    have tick := (Visit index).source.clock
    rw [← (Visit index).same_physical_successor, ← same_physical, ← history_succ] at tick
    rw [Nat.cast_succ, ← Nat.add_assoc]
    linarith only [tick, earlier]

theorem history_clock_is_cofinal (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (At n).current.physical.raw.clock := by
  have positive := initial.current.recipe.law.positive
  obtain ⟨elapsed, beyond⟩ := exists_nat_gt ((bound - (At start).current.physical.raw.clock) / quantum)
  have crossed := (div_lt_iff₀ positive).mp beyond
  have lower := history_clock_bound home replies initial policy start elapsed
  exact ⟨start + elapsed, Nat.le_add_right _ _, by linarith only [crossed, lower]⟩

def LivingVisitAt (n : Nat) : Prop :=
  let before := (At n).current.physical
  let after := (At (n + 1)).current.physical
  let read := (Visit n).source.round.visit.read
  read.effect.isAccepted = true ∧ read.effect.next = after ∧
    OriginalNeedFloor read.programme origin before.raw people read.commands ∧
    OriginalNeedFloor read.programme before.raw before.raw people read.commands ∧
    (∀ person ∈ people, ∃ word, Supply.Registered read.programme before.raw word ∧
      Supply.Period read.programme origin before.raw [person] word) ∧
    (∀ item ∈ read.effect.execution.items, ∀ key, Reparation.loss read.programme.law community item key = 0) ∧
    (∃ person good, before.raw.stock person good < after.raw.stock person good)

theorem history_is_living_and_peaceful (n : Nat) :
    LivingVisitAt home replies initial policy n := by
  unfold LivingVisitAt
  let actual := Visit n
  let round := actual.source.round
  have physical : round.next.physical = (At (n + 1)).current.physical := by
    rw [history_succ, same_physical]
    exact actual.source.physical.trans actual.same_physical_successor.symm
  refine ⟨round.realWrite, round.physicalNext.trans physical, round.needs.1, round.needs.2,
    round.exit, round.noDamage, ?_⟩
  rw [← physical]
  exact round.growth

theorem next_material_write_uses_the_whole_live_ledger (n : Nat) :
    let current := (At n).current
    let round := (Visit n).source.round
    let written := Installation.Live.action current.ledger round.visit.read true
    (⟨current.ledger.world, written.target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = round.next.ledger.resident.erase ∧
    let original := (Reparation.Actual.identityWhole current.ledger.resident.support).val
    HEq written.target.firstSuccessor.ledgerEvolution.destination original.destination ∧
      HEq written.target.firstSuccessor.ledgerEvolution.origin original.origin :=
  ⟨(Visit n).source.round.wholeNext, Installation.Live.original_rows_are_the_whole_first_write _ _ _⟩

theorem history_enters_the_exact_revised_world (n : Nat)
    (novel : ¬ (Effects n) ⊆ (At n).base.language.covered) :
    let generated := (revision home replies (At n) (InputAt n) novel).generate
    (⟨generated.NewN, generated.newLivingRoot.generatedNextCurrentAt
      (.finite generated.newRoot.toRoot.initialVisit)⟩ : AnyAuthoritativeRootCurrent) =
      (At (n + 1)).current.ledger.resident.erase := by
  have arrived := congrArg (fun state : St => state.current.ledger.resident.erase)
    (history_succ home replies initial policy n)
  exact (next_reads_generated_first_write home replies (At n) (InputAt n) novel).trans arrived.symm

/-- The physical round after a revision consumes its actual first-write
resident and compiles the whole ledger there. -/
theorem the_revised_resident_drives_the_next_material_write (n : Nat)
    (novel : ¬ (Effects n) ⊆ (At n).base.language.covered) :
    let round := (Visit (n + 1)).source.round
    let wholeFrom (ledger : Installation.Live.Ledger seed community cut) : Prop :=
      let written := Installation.Live.action ledger round.visit.read true
      (⟨ledger.world, written.target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = round.next.ledger.resident.erase ∧
      let original := (Reparation.Actual.identityWhole ledger.resident.support).val
      HEq written.target.firstSuccessor.ledgerEvolution.destination original.destination ∧
        HEq written.target.firstSuccessor.ledgerEvolution.origin original.origin
    wholeFrom (languageWrite home replies (At n) (InputAt n) novel).state := by
  intro round wholeFrom
  have landed := (congrArg (fun state : St => state.current.ledger)
    (history_succ home replies initial policy n)).trans
    (next_ledger home replies (At n) (InputAt n) novel)
  exact Eq.ndrec (motive := wholeFrom)
    (next_material_write_uses_the_whole_live_ledger home replies initial policy (n + 1)) landed

theorem history_covers_exactly_the_observed_effects (n : Nat)
    (effect : Effect Party Good Port Technology Instrument) :
    effect ∈ (At n).base.language.covered ↔
      effect ∈ initial.base.language.covered ∨ ∃ i < n, effect ∈ Effects i := by
  induction n with
  | zero => simp [history, Erasure.run]
  | succ n earlier =>
    rw [history_succ, coverage_eq, Set.mem_union, earlier]
    constructor
    · rintro ((already | ⟨i, before, found⟩) | now)
      · exact .inl already
      · exact .inr ⟨i, Nat.lt_succ_of_lt before, found⟩
      · exact .inr ⟨n, Nat.lt_succ_self n, now⟩
    · rintro (already | ⟨i, before, found⟩)
      · exact .inl (.inl already)
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with prior | now
        · exact .inl (.inr ⟨i, prior, found⟩)
        · subst i
          exact .inr found

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
