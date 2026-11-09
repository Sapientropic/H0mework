import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase.Synthesis

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.RebaseHistory

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open FixedPoint.OpenPeace.Operational (RecipeMenu)
open NoFreeProbe
open private dueInput from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase
open private publishOn publishedRead from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.ReadHistory
open private actual_stack_kept from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.History

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Native" => TerminalPeace.Universal.Runtime.Native Party Good Port Technology Instrument

/-- A scheduler's current with the reserve index supplied by its last
real production or accepted replacement. The state owns the same ledger. -/
abbrev Resident (seed cut : Conflict.Root.Cut Party Good Port Technology Instrument) (community : Party → Community)
    (origin : RawCurrent Party Good Technology Instrument) (people : List Party) (quantum : ℚ) :=
  Σ reserveBase : Raw, Runtime.State (seed := seed) (cut := cut) (community := community)
    origin people quantum (reserveBase := reserveBase)

local notation "St" => Resident seed cut community origin people quantum

abbrev Catalogue (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] :=
  (input : Capitalism.Universal.Root.ProgrammeSource.Input Party Good Port Technology Instrument) →
    (raw : RawCurrent Party Good Technology Instrument) → RecipeMenu input raw

inductive Command (Party Good Port Technology Instrument : Type)
  | scheduled (input : OpenPeace.Input Party Good Port Technology Instrument)
  | refresh

structure PaidEffect (community : Party → Community) (origin : Raw) (people : List Party)
    (before after : Native) where
  read : FixedPoint.Readout Party Good Port Technology Instrument
  beforeExact : read.before = before
  accepted : read.effect.isAccepted = true
  afterExact : read.effect.next = after
  originalNeeds : OriginalNeedFloor read.programme origin before.raw people read.commands
  currentNeeds : OriginalNeedFloor read.programme before.raw before.raw people read.commands
  independentExit : ∀ person ∈ people, ∃ word, Supply.Registered read.programme before.raw word ∧
    Supply.Period read.programme origin before.raw [person] word
  noDamage : ∀ item ∈ read.effect.execution.items, ∀ key, Reparation.loss read.programme.law community item key = 0
  growth : ∃ person good, before.raw.stock person good < after.raw.stock person good

private def paidEffect {reserveBase : Raw}
    {source : FixedPoint.Current (seed := seed) (cut := cut) (community := community)
      origin people quantum (reserveBase := reserveBase)}
    (actual : FixedPoint.Round source) {after : Native}
    (physical : actual.next.physical = after) : PaidEffect community origin people source.physical after := by
  subst after
  exact ⟨actual.visit.read, actual.before, actual.realWrite, actual.physicalNext, actual.needs.1, actual.needs.2,
    actual.exit, actual.noDamage, actual.growth⟩

structure Step (before : St) where
  next : St
  paid : PaidEffect community origin people before.2.current.physical next.2.current.physical
  clock : before.2.current.physical.raw.clock + quantum ≤ next.2.current.physical.raw.clock
  rows : next.2.current.ledger.stack.balances = before.2.current.ledger.stack.balances
  reads : ReadPath before.2.current.ledger.resident next.2.current.ledger.resident
  tariff : next.2.lanes.tariff.read = before.2.lanes.tariff.read
  payment : next.2.lanes.payment.read = before.2.lanes.payment.read
  openPayment : next.2.lanes.openPayment.read = before.2.lanes.openPayment.read
  terms : FixedPoint.KeepsPublicTerms before.2.current.programme next.2.current.programme
  wholeStack : HEq next.2.current.ledger.stack before.2.current.ledger.stack
  coverage : before.2.base.language.covered ⊆ next.2.base.language.covered
  reserveStocks : ∀ person good, before.1.stock person good ≤ next.1.stock person good
  reserveClaims : next.1.claims = before.1.claims
  reserveTechnology : next.1.technology = before.1.technology

variable (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)
  (before : Resident seed cut community origin people quantum)

set_option maxHeartbeats 800000 in
private def scheduled (input : OpenPeace.Input Party Good Port Technology Instrument) : Step before := by
  let actual := Runtime.source home replies before.2 input
  let landed := (Runtime.advance home replies before.2 input).next
  have physical : actual.source.round.next.physical = landed.current.physical :=
    actual.source.physical.trans (actual.same_physical_successor.symm.trans (Runtime.same_physical home replies before.2 input).symm)
  have rows : actual.next.native.ledger.stack.balances = actual.source.next.ledger.stack.balances := by
    generalize actual = value
    cases value <;> rfl
  have signed := Runtime.next_keeps_original_signatures home replies before.2 input
  refine ⟨⟨before.1, landed⟩, paidEffect actual.source.round physical, ?_,
    (Runtime.same_rows home replies before.2 input).trans (rows.trans actual.source.rows),
    Runtime.stepReads home replies before.2 input, signed.1, signed.2.1, signed.2.2,
    ?_, ?_, ?_, fun _ _ => le_rfl, rfl, rfl⟩
  · change _ ≤ landed.current.physical.raw.clock
    rw [← physical]
    exact actual.source.round.clock
  · rw [Runtime.same_programme]
    exact actual.keeps_public_terms
  · exact (Runtime.same_stack home replies before.2 input).trans
      (actual_stack_kept before.2.lanes.tariff.read home
        (input.orders before.2.lanes.payment.read before.2.lanes.openPayment.read)
        (input.replies replies) before.2.base.adaptive input.due)
  · rw [Runtime.coverage_eq]
    exact Set.subset_union_left

variable [DecidableEq (Request Party Good Port Technology Instrument)]

private def applyReplacement (menu : RecipeMenu before.2.current.programme before.2.current.physical.raw)
    (result : RetainedDue before.2 menu home replies ⊕ Rebased before.2 menu) : Step before := by
  cases result with
  | inl denied =>
    let due : OpenPeace.Input Party Good Port Technology Instrument := dueInput
    let written := scheduled home replies before due
    have physical : written.next.2.current.physical = denied.next.current.physical := denied.samePhysical.symm
    have rows : denied.next.current.ledger.stack.balances = written.next.2.current.ledger.stack.balances := denied.rows
    have programme : denied.next.current.programme = written.next.2.current.programme := denied.programme
    have language : denied.next.base.language = written.next.2.base.language := denied.language
    refine ⟨⟨before.1, denied.next⟩, physical ▸ written.paid, ?_, rows.trans written.rows, denied.reads,
      denied.tariff, denied.payment, denied.openPayment, ?_, denied.sameStack.trans written.wholeStack,
      ?_, fun _ _ => le_rfl, rfl, rfl⟩
    · change _ ≤ denied.next.current.physical.raw.clock
      rw [← physical]
      exact written.clock
    · change FixedPoint.KeepsPublicTerms _ denied.next.current.programme
      rw [programme]
      exact written.terms
    · change _ ⊆ denied.next.base.language.covered
      rw [language]
      exact written.coverage
  | inr selected =>
    have physical : selected.actual.next.physical = selected.next.current.physical :=
      congrArg FixedPoint.Current.physical selected.actualNext.symm
    refine ⟨⟨before.2.current.physical.raw, selected.next⟩, paidEffect selected.actual physical,
      ?_, ?_, selected.reads, ?_, ?_, ?_, ?_, ?_, ?_,
      before.2.current.reserved.stock, before.2.current.reserved.claims, before.2.current.reserved.technology⟩
    · change _ ≤ selected.next.current.physical.raw.clock
      rw [← physical]
      exact selected.actual.clock
    · rw [selected.actualNext]
      exact selected.actual.rows
    · rw [selected.keepsLanes]
      exact selected.reads.keeps before.2.lanes.tariff
    · rw [selected.keepsLanes]
      exact selected.reads.keeps before.2.lanes.payment
    · rw [selected.keepsLanes]
      exact selected.reads.keeps before.2.lanes.openPayment
    · rw [selected.programme]
      exact .refl _
    · rw [selected.actualNext, selected.actual.ledgerNext]
      exact HEq.rfl
    · change _ ⊆ selected.next.base.language.covered
      rw [selected.language]

private def saveAudit {Payload : Type} (first : Step before) (evidence : Payload) : Step before := by
  let reads := ReadPath.write first.next.2.current.ledger.ready evidence true
  exact { first with
    next := ⟨first.next.1, publishOn first.next.2 evidence⟩
    reads := first.reads.trans reads
    tariff := (reads.keeps first.next.2.lanes.tariff).trans first.tariff
    payment := (reads.keeps first.next.2.lanes.payment).trans first.payment
    openPayment := (reads.keeps first.next.2.lanes.openPayment).trans first.openPayment }

private def enact (menu : RecipeMenu before.2.current.programme before.2.current.physical.raw) :
    Runtime.RefreshDecision before.2 menu home replies → Step before
  | .retained denied => applyReplacement home replies before menu (.inl denied)
  | .registered paid => applyReplacement home replies before menu (.inr paid)
  | .generated each paid =>
    saveAudit before (applyReplacement home replies before _ (.inr paid))
      (Runtime.RefreshEvidence.repaired each paid.chosen : Runtime.RefreshEvidence before.2 menu)
  | .joint each edits basis width earlier paid =>
    saveAudit before (applyReplacement home replies before _ (.inr paid.actual))
      (Runtime.RefreshEvidence.joint each edits basis width earlier paid.plan : Runtime.RefreshEvidence before.2 menu)

set_option maxHeartbeats 650000 in
private def savedRead (menu : RecipeMenu before.2.current.programme before.2.current.physical.raw)
    (choice : Runtime.RefreshDecision before.2 menu home replies) :
    Option (ReadOn (enact home replies before menu choice).next.2.current.ledger.resident
      (Runtime.RefreshEvidence before.2 menu)) :=
  match choice with
  | .retained _ | .registered _ => none
  | .generated each paid =>
    let evidence : Runtime.RefreshEvidence before.2 menu := .repaired each paid.chosen
    some (publishedRead paid.next evidence)
  | .joint each edits basis width earlier paid =>
    let evidence : Runtime.RefreshEvidence before.2 menu := .joint each edits basis width earlier paid.plan
    some (publishedRead paid.actual.next evidence)

variable (catalogue : Catalogue Party Good Port Technology Instrument)

private abbrev offered := catalogue before.2.current.programme before.2.current.physical.raw
local notation "Offered" => offered before catalogue

private abbrev selectedDecision := Runtime.chooseRefresh before.2 Offered home replies
local notation "Decision" => selectedDecision home replies before catalogue

private def refresh : Step before := enact home replies before Offered Decision

/-- Registered reserve changes and language revisions are interleaved
by one scheduler. Every branch consumes the actual reached resident. -/
def advance : Command Party Good Port Technology Instrument → Step before
  | .scheduled input => scheduled home replies before input
  | .refresh => refresh home replies before catalogue

/-- The audit read is carried by the actual successor of a successful
repair. It contains the original rejects and the selection used for the write. -/
def refreshAudit :
    Option (ReadOn (advance home replies before catalogue .refresh).next.2.current.ledger.resident
      (Runtime.RefreshEvidence before.2 Offered)) :=
  savedRead home replies before Offered Decision

theorem refresh_audit_is_the_selected_decision :
    (refreshAudit home replies before catalogue).map ReadAt.read = (Decision).evidence := by
  have exactAudit (choice : Runtime.RefreshDecision before.2 Offered home replies)
      : (savedRead home replies before Offered choice).map ReadAt.read = choice.evidence := by
    cases choice <;> rfl
  exact exactAudit Decision

theorem refresh_uses_the_generated_replacement
    {replacement : Rebased before.2 (catalogue before.2.current.programme before.2.current.physical.raw)}
    (selected : Runtime.chooseReplacement before.2 (catalogue before.2.current.programme before.2.current.physical.raw)
      home replies = .inr replacement) :
    (advance home replies before catalogue .refresh).next = ⟨before.2.current.physical.raw, replacement.next⟩ := by
  unfold advance refresh
  have chosen : Decision = .registered replacement :=
    Runtime.chooseRefresh_keeps_the_registered_priority _ _ _ _ selected
  rw [chosen]
  rfl

theorem refresh_uses_the_generated_repair
    {each : Operational.RejectedRecipes before.2.current.programme origin before.2.current.physical.raw people
      (catalogue before.2.current.programme before.2.current.physical.raw)}
    {replacement : Rebased before.2 (Operational.Repair.candidates before.2.current.programme origin
      before.2.current.physical.raw people _ before.2.current.recipe.move.word each)}
    (selected : Decision = .generated each replacement) :
    (advance home replies before catalogue .refresh).next =
      ⟨before.2.current.physical.raw, publishOn replacement.next
        (Runtime.RefreshEvidence.repaired each replacement.chosen : Runtime.RefreshEvidence before.2 Offered)⟩ := by
  unfold advance refresh
  rw [selected]
  rfl

theorem refresh_uses_the_joint_first_write
    {each : Operational.RejectedRecipes before.2.current.programme origin before.2.current.physical.raw people Offered}
    {edits : Operational.RejectedRecipes before.2.current.programme origin before.2.current.physical.raw people
      (Operational.Repair.candidates before.2.current.programme origin before.2.current.physical.raw
        people Offered before.2.current.recipe.move.word each)}
    {basis : Fin (Offered).length} {width : Nat}
    {earlier : ∀ n < width, Operational.Joint.Obstruction before.2.current.programme origin
      before.2.current.physical.raw people Offered before.2.current.recipe.move.word Offered[basis] n}
    {paid : Runtime.JointRebased before.2 Offered basis width}
    (selected : Decision = .joint each edits basis width earlier paid) :
    (advance home replies before catalogue .refresh).next =
      ⟨before.2.current.physical.raw, publishOn paid.actual.next
        (Runtime.RefreshEvidence.joint each edits basis width earlier paid.plan :
          Runtime.RefreshEvidence before.2 Offered)⟩ := by
  unfold advance refresh
  rw [selected]
  rfl

theorem refresh_with_no_repair_keeps_the_paid_diagnostic
    {denied : RetainedDue before.2 (catalogue before.2.current.programme before.2.current.physical.raw) home replies}
    (selected : Decision = .retained denied) :
    (advance home replies before catalogue .refresh).next = ⟨before.1, denied.next⟩ := by
  unfold advance refresh
  rw [selected]
  rfl

variable (initial : Resident seed cut community origin people quantum)
  (policy : Nat → Resident seed cut community origin people quantum → Command Party Good Port Technology Instrument)

def history : Nat → St
  | 0 => initial
  | n + 1 => (advance home replies (history n) catalogue (policy n (history n))).next

local notation "Reached" => history home replies catalogue initial policy

def stepAt (n : Nat) : Step (Reached n) :=
  advance home replies (Reached n) catalogue (policy n (Reached n))

def historyReads : (n : Nat) → ReadPath initial.2.current.ledger.resident (Reached n).2.current.ledger.resident
  | 0 => ⟨id, fun _ => rfl⟩
  | n + 1 => (historyReads n).trans (stepAt home replies catalogue initial policy n).reads

theorem whole_stack_and_language (n : Nat) :
    HEq (Reached n).2.current.ledger.stack initial.2.current.ledger.stack ∧
    initial.2.base.language.covered ⊆ (Reached n).2.base.language.covered := by
  induction n with
  | zero => exact ⟨HEq.rfl, Set.Subset.rfl⟩
  | succ n earlier =>
    let step := stepAt home replies catalogue initial policy n
    exact ⟨step.wholeStack.trans earlier.1, earlier.2.trans step.coverage⟩

theorem original_reserve_coordinates (n : Nat) :
    (∀ person good, initial.1.stock person good ≤ (Reached n).1.stock person good) ∧
      (Reached n).1.claims = initial.1.claims ∧ (Reached n).1.technology = initial.1.technology := by
  induction n with
  | zero => exact ⟨fun _ _ => le_rfl, rfl, rfl⟩
  | succ n earlier =>
    let step := stepAt home replies catalogue initial policy n
    exact ⟨fun p g => (earlier.1 p g).trans (step.reserveStocks p g),
      step.reserveClaims.trans earlier.2.1, step.reserveTechnology.trans earlier.2.2⟩

theorem every_interleaving_keeps_the_original_rows_and_orders (n : Nat) :
    (Reached n).2.current.ledger.stack.balances = initial.2.current.ledger.stack.balances ∧
    (Reached n).2.lanes.tariff.read = initial.2.lanes.tariff.read ∧
    (Reached n).2.lanes.payment.read = initial.2.lanes.payment.read ∧
    (Reached n).2.lanes.openPayment.read = initial.2.lanes.openPayment.read ∧
    FixedPoint.KeepsPublicTerms initial.2.current.programme (Reached n).2.current.programme := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl, rfl, .refl _⟩
  | succ n earlier =>
    let now := stepAt home replies catalogue initial policy n
    exact ⟨now.rows.trans earlier.1, now.tariff.trans earlier.2.1, now.payment.trans earlier.2.2.1,
      now.openPayment.trans earlier.2.2.2.1, earlier.2.2.2.2.trans now.terms⟩

theorem clock_bound (n : Nat) :
    initial.2.current.physical.raw.clock + (n : ℚ) * quantum ≤ (Reached n).2.current.physical.raw.clock := by
  induction n with
  | zero => simp [history]
  | succ n earlier =>
    have paid := (stepAt home replies catalogue initial policy n).clock
    change (Reached n).2.current.physical.raw.clock + quantum ≤ (Reached (n + 1)).2.current.physical.raw.clock at paid
    rw [Nat.cast_succ]
    linarith only [earlier, paid]

theorem clock_is_cofinal (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (Reached n).2.current.physical.raw.clock := by
  have positive := initial.2.current.recipe.law.positive
  obtain ⟨n, passed⟩ := exists_nat_gt ((bound - initial.2.current.physical.raw.clock) / quantum)
  have advanced := (div_lt_iff₀ positive).mp passed
  have later := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_max_left n start)) positive.le
  exact ⟨max n start, le_max_right _ _, by
    linarith only [advanced, later, clock_bound home replies catalogue initial policy (max n start)]⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.RebaseHistory
