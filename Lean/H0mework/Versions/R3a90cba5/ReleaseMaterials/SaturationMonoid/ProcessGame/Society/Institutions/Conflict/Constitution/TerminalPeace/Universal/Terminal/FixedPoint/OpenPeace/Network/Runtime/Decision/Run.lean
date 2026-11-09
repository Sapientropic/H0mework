import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Select
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Advance
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

local notation "StateAt" => Runtime.State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)
local notation "StepAt" => Runtime.Step (seed := seed) (cut := cut) (community := community)
  (origin := origin) (people := people) (quantum := quantum) (reserveBase := reserveBase)
local notation "InputAt" => OpenPeace.Input Party Good Port Technology Instrument
local notation "EffectAt" => Effect Party Good Port Technology Instrument

/-- A point reader belongs to the language already installed at this
resident. It owns neither a schedule nor any responsibility row. -/
structure Reader (state : Runtime.State (seed := seed) (cut := cut) (community := community)
    origin people quantum (reserveBase := reserveBase)) where
  private mk ::
  probe : ReadSet state.base.language.covered
  words : ∀ claim : Claim Party Good Port Technology Instrument, (probe (.inl claim)).isSome = true

def Reader.start (state : StateAt) (initial : state.base.language = .initial) :
    Reader state :=
  ⟨fun point => Checked.map (by rw [initial]) (Language.readInitial point), fun _ => rfl⟩

variable [DecidableEq (Request Party Good Port Technology Instrument)]

def Advice (state : StateAt) : InputAt → Type 1
  | .native _ => PUnit.{2}
  | .proposal attempt => ProposalCode state.current.programme attempt.programme

def Advice.raw (state : StateAt) : (input : InputAt) → Advice state input
  | .native _ => PUnit.unit
  | .proposal attempt => ProposalCode.raw attempt.programme

private structure Inspection {ActorWord : Type} (observed earlier : Set (ActorWord ⊕ Unit)) where
  points : ReadSet observed
  words : ∀ word : ActorWord, (points (.inl word)).isSome = true
  known : Option (PLift (observed ⊆ earlier))

private def emptyInspection {ActorWord : Type} {observed earlier : Set (ActorWord ⊕ Unit)} (empty : observed = ∅) :
    Inspection observed earlier :=
  ⟨fun point => Checked.map (by rw [empty]) (readEmpty point), fun _ => rfl,
    some ⟨by rw [empty]; exact Set.empty_subset _⟩⟩

noncomputable section

variable (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)
  (before : Runtime.State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
  (input : OpenPeace.Input Party Good Port Technology Instrument)

local notation "Scope" => Runtime.scope home replies before input
local notation "Earlier" => Language.covered (OpenPeace.State.language before.base)
local notation "Actual" => Runtime.source home replies before input

private def inspect (read : Reader before) (advice : Advice before input) :
    Inspection Scope Earlier := by
  if unpaid : (Actual).source.paidWire.isNone = true then
    have absent := Option.isNone_iff_eq_none.mp unpaid
    exact emptyInspection (OpenPeace.no_unpaid_scope _ _ _ _ _ _ _ absent)
  else
    cases input with
    | native due => exact emptyInspection rfl
    | proposal attempt =>
      cases paid : (Runtime.source home replies before (.proposal attempt)).source with
      | ordinary _ _ =>
        have empty : Runtime.scope home replies before (.proposal attempt) = ∅ := by
          simp only [Runtime.scope, OpenPeace.scope, Runtime.source] at paid ⊢
          rw [paid]
        exact emptyInspection empty
      | prepaid wire allowed receipt =>
        have recorded : Runtime.scope home replies before (.proposal attempt) =
            paidEffects receipt attempt.programme :=
          OpenPeace.paid_proposal_scope _ _ _ _ _ _ _ paid
        rw [recorded]
        exact ⟨readPaidScope receipt attempt.programme advice.terms, fun _ => rfl,
          paidCoverage receipt advice read.probe⟩


private theorem known_if_unpaid (read : Reader before) (advice : Advice before input)
    (unpaid : (Actual).source.paidWire = none) :
    ∃ covered, (inspect home replies before input read advice).known = some covered := by
  unfold inspect
  rw [dif_pos (Option.isNone_iff_eq_none.mpr unpaid)]
  exact ⟨_, rfl⟩

/-- Missing evidence has no committed step. The material receipt is the
actual source already addressed by the input and may be checked again. -/
inductive Result (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)
    (before : Runtime.State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
    (input : OpenPeace.Input Party Good Port Technology Instrument) where
  | committed (step : StepAt) (exactStep : step = Runtime.advance home replies before input)
      (readNext : Reader step.next)
  | needsEvidence (wire : Wire Party Good Port Technology Instrument)
      (charged : (Runtime.source home replies before input).source.paidWire = some wire)


private def commitCovered (read : Reader before) (covered : Scope ⊆ Earlier) :
    Result home replies before input :=
  let step := Runtime.advanceChecked home replies before input (.isTrue covered)
  .committed step (Runtime.advanceChecked_eq_advance home replies before input _) ⟨read.probe, read.words⟩

private def missingEvidence (read : Reader before) : Result home replies before input :=
  match charged : (Actual).source.paidWire with
  | some wire => .needsEvidence wire charged
  | none => commitCovered home replies before input read (by
    change OpenPeace.scope _ _ _ _ _ _ _ ⊆ Earlier
    rw [OpenPeace.no_unpaid_scope _ _ _ _ _ _ _ charged]
    exact Set.empty_subset _)

/-- Select the same canonical physical or whole-network write using
source-derived finite tests. A finite scan can produce an exact new
effect, never a claim that unexamined effects do not exist. -/
def advance (read : Reader before) (advice : Advice before input) (proposedWitnesses : List EffectAt := []) :
    Result home replies before input :=
  let actual := inspect home replies before input read advice
  match actual.known with
  | some covered => commitCovered home replies before input read covered.down
  | none =>
    let witnesses := sourceProbes people before.current.move.word ++ proposedWitnesses
    match firstNovel actual.points read.probe witnesses with
    | none => missingEvidence home replies before input read
    | some witness =>
      let check := Decidable.isFalse witness.excludesCoverage
      let step := Runtime.advanceChecked home replies before input check
      have same : step = Runtime.advance home replies before input :=
        Runtime.advanceChecked_eq_advance home replies before input check
      let union := readUnion read.probe actual.points
      let atNext : ReadSet step.next.base.language.covered :=
        fun point => Checked.map (by rw [same, Runtime.coverage_eq]) (union point)
      .committed step same ⟨atNext, fun claim => by
        change (Checked.map _ (Checked.or (read.probe (.inl claim)) (actual.points (.inl claim)))).isSome = true
        exact Checked.map_complete _ (Checked.or_complete (read.words claim) (actual.words claim))⟩

/-- The unpaid branch never inspects candidate terms and retains the
single ordinary material successor even when supplied witnesses are forged. -/
theorem unpaid_is_committed (read : Reader before) (advice : Advice before input)
    (witnesses : List EffectAt) (unpaid : (Actual).source.paidWire = none) :
    ∃ step same readNext,
      advance home replies before input read advice witnesses = .committed step same readNext ∧
      step.write = none ∧ step.next.base.adaptive = (Actual).next := by
  obtain ⟨covered, readCovered⟩ := known_if_unpaid home replies before input read advice unpaid
  let step := Runtime.advanceChecked home replies before input (.isTrue covered.down)
  have same := Runtime.advanceChecked_eq_advance home replies before input (.isTrue covered.down)
  refine ⟨step, same, ⟨read.probe, read.words⟩, ?_, ?_, ?_⟩
  · simp only [advance, readCovered, commitCovered]
    rfl
  · rfl
  · rfl


/-- Every material effect has an exact finite test at every checked
epoch. A raw word is enough to trigger the canonical whole-ledger write
once the tests verify its original loss and lack of an older expression. -/
theorem advance_follows_a_material_witness (read : Reader before) (advice : Advice before input)
    (witnesses : List EffectAt) (claim : Claim Party Good Port Technology Instrument)
    (submitted : Sum.inl claim ∈ sourceProbes people before.current.move.word ++ witnesses)
    (lost : Sum.inl claim ∈ Scope) (fresh : Sum.inl claim ∉ Earlier) :
    ∃ step same readNext,
      advance home replies before input read advice witnesses = .committed step same readNext ∧
      step.write.isSome = true := by
  let view := inspect home replies before input read advice
  let witness : NovelPoint Scope Earlier := ⟨.inl claim, lost, fresh⟩
  have examined := Checked.exactTrue (view.points (.inl claim)) (view.words claim) lost
  have unseen := Checked.exactFalse (read.probe (.inl claim)) (read.words claim) fresh
  obtain ⟨selected, found⟩ :=
    firstNovel_finds_a_tested_witness view.points read.probe _ witness submitted examined unseen
  unfold advance
  dsimp only
  split
  · rename_i covered equal
    exact (fresh (covered.down lost)).elim
  · rw [found]
    let checked := Decidable.isFalse selected.excludesCoverage
    let step := Runtime.advanceChecked home replies before input checked
    let same := Runtime.advanceChecked_eq_advance home replies before input checked
    exact ⟨step, same, _, rfl, rfl⟩

/-- An actual paid gap whose old expressions are unreadable stays at
its charged prefix. Incomplete inspection grants no network write. -/
theorem advance_retains_an_unreadable_paid_scope (read : Reader before) (advice : Advice before input)
    (witnesses : List EffectAt) (wire : Wire Party Good Port Technology Instrument)
    (charged : (Actual).source.paidWire = some wire) (novel : ¬ Scope ⊆ Earlier)
    (unreadable : ∀ point ∈ Scope, read.probe point = none) :
    advance home replies before input read advice witnesses = .needsEvidence wire charged := by
  let view := inspect home replies before input read advice
  have noWitness : firstNovel view.points read.probe (sourceProbes people before.current.move.word ++ witnesses) = none := by
    unfold firstNovel
    apply List.findSome?_eq_none_iff.mpr
    intro point _
    cases observed : view.points point with
    | none => cases read.probe point <;> rfl
    | some fact =>
      cases fact with
      | isFalse _ => cases read.probe point <;> rfl
      | isTrue actual => rw [unreadable point actual]
  unfold advance
  dsimp only
  split
  · rename_i known _
    exact (novel known.down).elim
  · rw [noWitness]
    change missingEvidence home replies before input read = .needsEvidence wire charged
    unfold missingEvidence
    split
    · rename_i paid literal
      have same : paid = wire := Option.some.inj (literal.symm.trans charged)
      subst paid
      rfl
    · rename_i empty
      cases empty.symm.trans charged

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision
