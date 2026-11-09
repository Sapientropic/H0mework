import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase.History
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Clock

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.RebaseHistory

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open FixedPoint.OpenPeace.Operational (RecipeMenu)
open private enact saveAudit applyReplacement scheduled paidEffect from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase.History
open private dueInput from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  [DecidableEq (Request Party Good Port Technology Instrument)]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "St" => Resident seed cut community origin people quantum
local notation "Native" => TerminalPeace.Universal.Runtime.Native Party Good Port Technology Instrument

omit [DecidableEq Port] [DecidableEq (Request Party Good Port Technology Instrument)] in
theorem PaidEffect.exact_time {before after : Native} (paid : PaidEffect community origin people before after) :
    after.raw.clock = before.raw.clock + max 0 (paid.read.programme.law.duration before.raw) ∧
      after.raw.round = before.raw.round + 1 := by
  have exactTime := Physical.Public.an_actual_complete_word_is_one_real_period_or_the_original_state
    paid.read.programme paid.read.before paid.read.commands
  change (if paid.read.effect.isAccepted then
    paid.read.effect.next.raw.clock = paid.read.before.raw.clock + max 0 (paid.read.programme.law.duration paid.read.before.raw) ∧
      paid.read.effect.next.raw.round = paid.read.before.raw.round + 1 else
    paid.read.effect.next = paid.read.before) at exactTime
  rw [if_pos paid.accepted] at exactTime
  have time := congrArg (fun current : Native => current.raw.clock +
    max 0 (paid.read.programme.law.duration current.raw)) paid.beforeExact
  have ordinal := congrArg (fun current : Native => current.raw.round + 1) paid.beforeExact
  exact ⟨(congrArg (fun current : Native => current.raw.clock) paid.afterExact).symm.trans
      (exactTime.1.trans time),
    (congrArg (fun current : Native => current.raw.round) paid.afterExact).symm.trans (exactTime.2.trans ordinal)⟩

variable (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)
  (before : Resident seed cut community origin people quantum)

local notation "Now" => Runtime.State.current (Sigma.snd before)

omit [DecidableEq (Request Party Good Port Technology Instrument)] in
private theorem projected_paid_effect
    {reserveBase : RawCurrent Party Good Technology Instrument}
    {source : FixedPoint.Current (seed := seed) (cut := cut) (community := community)
      origin people quantum (reserveBase := reserveBase)}
    (actual : FixedPoint.Round source) {target : Native} (same : actual.next.physical = target) :
    (paidEffect actual same).read = actual.visit.read := by
  subst target
  rfl

omit [DecidableEq Port] [DecidableEq (Request Party Good Port Technology Instrument)] in
private theorem projected_paid_cast {prior actual target : Native}
    (same : actual = target) (effect : PaidEffect community origin people prior actual) :
    (same ▸ effect : PaidEffect community origin people prior target).read = effect.read := by
  subst target
  rfl

private def ReadsPaidProduction (step : Step before) : Prop :=
  step.paid.read.programme = (Now).programme ∧
    step.next.2.current.programme = (Now).programme ∧
    step.next.2.current.recipe.move.word = step.paid.read.commands

private theorem replacement_reads_paid_production
    (menu : RecipeMenu (Now).programme (Now).physical.raw)
    (result : RetainedDue before.2 menu home replies ⊕ Rebased before.2 menu) :
    ReadsPaidProduction before (applyReplacement home replies before menu result) := by
  cases result with
  | inr chosen =>
    have programme := chosen.actual.programmeNext.trans
      ((congrArg FixedPoint.Current.programme chosen.actualNext).symm.trans chosen.programme)
    have word := chosen.writes_its_chosen_word
    have exactRead : (applyReplacement home replies before menu (.inr chosen)).paid.read = chosen.actual.visit.read :=
      projected_paid_effect chosen.actual (congrArg FixedPoint.Current.physical chosen.actualNext.symm)
    exact ⟨(congrArg FixedPoint.Readout.programme exactRead).trans programme, chosen.programme,
      word.2.1.trans (word.1.symm.trans
      (congrArg FixedPoint.Readout.commands exactRead).symm)⟩
  | inl denied =>
    let input : OpenPeace.Input Party Good Port Technology Instrument := dueInput
    let round := FixedPoint.productiveRound (Now) .renew .renewed (Now).programme (Now).recipe
    have sameRound : (Runtime.source home replies before.2 input).source.round = round := rfl
    have programme : (Runtime.source home replies before.2 input).next.native.programme = (Now).programme := rfl
    have installed : (Runtime.advance home replies before.2 input).next.current.programme = (Now).programme :=
      (Runtime.same_programme home replies before.2 input).trans programme
    have keptWord : (Runtime.advance home replies before.2 input).next.current.recipe.move.word = (Now).recipe.move.word :=
      (Runtime.same_recipe_word home replies before.2 input).trans rfl
    have selected := FixedPoint.productiveRound_reads_selected_production (Now) .renew .renewed (Now).programme (Now).recipe
    have commands := selected.2.2.2.trans ((Now).recipe.moveAt_word (Now).physical.raw (Now).reserved)
    change (applyReplacement home replies before menu (.inl denied)).paid.read.programme = (Now).programme ∧
      denied.next.current.programme = (Now).programme ∧
      denied.next.current.recipe.move.word = (applyReplacement home replies before menu (.inl denied)).paid.read.commands
    have actualRead : (applyReplacement home replies before menu (.inl denied)).paid.read = round.visit.read := by
      let due := scheduled home replies before input
      let physical : due.next.2.current.physical = denied.next.current.physical := denied.samePhysical.symm
      change (physical ▸ due.paid : PaidEffect community origin people (Now).physical denied.next.current.physical).read = _
      refine (projected_paid_cast physical due.paid).trans ?_
      change (scheduled home replies before input).paid.read = _
      unfold scheduled
      exact (projected_paid_effect _ _).trans (congrArg (fun step => step.visit.read) sameRound)
    rw [actualRead]
    exact ⟨round.programmeNext.trans selected.2.2.1, denied.programme.trans installed,
      denied.recipeWord.trans (keptWord.trans commands.symm)⟩

variable (catalogue : Catalogue Party Good Port Technology Instrument)

theorem refresh_releases_only_the_actual_paid_word :
    ReadsPaidProduction before (advance home replies before catalogue .refresh) := by
  let menu := catalogue (Now).programme (Now).physical.raw
  change ReadsPaidProduction before (enact home replies before menu (Runtime.chooseRefresh before.2 menu home replies))
  generalize Runtime.chooseRefresh before.2 menu home replies = choice
  cases choice with
  | retained denied => exact replacement_reads_paid_production home replies before menu (.inl denied)
  | registered chosen => exact replacement_reads_paid_production home replies before menu (.inr chosen)
  | generated _ chosen => exact replacement_reads_paid_production home replies before _ (.inr chosen)
  | joint _ _ _ _ _ chosen => exact replacement_reads_paid_production home replies before _ (.inr chosen.actual)

def announcedClock : ℚ :=
  (Now).physical.raw.clock + max 0 ((Now).programme.law.duration (Now).physical.raw)

theorem the_refresh_lands_at_its_announced_clock :
    (advance home replies before catalogue .refresh).next.2.current.physical.raw.clock = announcedClock before := by
  have programme := (refresh_releases_only_the_actual_paid_word home replies before catalogue).1
  have clock := (advance home replies before catalogue .refresh).paid.exact_time.1
  rwa [programme] at clock

variable (policy : Nat → Resident seed cut community origin people quantum → Command Party Good Port Technology Instrument)

theorem reached_original_ordinal (n : Nat) :
    (history home replies catalogue before policy n).2.current.physical.raw.round = (Now).physical.raw.round + n := by
  induction n with
  | zero => rfl
  | succ n prior =>
    have next := (stepAt home replies catalogue before policy n).paid.exact_time.2
    change (history home replies catalogue before policy (n + 1)).2.current.physical.raw.round =
      (history home replies catalogue before policy n).2.current.physical.raw.round + 1 at next
    rw [next, prior, Nat.add_assoc]

theorem physical_ordinals_make_search_width_unbounded (n : Nat) :
    n ≤ Runtime.refreshWidth (history home replies catalogue before policy n).2 := by
  unfold Runtime.refreshWidth
  rw [reached_original_ordinal home replies before catalogue policy n]
  omega

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.RebaseHistory
