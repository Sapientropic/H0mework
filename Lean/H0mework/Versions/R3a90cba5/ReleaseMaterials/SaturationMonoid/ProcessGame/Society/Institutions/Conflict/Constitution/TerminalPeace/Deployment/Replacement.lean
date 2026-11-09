import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Production.Joint
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Transport

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Clearance.Joint.Reinterpreted
open Clearance.Joint.Reinterpreted.OriginalConsumer
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open FixedPoint.OpenPeace.Network.Runtime.Decision
open FixedPoint.OpenPeace.Operational (RejectedRecipes RecipeMenu)
open FixedPoint.OpenPeace.Operational.Repair (candidates select)
open private noSingleEdit attainedWidth from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Production.Joint
open private postRecipe from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase
open private publishOn from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.ReadHistory

noncomputable section

private def replaceCatalogue : Runtime.RebaseHistory.Catalogue Bool Bool Bool Unit Unit := by
  classical
  exact fun input raw => if same : input = revised then emptyMenu input same raw else []

abbrev menu := replaceCatalogue pending.live.current.programme pending.live.current.physical.raw

private theorem catalogue_at_pending : menu = emptyMenu _ pendingLaw _ := by
  simp only [menu, replaceCatalogue, dif_pos pendingLaw]

private theorem hasBasis : 0 < menu.length := by
  rw [catalogue_at_pending]
  exact Nat.zero_lt_one

private abbrev allIssues := RejectedRecipes pending.live.current.programme (originalRaw loss)
  pending.live.current.physical.raw (people loss front) menu

private abbrev editsFor (each : allIssues) :=
  candidates pending.live.current.programme (originalRaw loss) pending.live.current.physical.raw
    (people loss front) menu pending.live.current.recipe.move.word each

private abbrev repairDecision := select pending.live.current.programme (originalRaw loss)
  pending.live.current.physical.raw (people loss front) menu pending.live.current.recipe.move.word

private theorem allEditsFail : noSingleEdit repairDecision = true := by
  change noSingleEdit (select _ _ _ _ menu _) = true
  rw [catalogue_at_pending]
  exact the_empty_offer_exhausts_single_edits _ pendingLaw _ pendingStock _ pendingWord

private abbrev basis : Fin menu.length := ⟨0, hasBasis⟩

private abbrev jointDecision :=
  Operational.Joint.search pending.live.current.programme (originalRaw loss) pending.live.current.physical.raw
    (people loss front) menu pending.live.current.recipe.move.word menu[basis] (Runtime.refreshWidth pending.live)

private theorem generatedBySource :
    jointDecision.word = some jointWord ∧ attainedWidth jointDecision = some 4 := by
  let input := pending.live.current.programme
  let raw := pending.live.current.physical.raw
  let old := pending.live.current.recipe.move.word
  have read (options : RecipeMenu input raw) (exactMenu : options = emptyMenu _ pendingLaw _)
      (listed : 0 < options.length) :
      let selected := Operational.Joint.search input (originalRaw loss) raw
        (people loss front) options old (options[0]'listed) (raw.round + old.length)
      selected.word = some jointWord ∧ attainedWidth selected = some 4 := by
    subst options
    exact named_joint_source_writes_at_width_four _ pendingLaw _ pendingStock _ pendingWord
  exact read menu catalogue_at_pending hasBasis

private theorem cadence :
    opening.paid.next.programme.law.duration opening.paid.next.physical.raw ≤
      pending.live.current.programme.law.duration pending.live.current.physical.raw := by
  have before : opening.paid.next.programme.law.duration opening.paid.next.physical.raw = 1 := by
    rw [opening.paid.sameProgramme.trans refusedLaw, (congrArg (fun p => p.raw) opening.network.physical).symm,
      opening.exactStock]
    decide +kernel
  have now : 1 ≤ pending.live.current.programme.law.duration pending.live.current.physical.raw := by
    rw [pendingLaw, pendingStock]
    decide +kernel
  exact before.le.trans now

def rebaseStock : Original.Raw := revised.law.next chargedStock jointWord

structure Replacement where
  private mk ::
  each : allIssues
  repairs : RejectedRecipes pending.live.current.programme (originalRaw loss) pending.live.current.physical.raw
    (people loss front) (editsFor each)
  width : Nat
  shortest : width = 4
  earlier : ∀ n < width, Operational.Joint.Obstruction pending.live.current.programme (originalRaw loss)
    pending.live.current.physical.raw (people loss front) menu pending.live.current.recipe.move.word menu[basis] n
  joint : Runtime.JointRebased pending.live menu basis width
  selected : Runtime.chooseRefresh pending.live menu home namedReplies = .joint each repairs basis width earlier joint
  physical : joint.actual.next.current.physical.raw = rebaseStock
  word : joint.actual.next.current.recipe.move.word = jointWord

def replacement : Replacement := by
  have checked := allEditsFail
  have generated := generatedBySource
  cases edits : repairDecision with
  | registered picked => rw [edits] at checked; cases checked
  | generated each picked => rw [edits] at checked; cases checked
  | exhausted each repairs =>
    cases result : jointDecision with
    | pending tested => rw [result] at generated; cases generated.1
    | found width inside earlier plan =>
      rw [result] at generated
      have exactWord : plan.selected.recipe.move.word = jointWord := Option.some.inj generated.1
      have exactWidth : width = 4 := Option.some.inj generated.2
      let paid := postRecipe pending.live _ plan.selected cadence
      let installed : Runtime.JointRebased pending.live menu basis width := ⟨plan, paid, rfl⟩
      have chosen : Runtime.chooseRefresh pending.live menu home namedReplies =
          .joint each repairs basis width earlier installed :=
        Runtime.chooseRefresh_posts_the_first_joint_choice pending.live menu home namedReplies
          cadence each repairs edits hasBasis width inside earlier plan result
      have read := paid.writes_its_chosen_word
      refine ⟨each, repairs, width, exactWidth, earlier, installed, chosen, ?_, read.2.1.trans exactWord⟩
      change paid.next.current.physical.raw = _
      rw [read.2.2]
      change pending.live.current.programme.law.next pending.live.current.physical.raw plan.selected.recipe.move.word = _
      rw [exactWord, pendingLaw, pendingStock]
      rfl

def Replacement.record (chosen : Replacement) : Runtime.RefreshEvidence pending.live menu :=
  .joint chosen.each chosen.repairs basis chosen.width chosen.earlier chosen.joint.plan

def Replacement.recorded (chosen : Replacement) := publishOn chosen.joint.actual.next chosen.record

abbrev initial := Sigma.mk opening.paid.next.physical.raw pending.live

def policy (n : Nat) (_ : type_of% initial) : Runtime.RebaseHistory.Command Bool Bool Bool Unit Unit :=
  if n = 0 then .refresh else .scheduled (.native ⟨none, []⟩)

abbrev reached := Runtime.RebaseHistory.history home namedReplies replaceCatalogue initial policy 1
abbrev path := Runtime.RebaseHistory.historyReads home namedReplies replaceCatalogue initial policy 1

theorem reachedFromPending : reached = ⟨pending.live.current.physical.raw, replacement.recorded⟩ :=
  Runtime.RebaseHistory.refresh_uses_the_joint_first_write home namedReplies initial replaceCatalogue replacement.selected

theorem reachedStock : reached.2.current.physical.raw = rebaseStock := by
  rw [reachedFromPending]
  exact replacement.physical

theorem the_generated_production_is_the_original_first_write :
    let paid := replacement.joint.actual.actual
    let original := pending.live.current.ledger
    paid.visit.read.commands = jointWord ∧ paid.visit.read.effect.isAccepted = true ∧
      paid.visit.read.before = pending.live.current.physical ∧
      (⟨original.world, (Installation.Live.action original paid.visit.read true).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = replacement.joint.actual.next.current.ledger.resident.erase := by
  intro paid original
  have read := replacement.joint.actual.writes_its_chosen_word
  refine ⟨read.1.trans (read.2.1.symm.trans replacement.word), paid.realWrite, paid.before, ?_⟩
  rw [replacement.joint.actual.actualNext]
  exact paid.wholeNext

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment
