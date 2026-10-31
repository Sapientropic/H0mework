import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Recovery.GeneratedNormalForm

/-!
# Source-generated finite extensive search

This compatibility entry owns only the finite sequential history/search
readout over the generated normal form.  Search histories never write the
source occurrence or a responsibility current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement
open Settlement.SourceOwnedSettlementCompiler
open Source Source.FreeStrategicSyntax
open GeneratedTerminalExchange

namespace Source.FreeStrategicSyntax

abbrev RawHistory (program : FreeStrategicSyntax) :=
  Sigma fun depth : Fin (program.playerCount + 1) =>
    Fin depth.val → program.FutureCode

def RawHistory.Valid {program : FreeStrategicSyntax}
    (history : program.RawHistory) : Prop :=
  ∀ index : Fin history.1.val, (history.2 index).1.val = index.val

instance rawHistoryDecidableEq (program : FreeStrategicSyntax) :
    DecidableEq program.RawHistory :=
  inferInstance

noncomputable instance rawHistoryFintype (program : FreeStrategicSyntax) :
    Fintype program.RawHistory :=
  inferInstance

instance rawHistoryValidDecidable (program : FreeStrategicSyntax)
    (history : program.RawHistory) : Decidable history.Valid :=
  Classical.propDecidable _

abbrev GeneratedHistory (program : FreeStrategicSyntax) :=
  { history : program.RawHistory // history.Valid }

noncomputable instance generatedHistoryFintype
    (program : FreeStrategicSyntax) : Fintype program.GeneratedHistory :=
  inferInstance

inductive GeneratedFiniteExtensiveGame (program : FreeStrategicSyntax) : Type
  | generated

def recoverExtensiveGame (program : FreeStrategicSyntax) :
    GeneratedFiniteExtensiveGame program :=
  .generated

namespace GeneratedFiniteExtensiveGame

def authorityTree {program : FreeStrategicSyntax}
    (_game : GeneratedFiniteExtensiveGame program) :
    RootedAccountedUnfolding FreeClassicalAtom :=
  program.occurrence

@[simp] theorem authorityTree_eq_occurrence
    {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program) :
    game.authorityTree = program.occurrence :=
  rfl

theorem authorityTree_fold_unique
    {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program)
    {Carrier : Type*}
    (atOccurrence : FreeClassicalAtom → List Carrier → Carrier)
    (candidate : RootedAccountedUnfolding FreeClassicalAtom → Carrier)
    (commutes : ∀ (rootAtom : FreeClassicalAtom)
        (branches : AccountedBranches FreeClassicalAtom),
      candidate (.occur rootAtom branches) =
        atOccurrence rootAtom
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate game.authorityTree =
      game.authorityTree.fold atOccurrence :=
  RootedAccountedUnfolding.fold_unique
    atOccurrence candidate commutes game.authorityTree

abbrev Player {program : FreeStrategicSyntax}
    (_game : GeneratedFiniteExtensiveGame program) :=
  program.GeneratedPlayer

abbrev StrategyFor {program : FreeStrategicSyntax}
    (_game : GeneratedFiniteExtensiveGame program)
    (player : program.GeneratedPlayer) :=
  program.GeneratedStrategyFor player

abbrev Profile {program : FreeStrategicSyntax}
    (_game : GeneratedFiniteExtensiveGame program) :=
  program.GeneratedProfile

abbrev History {program : FreeStrategicSyntax}
    (_game : GeneratedFiniteExtensiveGame program) :=
  program.GeneratedHistory

def rootHistory {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program) : game.History :=
  ⟨⟨⟨0, Nat.zero_lt_succ _⟩, fun index => Fin.elim0 index⟩,
    fun index => Fin.elim0 index⟩

def owner? {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program)
    (history : game.History) : Option game.Player :=
  if within : history.1.1.val < program.playerCount then
    some (program.generatedPlayerOf ⟨history.1.1.val, within⟩)
  else
    none

def Playing {program : FreeStrategicSyntax}
    {game : GeneratedFiniteExtensiveGame program}
    (history : game.History) : Prop :=
  history.1.1.val < program.playerCount

def Complete {program : FreeStrategicSyntax}
    {game : GeneratedFiniteExtensiveGame program}
    (history : game.History) : Prop :=
  history.1.1.val = program.playerCount

def ActionAt {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program)
    (history : game.History) (within : game.Playing history) :=
  program.GeneratedStrategyFor
    (program.generatedPlayerOf ⟨history.1.1.val, within⟩)

def exactActionRestrictionAt {program : FreeStrategicSyntax}
    {game : GeneratedFiniteExtensiveGame program}
    (history : game.History) (within : game.Playing history)
    (action : game.ActionAt history within) :
    program.ExactActionRestriction :=
  program.exactActionRestriction action.1

theorem action_is_exact_occurrence_restriction
    {program : FreeStrategicSyntax}
    {game : GeneratedFiniteExtensiveGame program}
    (history : game.History) (within : game.Playing history)
    (action : game.ActionAt history within) :
    (game.exactActionRestrictionAt history within action).1 = action.1 ∧
      program.actionAtom action.1 ∈ program.occurrence.trace :=
  ⟨rfl, program.actionAtom_mem_trace action.1⟩

theorem history_actions_are_exact_occurrence_restrictions
    {program : FreeStrategicSyntax}
    {game : GeneratedFiniteExtensiveGame program}
    (history : game.History) :
    ∀ index : Fin history.1.1.val,
      ∃ restriction : program.ExactActionRestriction,
        restriction.1 = history.1.2 index ∧
          program.actionAtom restriction.1 ∈ program.occurrence.trace := by
  intro index
  exact ⟨program.exactActionRestriction (history.1.2 index), rfl,
    program.actionAtom_mem_trace (history.1.2 index)⟩

def History.extend {program : FreeStrategicSyntax}
    {game : GeneratedFiniteExtensiveGame program}
    (history : game.History) (within : game.Playing history)
    (action : game.ActionAt history within) : game.History := by
  let nextDepth : Fin (program.playerCount + 1) :=
    ⟨history.1.1.val + 1, Nat.succ_lt_succ within⟩
  let nextChoice : Fin nextDepth.val → program.FutureCode :=
    Fin.lastCases action.1 history.1.2
  refine ⟨⟨nextDepth, nextChoice⟩, ?_⟩
  intro index
  refine Fin.lastCases ?_ (fun oldIndex => ?_) index
  · have actionPlayer :=
      (program.generatedStrategy_mem_iff
        ⟨history.1.1.val, within⟩ action.1).1 action.2
    dsimp [nextChoice]
    simpa using congrArg Fin.val actionPlayer
  · dsimp [nextChoice]
    simpa using history.2 oldIndex

@[simp] theorem History.extend_depth {program : FreeStrategicSyntax}
    {game : GeneratedFiniteExtensiveGame program}
    (history : game.History) (within : game.Playing history)
    (action : game.ActionAt history within) :
    (history.extend within action).1.1.val = history.1.1.val + 1 :=
  rfl

def historyOfProfile {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program)
    (profile : game.Profile) : game.History := by
  let depth : Fin (program.playerCount + 1) :=
    ⟨program.playerCount, Nat.lt_succ_self _⟩
  let choices : Fin depth.val → program.FutureCode := fun player =>
    (profile (program.generatedPlayerOf player)).1
  refine ⟨⟨depth, choices⟩, ?_⟩
  intro player
  have member := (profile (program.generatedPlayerOf player)).2
  have playerEq :=
    (program.generatedStrategy_mem_iff player _).1 member
  exact congrArg Fin.val playerEq

@[simp] theorem historyOfProfile_complete
    {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program)
    (profile : game.Profile) :
    game.Complete (game.historyOfProfile profile) := by
  change program.playerCount = program.playerCount
  rfl

def canonicalProfileOfComplete
    {program : FreeStrategicSyntax}
    {game : GeneratedFiniteExtensiveGame program}
    (history : game.History) (complete : game.Complete history) :
    program.CanonicalProfile := fun player => by
  let historyPlayer : Fin history.1.1.val :=
    ⟨player.val, by rw [complete]; exact player.isLt⟩
  let code := history.1.2 historyPlayer
  have playerValue : code.1.val = player.val := history.2 historyPlayer
  have playerEq : code.1 = player := Fin.ext playerValue
  exact playerEq ▸ code.2

theorem canonicalProfile_historyOfProfile
    {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program)
    (profile : game.Profile) :
    game.canonicalProfileOfComplete (game.historyOfProfile profile)
        (game.historyOfProfile_complete profile) =
      program.generatedProfileEquivCanonical profile := by
  funext player
  rfl

inductive LeafStatus where
  | playing
  | cutoff
  | worldTerminal
  deriving DecidableEq, Repr

def status {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program)
    (history : game.History) : LeafStatus := by
  classical
  exact
    if within : game.Playing history then .playing
    else
      have complete : game.Complete history := by
        exact Nat.le_antisymm
          (Nat.le_of_lt_succ history.1.1.isLt) (Nat.le_of_not_gt within)
      if program.isWorldTerminal
          (game.canonicalProfileOfComplete history complete) then
        .worldTerminal
      else
        .cutoff

def outcome {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program)
    (profile : game.Profile) : Option (game.Player → ℚ) :=
  program.generatedOutcome profile

theorem outcome_is_M3_exchange_settlement_fold
    {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program)
    (profile : game.Profile)
    (terminal : program.isWorldTerminal
      (program.generatedProfileEquivCanonical profile) = true) :
    Nonempty (FullyFulfilledExchangeAt
      (terminalSettlementCompiler program)
      (terminalSettlement program
        (program.generatedTerminalRestriction profile terminal))) ∧
      game.outcome profile =
        some (fun player =>
          (terminalFulfilledPlayerLeg program
            (program.generatedTerminalRestriction profile terminal)
            (program.generatedPlayerIndex player)).obligation.residual) ∧
      ∀ player : game.Player,
        (terminalFulfilledPlayerLeg program
          (program.generatedTerminalRestriction profile terminal)
          (program.generatedPlayerIndex player)).obligation.bearer = player.1 :=
  program.generatedOutcome_is_whole_exchange_settlement_fold
    profile terminal

theorem search_actual_noninterference
    {program : FreeStrategicSyntax}
    (game : GeneratedFiniteExtensiveGame program)
    (_profile : game.Profile) :
    (program.processGame).occurrence = program.occurrence ∧
      program.occurrence.trace = .origin :: program.programEvents ∧
      FreeClassicalAtom.origin ∈ program.occurrence.trace :=
  ⟨rfl, program.occurrence_trace, program.origin_mem_trace⟩

end GeneratedFiniteExtensiveGame
end Source.FreeStrategicSyntax

end
end Classical
end Society
end ProcessGame
end SaturationMonoid
