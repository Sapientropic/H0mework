import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Recovery.GeneratedStrategicGame

/-!
# Zero-player source-native clearing exchange

A literal free strategic program with no players still emits the two padded
clearing actors required by reciprocal exchange.  Its unique generated profile
is terminal, so the source-native M3 pipeline admits, reciprocates, and fulfills
both clearing legs before producing the empty payoff vector.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M4ZeroPlayerClearingExchangeRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations
open _root_.SaturationMonoid.ProcessGame.Society.Classical
open _root_.SaturationMonoid.ProcessGame.Society.Classical.Source
open _root_.SaturationMonoid.ProcessGame.Society.Classical.Source.FreeStrategicSyntax
open _root_.SaturationMonoid.ProcessGame.Society.Classical.GeneratedTerminalExchange
open Exchange Settlement Settlement.SourceOwnedSettlementCompiler

/-- Literal source program; no independent target or completeness theorem
participates in its construction. -/
def program : FreeStrategicSyntax where
  playerCount := 0
  strategyCounts := []
  terminalFlags := [true]
  settlementValues := []
  authorityResiduals := []

/-- The generated player subtype is empty, hence its dependent profile is
uniquely obtained by eliminating the impossible player index. -/
def generatedProfile : program.GeneratedProfile :=
  fun player => Fin.elim0 (program.generatedPlayerIndex player)

theorem generatedProfile_unique (other : program.GeneratedProfile) :
    other = generatedProfile := by
  funext player
  exact Fin.elim0 (program.generatedPlayerIndex player)

theorem generatedProfile_is_terminal :
    program.isWorldTerminal
      (program.generatedProfileEquivCanonical generatedProfile) = true := by
  unfold FreeStrategicSyntax.isWorldTerminal
  change [true][program.profileIndex
    (program.generatedProfileEquivCanonical generatedProfile)]?.getD true = true
  generalize program.profileIndex
      (program.generatedProfileEquivCanonical generatedProfile) = index
  cases index with
  | zero => rfl
  | succ index => cases index <;> rfl

def terminal : program.ExactWorldTerminalRestriction :=
  program.generatedTerminalRestriction generatedProfile
    generatedProfile_is_terminal

abbrev exchangeSeed := exactTerminalExchangeSeed program terminal
abbrev exchangeCompiler := terminalExchangeCompiler program
abbrev exchangeLaw := terminalExchangeLaw program
abbrev relationCompiler := terminalRelationCompiler program
abbrev incidence := terminalExchangeIncidence program
abbrev P := TerminalExchangeP program

abbrev settlementCompiler := terminalSettlementCompiler program
abbrev settlement := terminalSettlement program terminal

def clearingBase : TerminalLegBase program := firstTerminalLegBase program
def leftLeg : TerminalLeg program := (clearingBase, false)
def rightLeg : TerminalLeg program := (clearingBase, true)

theorem terminalLeg_card : Fintype.card (TerminalLeg program) = 2 := by
  simp [TerminalLeg, TerminalLegBase, FreeStrategicSyntax.AuthorityBase,
    program]

theorem terminalLeg_exhaustive (leg : TerminalLeg program) :
    leg = leftLeg ∨ leg = rightLeg := by
  rcases leg with ⟨base, side⟩
  have baseEq : base = clearingBase := by
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (by
      simpa [TerminalLegBase, program] using base.isLt))
  subst base
  cases side <;> simp [leftLeg, rightLeg]

structure ExactReciprocityAt
    (leg counterleg : TerminalLeg program) : Prop where
  counterparty_eq :
    exchangeSeed.counterparty exchangeCompiler leg = counterleg
  sourceRestrictions_ne :
    exchangeSeed.sourceEvent exchangeCompiler leg ≠
      exchangeSeed.sourceEvent exchangeCompiler
        (exchangeSeed.counterparty exchangeCompiler leg)
  interest : relationCompiler.GeneratedInterestAt
    (exchangeSeed.actor exchangeCompiler leg)
    (exchangeSeed.relation exchangeCompiler leg)
  targetResponsibility : Nonempty (incidence.TargetResponsibilityAt
    (exchangeSeed.actor exchangeCompiler leg)
    (exchangeSeed.obligation exchangeCompiler leg)
    (exchangeSeed.sourceEvent exchangeCompiler leg))
  sourceOwnership : Nonempty (SourceOwnsResponsibilityIncidence
    program.SettlementV
    (exchangeSeed.sourceEvent exchangeCompiler leg)
    (exchangeSeed.obligation exchangeCompiler leg))
  bearerExact :
    (exchangeSeed.obligation exchangeCompiler leg).bearer =
      exchangeLaw.bearerOfActor (exchangeSeed.actor exchangeCompiler leg)
  beneficiaryCross :
    (exchangeSeed.obligation exchangeCompiler leg).beneficiary =
      exchangeLaw.protectedInterestOfActor
        (exchangeSeed.actor exchangeCompiler counterleg)

theorem exactReciprocityAt (leg counterleg : TerminalLeg program)
    (counterparty_eq :
      exchangeSeed.counterparty exchangeCompiler leg = counterleg) :
    ExactReciprocityAt leg counterleg := by
  let native := terminalExchange_native_reciprocity program terminal leg
  refine
    { counterparty_eq := counterparty_eq
      sourceRestrictions_ne :=
        terminalExchange_counterparty_sourceEvents_ne program terminal leg
      interest := native.1
      targetResponsibility := native.2.1
      sourceOwnership := native.2.2.1
      bearerExact := native.2.2.2.1
      beneficiaryCross := ?_ }
  rw [← counterparty_eq]
  exact native.2.2.2.2

theorem leftExactReciprocity : ExactReciprocityAt leftLeg rightLeg :=
  exactReciprocityAt leftLeg rightLeg rfl

theorem rightExactReciprocity : ExactReciprocityAt rightLeg leftLeg :=
  exactReciprocityAt rightLeg leftLeg rfl

noncomputable def leftExactFulfilled :
    FulfilledExchangeLegAt settlementCompiler settlement leftLeg :=
  (terminalFullyFulfilled program terminal).fulfilled leftLeg

noncomputable def rightExactFulfilled :
    FulfilledExchangeLegAt settlementCompiler settlement rightLeg :=
  (terminalFullyFulfilled program terminal).fulfilled rightLeg

theorem whole_run_nonempty :
    Nonempty (P.Run
      (exchangeSeed.generatedState exchangeCompiler).current
      (settlement.current settlementCompiler)) :=
  terminalSettlement_whole_run program terminal

theorem fully_fulfilled_nonempty :
    Nonempty (FullyFulfilledExchangeAt settlementCompiler settlement) :=
  (program.generatedOutcome_is_whole_exchange_settlement_fold
    generatedProfile generatedProfile_is_terminal).1

theorem open_settlement_isEmpty :
    IsEmpty (OpenSettlementAt settlementCompiler settlement) :=
  terminalSettlement_open_isEmpty program terminal

def emptyPayoff : program.GeneratedPlayer → ℚ :=
  fun player => Fin.elim0 (program.generatedPlayerIndex player)

/-- The outcome is read from the whole fulfilled exchange even though its
player-indexed payoff function has empty domain. -/
theorem generatedOutcome_eq_some_emptyPayoff :
    program.generatedOutcome generatedProfile = some emptyPayoff := by
  have folded :=
    program.generatedOutcome_is_whole_exchange_settlement_fold
      generatedProfile generatedProfile_is_terminal
  rw [folded.2.1]
  apply congrArg some
  funext player
  exact Fin.elim0 (program.generatedPlayerIndex player)

structure ZeroPlayerClearingExchangeCertificate : Prop where
  uniqueProfile : ∀ other : program.GeneratedProfile,
    other = generatedProfile
  terminalProfile : program.isWorldTerminal
    (program.generatedProfileEquivCanonical generatedProfile) = true
  twoLegs : Fintype.card (TerminalLeg program) = 2
  legsExhaustive : ∀ leg : TerminalLeg program,
    leg = leftLeg ∨ leg = rightLeg
  leftReciprocal : ExactReciprocityAt leftLeg rightLeg
  rightReciprocal : ExactReciprocityAt rightLeg leftLeg
  leftFulfilled :
    Nonempty (FulfilledExchangeLegAt settlementCompiler settlement leftLeg)
  rightFulfilled :
    Nonempty (FulfilledExchangeLegAt settlementCompiler settlement rightLeg)
  wholeRun : Nonempty (P.Run
    (exchangeSeed.generatedState exchangeCompiler).current
    (settlement.current settlementCompiler))
  fullyFulfilled :
    Nonempty (FullyFulfilledExchangeAt settlementCompiler settlement)
  noOpenSettlement : IsEmpty (OpenSettlementAt settlementCompiler settlement)
  emptyOutcome : program.generatedOutcome generatedProfile = some emptyPayoff

theorem zeroPlayerClearingExchangeDirectConsumer :
    ZeroPlayerClearingExchangeCertificate where
  uniqueProfile := generatedProfile_unique
  terminalProfile := generatedProfile_is_terminal
  twoLegs := terminalLeg_card
  legsExhaustive := terminalLeg_exhaustive
  leftReciprocal := leftExactReciprocity
  rightReciprocal := rightExactReciprocity
  leftFulfilled := ⟨leftExactFulfilled⟩
  rightFulfilled := ⟨rightExactFulfilled⟩
  wholeRun := whole_run_nonempty
  fullyFulfilled := fully_fulfilled_nonempty
  noOpenSettlement := open_settlement_isEmpty
  emptyOutcome := generatedOutcome_eq_some_emptyPayoff

end
end M4ZeroPlayerClearingExchangeRegression
end Society
end ProcessGame
end SaturationMonoid
