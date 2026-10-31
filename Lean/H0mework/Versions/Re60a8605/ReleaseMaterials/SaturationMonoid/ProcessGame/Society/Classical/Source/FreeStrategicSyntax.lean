import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List

/-!
# Target-independent free strategic syntax

The public source is a natural-number code decoded into one fixed first-order
program.  This module contains only the syntax, encoding, and its canonical
finite player, strategy, profile, future-code, outcome-index, and hidden
authority-event carriers.  The authority stream is not part of the recovered
classical image; downstream exchange settlement gives it actual consumers.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical
namespace Source

noncomputable section

structure FreeStrategicSyntax where
  playerCount : Nat
  strategyCounts : List Nat
  terminalFlags : List Bool
  settlementValues : List ℚ
  authorityResiduals : List ℚ
  deriving DecidableEq, Repr

def freeStrategicSyntaxEquiv :
    FreeStrategicSyntax ≃
      Nat × List Nat × List Bool × List ℚ × List ℚ where
  toFun program :=
    (program.playerCount, program.strategyCounts,
      program.terminalFlags, program.settlementValues,
      program.authorityResiduals)
  invFun data :=
    { playerCount := data.1
      strategyCounts := data.2.1
      terminalFlags := data.2.2.1
      settlementValues := data.2.2.2.1
      authorityResiduals := data.2.2.2.2 }
  left_inv := by intro program; cases program; rfl
  right_inv := by intro data; rcases data with ⟨a, b, c, d, e⟩; rfl

noncomputable instance : Encodable FreeStrategicSyntax :=
  Encodable.ofEquiv
    (Nat × List Nat × List Bool × List ℚ × List ℚ)
    freeStrategicSyntaxEquiv

abbrev ValidCode :=
  { code : Nat //
    (Encodable.decode (α := FreeStrategicSyntax) code).isSome }

noncomputable def syntaxOf (code : ValidCode) : FreeStrategicSyntax :=
  (Encodable.decode (α := FreeStrategicSyntax) code.1).get code.2

noncomputable def validCodeOfSyntax
    (program : FreeStrategicSyntax) : ValidCode :=
  ⟨Encodable.encode program, by simp⟩

@[simp] theorem syntaxOf_validCodeOfSyntax
    (program : FreeStrategicSyntax) :
    syntaxOf (validCodeOfSyntax program) = program := by
  simp [syntaxOf, validCodeOfSyntax]

namespace FreeStrategicSyntax

abbrev Player (program : FreeStrategicSyntax) := Fin program.playerCount

def actorCount (program : FreeStrategicSyntax) : Nat :=
  max program.playerCount 2

abbrev ActorIndex (program : FreeStrategicSyntax) :=
  Fin program.actorCount

def playerActorIndex (program : FreeStrategicSyntax)
    (player : program.Player) : program.ActorIndex :=
  ⟨player.val, player.isLt.trans_le (Nat.le_max_left _ _)⟩

def firstActorIndex (program : FreeStrategicSyntax) : program.ActorIndex :=
  ⟨0, (by decide : 0 < 2).trans_le (Nat.le_max_right _ _)⟩

def strategyCount (program : FreeStrategicSyntax)
    (player : program.Player) : Nat :=
  program.strategyCounts[player.val]?.getD 0

abbrev Strategy (program : FreeStrategicSyntax)
    (player : program.Player) :=
  Fin (program.strategyCount player)

abbrev CanonicalProfile (program : FreeStrategicSyntax) :=
  ∀ player : program.Player, program.Strategy player

abbrev FutureCode (program : FreeStrategicSyntax) :=
  Sigma fun player : program.Player => program.Strategy player

abbrev OutcomeIndex (program : FreeStrategicSyntax) :=
  program.CanonicalProfile × program.Player

abbrev AuthorityBase (program : FreeStrategicSyntax) :=
  Fin (max program.playerCount 1)

abbrev AuthorityIndex (program : FreeStrategicSyntax) :=
  program.CanonicalProfile × program.AuthorityBase

noncomputable instance strategyFintype (program : FreeStrategicSyntax)
    (player : program.Player) : Fintype (program.Strategy player) :=
  inferInstance

noncomputable instance canonicalProfileFintype
    (program : FreeStrategicSyntax) : Fintype program.CanonicalProfile :=
  inferInstance

noncomputable instance futureCodeFintype
    (program : FreeStrategicSyntax) : Fintype program.FutureCode :=
  inferInstance

noncomputable instance outcomeIndexFintype
    (program : FreeStrategicSyntax) : Fintype program.OutcomeIndex :=
  inferInstance

noncomputable instance authorityIndexFintype
    (program : FreeStrategicSyntax) : Fintype program.AuthorityIndex :=
  inferInstance

noncomputable def profileEquivFin (program : FreeStrategicSyntax) :
    program.CanonicalProfile ≃ Fin (Fintype.card program.CanonicalProfile) :=
  Fintype.equivFin _

noncomputable def outcomeEquivFin (program : FreeStrategicSyntax) :
    program.OutcomeIndex ≃ Fin (Fintype.card program.OutcomeIndex) :=
  Fintype.equivFin _

noncomputable def authorityEquivFin (program : FreeStrategicSyntax) :
    program.AuthorityIndex ≃
      Fin (Fintype.card program.AuthorityIndex) :=
  Fintype.equivFin _

noncomputable def profileIndex (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile) : Nat :=
  (program.profileEquivFin profile).val

noncomputable def outcomeIndex (program : FreeStrategicSyntax)
    (outcome : program.OutcomeIndex) : Nat :=
  (program.outcomeEquivFin outcome).val

noncomputable def authorityIndex (program : FreeStrategicSyntax)
    (authority : program.AuthorityIndex) : Nat :=
  (program.authorityEquivFin authority).val

noncomputable def isWorldTerminal (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile) : Bool :=
  program.terminalFlags[program.profileIndex profile]?.getD true

noncomputable def settlementValue (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile) (player : program.Player) : ℚ :=
  program.settlementValues[program.outcomeIndex (profile, player)]?.getD 0

/-- Source-native residual forgotten by the classical image.  Its authority
is installed downstream as a counterparty exchange obligation, not read as a
historical label. -/
noncomputable def authorityResidual (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile)
    (base : program.AuthorityBase) : ℚ :=
  program.authorityResiduals[
    program.authorityIndex (profile, base)]?.getD 0

end FreeStrategicSyntax
end
end Source
end Classical
end Society
end ProcessGame
end SaturationMonoid
