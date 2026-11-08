import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Obligation.RelationObligation

/-!
# Deduplicated closure gain

Closure gain is a readout of one compiler-generated obligation update.  Its
two ranks are the cardinalities of the update's deduplicated settled and new
debt key sets; no score, material heuristic or external engine datum enters
the definition.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

open Obligation

universe u v

/-- Cardinality readout before subtraction. -/
def closureGainOf {Key : Type u} [DecidableEq Key]
    (settled newDebt : Finset Key) : Int :=
  Int.ofNat settled.card - Int.ofNat newDebt.card

def settledRank {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Nat :=
  update.settledKeys.card

def newDebtRank {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Nat :=
  update.newDebtKeys.card

/-- `C(H,a) = settledRank(H,a) - newDebtRank(H,a)` on one exact actual
obligation update. -/
def closureGain {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Int :=
  closureGainOf update.settledKeys update.newDebtKeys

theorem closureGain_eq_settledRank_sub_newDebtRank
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) :
    closureGain update =
      Int.ofNat (settledRank update) - Int.ofNat (newDebtRank update) :=
  rfl

/-- Multiple consumer readouts of one source obligation deduplicate without
altering the unique compiler update or its closure gain. -/
theorem closureGain_ignores_duplicate_consumer_readout
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply)
    (key : face.SourceKey) (rest : List face.SourceKey) :
    update.settledReadoutKeys (key :: key :: rest) =
        update.settledReadoutKeys (key :: rest) ∧
      update.newDebtReadoutKeys (key :: key :: rest) =
        update.newDebtReadoutKeys (key :: rest) ∧
      closureGain update = closureGain update :=
  ⟨update.settledReadoutKeys_duplicate key rest,
    update.newDebtReadoutKeys_duplicate key rest, rfl⟩

/-! ## Invariance under generated key relabelling -/

/-- One bijection of obligation keys carries both rank sets.  This is the
readout contract induced by colour exchange or a local graph isomorphism. -/
structure ClosureKeyPresentationEquivalence
    {LeftKey : Type u} {RightKey : Type v}
    [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftSettled leftDebt : Finset LeftKey)
    (rightSettled rightDebt : Finset RightKey) where
  keyEquiv : LeftKey ≃ RightKey
  settled_image : leftSettled.image keyEquiv = rightSettled
  debt_image : leftDebt.image keyEquiv = rightDebt

namespace ClosureKeyPresentationEquivalence

theorem settled_card_eq
    {LeftKey : Type u} {RightKey : Type v}
    [DecidableEq LeftKey] [DecidableEq RightKey]
    {leftSettled leftDebt : Finset LeftKey}
    {rightSettled rightDebt : Finset RightKey}
    (equivalence : ClosureKeyPresentationEquivalence leftSettled leftDebt
      rightSettled rightDebt) :
    leftSettled.card = rightSettled.card := by
  have imageCard := Finset.card_image_of_injective leftSettled
    equivalence.keyEquiv.injective
  rw [equivalence.settled_image] at imageCard
  exact imageCard.symm

theorem debt_card_eq
    {LeftKey : Type u} {RightKey : Type v}
    [DecidableEq LeftKey] [DecidableEq RightKey]
    {leftSettled leftDebt : Finset LeftKey}
    {rightSettled rightDebt : Finset RightKey}
    (equivalence : ClosureKeyPresentationEquivalence leftSettled leftDebt
      rightSettled rightDebt) :
    leftDebt.card = rightDebt.card := by
  have imageCard := Finset.card_image_of_injective leftDebt
    equivalence.keyEquiv.injective
  rw [equivalence.debt_image] at imageCard
  exact imageCard.symm

theorem closureGainOf_eq
    {LeftKey : Type u} {RightKey : Type v}
    [DecidableEq LeftKey] [DecidableEq RightKey]
    {leftSettled leftDebt : Finset LeftKey}
    {rightSettled rightDebt : Finset RightKey}
    (equivalence : ClosureKeyPresentationEquivalence leftSettled leftDebt
      rightSettled rightDebt) :
    closureGainOf leftSettled leftDebt =
      closureGainOf rightSettled rightDebt := by
  simp only [closureGainOf, equivalence.settled_card_eq,
    equivalence.debt_card_eq]

end ClosureKeyPresentationEquivalence

/-- Presentation-level key relabelling preserves the cardinality readout.
This theorem does not claim that the relabelling was generated by an actual
source face; `ClosureInvariance` supplies that stronger mouth. -/
theorem closureGain_keyPresentation_invariant
    {LeftKey : Type u} {RightKey : Type v}
    [DecidableEq LeftKey] [DecidableEq RightKey]
    {leftSettled leftDebt : Finset LeftKey}
    {rightSettled rightDebt : Finset RightKey}
    (presentation : ClosureKeyPresentationEquivalence leftSettled leftDebt
      rightSettled rightDebt) :
    closureGainOf leftSettled leftDebt =
      closureGainOf rightSettled rightDebt :=
  presentation.closureGainOf_eq


/-! ## Strategic readouts -/

def MultiPurposeMove {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Prop :=
  1 < closureGain update

/-- Maintenance debit is exactly the deduplicated new-debt rank. -/
def MaintenanceDebit {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Nat :=
  newDebtRank update

/-- A heavy move generates at least two independent maintenance debts. -/
def HeavyMove {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Prop :=
  2 ≤ MaintenanceDebit update

/-- Continuation is closure-coherent when generated debt does not outrank
settled independent obligations. -/
def ContinuationCoherent {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Prop :=
  newDebtRank update ≤ settledRank update

def BadMove {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Prop :=
  ¬ ContinuationCoherent update

end Go
end ProcessGame
end SaturationMonoid
