import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRenewal
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Consumers.Orders

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer.RevisedOrders

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open FixedPoint.NoFreeProbe
open FixedPoint.OpenPeace.Network.Runtime.OriginalOrders (quote)
open private programmeOrder from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Consumers.Original
open private harmless admits_one from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.Original

noncomputable section

def shifted := { revised with initial := { revised.initial with clock := revised.initial.clock + 1 } }

def dropLocal := { revised with localAttempts := fun _ => [] }

private def signedAt (slot : Fin 2) : Proposal Bool Bool Bool Unit Unit :=
  let wire := (Runtime.OriginalOrders.proposal slot.succ).wire
  ⟨wire, if slot.val = 0 then shifted else dropLocal⟩

def proposal (home : AnyAuthoritativeRootCurrent.{0}) (slot : Fin 2) : Proposal Bool Bool Bool Unit Unit :=
  let literal := signedAt slot
  { literal with wire := { literal.wire with home := home } }

def openPayment : OpenOrders Bool Bool Bool Unit Unit :=
  fun clock bid programme person =>
    [signedAt 0, signedAt 1].any fun attempt => programmeOrder attempt clock bid programme person

theorem original_orders_apply (home : AnyAuthoritativeRootCurrent.{0}) (slot : Fin 2) :
    (Input.proposal (proposal home slot)).orders Runtime.OriginalOrders.payment openPayment
      (proposal home slot).wire.clock (bill quote (proposal home slot).wire) true = true := by
  let old := Runtime.OriginalOrders.proposal slot.succ
  have original := Runtime.OriginalOrders.original_order slot.succ
  change (Runtime.OriginalOrders.payment old.wire.clock (bill quote old.wire) true &&
    Runtime.OriginalOrders.openPayment old.wire.clock (bill quote old.wire) old.programme true) = true at original
  let literal := signedAt slot
  change (Runtime.OriginalOrders.payment old.wire.clock (bill quote old.wire) true &&
    openPayment literal.wire.clock (bill quote literal.wire) literal.programme true) = true
  refine Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp original).1, ?_⟩
  have listed : literal ∈ [signedAt 0, signedAt 1] := by
    have choice : slot = 0 ∨ slot = 1 := by
      have inRange := slot.isLt
      have indices : slot.val = 0 ∨ slot.val = 1 := by omega
      rcases indices with zero | one
      · exact .inl (Fin.ext zero)
      · exact .inr (Fin.ext one)
    rcases choice with rfl | rfl <;> simp [literal]
  apply List.any_eq_true.mpr
  refine ⟨literal, listed, ?_⟩
  classical
  unfold programmeOrder
  exact decide_eq_true ⟨rfl, rfl, rfl, rfl⟩

theorem public_screen (home : AnyAuthoritativeRootCurrent.{0}) (slot : Fin 2) :
    fundingScreen quote (proposal home slot).wire = true :=
  (admits_one harmless).passes_public_screen

theorem original_clock (home : AnyAuthoritativeRootCurrent.{0}) (slot : Fin 2) :
    (proposal home slot).wire.clock = 5 + (slot.val : ℚ) := by
  change (Runtime.OriginalOrders.proposal slot.succ).wire.clock = _
  rw [Runtime.OriginalOrders.clock_at]
  change Settlement.settledCut.raw.clock + ((slot.val + 1 : Nat) : ℚ) = _
  rw [Settlement.settled_raw, Nat.cast_add, Nat.cast_one]
  change 4 + ((slot.val : ℚ) + 1) = 5 + _
  ring

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer.RevisedOrders
