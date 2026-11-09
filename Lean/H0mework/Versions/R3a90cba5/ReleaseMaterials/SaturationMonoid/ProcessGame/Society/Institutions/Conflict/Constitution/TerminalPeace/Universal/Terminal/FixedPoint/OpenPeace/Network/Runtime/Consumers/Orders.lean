import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Consumers.Scopes
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.OriginalOrders

open Capitalism.Universal.Source.Program
open NoFreeProbe
open NoFreeProbe.Prepayment (CanPrepay PaymentOrders registeredTerms)
open OriginalScopes
open Supply.Consumers (refillWord)
open private tariff wireFor harmless admits_one from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.Original
open private signedOrder own_literal_order original_budget from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Consumers.Original
open private programmeOrder from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Consumers.Original

noncomputable section

private abbrev Packet := Wire Bool Bool Bool Unit Unit
private abbrev Attempt := OpenPeace.Proposal Bool Bool Bool Unit Unit
private abbrev Programme := Capitalism.Universal.Root.ProgrammeSource.Input Bool Bool Bool Unit Unit
private abbrev initial := OriginalReview.initial
private abbrev baseWire := wireFor harmless

private def literalProposal (ordinal : Fin 3) : Attempt :=
  ⟨{ baseWire with clock := initial.physical.raw.clock + (ordinal.val : ℚ) },
    if ordinal.val = 0 then dropLocal else shifted⟩

private def authorized : List Attempt := [literalProposal 0, literalProposal 1, literalProposal 2]

def payment : PaymentOrders Bool Bool Bool Unit Unit :=
  fun clock bill payer => authorized.any fun attempt => signedOrder attempt.wire clock bill payer

def openPayment : OpenOrders Bool Bool Bool Unit Unit :=
  fun clock bill programme payer => authorized.any fun attempt => programmeOrder attempt clock bill programme payer

def quote := tariff

def tariffWrite := Installation.Live.publish initial.ledger quote true
def paymentWrite := Installation.Live.publish tariffWrite.state payment true
def registration := paymentWrite.state.resident.erase

def proposal (ordinal : Fin 3) : Attempt :=
  { literalProposal ordinal with wire := { (literalProposal ordinal).wire with home := registration } }

def wrongSigner (ordinal : Fin 3) : Attempt :=
  { proposal ordinal with wire := { (proposal ordinal).wire with sender := false, payer := false } }

theorem clock_at (ordinal : Fin 3) :
    (proposal ordinal).wire.clock = initial.physical.raw.clock + (ordinal.val : ℚ) :=
  rfl

theorem original_order (ordinal : Fin 3) :
    (Input.proposal (proposal ordinal)).orders payment openPayment
      (proposal ordinal).wire.clock (bill quote (proposal ordinal).wire) true = true := by
  let exactProposal := literalProposal ordinal
  have listed : exactProposal ∈ authorized := by
    have index : ordinal = 0 ∨ ordinal = 1 ∨ ordinal = 2 := by
      have bound := ordinal.isLt
      have value : ordinal.val = 0 ∨ ordinal.val = 1 ∨ ordinal.val = 2 := by omega
      rcases value with zero | one | two
      · exact .inl (Fin.ext zero)
      · exact .inr (.inl (Fin.ext one))
      · exact .inr (.inr (Fin.ext two))
    rcases index with rfl | rfl | rfl <;> simp [exactProposal, authorized]
  change (payment exactProposal.wire.clock (bill tariff exactProposal.wire) true &&
    openPayment exactProposal.wire.clock (bill tariff exactProposal.wire) exactProposal.programme true) = true
  refine Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨exactProposal, listed, ?_⟩,
    List.any_eq_true.mpr ⟨exactProposal, listed, ?_⟩⟩
  · exact own_literal_order exactProposal.wire
  · change programmeOrder exactProposal exactProposal.wire.clock (bill tariff exactProposal.wire)
      exactProposal.programme exactProposal.wire.payer = true
    simp [programmeOrder]

theorem wrong_signer_passes_public_screen (ordinal : Fin 3) :
    fundingScreen quote (wrongSigner ordinal).wire = true :=
  (admits_one harmless).passes_public_screen

theorem wrong_signer_has_no_order (ordinal : Fin 3) (clock : ℚ) :
    (Input.proposal (wrongSigner ordinal)).orders payment openPayment clock
      (bill quote (wrongSigner ordinal).wire) false = false := by
  change (payment clock (bill tariff (wrongSigner ordinal).wire) false &&
    openPayment clock (bill tariff (wrongSigner ordinal).wire) (wrongSigner ordinal).programme false) = false
  have absent : payment clock (bill tariff (wrongSigner ordinal).wire) false = false := by
    apply Bool.eq_false_of_not_eq_true
    intro approved
    obtain ⟨attempt, listed, signed⟩ := List.any_eq_true.mp approved
    have payer : attempt.wire.payer = true := by
      simp only [authorized, List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with rfl | rfl | rfl <;> rfl
    simp [signedOrder, payer] at signed
  simp [absent]

theorem can_pay (native : OriginalReview.State) (ordinal : Fin 3)
    (stamp : (proposal ordinal).wire.clock = native.physical.raw.clock)
    (same : native.programme = OriginalRecipe.programme) (word : native.recipe.move.word = refillWord) :
    CanPrepay (registeredTerms : OriginalReview.State → _)
      quote registration ((Input.proposal (proposal ordinal)).orders payment openPayment)
      (registeredTerms native) native.physical.raw.clock (proposal ordinal).wire := by
  refine ⟨rfl, stamp, (admits_one harmless).passes_public_screen, by change true ∈ [false, true]; decide, ?_,
    (Prepayment.uniform_registered_budget_iff native _).mpr ?_⟩
  · rw [← stamp]
    exact original_order ordinal
  · rw [congrArg (fun input : Programme => input.law) same, word]
    exact ⟨original_budget.legal, original_budget.nonnegative, original_budget.fits, original_budget.surplus⟩

theorem next_clock (native : OriginalReview.State) (same : native.programme = OriginalRecipe.programme) :
    native.move.next.clock = native.physical.raw.clock + 1 := by
  change (native.programme.law.next native.physical.raw native.move.word).clock = _
  rw [congrArg (fun input : Programme => input.law) same]
  change native.physical.raw.clock + max 0 (1 : ℚ) = _
  norm_num

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.OriginalOrders
