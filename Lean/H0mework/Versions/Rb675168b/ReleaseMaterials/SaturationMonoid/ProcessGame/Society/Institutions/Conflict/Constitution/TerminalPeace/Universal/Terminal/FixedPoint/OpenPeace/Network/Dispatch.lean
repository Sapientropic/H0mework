import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Revision
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

variable (tariff : Tariff Party Good Port Technology Instrument) (home : AnyAuthoritativeRootCurrent.{0})
  (orders : PaymentOrders Party Good Port Technology Instrument)
  (openOrders : OpenOrders Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (before : OpenPeace.State (seed := seed) (cut := cut) (community := community) origin people quantum)
  (input : Input Party Good Port Technology Instrument)

local notation "Visit" => OpenPeace.source tariff home orders openOrders replies before input
local notation "Scope" => OpenPeace.scope tariff home orders openOrders replies before input
local notation "Ordinary" => OpenPeace.next tariff home orders openOrders replies before input

/-- The audit consumes the original charged refusal's resident, before
any change in refusal language is installed. -/
abbrev reviewedLedger := (Visit).next.native.ledger

local notation "Ledger" => reviewedLedger tariff home orders openOrders replies before input

theorem a_new_scope_has_an_actual_payment (novel : ¬ Scope ⊆ before.language.covered) :
    ∃ wire, (Visit).source.paidWire = some wire := by
  cases posted : (Visit).source.paidWire with
  | none =>
    have erased := no_unpaid_scope tariff home orders openOrders replies before input posted
    exact (novel (erased.symm ▸ Set.empty_subset _)).elim
  | some wire => exact ⟨wire, rfl⟩

variable {oldU7 : U7ProducerCalculus (reviewedLedger tariff home orders openOrders replies before input).world}
  (oldCalculus : U7ObstructionEvolutionCalculus
    (reviewedLedger tariff home orders openOrders replies before input).world oldU7)

def checkedFailure (novel : ¬ Scope ⊆ before.language.covered) :=
  rootedFailure Ledger before.language Scope (LocalU7.native ⟨oldU7, oldCalculus⟩) novel

def checkedRevision (novel : ¬ Scope ⊆ before.language.covered) :=
  revised Ledger before.language Scope (LocalU7.native ⟨oldU7, oldCalculus⟩) novel

def checkedSuccessor (novel : ¬ Scope ⊆ before.language.covered) :=
  generatedNext Ledger before.language Scope (LocalU7.native ⟨oldU7, oldCalculus⟩) novel

/-- The dispatcher decides novelty from the posted source scope. A
novel branch returns the realized whole-network first-write successor. -/
def nextCurrent : AnyAuthoritativeRootCurrent := by
  classical
  exact if novel : ¬ Scope ⊆ before.language.covered then
    (checkedSuccessor tariff home orders openOrders replies before input oldCalculus novel).erase
  else (Ordinary).adaptive.native.ledger.resident.erase

theorem paid_novel_branch (novel : ¬ Scope ⊆ before.language.covered) :
    nextCurrent tariff home orders openOrders replies before input oldCalculus =
      (checkedSuccessor tariff home orders openOrders replies before input oldCalculus novel).erase := by
  simp only [nextCurrent, dif_pos novel]

theorem covered_branch (known : Scope ⊆ before.language.covered) :
    nextCurrent tariff home orders openOrders replies before input oldCalculus =
      (Ordinary).adaptive.native.ledger.resident.erase := by
  simp only [nextCurrent, dif_neg (not_not.mpr known)]

theorem no_unpaid_network_revision
    (unpaid : (Visit).source.paidWire = none) :
    nextCurrent tariff home orders openOrders replies before input oldCalculus =
      (Ordinary).adaptive.native.ledger.resident.erase := by
  apply covered_branch
  rw [no_unpaid_scope tariff home orders openOrders replies before input unpaid]
  exact Set.empty_subset _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
