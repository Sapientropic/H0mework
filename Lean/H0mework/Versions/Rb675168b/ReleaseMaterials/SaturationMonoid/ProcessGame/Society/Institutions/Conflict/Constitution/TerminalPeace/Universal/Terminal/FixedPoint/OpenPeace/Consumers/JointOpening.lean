import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Universal
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Consumers.JointOpening

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.JointOpening

open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)
open Clearance.Joint.OriginalExchange hiding offers

noncomputable section

theorem the_original_exchange_installs_open_permanent_peace
    (policyReplies : Replies Bool Bool Bool Unit Unit) (tariff : Tariff Bool Bool Bool Unit Unit)
    (orders : PaymentOrders Bool Bool Bool Unit Unit) (openOrders : OpenOrders Bool Bool Bool Unit Unit) :
    ∃ first credit opening,
      compileOpenPeace loss replies reserve [grow] FixedPoint.JointOpening.offers policyReplies tariff orders openOrders =
        .installed first credit opening ∧
      opening.source.source.source.source.word.length ≤ 9 ∧ opening.initial.language.covered = ∅ ∧
      ∀ policy : Policy Bool Bool Bool Unit Unit,
        (∀ n, ∀ row ∈ (opening.run policy n).1.adaptive.native.ledger.stack.balances, row.2.remaining = 0) ∧
        ∀ start bound, ∃ n ≥ start, bound < (opening.run policy n).1.adaptive.native.physical.raw.clock := by
  obtain ⟨first, credit, prepaid, actual, short, _, _⟩ :=
    NoFreeProbe.Prepayment.JointOpening.the_original_exchange_installs_the_prepaid_scheduler policyReplies tariff orders
  obtain ⟨adaptive, installed, samePrepaid⟩ := AdaptivePeace.installs_at_the_same_prepaid_entrance
    loss replies reserve [grow] FixedPoint.JointOpening.offers policyReplies tariff orders actual
  obtain ⟨opening, written, sameAdaptive⟩ := installs_at_the_same_original_entrance
    loss replies reserve [grow] FixedPoint.JointOpening.offers policyReplies tariff orders openOrders installed
  refine ⟨first, credit, opening, written, ?_, opening.no_future_expressions_are_installed, ?_⟩
  · rw [sameAdaptive, samePrepaid]
    exact short
  · intro policy
    have guarantee := opening.open_future_permanent_peace
      (Syntax := fun _ _ _ _ _ => Input Bool Bool Bool Unit Unit) (fun _ _ _ _ _ => some) policy
    exact ⟨fun n => ((guarantee.2.1 n).2).2, guarantee.2.2.2.2.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.JointOpening
