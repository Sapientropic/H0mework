import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Compiler
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Consumers.JointOpening

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.JointOpening

open Capitalism.Universal.Source.Program
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)
open Clearance.Joint.OriginalExchange hiding offers

noncomputable section

theorem the_original_exchange_installs_adaptive_peace
    (policyReplies : Replies Bool Bool Bool Unit Unit) (tariff : Tariff Bool Bool Bool Unit Unit)
    (orders : PaymentOrders Bool Bool Bool Unit Unit) :
    ∃ first credit opening,
      compileAdaptivePeace loss replies reserve [grow] FixedPoint.JointOpening.offers policyReplies tariff orders =
        .installed first credit opening ∧
      opening.source.source.source.word.length ≤ 9 ∧ opening.initial.covered = ∅ ∧
      ∀ (policy : Policy Bool Bool Bool Unit Unit),
        (∀ n, HEq (opening.run policy n).1.native.ledger.stack opening.source.source.source.entry.current.ledger.stack) ∧
        ∀ start bound, ∃ n ≥ start, bound < (opening.run policy n).1.native.physical.raw.clock := by
  obtain ⟨first, credit, prior, actual, short, _, _⟩ :=
    Prepayment.JointOpening.the_original_exchange_installs_the_prepaid_scheduler policyReplies tariff orders
  obtain ⟨opening, installed, same⟩ := installs_at_the_same_prepaid_entrance
    loss replies reserve [grow] FixedPoint.JointOpening.offers policyReplies tariff orders actual
  refine ⟨first, credit, opening, installed, same ▸ short, opening.initial_has_no_preset_amendments, ?_⟩
  intro policy
  exact ⟨opening.run_keeps_the_original_stack policy,
    original_clock_is_cofinal opening.source.source.installation.read opening.source.home
      opening.source.installation.read policyReplies opening.initial policy⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.JointOpening
