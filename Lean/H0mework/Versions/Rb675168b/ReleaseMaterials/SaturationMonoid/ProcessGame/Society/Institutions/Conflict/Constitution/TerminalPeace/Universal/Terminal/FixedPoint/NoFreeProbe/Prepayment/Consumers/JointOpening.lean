import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Compiler
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.JointOpening

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.JointOpening

open Capitalism.Universal.Source.Program
open Clearance.Joint.OriginalExchange hiding offers

noncomputable section

theorem the_original_exchange_installs_the_prepaid_scheduler
    (policyReplies : Replies Bool Bool Bool Unit Unit) (tariff : Tariff Bool Bool Bool Unit Unit)
    (orders : PaymentOrders Bool Bool Bool Unit Unit) :
    ∃ first credit opening,
      compilePrepaidPeace loss replies reserve [grow] FixedPoint.JointOpening.offers policyReplies tariff orders =
        .installed first credit opening ∧
      opening.source.source.word.length ≤ 9 ∧ opening.installation.read = orders ∧
      ∀ (policy : AdaptivePolicy (RawLaw Bool Bool Bool Unit Unit × RawEvent Bool Bool Bool Unit Unit)
          Bool Bool Bool Unit Unit),
        (∀ n, HEq (opening.run policy n).1.ledger.stack opening.source.source.entry.current.ledger.stack) ∧
        ∀ start bound, ∃ n ≥ start, bound < (opening.run policy n).1.physical.raw.clock := by
  obtain ⟨first, credit, prior, actual, short, _, _⟩ :=
    NoFreeProbe.JointOpening.the_original_joint_exchange_installs_probe_protection policyReplies tariff
  obtain ⟨opening, installed, same⟩ := installs_on_the_same_jointly_cleared_entrance
    loss replies reserve [grow] FixedPoint.JointOpening.offers policyReplies tariff orders actual
  refine ⟨first, credit, opening, installed, same ▸ short, rfl, fun policy => ⟨opening.run_keeps_the_original_stack policy, ?_⟩⟩
  rw [opening.run_reads_the_same_original_scheduler]
  exact original_clock_is_cofinal opening.source.installation.read (fun current => registeredTerms current)
    opening.home opening.installation.read policyReplies opening.current policy

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.JointOpening
