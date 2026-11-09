import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Compiler
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.JointOpening

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.JointOpening

open Capitalism.Universal.Source.Program
open Clearance.Joint.OriginalExchange hiding offers

noncomputable section

/-- The joint exchange consumes the protected compiler at its reached
settlement. Every adaptive continuation runs the installed dispatch. -/
theorem the_original_joint_exchange_installs_probe_protection
    (policyReplies : Replies Bool Bool Bool Unit Unit) (tariff : Tariff Bool Bool Bool Unit Unit) :
    ∃ first credit opening,
      compileProtectedPeace loss replies reserve [grow] FixedPoint.JointOpening.offers policyReplies tariff =
        .installed first credit opening ∧
      opening.source.word.length ≤ 9 ∧ opening.installation.read = tariff ∧
      ∀ (policy : CoalitionPolicy Bool Bool Bool Unit Unit)
        (traffic : PresentationPolicy Bool Bool Bool Unit Unit),
        concurrentHistory opening.installation.read policyReplies opening.current policy traffic = opening.run policy ∧
        (∀ n, (opening.run policy n).1.ledger.stack.balances.map Prod.fst =
          (Occurrence.originState loss).stack.balances.map Prod.fst ∧
          ∀ row ∈ (opening.run policy n).1.ledger.stack.balances, row.2.remaining = 0) ∧
        ∀ start bound, ∃ n ≥ start, bound < (opening.run policy n).1.physical.raw.clock := by
  obtain ⟨first, credit, peace, actual, short, _, _, _⟩ :=
    FixedPoint.JointOpening.the_actual_exchange_installs_the_peace_fixed_point policyReplies
  obtain ⟨opening, installed, same⟩ := installs_at_the_same_original_entrance
    loss replies reserve [grow] FixedPoint.JointOpening.offers policyReplies tariff actual
  refine ⟨first, credit, opening, installed, same ▸ short, opening.reads_the_installed_tariff, ?_⟩
  intro policy traffic
  refine ⟨(arbitrary_parallel_presentations_have_no_effect opening.installation.read policyReplies opening.current
    policy traffic traffic).1, opening.every_cut_retains_the_original_paid_addresses policy, ?_⟩
  exact original_clock_is_cofinal opening.installation.read policyReplies opening.current policy

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.JointOpening
