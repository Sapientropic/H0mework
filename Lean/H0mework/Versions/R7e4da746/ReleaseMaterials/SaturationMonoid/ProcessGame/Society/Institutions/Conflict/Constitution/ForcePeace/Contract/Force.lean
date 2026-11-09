import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Contract.Policy
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Fibre.Characterization
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Fibre.Viability
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Time
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Uniform

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open PublicFunction.Mandate Counterplay

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]
  {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port (State Party Technology) Instrument
local notation "Pos" => Position Party Good Port (State Party Technology) Instrument CivilView OpponentView
local notation "Plan" => CivilPlan Party Good Port (State Party Technology) Instrument CivilView
local notation "Opponent" => List OpponentView → Input
local notation "Arbitration" => Nat → C → Turn

variable (game : Game Party Good Port (State Party Technology) Instrument Community CivilView OpponentView)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (actor : Party)

omit [DecidableEq Technology] in
theorem peace_through_every_constitutional_prefix_iff_the_actual_observation_fibres_close :
    (∃ plan : Plan, (∀ seen, signedChoice game scope actor seen (plan.submit seen)) ∧
      game.PreservesAllowedPrefixes (constitutionalMove game) plan) ↔
    ∃ family : Pos → Prop, family game.start ∧
      game.FibreCloses (signedChoice game scope actor) (constitutionalMove game) family :=
  game.one_observation_plan_preserves_the_allowed_prefixes_iff_a_family_closes
    (signedChoice game scope actor) (constitutionalMove game)

variable {base : RawLaw Party Good Port Technology Instrument}

/-- The same local choices generate a policy before the rivals move,
an actual legal play, and protection of every legal continuation. -/
theorem the_original_live_fibres_force_the_submitted_withdrawal_and_preserve_independent_exit
    (installed : Emergency.Installed (submittedCut game) base scope)
    (admitted : ReviewAvailable (submittedCut game) ∧
      (law base scope).Valid (submittedCut game).raw (withdrawal scope (submittedCut game) actor))
    (family : Pos → Prop) (initial : family game.start)
    (closed : game.FibreCloses (signedChoice game scope actor) (constitutionalMove game) family)
    (live : Game.LocalMenusNonempty (constitutionalMove game) family
      (game.compileFibre (signedChoice game scope actor) (constitutionalMove game) family closed)) :
    ∃ plan : Plan, (∀ seen, signedChoice game scope actor seen (plan.submit seen)) ∧
      game.PreservesAllowedPrefixes (constitutionalMove game) plan ∧
      game.WinsWithin (SignedConstitutionalPlay game scope actor) (game.WithdrawalComplete base scope actor) plan := by
  let plan := game.compileFibre (signedChoice game scope actor) (constitutionalMove game) family closed
  let actual := game.compileAllowedReplay (signedChoice game scope actor) (constitutionalMove game)
    family initial closed live
  have chosen := game.compileFibre_uses_the_original_civil_choice _ _ family closed
  have protects := game.compileFibre_preserves_each_allowed_original_prefix _ _ family initial closed
  refine ⟨plan, chosen, protects, ⟨actual.opponent, actual.arbitrate, chosen, actual.legal⟩, ?_⟩
  intro opponent schedule lawful
  have exact := an_admitted_constitutional_policy_keeps_its_exact_payment_and_life_at_every_cut
    game scope actor plan opponent schedule installed admitted chosen protects lawful.2
  exact ⟨exact.1, reservedRank game + 1, exact.2.1⟩

/-- Losing the right to force peace has an original path witness whenever
the policy has a legal interleaving. The quantifier over policies stays outside. -/
theorem no_policy_forces_peace_iff_each_has_a_native_counter_or_no_legal_interleaving :
    (¬ ∃ plan : Plan, game.WinsWithin (SignedConstitutionalPlay game scope actor)
      (game.WithdrawalComplete base scope actor) plan) ↔
    ∀ plan : Plan, ¬ Game.HasAllowed (SignedConstitutionalPlay game scope actor) plan ∨
      game.CounterWithin (SignedConstitutionalPlay game scope actor) (game.WithdrawalComplete base scope actor) plan :=
  game.no_winning_policy_iff_each_has_no_allowed_play_or_an_actual_counter _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
