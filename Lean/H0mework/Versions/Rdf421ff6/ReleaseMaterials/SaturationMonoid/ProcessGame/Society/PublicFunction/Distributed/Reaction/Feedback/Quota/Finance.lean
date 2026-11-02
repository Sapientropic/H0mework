import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Plan
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.PrefixCoupling

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Finance

open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code)
  (cut : Nat) (position : Repayment.Position Party Instrument)
  (site : Fin source.code.sites) (owner : source.code.siteParty site = position.debtor)

abbrev target := planned source input cut position site owner
abbrev originalAccount := account source cut
abbrev plannedAccount := account (target source input cut position site owner) cut
abbrev Transport := Native.Coupling.Match source.code source.input
  (target source input cut position site owner).input (originalAccount source cut)
  (plannedAccount source input cut position site owner)
abbrev Difference := Native.Coupling.Mismatch source.code source.input
  (target source input cut position site owner).input (originalAccount source cut)
  (plannedAccount source input cut position site owner)

structure Supported where
  transport : Transport source input cut position site owner
  actual_bound : amount source input cut position ≤ support (target source input cut position site owner) cut position

inductive Outcome where
  | supported (certificate : Supported source input cut position site owner)
  | different (witness : Difference source input cut position site owner)

def generate : Outcome source input cut position site owner :=
  match Native.Coupling.generate source.code source.input
      (target source input cut position site owner).input (originalAccount source cut)
      (plannedAccount source input cut position site owner) with
  | .mismatch witness => .different witness
  | .matched transport => .supported ⟨transport, by
      have same := transport.same_native_quota position.instrument position.debtor position.creditor
      change support (target source input cut position site owner) cut position = support source cut position at same
      rw [same]
      exact amount_is_native_supported source input cut position⟩

def Outcome.accepted : Outcome source input cut position site owner → Bool
  | .supported _ => true
  | .different _ => false

theorem Outcome.certificate : (outcome : Outcome source input cut position site owner) →
    outcome.accepted = true → Supported source input cut position site owner
  | .supported certificate, _ => certificate
  | .different _, impossible => False.elim (Bool.noConfusion impossible)

def verify := Native.Coupling.verify source.code source.input
  (target source input cut position site owner).input (originalAccount source cut)
  (plannedAccount source input cut position site owner)

theorem generated_transport_iff :
    (generate source input cut position site owner).accepted = true ↔
      Transport source input cut position site owner := by
  unfold generate
  cases Native.Coupling.generate source.code source.input
      (target source input cut position site owner).input (originalAccount source cut)
      (plannedAccount source input cut position site owner) with
  | matched transport => exact ⟨fun _ => transport, fun _ => rfl⟩
  | mismatch witness =>
      exact ⟨fun impossible => Bool.noConfusion impossible,
        fun matched => False.elim (matched.excludes_every_concrete_mismatch witness)⟩

theorem independent_verifier_agrees :
    verify source input cut position site owner = true ↔
      (generate source input cut position site owner).accepted = true :=
  (Native.Coupling.verify_iff _ _ _ _ _).trans (generated_transport_iff _ _ _ _ _ _).symm

theorem source_generates_complete_transport : Transport source input cut position site owner :=
  Native.Coupling.State.every_prior_account_is_financially_coupled source cut _ _ (Nat.le_refl _)

theorem every_generated_transport_is_supported : (generate source input cut position site owner).accepted = true :=
  (generated_transport_iff source input cut position site owner).mpr
    (source_generates_complete_transport source input cut position site owner)

theorem generated_support : Supported source input cut position site owner :=
  Outcome.certificate source input cut position site owner (generate source input cut position site owner)
    (every_generated_transport_is_supported source input cut position site owner)

theorem every_generated_transport_is_independently_verified : verify source input cut position site owner = true :=
  (independent_verifier_agrees source input cut position site owner).mpr
    (every_generated_transport_is_supported source input cut position site owner)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Finance
