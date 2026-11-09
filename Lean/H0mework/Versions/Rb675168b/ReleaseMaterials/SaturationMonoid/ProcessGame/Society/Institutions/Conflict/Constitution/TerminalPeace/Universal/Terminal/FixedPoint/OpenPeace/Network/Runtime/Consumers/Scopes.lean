import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Payment
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalReview

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.OriginalScopes

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Migration (sourceAlphabet)
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact (originalWord)
open NoFreeProbe (PaidReview)
open TerminalPeace.Supply (grow personalWord)
open private personal_registered from H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalRecipe

noncomputable section

private abbrev Programme := ProgrammeSource.Input Bool Bool Bool Unit Unit
private abbrev EffectAt := Effect Bool Bool Bool Unit Unit
private abbrev original := OriginalRecipe.programme
private abbrev exitWord := personalWord true
private abbrev exitClaim : Claim Bool Bool Bool Unit Unit := ([true], exitWord)

def exitEffect : EffectAt := .inl exitClaim
def termsEffect : EffectAt := .inr ()

/-- Remove local registrations while keeping every protected public term. -/
def dropLocal : Programme :=
  { original with localAttempts := fun _ => [] }

/-- Move only the declared origin of the programme. Its material
instructions, registrations and physical law still agree. -/
def shifted : Programme :=
  { original with initial := { original.initial with clock := original.initial.clock + 1 } }

private theorem the_original_personal_word_stays_paid (native : OriginalReview.State) :
    Supply.Period original OriginalReview.origin native.physical.raw [true] exitWord := by
  have base := OriginalRecipe.paidAt OriginalReview.origin Settlement.settledCut.raw [true] exitWord (by
    rw [Settlement.settled_raw]
    decide +kernel)
  let recipe := OriginalRecipe.originalRecipe OriginalReview.origin
  let extra := InReserve.extra Settlement.settledCut.raw native.physical.raw
  have nonnegative := native.reserved.extra_nonnegative
  have duration := recipe.law.positive.trans_le
    (recipe.law.duration extra nonnegative native.physical.raw.clock native.physical.raw.round)
  have later := base.after_reserve_and_clock recipe.law.timing recipe.law.reserve
    extra nonnegative native.physical.raw.clock native.physical.raw.round duration
  rwa [← native.reserved.exact_raw] at later

private theorem the_removed_word_is_absent (raw : TerminalPeace.Original.Raw) :
    ¬ Supply.Registered dropLocal raw exitWord := by
  intro registered
  have absent : grow true ∉ originalWord := by decide +kernel
  exact absent (registered (grow true) List.mem_cons_self)

variable {native : OriginalReview.State} {bid : ReviewBid Bool Bool Bool Unit Unit}

theorem dropLocal_loses_the_original_exit (same : native.programme = original) :
    exitClaim ∈ losses native dropLocal := by
  refine ⟨?_, fun kept => the_removed_word_is_absent native.physical.raw kept.1⟩
  unfold nativeContinuation
  rw [same]
  exact ⟨personal_registered native.physical.raw true, the_original_personal_word_stays_paid native⟩

theorem dropLocal_paid_has_exit (paid : PaidReview native bid) (same : native.programme = original) :
    exitEffect ∈ paidEffects paid dropLocal := by
  rw [exitEffect, paidEffects_loss, paidLosses_eq]
  exact dropLocal_loses_the_original_exit same

theorem dropLocal_paid_has_no_terms (paid : PaidReview native bid) (same : native.programme = original) :
    termsEffect ∉ paidEffects paid dropLocal := by
  rw [termsEffect, paidEffects_public_terms, same, not_not]
  rfl

theorem shifted_paid_scope (paid : PaidReview native bid) (same : native.programme = original) :
    paidEffects paid shifted = {termsEffect} := by
  have noLosses : paidLosses paid shifted = ∅ := by
    rw [paidLosses_eq]
    apply no_rewrite_of_existing_alphabet_has_no_losses
    · exact (congrArg ProgrammeSource.Input.law same).symm
    · intro request registered
      change request ∈ sourceAlphabet original native.physical.raw
      rwa [same] at registered
  have terms : ¬ KeepsPublicTerms native.programme shifted := by
    rw [same]
    intro kept
    have changed := congrArg (fun input : Programme => input.initial.clock) kept
    change original.initial.clock + 1 = original.initial.clock at changed
    linarith only [changed]
  ext effect
  cases effect with
  | inl claim => simp [paidEffects_loss, noLosses, termsEffect]
  | inr term =>
    cases term
    exact (paidEffects_public_terms paid shifted).trans ⟨fun _ => rfl, fun _ => terms⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.OriginalScopes
