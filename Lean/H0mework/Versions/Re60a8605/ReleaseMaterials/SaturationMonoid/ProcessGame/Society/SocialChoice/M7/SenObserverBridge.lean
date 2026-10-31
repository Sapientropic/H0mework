import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.SocialChoice.M7.PreferenceReadout

/-!
# Sen-style visible liberty axioms and authority strengthening

The standard visible bundle contains unrestricted preference domain, Pareto,
and minimal liberty: two distinct agents each control at least one nontrivial
personal pair in both directions.  Those axioms constrain collective
preference but do not encode occurrence identity or source-native authority.
The latter is isolated as an explicit extra completeness assumption and
rejected by the M6 attachment boundary.

This bridge neither states nor assumes Sen's classical liberal paradox.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace SocialChoice
namespace M7
namespace SenObserverBridge

open Observer

universe uAgent uAlternative uOccurrence uVisible uHidden uResidual

variable {Agent : Type uAgent}
variable {Alternative : Type uAlternative}
variable {Occurrence : Type uOccurrence}
variable {Visible : Type uVisible}
variable {Hidden : Type uHidden}
variable {Residual : Type uResidual}

/-- Visible individual preference profiles and collective weak preference. -/
structure SenPreferenceReadout where
  preferenceReadout : Visible → PreferenceProfile Agent Alternative
  collectiveReadout : Visible → WeakPreference Alternative

namespace SenPreferenceReadout

variable (rule : SenPreferenceReadout
  (Agent := Agent) (Alternative := Alternative) (Visible := Visible))

/-- One agent has personal decisiveness over one nontrivial pair in both
directions. -/
def HasPersonalDecisiveness
    (agent : Agent) (left right : Alternative) : Prop :=
  left ≠ right ∧
    ∀ visible,
      (WeakPreference.Strict
          (rule.preferenceReadout visible agent) left right →
        WeakPreference.Strict
          (rule.collectiveReadout visible) left right) ∧
      (WeakPreference.Strict
          (rule.preferenceReadout visible agent) right left →
        WeakPreference.Strict
          (rule.collectiveReadout visible) right left)

end SenPreferenceReadout

/-- Standard visible unrestricted-domain, Pareto, and minimal-liberty bundle. -/
structure SenVisibleAxiomBundle
    (rule : SenPreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible)) :
    Prop where
  unrestrictedDomain : Function.Surjective rule.preferenceReadout
  pareto : ∀ visible left right,
    (∀ agent, WeakPreference.Strict
      (rule.preferenceReadout visible agent) left right) →
      WeakPreference.Strict (rule.collectiveReadout visible) left right
  minimalLiberty : ∃ firstAgent secondAgent : Agent,
    firstAgent ≠ secondAgent ∧
      (∃ firstLeft firstRight : Alternative,
        rule.HasPersonalDecisiveness firstAgent firstLeft firstRight) ∧
      (∃ secondLeft secondRight : Alternative,
        rule.HasPersonalDecisiveness secondAgent secondLeft secondRight)

/-- Explicit nonstandard strengthening: the collective visible preference
must decode actual occurrence authority. -/
structure SenOccurrenceAuthorityCompleteness
    (O : AuthorityObserver Occurrence Visible Residual)
    (rule : SenPreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible))
    (_standard : SenVisibleAxiomBundle rule) where
  authorityDecode : WeakPreference Alternative → Residual
  collective_recovers_authority : ∀ occurrence,
    authorityDecode (rule.collectiveReadout (O.forget occurrence)) =
      O.authorityK occurrence

variable {O : AuthorityObserver Occurrence Visible Residual}
variable {rule : SenPreferenceReadout
  (Agent := Agent) (Alternative := Alternative) (Visible := Visible)}
variable {standard : SenVisibleAxiomBundle rule}

def collectiveOccurrenceReadout
    (O : AuthorityObserver Occurrence Visible Residual)
    (rule : SenPreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible)) :
    OccurrenceReadout Occurrence (WeakPreference Alternative) :=
  OccurrenceReadout.ofVisible O rule.collectiveReadout

def collectiveReadoutFactorization
    (O : AuthorityObserver Occurrence Visible Residual)
    (rule : SenPreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible)) :
    ReadoutFactorization O (collectiveOccurrenceReadout O rule) :=
  ReadoutFactorization.ofVisible O rule.collectiveReadout

namespace SenOccurrenceAuthorityCompleteness

def toAuthorityCompleteReadout
    (complete : SenOccurrenceAuthorityCompleteness O rule standard) :
    AuthorityCompleteReadoutAt O (collectiveOccurrenceReadout O rule) where
  decodeAuthority := complete.authorityDecode
  readsActualAuthority := complete.collective_recovers_authority

end SenOccurrenceAuthorityCompleteness

/-- Only the explicit authority strengthening generates the generic M7
authority factorization. -/
def authorityFactorization
    (complete : SenOccurrenceAuthorityCompleteness O rule standard) :
    AuthorityFactorization O :=
  (collectiveReadoutFactorization O rule).toAuthorityFactorization
    complete.toAuthorityCompleteReadout

/-- Generated-boundary verdict for the nonstandard Sen authority
strengthening. -/
theorem senAuthorityStrengtheningNoGo
    {vertical : AuthorityChangingVerticalAutomorphism O}
    {rooted : RootedObserverObstructionAt vertical}
    (attachment : SourceGeneratedObserverAttachingDirectionAt rooted) :
    ¬ Nonempty (SenOccurrenceAuthorityCompleteness O rule standard) := by
  rintro ⟨complete⟩
  exact attachment.boundary_rejectsAuthorityCompleteReadout
    (collectiveReadoutFactorization O rule)
    complete.toAuthorityCompleteReadout

section HiddenFibreControl

variable (rule)
variable (extension : HiddenFibreExtension Hidden Residual)

theorem preferenceReadouts_hidden_invariant
    (visible : Visible) (firstHidden secondHidden : Hidden) :
    HiddenFibreExtension.pullback rule.preferenceReadout
        (visible, firstHidden) =
        HiddenFibreExtension.pullback rule.preferenceReadout
          (visible, secondHidden) ∧
      HiddenFibreExtension.pullback rule.collectiveReadout
        (visible, firstHidden) =
        HiddenFibreExtension.pullback rule.collectiveReadout
          (visible, secondHidden) :=
  ⟨rfl, rfl⟩

/-- Standard Pareto and minimal liberty survive projection unchanged, while
the generated hidden-fibre boundary still rejects authority factorization. -/
theorem standardSenAxiomsDoesNotForceAuthority
    (standardAxioms : SenVisibleAxiomBundle rule)
    (visible : Visible) :
    ¬ (SenVisibleAxiomBundle rule →
      Nonempty (AuthorityFactorization
        (HiddenFibreExtension.observer
          (Visible := Visible) extension))) := by
  intro standardForcesAuthority
  exact HiddenFibreExtension.attachment_noAuthorityFactorization
    extension visible
    (standardForcesAuthority standardAxioms)

end HiddenFibreControl

end SenObserverBridge
end M7
end SocialChoice
end Society
end ProcessGame
end SaturationMonoid
