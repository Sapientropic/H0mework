import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.SocialChoice.M7.PreferenceReadout

/-!
# Arrow-style visible axioms and occurrence-authority strengthening

The named standard bundle contains unrestricted domain, Pareto, IIA, and
non-dictatorship only.  These properties concern visible preference data and
do not recover hidden occurrence authority.  A separate, explicitly
nonstandard occurrence-authority completeness condition would make the
collective preference readout encode `K`; that strengthening is rejected by
an M6 generated attachment boundary.

No claim here is the classical Arrow theorem itself.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace SocialChoice
namespace M7
namespace ArrowObserverBridge

open Observer

universe uAgent uAlternative uOccurrence uVisible uHidden uResidual

variable {Agent : Type uAgent}
variable {Alternative : Type uAlternative}
variable {Occurrence : Type uOccurrence}
variable {Visible : Type uVisible}
variable {Hidden : Type uHidden}
variable {Residual : Type uResidual}

/-- Visible individual profiles together with the visible collective weak
preference returned by a social-welfare rule. -/
structure ArrowPreferenceReadout where
  preferenceReadout : Visible → PreferenceProfile Agent Alternative
  collectiveReadout : Visible → WeakPreference Alternative

/-- The standard visible Arrow axiom bundle.  Alternative-count hypotheses
belong to the classical impossibility theorem and are deliberately not
invented here; this bridge is polymorphic in both carrier types. -/
structure ArrowVisibleAxiomBundle
    (rule : ArrowPreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible)) :
    Prop where
  unrestrictedDomain : Function.Surjective rule.preferenceReadout
  pareto : ∀ visible left right,
    (∀ agent, WeakPreference.Strict
      (rule.preferenceReadout visible agent) left right) →
      WeakPreference.Strict (rule.collectiveReadout visible) left right
  independenceOfIrrelevantAlternatives :
    ∀ firstVisible secondVisible left right,
      (∀ agent,
        (rule.preferenceReadout firstVisible agent).ranks left right ↔
          (rule.preferenceReadout secondVisible agent).ranks left right) →
      (∀ agent,
        (rule.preferenceReadout firstVisible agent).ranks right left ↔
          (rule.preferenceReadout secondVisible agent).ranks right left) →
      ((rule.collectiveReadout firstVisible).ranks left right ↔
          (rule.collectiveReadout secondVisible).ranks left right) ∧
        ((rule.collectiveReadout firstVisible).ranks right left ↔
          (rule.collectiveReadout secondVisible).ranks right left)
  nonDictatorship : ∀ agent,
    ¬ ∀ visible left right,
      WeakPreference.Strict
          (rule.preferenceReadout visible agent) left right →
        WeakPreference.Strict (rule.collectiveReadout visible) left right

/-- Extra authority-completeness assumption absent from the standard Arrow
bundle: one decoder of the collective visible preference must recover the
source-native authority of every actual occurrence. -/
structure ArrowOccurrenceAuthorityCompleteness
    (O : AuthorityObserver Occurrence Visible Residual)
    (rule : ArrowPreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible))
    (_standard : ArrowVisibleAxiomBundle rule) where
  authorityDecode : WeakPreference Alternative → Residual
  collective_recovers_authority : ∀ occurrence,
    authorityDecode (rule.collectiveReadout (O.forget occurrence)) =
      O.authorityK occurrence

variable {O : AuthorityObserver Occurrence Visible Residual}
variable {rule : ArrowPreferenceReadout
  (Agent := Agent) (Alternative := Alternative) (Visible := Visible)}
variable {standard : ArrowVisibleAxiomBundle rule}

/-- Occurrence-level collective preference readout induced solely from the
visible social-welfare output. -/
def collectiveOccurrenceReadout
    (O : AuthorityObserver Occurrence Visible Residual)
    (rule : ArrowPreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible)) :
    OccurrenceReadout Occurrence (WeakPreference Alternative) :=
  OccurrenceReadout.ofVisible O rule.collectiveReadout

/-- The collective readout has a definitional visible factorization. -/
def collectiveReadoutFactorization
    (O : AuthorityObserver Occurrence Visible Residual)
    (rule : ArrowPreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible)) :
    ReadoutFactorization O (collectiveOccurrenceReadout O rule) :=
  ReadoutFactorization.ofVisible O rule.collectiveReadout

namespace ArrowOccurrenceAuthorityCompleteness

/-- Expose the extra Arrow authority-strengthening through the generic M7
readout-completeness interface. -/
def toAuthorityCompleteReadout
    (complete : ArrowOccurrenceAuthorityCompleteness O rule standard) :
    AuthorityCompleteReadoutAt O (collectiveOccurrenceReadout O rule) where
  decodeAuthority := complete.authorityDecode
  readsActualAuthority := complete.collective_recovers_authority

end ArrowOccurrenceAuthorityCompleteness

/-- The explicit authority strengthening, not the standard Arrow axioms,
constructs visible-only authority factorization. -/
def authorityFactorization
    (complete : ArrowOccurrenceAuthorityCompleteness O rule standard) :
    AuthorityFactorization O :=
  (collectiveReadoutFactorization O rule).toAuthorityFactorization
    complete.toAuthorityCompleteReadout

/-- An M6 attachment boundary rejects the nonstandard authority-completeness
strengthening.  This is an observer bridge, not a proof of Arrow's theorem. -/
theorem arrowAuthorityStrengtheningNoGo
    {vertical : AuthorityChangingVerticalAutomorphism O}
    {rooted : RootedObserverObstructionAt vertical}
    (attachment : SourceGeneratedObserverAttachingDirectionAt rooted) :
    ¬ Nonempty (ArrowOccurrenceAuthorityCompleteness O rule standard) := by
  rintro ⟨complete⟩
  exact attachment.boundary_rejectsAuthorityCompleteReadout
    (collectiveReadoutFactorization O rule)
    complete.toAuthorityCompleteReadout

section HiddenFibreControl

variable (rule)
variable (extension : HiddenFibreExtension Hidden Residual)

/-- Both the individual preference profile and the collective preference are
unchanged across an arbitrary hidden fibre. -/
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

/-- Machine negative control: whenever one visible rule satisfies the
standard Arrow bundle, that same rule coexists with a generated hidden-fibre
boundary that forbids authority factorization.  Hence the standard axioms do
not by themselves force occurrence authority. -/
theorem standardArrowAxiomsDoesNotForceAuthority
    (standardAxioms : ArrowVisibleAxiomBundle rule)
    (visible : Visible) :
    ¬ (ArrowVisibleAxiomBundle rule →
      Nonempty (AuthorityFactorization
        (HiddenFibreExtension.observer
          (Visible := Visible) extension))) := by
  intro standardForcesAuthority
  exact HiddenFibreExtension.attachment_noAuthorityFactorization
    extension visible
    (standardForcesAuthority standardAxioms)

end HiddenFibreControl

end ArrowObserverBridge
end M7
end SocialChoice
end Society
end ProcessGame
end SaturationMonoid
