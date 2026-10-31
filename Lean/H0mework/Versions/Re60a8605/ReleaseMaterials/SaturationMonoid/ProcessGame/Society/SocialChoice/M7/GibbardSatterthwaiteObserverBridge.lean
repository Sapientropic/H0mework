import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.SocialChoice.M7.PreferenceReadout

/-!
# Gibbard--Satterthwaite-style visible axioms and authority strengthening

The standard bundle below names the visible hypotheses: an unrestricted
strict/linear preference domain, at least three outcomes, onto,
non-dictatorship, and strategy-proofness against unilateral misreports.  None
of them says that the chosen alternative encodes the actual occurrence or its
source-native authority.  That extra claim is isolated as
`GibbardSatterthwaiteOccurrenceAuthorityCompleteness` and rejected by the M6
attachment boundary.

This is an observer bridge, not a formalization or invocation of the
classical Gibbard--Satterthwaite theorem.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace SocialChoice
namespace M7
namespace GibbardSatterthwaiteObserverBridge

open Observer

universe uAgent uAlternative uOccurrence uVisible uHidden uResidual

variable {Agent : Type uAgent}
variable {Alternative : Type uAlternative}
variable {Occurrence : Type uOccurrence}
variable {Visible : Type uVisible}
variable {Hidden : Type uHidden}
variable {Residual : Type uResidual}

/-- Visible strict/linear preference reports and the chosen alternative. -/
structure GibbardSatterthwaitePreferenceReadout where
  preferenceReadout : Visible → LinearPreferenceProfile Agent Alternative
  choiceReadout : Visible → Alternative

namespace GibbardSatterthwaitePreferenceReadout

variable (rule : GibbardSatterthwaitePreferenceReadout
  (Agent := Agent) (Alternative := Alternative) (Visible := Visible))

/-- Two reports differ, if at all, only in one agent's preference. -/
def UnilateralDeviation
    (agent : Agent) (truthful reported : Visible) : Prop :=
  ∀ other, other ≠ agent →
    rule.preferenceReadout truthful other =
      rule.preferenceReadout reported other

/-- The selected alternative is maximal for one agent at one visible
profile. -/
def ChoosesAgentTop (agent : Agent) (visible : Visible) : Prop :=
  ∀ alternative,
    (rule.preferenceReadout visible agent).ranks
      (rule.choiceReadout visible) alternative

end GibbardSatterthwaitePreferenceReadout

/-- Standard visible Gibbard--Satterthwaite hypothesis bundle. -/
structure GibbardSatterthwaiteVisibleAxiomBundle
    (rule : GibbardSatterthwaitePreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible)) :
    Prop where
  atLeastThreeOutcomes : ∃ first second third : Alternative,
    first ≠ second ∧ first ≠ third ∧ second ≠ third
  unrestrictedDomain : Function.Surjective rule.preferenceReadout
  onto : Function.Surjective rule.choiceReadout
  nonDictatorship : ∀ agent,
    ¬ ∀ visible, rule.ChoosesAgentTop agent visible
  strategyProof : ∀ agent truthful reported,
    rule.UnilateralDeviation agent truthful reported →
      ¬ LinearPreference.Strict
        (rule.preferenceReadout truthful agent)
        (rule.choiceReadout reported)
        (rule.choiceReadout truthful)

/-- Explicit nonstandard strengthening: the visible chosen alternative must
decode the actual source-native authority at every occurrence. -/
structure GibbardSatterthwaiteOccurrenceAuthorityCompleteness
    (O : AuthorityObserver Occurrence Visible Residual)
    (rule : GibbardSatterthwaitePreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible))
    (_standard : GibbardSatterthwaiteVisibleAxiomBundle rule) where
  authorityDecode : Alternative → Residual
  choice_recovers_authority : ∀ occurrence,
    authorityDecode (rule.choiceReadout (O.forget occurrence)) =
      O.authorityK occurrence

variable {O : AuthorityObserver Occurrence Visible Residual}
variable {rule : GibbardSatterthwaitePreferenceReadout
  (Agent := Agent) (Alternative := Alternative) (Visible := Visible)}
variable {standard : GibbardSatterthwaiteVisibleAxiomBundle rule}

def choiceOccurrenceReadout
    (O : AuthorityObserver Occurrence Visible Residual)
    (rule : GibbardSatterthwaitePreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible)) :
    OccurrenceReadout Occurrence Alternative :=
  OccurrenceReadout.ofVisible O rule.choiceReadout

def choiceReadoutFactorization
    (O : AuthorityObserver Occurrence Visible Residual)
    (rule : GibbardSatterthwaitePreferenceReadout
      (Agent := Agent) (Alternative := Alternative) (Visible := Visible)) :
    ReadoutFactorization O (choiceOccurrenceReadout O rule) :=
  ReadoutFactorization.ofVisible O rule.choiceReadout

namespace GibbardSatterthwaiteOccurrenceAuthorityCompleteness

def toAuthorityCompleteReadout
    (complete : GibbardSatterthwaiteOccurrenceAuthorityCompleteness
      O rule standard) :
    AuthorityCompleteReadoutAt O (choiceOccurrenceReadout O rule) where
  decodeAuthority := complete.authorityDecode
  readsActualAuthority := complete.choice_recovers_authority

end GibbardSatterthwaiteOccurrenceAuthorityCompleteness

/-- The explicit strengthening actually produces the generic M7 authority
factorization. -/
def authorityFactorization
    (complete : GibbardSatterthwaiteOccurrenceAuthorityCompleteness
      O rule standard) :
    AuthorityFactorization O :=
  (choiceReadoutFactorization O rule).toAuthorityFactorization
    complete.toAuthorityCompleteReadout

/-- Boundary verdict for the nonstandard occurrence-authority strengthening. -/
theorem gibbardSatterthwaiteAuthorityStrengtheningNoGo
    {vertical : AuthorityChangingVerticalAutomorphism O}
    {rooted : RootedObserverObstructionAt vertical}
    (attachment : SourceGeneratedObserverAttachingDirectionAt rooted) :
    ¬ Nonempty
      (GibbardSatterthwaiteOccurrenceAuthorityCompleteness
        O rule standard) := by
  rintro ⟨complete⟩
  exact attachment.boundary_rejectsAuthorityCompleteReadout
    (choiceReadoutFactorization O rule)
    complete.toAuthorityCompleteReadout

section HiddenFibreControl

variable (rule)
variable (extension : HiddenFibreExtension Hidden Residual)

/-- Preference reports and the chosen outcome ignore arbitrary hidden
occurrence coordinates. -/
theorem preferenceAndChoice_hidden_invariant
    (visible : Visible) (firstHidden secondHidden : Hidden) :
    HiddenFibreExtension.pullback rule.preferenceReadout
        (visible, firstHidden) =
        HiddenFibreExtension.pullback rule.preferenceReadout
          (visible, secondHidden) ∧
      HiddenFibreExtension.pullback rule.choiceReadout
        (visible, firstHidden) =
        HiddenFibreExtension.pullback rule.choiceReadout
          (visible, secondHidden) :=
  ⟨rfl, rfl⟩

/-- Standard visible GS hypotheses remain intact on the projection image and
therefore do not force occurrence-authority factorization. -/
theorem standardGibbardSatterthwaiteAxiomsDoesNotForceAuthority
    (standardAxioms : GibbardSatterthwaiteVisibleAxiomBundle rule)
    (visible : Visible) :
    ¬ (GibbardSatterthwaiteVisibleAxiomBundle rule →
      Nonempty (AuthorityFactorization
        (HiddenFibreExtension.observer
          (Visible := Visible) extension))) := by
  intro standardForcesAuthority
  exact HiddenFibreExtension.attachment_noAuthorityFactorization
    extension visible
    (standardForcesAuthority standardAxioms)

end HiddenFibreControl

end GibbardSatterthwaiteObserverBridge
end M7
end SocialChoice
end Society
end ProcessGame
end SaturationMonoid
