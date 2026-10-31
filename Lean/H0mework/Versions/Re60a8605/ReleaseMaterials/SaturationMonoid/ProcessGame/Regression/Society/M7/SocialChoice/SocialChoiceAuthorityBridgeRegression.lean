import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.SocialChoice.M7.ArrowObserverBridge
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.SocialChoice.M7.GibbardSatterthwaiteObserverBridge
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.SocialChoice.M7.SenObserverBridge
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.NaturalReconstructionNoGoRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M7.SocialChoice.HiddenFibreControlRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M7.SocialChoice.HiddenFibreControlRegression

/-!
# M7 Society social-choice observer consumers

For arbitrary agent and alternative carriers, every supplied visible rule and
its actual standard axiom bundle is kept intact.  Only the separately named
occurrence-authority completeness strengthening is rejected, directly by the
existing Society M6 source-generated attachment boundary.

The hidden-fibre controls are likewise universe-polymorphic.  No false Arrow,
Gibbard--Satterthwaite, or Sen instance is manufactured here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M7SocialChoiceAuthorityBridgeRegression

noncomputable section

open Observer
open M6NormalizedAuthorityObserverFixture
open M6FaithfulReconstructionNoGoRegression
open M6NaturalReconstructionNoGoRegression
open SocialChoice M7
open M7.ArrowObserverBridge
open M7.GibbardSatterthwaiteObserverBridge
open M7.SenObserverBridge

universe uAgent uAlternative uHidden uHiddenResidual

variable {Agent : Type uAgent}
variable {Alternative : Type uAlternative}
variable {Hidden : Type uHidden}
variable {HiddenResidual : Type uHiddenResidual}

/-! ## Actual Society attachment verdicts -/

theorem society_arrowAuthorityStrengtheningNoGo
    (rule : ArrowPreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (standard : ArrowVisibleAxiomBundle rule) :
    ¬ Nonempty (ArrowOccurrenceAuthorityCompleteness
      societyObserver rule standard) :=
  arrowAuthorityStrengtheningNoGo
    societySourceGeneratedAttachingDirection

theorem society_gibbardSatterthwaiteAuthorityStrengtheningNoGo
    (rule : GibbardSatterthwaitePreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (standard : GibbardSatterthwaiteVisibleAxiomBundle rule) :
    ¬ Nonempty (GibbardSatterthwaiteOccurrenceAuthorityCompleteness
      societyObserver rule standard) :=
  gibbardSatterthwaiteAuthorityStrengtheningNoGo
    societySourceGeneratedAttachingDirection

theorem society_senAuthorityStrengtheningNoGo
    (rule : SenPreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (standard : SenVisibleAxiomBundle rule) :
    ¬ Nonempty (SenOccurrenceAuthorityCompleteness
      societyObserver rule standard) :=
  senAuthorityStrengtheningNoGo
    societySourceGeneratedAttachingDirection

/-! ## Arbitrary hidden-fibre negative controls -/

theorem society_standardArrowAxiomsDoesNotForceAuthority
    (extension : HiddenFibreExtension Hidden HiddenResidual)
    (rule : ArrowPreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (standard : ArrowVisibleAxiomBundle rule) :
    ¬ (ArrowVisibleAxiomBundle rule →
      Nonempty (AuthorityFactorization
        (HiddenFibreExtension.observer
          (Visible := NormalizedImage) extension))) :=
  standardArrowAxiomsDoesNotForceAuthority
    rule extension standard commonImage

theorem society_standardGibbardSatterthwaiteAxiomsDoesNotForceAuthority
    (extension : HiddenFibreExtension Hidden HiddenResidual)
    (rule : GibbardSatterthwaitePreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (standard : GibbardSatterthwaiteVisibleAxiomBundle rule) :
    ¬ (GibbardSatterthwaiteVisibleAxiomBundle rule →
      Nonempty (AuthorityFactorization
        (HiddenFibreExtension.observer
          (Visible := NormalizedImage) extension))) :=
  standardGibbardSatterthwaiteAxiomsDoesNotForceAuthority
    rule extension standard commonImage

theorem society_standardSenAxiomsDoesNotForceAuthority
    (extension : HiddenFibreExtension Hidden HiddenResidual)
    (rule : SenPreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (standard : SenVisibleAxiomBundle rule) :
    ¬ (SenVisibleAxiomBundle rule →
      Nonempty (AuthorityFactorization
        (HiddenFibreExtension.observer
          (Visible := NormalizedImage) extension))) :=
  standardSenAxiomsDoesNotForceAuthority
    rule extension standard commonImage

/-! ## Whole conditional certificate -/

/-- One conditional certificate consumes the actual Society attachment and
an arbitrary hidden-fibre extension without asserting that any classical
standard bundle is inhabited. -/
structure SocietySocialChoiceAuthorityBridgeCertificate
    (extension : HiddenFibreExtension Hidden HiddenResidual)
    (arrowRule : ArrowPreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (arrowStandard : ArrowVisibleAxiomBundle arrowRule)
    (gsRule : GibbardSatterthwaitePreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (gsStandard : GibbardSatterthwaiteVisibleAxiomBundle gsRule)
    (senRule : SenPreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (senStandard : SenVisibleAxiomBundle senRule) : Prop where
  actualSocietyAttachment : Nonempty
    (SourceGeneratedObserverAttachingDirectionAt
      societyRootedObserverObstruction)
  actualSocietyBoundaryExact :
    societySourceGeneratedAttachingDirection.boundaryKernelPair =
      societyRootedObserverObstruction.kernelPair
  arrowStandardPreserved : ArrowVisibleAxiomBundle arrowRule
  arrowAuthorityStrengtheningNoGo :
    ¬ Nonempty (ArrowOccurrenceAuthorityCompleteness
      societyObserver arrowRule arrowStandard)
  arrowReadoutsIgnoreHidden : ∀ firstHidden secondHidden : Hidden,
    HiddenFibreExtension.pullback arrowRule.preferenceReadout
        (commonImage, firstHidden) =
        HiddenFibreExtension.pullback arrowRule.preferenceReadout
          (commonImage, secondHidden) ∧
      HiddenFibreExtension.pullback arrowRule.collectiveReadout
        (commonImage, firstHidden) =
        HiddenFibreExtension.pullback arrowRule.collectiveReadout
          (commonImage, secondHidden)
  arrowStandardDoesNotForceAuthority :
    ¬ (ArrowVisibleAxiomBundle arrowRule →
      Nonempty (AuthorityFactorization
        (HiddenFibreExtension.observer
          (Visible := NormalizedImage) extension)))
  gsStandardPreserved : GibbardSatterthwaiteVisibleAxiomBundle gsRule
  gsAuthorityStrengtheningNoGo :
    ¬ Nonempty (GibbardSatterthwaiteOccurrenceAuthorityCompleteness
      societyObserver gsRule gsStandard)
  gsReadoutsIgnoreHidden : ∀ firstHidden secondHidden : Hidden,
    HiddenFibreExtension.pullback gsRule.preferenceReadout
        (commonImage, firstHidden) =
        HiddenFibreExtension.pullback gsRule.preferenceReadout
          (commonImage, secondHidden) ∧
      HiddenFibreExtension.pullback gsRule.choiceReadout
        (commonImage, firstHidden) =
        HiddenFibreExtension.pullback gsRule.choiceReadout
          (commonImage, secondHidden)
  gsStandardDoesNotForceAuthority :
    ¬ (GibbardSatterthwaiteVisibleAxiomBundle gsRule →
      Nonempty (AuthorityFactorization
        (HiddenFibreExtension.observer
          (Visible := NormalizedImage) extension)))
  senStandardPreserved : SenVisibleAxiomBundle senRule
  senAuthorityStrengtheningNoGo :
    ¬ Nonempty (SenOccurrenceAuthorityCompleteness
      societyObserver senRule senStandard)
  senReadoutsIgnoreHidden : ∀ firstHidden secondHidden : Hidden,
    HiddenFibreExtension.pullback senRule.preferenceReadout
        (commonImage, firstHidden) =
        HiddenFibreExtension.pullback senRule.preferenceReadout
          (commonImage, secondHidden) ∧
      HiddenFibreExtension.pullback senRule.collectiveReadout
        (commonImage, firstHidden) =
        HiddenFibreExtension.pullback senRule.collectiveReadout
          (commonImage, secondHidden)
  senStandardDoesNotForceAuthority :
    ¬ (SenVisibleAxiomBundle senRule →
      Nonempty (AuthorityFactorization
        (HiddenFibreExtension.observer
          (Visible := NormalizedImage) extension)))
  hiddenBoundaryNoAuthorityFactorization :
    ¬ Nonempty (AuthorityFactorization
      (HiddenFibreExtension.observer
        (Visible := NormalizedImage) extension))

theorem societySocialChoiceAuthorityBridgeDirectConsumer
    (extension : HiddenFibreExtension Hidden HiddenResidual)
    (arrowRule : ArrowPreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (arrowStandard : ArrowVisibleAxiomBundle arrowRule)
    (gsRule : GibbardSatterthwaitePreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (gsStandard : GibbardSatterthwaiteVisibleAxiomBundle gsRule)
    (senRule : SenPreferenceReadout
      (Agent := Agent) (Alternative := Alternative)
      (Visible := NormalizedImage))
    (senStandard : SenVisibleAxiomBundle senRule) :
    SocietySocialChoiceAuthorityBridgeCertificate
      extension arrowRule arrowStandard gsRule gsStandard
        senRule senStandard where
  actualSocietyAttachment :=
    ⟨societySourceGeneratedAttachingDirection⟩
  actualSocietyBoundaryExact := society_attaching_boundary_exact
  arrowStandardPreserved := arrowStandard
  arrowAuthorityStrengtheningNoGo :=
    society_arrowAuthorityStrengtheningNoGo arrowRule arrowStandard
  arrowReadoutsIgnoreHidden := fun firstHidden secondHidden =>
    preferenceReadouts_hidden_invariant
      arrowRule commonImage firstHidden secondHidden
  arrowStandardDoesNotForceAuthority :=
    society_standardArrowAxiomsDoesNotForceAuthority
      extension arrowRule arrowStandard
  gsStandardPreserved := gsStandard
  gsAuthorityStrengtheningNoGo :=
    society_gibbardSatterthwaiteAuthorityStrengtheningNoGo
      gsRule gsStandard
  gsReadoutsIgnoreHidden := fun firstHidden secondHidden =>
    preferenceAndChoice_hidden_invariant
      gsRule commonImage firstHidden secondHidden
  gsStandardDoesNotForceAuthority :=
    society_standardGibbardSatterthwaiteAxiomsDoesNotForceAuthority
      extension gsRule gsStandard
  senStandardPreserved := senStandard
  senAuthorityStrengtheningNoGo :=
    society_senAuthorityStrengtheningNoGo senRule senStandard
  senReadoutsIgnoreHidden := fun firstHidden secondHidden =>
    SenObserverBridge.preferenceReadouts_hidden_invariant
      senRule commonImage firstHidden secondHidden
  senStandardDoesNotForceAuthority :=
    society_standardSenAxiomsDoesNotForceAuthority
      extension senRule senStandard
  hiddenBoundaryNoAuthorityFactorization :=
    HiddenFibreExtension.attachment_noAuthorityFactorization
      extension commonImage

/-! ## Minimal Boolean control remains a regression only -/

theorem booleanHiddenFibre_minimalBoundaryNoAuthorityFactorization :
    ¬ Nonempty (AuthorityFactorization
      (HiddenFibreExtension.observer
        (Visible := NormalizedImage)
        BooleanHiddenFibreControl.extension)) :=
  HiddenFibreExtension.attachment_noAuthorityFactorization
    BooleanHiddenFibreControl.extension commonImage

end
end M7SocialChoiceAuthorityBridgeRegression
end Society
end ProcessGame
end SaturationMonoid
