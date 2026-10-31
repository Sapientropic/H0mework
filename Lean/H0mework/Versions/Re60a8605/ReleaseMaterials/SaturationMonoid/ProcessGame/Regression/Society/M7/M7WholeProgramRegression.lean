import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.M6WholeProgramRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M7.M7ReadoutFactorizationWholeRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M7.SocialChoice.SocialChoiceAuthorityBridgeRegression

/-!
# M7 whole-program sink

The sink inherits the exact M6 obstruction and jointly consumes positive
visible matching, trace-constrained narrative, arbitrary-horizon Go readouts,
and the three conditional social-choice observer bridges.  Standard visible
axiom bundles are retained as inputs to the bridge theorem; no fictitious
Arrow, Gibbard--Satterthwaite, or Sen instance is asserted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M7WholeProgramRegression

open M6NormalizedAuthorityObserverFixture
open M6WholeProgramRegression
open M7ReadoutFactorizationWholeRegression
open M7SocialChoiceAuthorityBridgeRegression
open SocialChoice M7
open M7.ArrowObserverBridge
open M7.GibbardSatterthwaiteObserverBridge
open M7.SenObserverBridge

universe u v uAgent uAlternative uHidden uHiddenResidual

structure M7WholeProgramCertificate : Prop where
  inheritedM6 : M6WholeProgramCertificate.{u, v}
  matchingHistoryAndGo : M7ReadoutFactorizationWholeCertificate
  socialChoice :
    ∀ {Agent : Type uAgent} {Alternative : Type uAlternative}
      {Hidden : Type uHidden} {HiddenResidual : Type uHiddenResidual}
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
      (senStandard : SenVisibleAxiomBundle senRule),
      SocietySocialChoiceAuthorityBridgeCertificate
        extension arrowRule arrowStandard gsRule gsStandard
          senRule senStandard
  minimalHiddenControl :
    ¬ Nonempty (Observer.AuthorityFactorization
      (HiddenFibreExtension.observer
        (Visible := NormalizedImage)
        BooleanHiddenFibreControl.extension))

theorem m7WholeProgram :
    M7WholeProgramCertificate.{u, v, uAgent, uAlternative,
      uHidden, uHiddenResidual} where
  inheritedM6 := m6WholeProgram
  matchingHistoryAndGo := m7ReadoutFactorizationWholeDirectConsumer
  socialChoice := fun extension arrowRule arrowStandard gsRule gsStandard
      senRule senStandard =>
    societySocialChoiceAuthorityBridgeDirectConsumer
      extension arrowRule arrowStandard gsRule gsStandard
        senRule senStandard
  minimalHiddenControl :=
    booleanHiddenFibre_minimalBoundaryNoAuthorityFactorization

end M7WholeProgramRegression
end Society
end ProcessGame
end SaturationMonoid
