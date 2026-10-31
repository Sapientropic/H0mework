import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.M8RenewalFoundationRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Election.ActualElectionMandateRenewalRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Money.PurchasingPowerStandingRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.RootInstallation.M8JointRootInstallationRegression

/-!
# M8 renewal-authority whole-program regression

This closes the four M8 domain machines and their common operational seam:

* actual election renews a mandate/power lineage;
* accepted tender plus open settlement renews purchasing power;
* exact maintenance permission and debt-flow fibres expose relationship
  asymmetry;
* trace-witnessed AI lineage enters responsibility renewal; and
* all four are installed before emission as coordinates of one unchanged
  living-root source/ledger compiler and consume one exact temporal next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8WholeProgramRegression

open Renewal
open M8RenewalFoundationRegression
open M8ActualElectionMandateRenewalRegression
open M8PurchasingPowerStandingRegression
open M8RelationshipMaintenanceRenewalRegression
open M8AIStandingRenewalRegression
open M8JointRootInstallationRegression

noncomputable section

universe u v uAgent uAlternative uHidden uHiddenResidual

structure M8WholeProgramCertificate where
  inheritedFoundation :
    M8RenewalFoundationCertificate.{u, v, uAgent, uAlternative,
      uHidden, uHiddenResidual}
  actualElection : ActualElectionMandateRenewalCertificate
  purchasingPower : PurchasingPowerStandingCertificate
  relationshipMaintenance : RelationshipLocalRenewalFaceCertificate
  aiStanding : AILocalRenewalFaceCertificate
  jointSameRoot : JointM8RootInstallationCertificate
  noFreeAISeed :
    SourceSeed threeAgentOccurrenceOf Empty noAISeedAt
      threeAgentProcessGame.source → False

def m8WholeProgram : M8WholeProgramCertificate.{u, v, uAgent,
    uAlternative, uHidden, uHiddenResidual} where
  inheritedFoundation := m8RenewalFoundation
  actualElection := actualElectionMandateRenewalDirectConsumer
  purchasingPower := purchasingPowerStandingDirectConsumer
  relationshipMaintenance := relationshipLocalRenewalFaceDirectConsumer
  aiStanding := aiLocalRenewalFaceDirectConsumer
  jointSameRoot := jointM8RootInstallationDirectConsumer
  noFreeAISeed := fun seed => nomatch seed.1

end
end M8WholeProgramRegression
end Society
end ProcessGame
end SaturationMonoid
