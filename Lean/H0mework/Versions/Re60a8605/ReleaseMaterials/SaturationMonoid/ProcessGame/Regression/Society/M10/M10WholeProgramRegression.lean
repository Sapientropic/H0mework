import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.M9WholeProgramRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.OccurrenceCapacityPhaseRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.OccurrenceCapacityTransitionRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.OccurrenceCapacityDebitConsumerRegression

/-!
# M10 occurrence-capacity whole-program regression

M10 closes only when one source-position queue and one installed renewal row
jointly generate all three phases, preserve recurrent occurrence provenance,
produce the stable→critical→anomie transition law, exhaust an actual critical
debit run, and reject full debit certification in anomie.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M10WholeProgramRegression

noncomputable section

open M9WholeProgramRegression
open M10OccurrenceCapacityPhaseRegression
open M10OccurrenceCapacityTransitionRegression
open M10OccurrenceCapacityDebitConsumerRegression

universe u v uAgent uAlternative uHidden uHiddenResidual

structure M10WholeProgramCertificate where
  inheritedM9 : M9WholeProgramCertificate.{u, v, uAgent, uAlternative,
    uHidden, uHiddenResidual}
  phases : OccurrenceCapacityPhaseCertificate
  transitions : OccurrenceCapacityTransitionCertificate
  actualDebit : OccurrenceCapacityDebitConsumerCertificate

def m10WholeProgram : M10WholeProgramCertificate.{u, v, uAgent,
    uAlternative, uHidden, uHiddenResidual} where
  inheritedM9 := m9WholeProgram
  phases := occurrenceCapacityPhaseDirectConsumer
  transitions := occurrenceCapacityTransitionDirectConsumer
  actualDebit := occurrenceCapacityDebitDirectConsumer

end
end M10WholeProgramRegression
end Society
end ProcessGame
end SaturationMonoid
