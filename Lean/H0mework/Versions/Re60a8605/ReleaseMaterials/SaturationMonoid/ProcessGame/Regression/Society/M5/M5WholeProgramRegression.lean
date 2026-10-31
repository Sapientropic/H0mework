import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M4.M4WholeProgramRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M5.GoCrossOccurrenceResidualRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M5.SourceFirstCrossOccurrenceResidual

/-!
# M5 whole-program sink

The Society source-first pair and the inherited Go pair both realize the
strong cross-occurrence shape: unequal actual occurrences, honest equivalent
classical images, independently generated residual authority, and failure of
classical-image determination.  This is the strict residual checkpoint, not
the M6 natural no-section theorem.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M5WholeProgramRegression

universe u v

structure M5WholeProgramCertificate : Prop where
  inheritedM4 :
    M4WholeProgramRegression.M4WholeProgramCertificate.{u, v}
  sourceFirst :
    M5SourceFirstCrossOccurrenceResidual.SourceFirstCrossOccurrenceResidualCertificate
  go : ∀ horizon : Nat,
    M5GoCrossOccurrenceResidualRegression.GoCrossOccurrenceResidualCertificate
      horizon

theorem m5WholeProgram : M5WholeProgramCertificate.{u, v} where
  inheritedM4 := M4WholeProgramRegression.m4WholeProgram
  sourceFirst :=
    M5SourceFirstCrossOccurrenceResidual.sourceFirstCrossOccurrenceResidualDirectConsumer
  go :=
    M5GoCrossOccurrenceResidualRegression.goCrossOccurrenceResidualDirectConsumer

end M5WholeProgramRegression
end Society
end ProcessGame
end SaturationMonoid
