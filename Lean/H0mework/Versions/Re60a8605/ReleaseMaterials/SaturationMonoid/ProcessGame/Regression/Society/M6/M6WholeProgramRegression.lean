import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M5.M5WholeProgramRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.GoNaturalAuthorityReconstructionRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.NaturalReconstructionNoGoRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.NaturalReconstructionIdentityControl

/-!
# M6 whole-program sink

The unrestricted observer theorems live in the production `Observer` modules;
this sink does not narrow them to a finite carrier.  It jointly consumes the
inherited M5 strict residual, the source-first Society authority fibre, and the
Go cross-replay fibre at every observation horizon.  Both domains retain an
ordinary surrogate right section while rejecting faithful authority recovery
and genuinely natural representative choice.  The arbitrary-type identity
observer control proves that natural reconstruction itself remains inhabited
when no authority fibre is collapsed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M6WholeProgramRegression

universe u v

structure M6WholeProgramCertificate : Prop where
  inheritedM5 :
    M5WholeProgramRegression.M5WholeProgramCertificate.{u, v}
  society :
    M6NaturalReconstructionNoGoRegression.SocietyNaturalReconstructionNoGoCertificate
  go : ∀ horizon : Nat,
    M6GoNaturalAuthorityReconstructionRegression.GoNaturalAuthorityNoGoCertificate
      horizon

theorem m6WholeProgram : M6WholeProgramCertificate.{u, v} where
  inheritedM5 := M5WholeProgramRegression.m5WholeProgram
  society :=
    M6NaturalReconstructionNoGoRegression.societyNaturalReconstructionNoGoDirectConsumer
  go :=
    M6GoNaturalAuthorityReconstructionRegression.goNaturalAuthorityNoGoDirectConsumer

end M6WholeProgramRegression
end Society
end ProcessGame
end SaturationMonoid
