import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G7.SourceGeneratedClassicalConsumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M4.AutomaticFullFulfillmentRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M4.EssentialSurjectivityRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M4.GeneratedExtensiveGameRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M4.SourceFirstIndependentPreimageRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M4.ZeroPlayerClearingExchangeRegression

/-!
# M4 whole-program sink

One certificate keeps the two authorities separate: source-first recovery is
the producer for every code, while essential surjectivity is the independent
representation-completeness transporter.  It also consumes the boundary and
asymmetric targets, source-native extensive game, automatic whole-exchange
fulfillment, and the existing Go G1/G5/G7 classical chain.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M4WholeProgramRegression

open _root_.SaturationMonoid.ProcessGame.Society.Classical
open _root_.SaturationMonoid.ProcessGame.Society.Classical.Independent
open _root_.SaturationMonoid.ProcessGame.Society.Classical.Recovery
open _root_.SaturationMonoid.ProcessGame.Society.Classical.Recovery.EssentialSurjectivity
open _root_.SaturationMonoid.ProcessGame.Society.Classical.Source

universe u v

structure M4WholeProgramCertificate : Prop where
  sourceNative : ∀ code : ValidCode, SourceNativeRecoveryAt code
  representationCompleteness : ∀ target : FiniteStrategicGame.{u, v},
    ∃ code : ValidCode,
      Nonempty (StrategicGameIso (recovered code) target)
  generatedExtensive :
    M4GeneratedExtensiveGameRegression.GeneratedExtensiveGameCertificate
  automaticWholeFulfillment :
    M4AutomaticFullFulfillmentRegression.AutomaticFullFulfillmentCertificate
  independentTargets :
    M4EssentialSurjectivityRegression.EssentialSurjectivityDirectCertificate
  sourceFirstIndependent :
    M4SourceFirstIndependentPreimageRegression.SourceFirstIndependentPreimageCertificate
  zeroPlayerClearing :
    M4ZeroPlayerClearingExchangeRegression.ZeroPlayerClearingExchangeCertificate
  goG1G5G7 :
    Go.G7SourceGeneratedClassicalConsumer.G7SourceGeneratedClassicalCertificate

theorem m4WholeProgram : M4WholeProgramCertificate.{u, v} where
  sourceNative := recovered_source_native
  representationCompleteness :=
    recovery_representation_essentially_surjective
  generatedExtensive :=
    M4GeneratedExtensiveGameRegression.generated_extensive_game_end_to_end
  automaticWholeFulfillment :=
    M4AutomaticFullFulfillmentRegression.automaticFullFulfillmentDirectConsumer
  independentTargets :=
    M4EssentialSurjectivityRegression.essentialSurjectivityDirectConsumer
  sourceFirstIndependent :=
    M4SourceFirstIndependentPreimageRegression.sourceFirstIndependentPreimageDirectConsumer
  zeroPlayerClearing :=
    M4ZeroPlayerClearingExchangeRegression.zeroPlayerClearingExchangeDirectConsumer
  goG1G5G7 :=
    Go.G7SourceGeneratedClassicalConsumer.source_generated_classical_readout_consumes_G1_G5_G7

end M4WholeProgramRegression
end Society
end ProcessGame
end SaturationMonoid
