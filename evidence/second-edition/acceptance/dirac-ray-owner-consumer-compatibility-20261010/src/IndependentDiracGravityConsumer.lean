import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeDiracRay
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeGravityScalarReturn
import Lean
set_option autoImplicit false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for text in ["LowEnergy.SourcePropagationNativeActionHessian.h0meworkNativeDiracRayNormedAddCommGroup", "LowEnergy.SourcePropagationNativeActionHessian.h0meworkNativeDiracRaySeminormedAddCommGroup", "LowEnergy.SourcePropagationNativeActionHessian.h0meworkNativeDiracRayNormedSpace"] do
    let name := (text.splitOn ".").foldl Name.str .anonymous
    let some constant := env.find? name | throwError "Missing constant {name}"
    let some index := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    logInfo m!"OWNER {name} = {env.header.moduleNames[index]!}"
    logInfo m!"TYPE {name} = {constant.type}"
open LowEnergy.SourcePropagationNativeActionHessian
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open StageNineDiracMatterCoordinateCalculus StageNineMatterVariation
example (p : Fin 4 → ℂ) : (nativeJacobi (-p)).transpose = nativeJacobi p :=
  nativeJacobi_formalAdjoint p
example (jet : NativeFirstJet) (mu : Fin 4) :
    matterCoordinateEquiv (nativeMatterCovariant jet mu) =
      fieldDirectionalDerivative (fun x => matterCoordinateEquiv (actual.matter x)) 0 mu +
      rotatedPrimalDerivative jet mu +
      diracSpinAction (diracSpinBase mu + diracSpinVariation jet mu)
        (diracPrimalBase + primalInsertionCLM jet.1) +
      diracGaugeAction (diracGaugeBase mu + diracGaugeVariation jet mu)
        (diracPrimalBase + primalInsertionCLM jet.1) :=
  diracCovariant_coordinates jet mu
#print axioms nativeJacobi_formalAdjoint
#print axioms diracCovariant_coordinates
