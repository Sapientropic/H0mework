import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorJointFacts
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorExchangeSelection
import Lean
set_option autoImplicit false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for text in ["LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorCARLocal1", "LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorColorActionLocal1", "LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorColorColumnsLocal1", "LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorColorMatrixLocal1", "LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorExchangeSelectionLocal1", "LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorGramLocal1", "LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorOccupationLocal1", "LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorPhaseChargeLocal1", "LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorPhaseChargeLocal2", "LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorSpinLocal1", "LowEnergy.MixedSpectatorCandidate.h0R9c73a630MixedSpectatorSpinLocal2"] do
    let name := (text.splitOn ".").foldl Name.str .anonymous
    let some info := env.checked.get.find? name | throwError "Missing checked constant {name}"
    let some index := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    unless (info.value? true).isSome do throwError "Missing value {name}"
    logInfo m!"OWNER {name} = {env.header.moduleNames[index]!}"
    logInfo m!"TYPE {name} = {info.type}"
namespace LowEnergy.MixedSpectatorCandidate
open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open ActiveMatterSectorCharge
open scoped BigOperators InnerProductSpace

example (dual : Bool) :
    inner ℂ (candidate dual) (candidate dual) = 2 ∧
    candidate dual ≠ 0 ∧
    phaseCharge (candidate dual) = (if dual then (-1 : ℂ) else 1) • candidate dual ∧
    NamedColorQtNext.originalSpinCasimir (candidate dual) = (3/4 : ℂ) • candidate dual ∧
    (∀ A : SU3BlockLieMatrix, GaussNativeMatter.nativeFock (colorNative A) (candidate dual) = 0) ∧
    ActiveMatterSectorCharge.occupation (fiberCoordinates (candidate dual)) =
      (if dual then (-3 : ℂ) else 3) • fiberCoordinates (candidate dual) ∧
    (∀ q : ExteriorBasisIndex 4 → ℂ, fiberCharge (degreeFourWeight q) (candidate dual) = 0) ∧
    GaussCoreLabel.fiberPiece (3,0) (candidate dual) = candidate dual := actual_charged_color_singlet_spin_half dual
end LowEnergy.MixedSpectatorCandidate
#print axioms LowEnergy.MixedSpectatorCandidate.actual_charged_color_singlet_spin_half
