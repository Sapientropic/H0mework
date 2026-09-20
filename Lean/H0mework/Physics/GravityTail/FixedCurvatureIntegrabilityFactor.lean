import H0mework.Physics.GravityTail.FixedJointPath

/-!
# Constraint/Cauchy gravity-tail curvature integrability factor

The source/current-only gravity-tail occurrence has already emitted its
global coframe and connection path.  This module reads the exact factor left
between that actual curvature and the occurrence-local action target.

The factor is not supplied to the writer.  It is generated after the output
exists and splits canonically into connection-value bracket drift and the
transverse radial exactification defect.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailJointPath
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual

private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Current

private abbrev Output : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual

private abbrev Contact (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailProfileContact Source Current point

private theorem output_connection_eq_base_add_profileLorentzJetDrift
    (point : BasePoint) :
    Output.gravityConnection point =
      Base.gravityConnection point +
        lorentzSkewConnectionOfBivectorOneForm
          (fixedP506L0CartanECConstraintCauchyGravityTailProfileLorentzJetDriftRadialIncrement
            point) := by
  change
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.gravityConnection
        point = _
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityConnection]
  unfold cartanECSynchronizedGravityTailPathConnectionField
    cartanECSynchronizedGravityTailPathAnchor
  calc
    Base.gravityConnection 0 +
          lorentzSkewConnectionOfBivectorOneForm
            (cartanECSynchronizedGravityTailRadialIncrement
              Source Current point) =
        Base.gravityConnection point +
          (lorentzSkewConnectionOfBivectorOneForm
              (cartanECSynchronizedGravityTailRadialIncrement
                Source Current point) -
            (Base.gravityConnection point - Base.gravityConnection 0)) := by
      abel
    _ = _ := by
      rw [
        fixedP506L0CartanECConstraintCauchyGravityTailRadialConnectionDisplacementDefect_eq_profileLorentzJetDrift]

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailProfileContact_curvature_eq_target
    (point : BasePoint) :
    holonomicGravityCurvature (Contact point) 0 =
      cartanECSynchronizedGravityTailProfileTarget Source Current point := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [cartanECSynchronizedGravityTailProfileContact_connection_normalForm]
  exact congrFun (congrFun
    (holonomicGravityCurvature_normalizedAffineConfiguration_zero
      (cartanECSynchronizedGravityTailProfileOrigin Source Current point)
      (cartanECSynchronizedGravityTailProfileTarget Source Current point))
    internalPair) spacetimePair

/-- Curvature normal form obtained from the sampled endpoint profile before
the radial exactification defect is added. -/
def fixedP506L0CartanECConstraintCauchyGravityTailEndpointProfileCurvature
    (point : BasePoint) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    let internalOut := pairFirst internalPair
    let internalIn := pairSecond internalPair
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    let sign := minkowskiInternalSign internalOut
    sign *
      (sign *
          cartanECSynchronizedGravityTailJetCLM Source Current point
            (coordinateDirection first) second internalPair -
        sign *
          cartanECSynchronizedGravityTailJetCLM Source Current point
            (coordinateDirection second) first internalPair +
        ∑ middle : LorentzianIndex,
          (Output.gravityConnection point first internalOut middle *
              Output.gravityConnection point second middle internalIn -
            Output.gravityConnection point second internalOut middle *
              Output.gravityConnection point first middle internalIn))

/-- Exact curvature contribution of the generated radial exactification
defect. -/
def fixedP506L0CartanECConstraintCauchyGravityTailTransverseCurvatureDefect
    (point : BasePoint) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    let sign := minkowskiInternalSign (pairFirst internalPair)
    sign *
      (sign *
          fixedP506L0CartanECConstraintCauchyGravityTailRadialExactificationDefect
            point (coordinateDirection first) second internalPair -
        sign *
          fixedP506L0CartanECConstraintCauchyGravityTailRadialExactificationDefect
            point (coordinateDirection second) first internalPair)

/-- Bracket drift caused by the emitted global connection value differing
from the local profile origin at the same occurrence. -/
def fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueBracketDefect
    (point : BasePoint) : PhysicalBivector :=
  originLorentzBracketCurvature (Output.gravityConnection point) -
    originLorentzBracketCurvature
      (cartanECSynchronizedGravityTailProfileOrigin Source Current point)

private theorem connectionValueBracketDefect_eq_profileLorentzJetDrift
    (point : BasePoint) :
    fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueBracketDefect
        point =
      originLorentzBracketCurvature
          (Base.gravityConnection point +
            lorentzSkewConnectionOfBivectorOneForm
              (fixedP506L0CartanECConstraintCauchyGravityTailProfileLorentzJetDriftRadialIncrement
                point)) -
        originLorentzBracketCurvature (Base.gravityConnection point) := by
  unfold
    fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueBracketDefect
  rw [output_connection_eq_base_add_profileLorentzJetDrift,
    cartanECSynchronizedGravityTailProfileOrigin_eq_base]

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailEndpointProfileCurvature_eq_target_add_valueDefect
    (point : BasePoint) :
    fixedP506L0CartanECConstraintCauchyGravityTailEndpointProfileCurvature point =
      cartanECSynchronizedGravityTailProfileTarget Source Current point +
        fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueBracketDefect
          point := by
  rw [←
    fixedP506L0CartanECConstraintCauchyGravityTailProfileContact_curvature_eq_target
      point]
  funext internalPair spacetimePair
  have contactConnection :
      (Contact point).gravityConnection 0 =
        cartanECSynchronizedGravityTailProfileOrigin Source Current point := by
    rw [cartanECSynchronizedGravityTailProfileContact_connection_normalForm]
    exact normalizedAffineLorentzConnectionField_zero _ _
  unfold
    fixedP506L0CartanECConstraintCauchyGravityTailEndpointProfileCurvature
    fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueBracketDefect
    holonomicGravityCurvature
  dsimp only
  rw [cartanECSynchronizedGravityTailJetCLM_coordinate,
    cartanECSynchronizedGravityTailJetCLM_coordinate]
  unfold cartanECSynchronizedGravityTailJetOneForm
    cartanECSynchronizedGravityTailLoweredConnectionFirstJet
  rw [contactConnection]
  unfold originLorentzBracketCurvature
  dsimp only
  fin_cases internalPair <;>
    simp [minkowskiInternalSign, pairFirst, pairSecond] <;>
    ring

theorem
    fixedP506L0CartanECConstraintCauchyGravityTail_gravityCurvature_eq_endpointProfile_add_transverseDefect
    (point : BasePoint) :
    holonomicGravityCurvature Output point =
      fixedP506L0CartanECConstraintCauchyGravityTailEndpointProfileCurvature
          point +
        fixedP506L0CartanECConstraintCauchyGravityTailTransverseCurvatureDefect
          point := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_gravityCurvature_normalForm]
  funext internalPair spacetimePair
  unfold
    fixedP506L0CartanECConstraintCauchyGravityTailRadialGravityCurvatureNormalForm
    fixedP506L0CartanECConstraintCauchyGravityTailEndpointProfileCurvature
    fixedP506L0CartanECConstraintCauchyGravityTailTransverseCurvatureDefect
  dsimp only
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailRadialFirstJet_eq_profile_add_defect]
  simp only [Pi.add_apply, add_apply]
  ring

/-- The single generated factor left between the emitted global curvature
and the exact local action target. -/
def fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
    (point : BasePoint) : PhysicalBivector :=
  fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueBracketDefect
      point +
    fixedP506L0CartanECConstraintCauchyGravityTailTransverseCurvatureDefect
      point

/-- Once the normalized-affine connection displacement has been reduced to
the typed profile drift, the curvature factor has only two generated terms:
the resulting bracket change and the transverse radial exactification
defect. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor_eq_profileLorentzJetDriftBracket_add_transverseDefect
    (point : BasePoint) :
    fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
        point =
      (originLorentzBracketCurvature
          (Base.gravityConnection point +
            lorentzSkewConnectionOfBivectorOneForm
              (fixedP506L0CartanECConstraintCauchyGravityTailProfileLorentzJetDriftRadialIncrement
                point)) -
        originLorentzBracketCurvature (Base.gravityConnection point)) +
      fixedP506L0CartanECConstraintCauchyGravityTailTransverseCurvatureDefect
        point := by
  unfold
    fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
  rw [connectionValueBracketDefect_eq_profileLorentzJetDrift]

theorem
    fixedP506L0CartanECConstraintCauchyGravityTail_gravityCurvature_eq_target_add_integrabilityFactor
    (point : BasePoint) :
    holonomicGravityCurvature Output point =
      cartanECSynchronizedGravityTailProfileTarget Source Current point +
        fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
          point := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTail_gravityCurvature_eq_endpointProfile_add_transverseDefect,
    fixedP506L0CartanECConstraintCauchyGravityTailEndpointProfileCurvature_eq_target_add_valueDefect]
  unfold
    fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
  abel

/-- Exact all-point consumer mouth for the remaining generated factor. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTail_gravityCurvature_eq_target_iff_integrabilityFactor_zero
    (point : BasePoint) :
    holonomicGravityCurvature Output point =
        cartanECSynchronizedGravityTailProfileTarget Source Current point ↔
      fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
          point = 0 := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTail_gravityCurvature_eq_target_add_integrabilityFactor]
  constructor
  · intro equality
    exact add_left_cancel (equality.trans (add_zero _).symm)
  · intro zero
    rw [zero, add_zero]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
