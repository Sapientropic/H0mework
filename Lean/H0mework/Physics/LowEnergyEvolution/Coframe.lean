import H0mework.Physics.LowEnergyEvolution.Curvature

/-! The original coframe reaction consumes all components of the actual curvature. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineCartanTangentSimplicityResponse StageNineTopologicalFourFormPairing
open StageNineFormNativeCoframeLocalVariation StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineBlockwiseConstitutive Stage9C.Reduction StageNineFormNativeP286GaugeYangMillsReadout
noncomputable section

def movingReaction (n a h k dh dk : ℝ) : PhysicalBivector :=
  gravityInternalDualEquiv (physicalIIPlusBivector (diagonalCoframe n a)) -
    gravityInternalPairVarianceNormalization (movingCurvature h k dh dk)

theorem movingReaction_coordinates (n a h k dh dk : ℝ) (row col : LorentzianIndex) :
    gravityTopologicalWedgeCoefficient (movingReaction n a h k dh dk)
      (physicalIIPlusCoframeTangent (diagonalCoframe n a) (Matrix.single row col 1)) =
      if row = col then
        if row = 0 then 3*a^3+3*a*h^2-3*a*k^2
        else 3*n*a^2+n*h^2-n*k^2+2*a*dh
      else 0 := by
  fin_cases row <;> fin_cases col <;>
    simp [movingReaction, movingCurvature, gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit, physicalIIPlusCoframeTangent,
      physicalIIPlusBivector, coframeWedgeTangent, coframeWedge,
      gravityInternalDualEquiv, gravityInternalDualLinear, internalBivectorDual,
      lorentzianCoframeHodge, gravityInternalPairVarianceNormalization,
      lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
      Fin.sum_univ_six, diagonalCoframe, Matrix.single_apply] <;> ring

theorem Solution.gravity_reaction {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    flow.configuration.gravitySimplicityMultiplier point =
      movingReaction (clock (flow.pointState point)) (flow.pointState point 0)
        (flow.pointState point 1) (contorsion (flow.pointState point))
        (generator (flow.pointState point) 1) (torsionRate (flow.pointState point)) := by
  have generated : flow.configuration.gravitySimplicityMultiplier =
      formNativeGravityReactionField flow.configuration :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
      positiveSmoothUnifiedSource (formNativeP286GaugeConstitutiveReadout positiveSmoothUnifiedSource flow.raw)
  rw [generated]
  change gravityInternalDualEquiv (physicalIIPlusBivector (flow.configuration.coframe point)) -
    gravityInternalPairVarianceNormalization (holonomicGravityCurvature flow.configuration point) = _
  rw [flow.coframe, flow.gravity_curvature point inside]
  rfl

theorem Solution.gravity_reaction_coordinates {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (row col : LorentzianIndex) :
    formNativeCoframeConstraintReaction (toContinuumPointField flow.configuration point)
      (Matrix.single row col 1) =
      if row = col then
        if row = 0 then 3*(flow.pointState point 0)^3 +
          3*flow.pointState point 0*(flow.pointState point 1)^2 -
          3*flow.pointState point 0*(contorsion (flow.pointState point))^2
        else 3*clock (flow.pointState point)*(flow.pointState point 0)^2 +
          clock (flow.pointState point)*(flow.pointState point 1)^2 -
          clock (flow.pointState point)*(contorsion (flow.pointState point))^2 +
          2*flow.pointState point 0*generator (flow.pointState point) 1
      else 0 := by
  change gravityTopologicalWedgeCoefficient (flow.configuration.gravitySimplicityMultiplier point)
    (physicalIIPlusCoframeTangent (flow.configuration.coframe point) (Matrix.single row col 1)) = _
  rw [flow.gravity_reaction point inside, flow.coframe, movingReaction_coordinates]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
