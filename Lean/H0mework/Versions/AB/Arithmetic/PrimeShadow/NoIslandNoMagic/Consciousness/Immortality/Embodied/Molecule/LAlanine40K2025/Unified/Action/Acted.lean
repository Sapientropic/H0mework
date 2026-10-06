import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.Orbitals

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift SU7MotherLieAlgebra
open scoped ContDiff
noncomputable section

def coordinateAction (action : Module.End ℂ DiracExteriorMatterCarrier) :
    MatterCoordinateCarrier →L[ℂ] MatterCoordinateCarrier :=
  (matterCoordinateEquiv.toLinearMap.comp (action.comp matterCoordinateEquiv.symm.toLinearMap)).toContinuousLinearMap

theorem coordinateAction_apply (action : Module.End ℂ DiracExteriorMatterCarrier) (v : DiracExteriorMatterCarrier) :
    coordinateAction action (matterCoordinateEquiv v) = matterCoordinateEquiv (action v) := by
  simp [coordinateAction]

def connectionAction (p : BasePoint) (direction : LorentzianIndex) : Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction (diracSpinConnectionLift (Stage10.Runtime.configuration.gravityConnection p) direction) +
    diracExteriorMotherLieAction (p286LieBlockEmbed (Stage10.Runtime.configuration.gaugeConnection p direction))

def actedWeighted (action : Module.End ℂ DiracExteriorMatterCarrier) (weight : BasePoint → ℂ) :
    StageNineHolonomicConfiguration :=
  { Stage10.Runtime.configuration with matter := fun p => weight p • action (Stage10.Runtime.configuration.matter p) }

/-- Full mother actions can leave the occupied coordinates; the connection commutator is retained. -/
theorem acted_weighted_covariant (action : Module.End ℂ DiracExteriorMatterCarrier)
    (weight : BasePoint → ℂ) (p : BasePoint) (differentiable : DifferentiableAt ℝ weight p)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative (actedWeighted action weight) p direction =
      weight p • action (holonomicMatterCovariantDerivative Stage10.Runtime.configuration p direction) +
      fieldDirectionalDerivative weight p direction • action (Stage10.Runtime.configuration.matter p) +
      weight p • ((connectionAction p direction).comp action - action.comp (connectionAction p direction))
        (Stage10.Runtime.configuration.matter p) := by
  have dm := (original_matter_smooth.differentiable (by simp) p).hasFDerivAt
  have da := (coordinateAction action).restrictScalars ℝ |>.hasFDerivAt.comp p dm
  have dw := differentiable.hasFDerivAt.smul da
  have same : (fun x => matterCoordinateEquiv ((actedWeighted action weight).matter x)) =
      fun x => weight x • coordinateAction action (matterCoordinateEquiv (Stage10.Runtime.configuration.matter x)) := by
    funext x
    rw [coordinateAction_apply]
    exact map_smul matterCoordinateEquiv (weight x) _
  have derivative := congrArg (fun A : BasePoint →L[ℝ] MatterCoordinateCarrier => A (coordinateDirection direction)) dw.fderiv
  change (fderiv ℝ (fun x => weight x • coordinateAction action
    (matterCoordinateEquiv (Stage10.Runtime.configuration.matter x))) p) (coordinateDirection direction) = _ at derivative
  rw [← same] at derivative
  simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply,Function.comp_def] at derivative
  unfold holonomicMatterCovariantDerivative fieldDirectionalDerivative
  rw [derivative]
  simp only [map_add,map_smul,actedWeighted,connectionAction]
  have recover (v : MatterCoordinateCarrier) : matterCoordinateEquiv.symm (coordinateAction action v) =
      action (matterCoordinateEquiv.symm v) := by simp [coordinateAction]
  have restrict_apply (v : MatterCoordinateCarrier) :
      (coordinateAction action).restrictScalars ℝ v = coordinateAction action v := rfl
  simp only [restrict_apply,recover,LinearEquiv.symm_apply_apply]
  dsimp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.add_apply]
  simp only [map_add]
  module

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
