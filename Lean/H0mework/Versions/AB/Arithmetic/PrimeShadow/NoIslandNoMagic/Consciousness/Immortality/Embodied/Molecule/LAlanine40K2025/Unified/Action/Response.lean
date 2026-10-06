import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.Orbitals
import H0mework.Versions.R2.Physics.YangMillsFlatQuantum.PairingOrigin

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open BasinRefinement SourceGaussianModel SourceFiniteData
open Stage9DEF
noncomputable section

/-- The complete U consumer supplies the original independent dual, not a replacement adjoint. -/
theorem full_U_action_response (p : BasePoint) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    Stage10.Runtime.configuration.conjugateMatter p (action (Stage10.Runtime.configuration.matter p)) =
      4 * (Stage9C.Material.SpinPair.spinScale : ℂ) *
        State.vectorEvaluation (Stage10.Runtime.tick.answer p) (Compatibility.responseMatrix action) := by
  have h := Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.quantumClosure.sourceResponse p action
  rw [Runtime.firstQuantumTick_answer, Runtime.fieldAt_eq_vector] at h
  simpa only [Stage10.Runtime.configuration_eq, Stage10.Runtime.tick_vector] using h

def testResponseMatrix (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex)
    (action : Module.End ℂ DiracExteriorMatterCarrier) : Matrix Basis Basis ℂ :=
  fun left right => star (orbitalWeight left scale p) *
    Stage10.Runtime.configuration.conjugateMatter p
      (action (holonomicMatterCovariantDerivative (orbitalTest right scale) p direction))

def sourceResponse (p : BasePoint) (action : Module.End ℂ DiracExteriorMatterCarrier) : ℂ :=
  4 * (Stage9C.Material.SpinPair.spinScale : ℂ) *
    State.vectorEvaluation (Stage10.Runtime.tick.answer p) (Compatibility.responseMatrix action)

/-- The original AO test matrix reads the full connection action and its spatial derivative term. -/
theorem original_AO_action_matrix (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex)
    (action : Module.End ℂ DiracExteriorMatterCarrier) (left right : Basis) :
    testResponseMatrix scale p direction action left right =
      star (orbitalWeight left scale p) * orbitalWeight right scale p *
        sourceResponse p (action.comp (Compatibility.covariantAction direction)) +
      star (orbitalWeight left scale p) * fieldDirectionalDerivative (orbitalWeight right scale) p direction *
        sourceResponse p action := by
  have original : holonomicMatterCovariantDerivative Stage10.Runtime.configuration p direction =
      Compatibility.covariantAction direction (Stage10.Runtime.configuration.matter p) := by
    rw [Stage10.Runtime.configuration_eq]
    exact (Compatibility.actual_covariantAction p direction).symm
  unfold testResponseMatrix
  rw [original_orbital_covariant, original]
  simp only [map_add,map_smul,smul_eq_mul]
  have first := full_U_action_response p (action.comp (Compatibility.covariantAction direction))
  have second := full_U_action_response p action
  simp only [LinearMap.comp_apply] at first
  rw [first,second]
  unfold sourceResponse
  ring

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
