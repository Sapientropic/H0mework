import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.Acted
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.Response

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open BasinRefinement SourceGaussianModel SourceFiniteData
open Stage9DEF
noncomputable section

def fullTestResponseMatrix (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex)
    (preparation observer : Module.End ℂ DiracExteriorMatterCarrier) : Matrix Basis Basis ℂ :=
  fun left right => star (orbitalWeight left scale p) *
    Stage10.Runtime.configuration.conjugateMatter p
      (observer (holonomicMatterCovariantDerivative
        (actedWeighted preparation (orbitalWeight right scale)) p direction))

/-- No occupied-coordinate truncation: the full mother preparation and its connection exchange enter the same matrix. -/
theorem full_AO_action_matrix (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex)
    (preparation observer : Module.End ℂ DiracExteriorMatterCarrier) (left right : Basis) :
    fullTestResponseMatrix scale p direction preparation observer left right =
      star (orbitalWeight left scale p) * orbitalWeight right scale p *
        sourceResponse p (observer.comp (preparation.comp (Compatibility.covariantAction direction))) +
      star (orbitalWeight left scale p) * fieldDirectionalDerivative (orbitalWeight right scale) p direction *
        sourceResponse p (observer.comp preparation) +
      star (orbitalWeight left scale p) * orbitalWeight right scale p *
        sourceResponse p (observer.comp ((connectionAction p direction).comp preparation -
          preparation.comp (connectionAction p direction))) := by
  have original : holonomicMatterCovariantDerivative Stage10.Runtime.configuration p direction =
      Compatibility.covariantAction direction (Stage10.Runtime.configuration.matter p) := by
    rw [Stage10.Runtime.configuration_eq]
    exact (Compatibility.actual_covariantAction p direction).symm
  unfold fullTestResponseMatrix
  rw [acted_weighted_covariant preparation (orbitalWeight right scale) p
    ((orbitalWeight_smooth right scale).differentiable (by simp) p),original]
  simp only [map_add,map_smul,smul_eq_mul]
  have first := full_U_action_response p (observer.comp (preparation.comp (Compatibility.covariantAction direction)))
  have second := full_U_action_response p (observer.comp preparation)
  have third := full_U_action_response p (observer.comp ((connectionAction p direction).comp preparation -
    preparation.comp (connectionAction p direction)))
  simp only [LinearMap.comp_apply] at first second third
  rw [first,second,third]
  unfold sourceResponse
  ring

theorem identity_preparation_recovers (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex)
    (observer : Module.End ℂ DiracExteriorMatterCarrier) :
    fullTestResponseMatrix scale p direction (LinearMap.id) observer =
      testResponseMatrix scale p direction observer := rfl

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
