import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.TwoBodyResponse
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData
open scoped Matrix
noncomputable section

structure Material where
  parent : ManyBody.Material
  twoBody : SpinBasis → SpinBasis → SpinBasis → SpinBasis → ℂ
  spinSummed : Basis → Basis → Basis → Basis → ℂ

def material : Material where
  parent := ManyBody.material
  twoBody := ManyBody.twoBodyContraction
  spinSummed := ManyBody.spinSummedTwoBody

theorem parent_identity : material.parent = ManyBody.material := rfl
theorem source_state : material.parent.state = ManyBody.slaterState := rfl
theorem double_replacement_response : type_of% ManyBody.dual_double_replaced :=
  ManyBody.dual_double_replaced
theorem actual_pair_contraction (x₁ x₂ y₁ y₂ : SpinBasis) :
    material.twoBody x₁ x₂ y₁ y₂ =
      material.parent.oneBody x₁ y₁ * material.parent.oneBody x₂ y₂ -
        material.parent.oneBody x₁ y₂ * material.parent.oneBody x₂ y₁ :=
  ManyBody.two_body_wick x₁ x₂ y₁ y₂
theorem actual_pair_projector (x₁ x₂ y₁ y₂ : SpinBasis) :
    material.twoBody x₁ x₂ y₁ y₂ =
      spinProjector x₁ y₁ * spinProjector x₂ y₂ -
        spinProjector x₁ y₂ * spinProjector x₂ y₁ :=
  ManyBody.two_body_source_projector x₁ x₂ y₁ y₂
theorem actual_pair_exchange (x₁ x₂ y₁ y₂ : SpinBasis) :
    material.twoBody x₂ x₁ y₁ y₂ = -material.twoBody x₁ x₂ y₁ y₂ :=
  ManyBody.two_body_left_exchange x₁ x₂ y₁ y₂
theorem actual_pair_diagonal_zero (x y₁ y₂ : SpinBasis) :
    material.twoBody x x y₁ y₂ = 0 :=
  ManyBody.two_body_same_spin_orbital x y₁ y₂
theorem actual_spin_summed_pair (i j k l : Basis) :
    material.spinSummed i j k l =
      (4 : ℂ) * projector24 i k * projector24 j l -
        (2 : ℂ) * projector24 i l * projector24 j k :=
  ManyBody.spin_summed_two_body i j k l

structure Closure : Prop where
  parent : ManyBody.Closure
  parentIdentity : type_of% parent_identity
  sourceState : type_of% source_state
  doubleReplacement : type_of% double_replacement_response
  oneBody : type_of% actual_pair_contraction
  projector : type_of% actual_pair_projector
  exchange : type_of% actual_pair_exchange
  diagonal : type_of% actual_pair_diagonal_zero
  spinSum : type_of% actual_spin_summed_pair

theorem sourceGeneratedClosure : Closure :=
  ⟨ManyBody.sourceGeneratedClosure,parent_identity,source_state,double_replacement_response,
    actual_pair_contraction,actual_pair_projector,actual_pair_exchange,
    actual_pair_diagonal_zero,actual_spin_summed_pair⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
