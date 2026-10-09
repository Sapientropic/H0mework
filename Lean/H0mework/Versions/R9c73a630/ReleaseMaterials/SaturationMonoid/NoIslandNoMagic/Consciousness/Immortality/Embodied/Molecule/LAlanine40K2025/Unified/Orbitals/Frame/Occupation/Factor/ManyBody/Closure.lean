import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Spectral.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
noncomputable section

structure Material where
  parent : Spectral.Material
  state : ⋀[ℂ]^48 OneBody
  spatialState : ℝ → ⋀[ℂ]^48 SpinWaveSpace
  dual : Module.Dual ℂ (⋀[ℂ]^48 OneBody)
  oneBody : Matrix SpinBasis SpinBasis ℂ
  spinSummed : Matrix Basis Basis ℂ

def material : Material where
  parent := Spectral.material
  state := slaterState
  spatialState := spatialSlaterState
  dual := slaterDual
  oneBody := fun x y => oneBodyContraction x y
  spinSummed := spinSummedContraction

theorem parent_identity : material.parent = Spectral.material := rfl
theorem state_pairing : material.dual material.state = 1 := slater_pairing
theorem state_nonzero : material.state ≠ 0 := slater_nonzero
theorem physical_state_nonzero (time : ℝ) : material.spatialState time ≠ 0 :=
  spatial_slater_nonzero time
theorem physical_state_source (time : ℝ) : material.spatialState time =
    exteriorPower.ιMulti ℂ 48
      (fun k => preparedSpinWave time (orbitalFamily k)) :=
  spatial_slater_source time
theorem state_exchange (σ : Equiv.Perm (Fin 48)) :
    exteriorPower.ιMulti ℂ 48 (orbitalFamily ∘ σ) =
      Equiv.Perm.sign σ • material.state := slater_exchange σ
theorem one_body_from_state (x y : SpinBasis) :
    material.oneBody x y = material.parent.parent.spinProjector x y :=
  one_body_contraction_exact x y
theorem spin_summed_from_state :
    material.spinSummed = material.parent.parent.spinSummed := spin_summed_contraction
theorem gamma_from_state_error :
    ‖material.parent.originalGamma - material.spinSummed‖ < (1 / 10^5 : ℝ) :=
  actual_U_one_body_error

structure Closure : Prop where
  parent : Spectral.Closure
  parentIdentity : type_of% parent_identity
  paired : material.dual material.state = 1
  nonzero : material.state ≠ 0
  spatialNonzero : type_of% physical_state_nonzero
  spatialSource : type_of% physical_state_source
  exchange : type_of% state_exchange
  oneBody : type_of% one_body_from_state
  spinSum : type_of% spin_summed_from_state
  gammaError : ‖material.parent.originalGamma - material.spinSummed‖ <
    (1 / 10^5 : ℝ)

theorem sourceGeneratedClosure : Closure :=
  ⟨Spectral.sourceGeneratedClosure,parent_identity,state_pairing,state_nonzero,
    physical_state_nonzero,physical_state_source,state_exchange,one_body_from_state,
    spin_summed_from_state,gamma_from_state_error⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
