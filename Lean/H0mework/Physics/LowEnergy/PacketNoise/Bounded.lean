import H0mework.Physics.LowEnergy.PacketNoise.Transforms

/-! The original graph identities generate the bounded composite A_h R; no current-domain certificate is an input. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen GaugeHistory Stage9C.Dynamics.Homogeneous
open Stage9C.Material.SpinPair
noncomputable section
attribute [local irreducible] freeAction yukawaOperator inversePrincipal

def SourceMap.current {energy damping : ℝ} (map : SourceMap energy damping) (transfer : Position) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction.comp ((cosineShift transfer).comp map.hamiltonian)+
      (map.boundary.cosine transfer).adjointHamiltonian)

theorem SourceMap.current_value {energy damping : ℝ} (map : SourceMap energy damping)
    (positive : 0 < damping) (transfer : Position) (input : FullMatterL2) :
    map.current transfer input=(((lapse^2)⁻¹ : ℝ) : ℂ) •
      (boundaryAction (cosineShift transfer (sourceHamiltonian (map.generator positive input)))+
        conjugateHamiltonian ((map.boundary.cosine transfer).generator positive input)) := by
  change (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction (cosineShift transfer (map.hamiltonian input))+
      (map.boundary.cosine transfer).adjointHamiltonian input)=_
  rw [← map.hamiltonian_value positive input,
    ← (map.boundary.cosine transfer).adjoint_hamiltonian_value positive input]

def currentGreen (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  (greenMap energy damping positive).current transfer

def currentFilter (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ) • currentGreen energy damping positive transfer

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
