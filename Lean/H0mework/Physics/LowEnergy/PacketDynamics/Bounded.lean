import H0mework.Physics.LowEnergy.PacketDynamics.Flow
import H0mework.Physics.LowEnergy.PacketDynamics.AdjointGraph

/-! Both ordered terms of the original time current are composed on source-generated graphs before readback. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace SpatialGreen PacketNoise Stage9C.Material.SpinPair
noncomputable section

def currentMap {energy damping : ℝ} (map : SourceMap energy damping) (shift : Position) (time : ℝ) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction.comp ((spatialFlow 0 (-time)).comp
      ((cosineShift shift).comp (evolve map time).hamiltonian))+
      (adjointFlow time).comp ((adjointEvolve map.boundary (-time)).cosine shift).adjointHamiltonian)

def timeCurrentGreen (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  currentMap (greenMap energy damping positive) shift time

def timeCurrentFilter (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ) • timeCurrentGreen energy damping positive shift time

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
