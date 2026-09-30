import H0mework.Physics.LowEnergy.PacketFourier.Readback
import H0mework.Physics.LowEnergy.PacketFourier.Current

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace PacketNoise PacketDynamics GaugeHistory HistoryPrepared Stage9C.Material.SpinPair
noncomputable section
attribute [local irreducible] freeAction

theorem phaseCurrentMap_original {energy damping : ℝ} (map : SourceMap energy damping)
    (positive : 0 < damping) (shift : Position) (time : ℝ) (input : FullMatterL2) :
    phaseCurrentMap map shift time input=phaseCurrentField shift time (map.generator positive input) := by
  rw [phaseCurrentField_apply]
  change (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction (spatialFlow 0 (-time) (phaseShift shift ((evolve map time).hamiltonian input)))+
      adjointFlow time (((adjointEvolve map.boundary (-time)).shift shift).adjointHamiltonian input))=_
  rw [← (evolve map time).hamiltonian_value positive,
    ← ((adjointEvolve map.boundary (-time)).shift shift).adjoint_hamiltonian_value positive]
  have first : (evolve map time).generator positive input=flowDomain time (map.generator positive input) := Subtype.ext rfl
  have second : ((adjointEvolve map.boundary (-time)).shift shift).generator positive input=
      phaseDomain shift (adjointDomain (-time) (boundaryDomain (map.generator positive input))) := Subtype.ext rfl
  rw [first,second]

theorem phaseCurrentFilter_original (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (time : ℝ) (input : FullMatterL2) :
    phaseCurrentFilter energy damping positive shift time input=
      phaseCurrentField shift time (responseDomain energy damping positive input) := by
  change ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ) •
    phaseCurrentMap (greenMap energy damping positive) shift time input=_
  rw [phaseCurrentMap_original _ positive]
  exact (phaseCurrentField_smul shift time _ _).symm

theorem phaseCurrentFilter_prepared (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    phaseCurrentFilter energy damping positive shift time preparedPacket=
      phaseCurrentField shift time (preparedDomain energy damping positive) := by
  rw [phaseCurrentFilter_original]
  congr 1

theorem phaseMean_opposite (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    star (phaseMean energy damping positive shift time)=phaseMean energy damping positive (-shift) time := by
  simp only [phaseMean,phaseCurrentFilter_prepared]
  exact phaseCurrentMean_conj shift time (preparedDomain energy damping positive)

theorem phasePacket_original (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    phasePacket energy damping positive shift time=
      phaseCurrentField shift time (preparedDomain energy damping positive)-
        phaseCurrentMean shift time (preparedDomain energy damping positive) • filteredPacket energy damping positive := by
  change phaseCurrentFilter energy damping positive shift time preparedPacket-
    phaseMean energy damping positive shift time • filteredPacket energy damping positive=_
  rw [phaseCurrentFilter_prepared,phaseMean,phaseCurrentFilter_prepared]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
