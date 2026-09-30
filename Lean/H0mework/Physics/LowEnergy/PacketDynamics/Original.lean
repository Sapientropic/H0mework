import H0mework.Physics.LowEnergy.PacketDynamics.Readback
import H0mework.Physics.LowEnergy.PacketDynamics.Current

/-! The time-dependent bounded source composite is the original domain current; its zero-time value is the certified continuum packet current. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace PacketNoise GaugeHistory HistoryPrepared Stage9C.Material.SpinPair
noncomputable section
attribute [local irreducible] freeAction

theorem currentMap_original {energy damping : ℝ} (map : SourceMap energy damping)
    (positive : 0 < damping) (shift : Position) (time : ℝ) (input : FullMatterL2) :
    currentMap map shift time input=timeCurrentField shift time (map.generator positive input) := by
  rw [timeCurrentField_apply]
  change (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction (spatialFlow 0 (-time) (cosineShift shift ((evolve map time).hamiltonian input)))+
      adjointFlow time (((adjointEvolve map.boundary (-time)).cosine shift).adjointHamiltonian input))=_
  rw [← (evolve map time).hamiltonian_value positive,
    ← ((adjointEvolve map.boundary (-time)).cosine shift).adjoint_hamiltonian_value positive]
  have first : (evolve map time).generator positive input=flowDomain time (map.generator positive input) := Subtype.ext rfl
  have second : ((adjointEvolve map.boundary (-time)).cosine shift).generator positive input=
      cosineDomain shift (adjointDomain (-time) (boundaryDomain (map.generator positive input))) := Subtype.ext rfl
  rw [first,second]

theorem timeCurrentFilter_original (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (time : ℝ) (input : FullMatterL2) :
    timeCurrentFilter energy damping positive shift time input=
      timeCurrentField shift time (responseDomain energy damping positive input) := by
  change ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ) •
    currentMap (greenMap energy damping positive) shift time input=_
  rw [currentMap_original _ positive]
  exact (timeCurrentField_smul shift time _ _).symm

theorem timeCurrentFilter_prepared (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    timeCurrentFilter energy damping positive shift time preparedPacket=
      timeCurrentField shift time (preparedDomain energy damping positive) := by
  rw [timeCurrentFilter_original]
  congr 1

theorem timeMean_real (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    star (timeMean energy damping positive shift time)=timeMean energy damping positive shift time := by
  rw [timeMean,timeCurrentFilter_prepared]
  exact timeCurrentMean_real shift time (preparedDomain energy damping positive)

theorem timeCurrentFilter_zero (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    timeCurrentFilter energy damping positive shift 0=currentFilter energy damping positive shift := by
  ext input
  rw [timeCurrentFilter_original,timeCurrentField_zero,← currentFilter_original]

theorem timeMean_zero (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    timeMean energy damping positive shift 0=packetMean energy damping positive shift := by
  rw [timeMean,timeCurrentFilter_zero]
  rfl

theorem timeCenteredFilter_zero (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    timeCenteredFilter energy damping positive shift 0=centeredFilter energy damping positive shift := by
  rw [timeCenteredFilter,timeCurrentFilter_zero,timeMean_zero]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
