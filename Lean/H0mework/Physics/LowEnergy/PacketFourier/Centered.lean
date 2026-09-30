import H0mework.Physics.LowEnergy.PacketFourier.Original
import H0mework.Physics.LowEnergy.PacketFourier.Quadrature
import H0mework.Physics.LowEnergy.PacketDynamics.Native

/-! The actual cosine and sine responses are two quadratures of one Fourier current and one fixed source preparation. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace PacketNoise PacketDynamics HistoryPrepared
noncomputable section

theorem currentFilter_cosine (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    timeCurrentFilter energy damping positive shift time=(1/2 : ℂ) •
      (phaseCurrentFilter energy damping positive shift time+phaseCurrentFilter energy damping positive (-shift) time) := by
  apply ContinuousLinearMap.ext
  intro input
  change timeCurrentFilter energy damping positive shift time input=(1/2 : ℂ) •
    (phaseCurrentFilter energy damping positive shift time input+phaseCurrentFilter energy damping positive (-shift) time input)
  rw [timeCurrentFilter_original,phaseCurrentFilter_original,phaseCurrentFilter_original]
  exact (phaseCurrent_cosine shift time _).symm

theorem mean_cosine (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    timeMean energy damping positive shift time=(1/2 : ℂ)*
      (phaseMean energy damping positive shift time+phaseMean energy damping positive (-shift) time) := by
  rw [timeMean,currentFilter_cosine]
  change inner ℂ (filteredPacket energy damping positive) ((1/2 : ℂ) •
    (phaseCurrentFilter energy damping positive shift time preparedPacket+
      phaseCurrentFilter energy damping positive (-shift) time preparedPacket))=_
  rw [inner_smul_right,inner_add_right]
  rfl

def sineCurrentFilter (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  (2*Complex.I)⁻¹ •
    (phaseCurrentFilter energy damping positive shift time-phaseCurrentFilter energy damping positive (-shift) time)

theorem sineCurrentFilter_original (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (time : ℝ) (input : FullMatterL2) :
    sineCurrentFilter energy damping positive shift time input=
      sineCurrentField shift time (responseDomain energy damping positive input) := by
  change (2*Complex.I)⁻¹ •
    (phaseCurrentFilter energy damping positive shift time input-phaseCurrentFilter energy damping positive (-shift) time input)=_
  rw [phaseCurrentFilter_original,phaseCurrentFilter_original,sineCurrentField_apply]

def sineMean (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) : ℂ :=
  inner ℂ (filteredPacket energy damping positive) (sineCurrentFilter energy damping positive shift time preparedPacket)

theorem mean_sine (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    sineMean energy damping positive shift time=(2*Complex.I)⁻¹*
      (phaseMean energy damping positive shift time-phaseMean energy damping positive (-shift) time) := by
  change inner ℂ (filteredPacket energy damping positive) ((2*Complex.I)⁻¹ •
    (phaseCurrentFilter energy damping positive shift time preparedPacket-
      phaseCurrentFilter energy damping positive (-shift) time preparedPacket))=_
  rw [inner_smul_right,inner_sub_right]
  rfl

def sinePacket (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) : FullMatterL2 :=
  sineCurrentFilter energy damping positive shift time preparedPacket-
    sineMean energy damping positive shift time • filteredPacket energy damping positive

theorem packet_cosine (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    packetCurrent energy damping positive shift time=(1/2 : ℂ) •
      (phasePacket energy damping positive shift time+phasePacket energy damping positive (-shift) time) := by
  change timeCurrentFilter energy damping positive shift time preparedPacket-
    timeMean energy damping positive shift time • filteredPacket energy damping positive=_
  rw [currentFilter_cosine,mean_cosine]
  change (1/2 : ℂ) • (phaseCurrentFilter energy damping positive shift time preparedPacket+
      phaseCurrentFilter energy damping positive (-shift) time preparedPacket)-
    ((1/2 : ℂ)*(phaseMean energy damping positive shift time+phaseMean energy damping positive (-shift) time)) •
      filteredPacket energy damping positive=
    (1/2 : ℂ) • ((phaseCurrentFilter energy damping positive shift time preparedPacket-
        phaseMean energy damping positive shift time • filteredPacket energy damping positive)+
      (phaseCurrentFilter energy damping positive (-shift) time preparedPacket-
        phaseMean energy damping positive (-shift) time • filteredPacket energy damping positive))
  module

theorem packet_sine (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    sinePacket energy damping positive shift time=(2*Complex.I)⁻¹ •
      (phasePacket energy damping positive shift time-phasePacket energy damping positive (-shift) time) := by
  rw [sinePacket,mean_sine]
  change (2*Complex.I)⁻¹ • (phaseCurrentFilter energy damping positive shift time preparedPacket-
      phaseCurrentFilter energy damping positive (-shift) time preparedPacket)-
    ((2*Complex.I)⁻¹*(phaseMean energy damping positive shift time-phaseMean energy damping positive (-shift) time)) •
      filteredPacket energy damping positive=
    (2*Complex.I)⁻¹ • ((phaseCurrentFilter energy damping positive shift time preparedPacket-
        phaseMean energy damping positive shift time • filteredPacket energy damping positive)-
      (phaseCurrentFilter energy damping positive (-shift) time preparedPacket-
        phaseMean energy damping positive (-shift) time • filteredPacket energy damping positive))
  module

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
