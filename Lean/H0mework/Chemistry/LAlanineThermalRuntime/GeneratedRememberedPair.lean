import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedPairLaw
import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedThermalCollision
import H0mework.Chemistry.LAlanineEntropy.JointEnergyReadout

/-! # The remembered collision is the initial current of the timed pair flow -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Producer

open Propagation.Interface Propagation.Producer Collision Quantum
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
open scoped ComplexOrder

noncomputable section

def rememberedJoint (elapsed : ℝ) : JointMatrix Basis := timedPairAdvance elapsed generatedJoint
def rememberedSystem (elapsed : ℝ) : SystemMatrix Basis := systemReduce (rememberedJoint elapsed)
def rememberedBath (elapsed : ℝ) : SystemMatrix Basis := bathReduce (rememberedJoint elapsed)

theorem rememberedJoint_initial : rememberedJoint 0 = generatedJoint := timedPairAdvance_zero _

theorem rememberedJoint_receives_next (elapsed : ℝ) :
    rememberedJoint (elapsed + (nativeClockStep : ℝ)) = timedPairNativeStep (rememberedJoint elapsed) := by
  rw [add_comm]
  exact timedPairAdvance_add _ _ _

theorem rememberedJoint_posSemidef (elapsed : ℝ) : (rememberedJoint elapsed).PosSemidef :=
  timedPairAdvance_posSemidef elapsed generatedJoint generatedJoint_posSemidef

theorem rememberedJoint_trace (elapsed : ℝ) : (rememberedJoint elapsed).trace = 1 :=
  (timedPairAdvance_trace elapsed generatedJoint).trans generatedJoint_trace

theorem rememberedSystem_posSemidef (elapsed : ℝ) : (rememberedSystem elapsed).PosSemidef :=
  systemReduce_posSemidef _ (rememberedJoint_posSemidef elapsed)

theorem rememberedBath_posSemidef (elapsed : ℝ) : (rememberedBath elapsed).PosSemidef :=
  bathReduce_posSemidef _ (rememberedJoint_posSemidef elapsed)

theorem rememberedSystem_trace (elapsed : ℝ) : (rememberedSystem elapsed).trace = 1 :=
  (systemReduce_trace _).trans (rememberedJoint_trace elapsed)

theorem rememberedBath_trace (elapsed : ℝ) : (rememberedBath elapsed).trace = 1 :=
  (bathReduce_trace _).trans (rememberedJoint_trace elapsed)

theorem rememberedJoint_entropy (elapsed : ℝ) :
    spectralEntropy (rememberedJoint elapsed) (rememberedJoint_posSemidef elapsed)
      (rememberedJoint_trace elapsed) =
      spectralEntropy generatedJoint generatedJoint_posSemidef generatedJoint_trace :=
  pairAdvance_spectralEntropy energyHamiltonian energyHamiltonian_hermitian pairCoupling elapsed
    generatedJoint generatedJoint_posSemidef generatedJoint_trace

theorem rememberedPair_bareEnergy (elapsed : ℝ) :
    energy (jointHamiltonian energyHamiltonian) (rememberedJoint elapsed) =
      energy (jointHamiltonian energyHamiltonian) generatedJoint :=
  congrArg Complex.re (pairAdvance_bareEnergy energyHamiltonian energyHamiltonian_hermitian
    pairCoupling elapsed generatedJoint)

theorem rememberedPair_reducedEnergy (elapsed : ℝ) :
    energy energyHamiltonian (rememberedSystem elapsed) + energy energyHamiltonian (rememberedBath elapsed) =
      energy energyHamiltonian generatedSystem + energy energyHamiltonian generatedBath := by
  simpa only [jointEnergy_real_eq_reduced, rememberedSystem, rememberedBath,
    generatedSystem, generatedBath] using rememberedPair_bareEnergy elapsed

def couplingSetupEnergy : ℝ := energy ((pairCoupling : ℂ) • swapOperator) generatedJoint

theorem rememberedPair_interactionEnergy (elapsed : ℝ) :
    energy ((pairCoupling : ℂ) • swapOperator) (rememberedJoint elapsed) = couplingSetupEnergy :=
  congrArg Complex.re (pairAdvance_interactionEnergy energyHamiltonian energyHamiltonian_hermitian
    pairCoupling elapsed generatedJoint)

theorem rememberedPair_totalEnergy (elapsed : ℝ) :
    energy (pairH energyHamiltonian pairCoupling) (rememberedJoint elapsed) =
      energy (pairH energyHamiltonian pairCoupling) generatedJoint :=
  congrArg Complex.re (pairAdvance_totalEnergy energyHamiltonian energyHamiltonian_hermitian
    pairCoupling elapsed generatedJoint)

/-- Turning on the interaction has an explicit setup balance, even when later evolution conserves it. -/
theorem couplingSetup_disposition :
    energy (pairH energyHamiltonian pairCoupling) generatedJoint =
      energy (jointHamiltonian energyHamiltonian) generatedJoint + couplingSetupEnergy := by
  simp only [pairH, freePairH, energy, Matrix.add_mul, Matrix.trace_add, Complex.add_re,
    couplingSetupEnergy]

end

end LAlanine40K2025.Thermal.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
