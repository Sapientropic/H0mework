import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Producer.SourceGeneratedPointerEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerEnvironmentPreparation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Live

open Load.Source Powered.Dynamics
open scoped Matrix ComplexOrder
noncomputable section

abbrev ThermalSystem := (PairController × PairController) ⊕ (PairController × PairController)
def referenceSystem : Matrix ThermalSystem ThermalSystem ℂ := prepared Current.referencePair

theorem referenceSystem_positive : referenceSystem.PosSemidef :=
  prepared_positive _ Current.referencePair_positive

theorem referenceSystem_trace : referenceSystem.trace = 1 :=
  (prepared_trace _).trans Current.referencePair_trace

def thermalAction (current : State) : Matrix.unitaryGroup (ThermalSystem × Fin 2) ℂ :=
  Environment.reframeUnitary (current.action * blockUnitary received.action received.action)

def thermalJoint (current : State) : Matrix (ThermalSystem × Fin 2) (ThermalSystem × Fin 2) ℂ :=
  Environment.reframe current.joint

theorem thermalJoint_generated (current : State) :
    thermalJoint current = Load.Quantum.unitaryGibbsJoint referenceSystem environmentEnergies 1 (thermalAction current) :=
  Environment.actual_joint_gibbs Current.referencePair environmentEnergies 1 received.action current.action

theorem thermalJoint_positive (current : State) : (thermalJoint current).PosSemidef :=
  Environment.reframe_positive _ current.positive

theorem thermalJoint_trace (current : State) : (thermalJoint current).trace = 1 :=
  (Environment.reframe_trace _).trans current.normalized

def entropyProduction (current : State) : ℝ :=
  Load.Quantum.entropyProduction referenceSystem referenceSystem_positive referenceSystem_trace
    environmentEnergies 1 (thermalAction current)

theorem entropyProduction_nonnegative (current : State) : 0 ≤ entropyProduction current := by
  have : MeasurableSingletonClass ThermalSystem := ⟨by
    intro x
    cases x <;> simp [measurableSet_sum_iff, Set.preimage]⟩
  exact Load.Quantum.entropyProduction_nonnegative _ _ _ _ _ _

theorem entropyProduction_disposition (current : State) :
    entropyProduction current =
      Load.Quantum.jointMutualInformation referenceSystem referenceSystem_positive referenceSystem_trace
        environmentEnergies 1 (thermalAction current) +
      Load.Quantum.environmentGibbsExcess referenceSystem referenceSystem_positive referenceSystem_trace
        environmentEnergies 1 (thermalAction current) :=
  Load.Quantum.entropyProduction_eq_mutual_add_gibbs _ _ _ _ _ _

theorem initial_entropyProduction :
    entropyProduction initial = Current.entropyProduction received := by
  have kept := Environment.entropyProduction_prepared Current.referencePair Current.referencePair_positive
    Current.referencePair_trace environmentEnergies 1 received.action
  simpa only [entropyProduction, referenceSystem, thermalAction, initial, one_mul, Current.entropyProduction] using kept

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Live
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
