import H0mework.Versions.Y.Arithmetic.FockState.ParityMeasurement

/-!
# Source-generated species flux of an actual repair channel

The existing operational receipt, its coarse Fock-kernel trace, and the
ordered Z/2 current are retained in one dependent package.  This prevents a
factor-2 transition from being silently treated as invisible merely because
total additive charge is conserved.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFock

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticFullFactorRepairProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer

noncomputable section

/-- Actual repair receipt with both the old charge-kernel trace and its newly
visible ordered species current. -/
structure GeneratedRepairSpeciesFluxAt
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (receipt : OperationalFactorDecayChannelReceiptAt (.repair alternative)) :
    Type where
  private mk ::
  coarseTrace : GeneratedFactorDecayFockTraceAt (.repair alternative) receipt
  coarseTrace_eq : coarseTrace =
    generateFactorDecayFockTrace (.repair alternative) receipt
  speciesFlux : SpeciesGrade × SpeciesGrade
  speciesFlux_eq : speciesFlux = repairSpeciesFlux alternative
  speciesFluxZeroIffOddFactor :
    speciesFlux = 0 ↔ alternative.factor ≠ 2
  refinedMeasurementEqualIffOddFactor :
    atomicJointMeasurement alternative.target = atomicJointMeasurement source ↔
      alternative.factor ≠ 2
  coarseMeasurementConserved :
    jointMeasurement (splitParticleState source) =
      jointMeasurement (splitParticleState alternative.target)
  recollects :
    coarseTrace.targetState + coarseTrace.trace = coarseTrace.sourceState

def generateRepairSpeciesFlux
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (receipt : OperationalFactorDecayChannelReceiptAt (.repair alternative)) :
    GeneratedRepairSpeciesFluxAt alternative receipt :=
  { coarseTrace := generateFactorDecayFockTrace (.repair alternative) receipt
    coarseTrace_eq := rfl
    speciesFlux := repairSpeciesFlux alternative
    speciesFlux_eq := rfl
    speciesFluxZeroIffOddFactor :=
      repairSpeciesFlux_eq_zero_iff_factor_ne_two alternative
    refinedMeasurementEqualIffOddFactor :=
      repair_atomicJointMeasurement_eq_iff_factor_ne_two alternative
    coarseMeasurementConserved :=
      factorDecay_split_measurement_eq (.repair alternative)
    recollects := (generateFactorDecayFockTrace
      (.repair alternative) receipt).recollects }

theorem generatedRepair_factorTwo_visible
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (receipt : OperationalFactorDecayChannelReceiptAt (.repair alternative))
    (factorTwo : alternative.factor = 2) :
    (generateRepairSpeciesFlux alternative receipt).speciesFlux ≠ 0 ∧
      atomicJointMeasurement alternative.target ≠
        atomicJointMeasurement source := by
  constructor
  · exact repairSpeciesFlux_ne_zero_of_factor_eq_two
      alternative factorTwo
  · exact repair_atomicJointMeasurement_ne_of_factor_eq_two
      alternative factorTwo

theorem generatedRepair_oddFactor_coherent
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (receipt : OperationalFactorDecayChannelReceiptAt (.repair alternative))
    (factorNeTwo : alternative.factor ≠ 2) :
    (generateRepairSpeciesFlux alternative receipt).speciesFlux = 0 ∧
      atomicJointMeasurement alternative.target =
        atomicJointMeasurement source :=
  ⟨repairSpeciesFlux_eq_zero_of_factor_ne_two alternative factorNeTwo,
    repair_atomicJointMeasurement_eq_of_factor_ne_two alternative factorNeTwo⟩

end

end ParticleWaveFock
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
