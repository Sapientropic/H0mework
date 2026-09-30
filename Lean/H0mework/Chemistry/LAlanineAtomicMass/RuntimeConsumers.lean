import H0mework.Chemistry.LAlanineAtomicMass.RuntimeParentConsumers

/-! The installed isotope certificate feeds the exact original M3 dynamical readouts. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.AtomicMass.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

theorem atomicMassRuntime_identity :
    type_of% (atomicMassRuntimeFace_factorizes atomicMassRuntimeSeed (.component .certificate)) ∧
    type_of% Source.preparation_convention ∧ type_of% Source.actualMass_original ∧
    type_of% Source.preparation_conversion ∧ type_of% Source.massNumber_eq_recorded ∧
    type_of% Source.massNumber_positive ∧ type_of% Source.source_integer_margin ∧
    type_of% source_isotope_assignment ∧ type_of% isotopeFace_kernelExact ∧
    type_of% everyAtomicConsumer_uniqueFactorization ∧ type_of% atomicResidual_reconstructs ∧
    type_of% source_isotope_census ∧ type_of% nitrogen_isotope :=
  ⟨atomicMassRuntime_sourceCertificate.1, atomicMassRuntime_sourceCertificate.2.convention,
    atomicMassRuntime_sourceCertificate.2.originalMass, atomicMassRuntime_sourceCertificate.2.conversion,
    atomicMassRuntime_sourceCertificate.2.integerRecognition,
    atomicMassRuntime_sourceCertificate.2.integerPositive, atomicMassRuntime_sourceCertificate.2.integerMargin,
    atomicMassRuntime_sourceCertificate.2.sourceSpecies, atomicMassRuntime_sourceCertificate.2.exactKernel,
    atomicMassRuntime_sourceCertificate.2.everyConsumer, atomicMassRuntime_sourceCertificate.2.retainedAtom,
    atomicMassRuntime_sourceCertificate.2.census, atomicMassRuntime_sourceCertificate.2.nitrogen⟩

theorem atomicMassRuntime_dynamics :
    type_of% (atomicMassRuntimeFace_factorizes atomicMassRuntimeSeed (.component .certificate)) ∧
    type_of% Source.massNumberResidual_bound ∧ type_of% Source.conversionResidual_bound ∧
    type_of% Source.reconstructedMass_eq_actual ∧ type_of% Source.preparedMass_reconstruction ∧
    type_of% Dynamics.actual_target_from_isotope_mass ∧ type_of% Dynamics.actual_kinetic_from_isotope_mass ∧
    type_of% Dynamics.actual_energy_from_isotope_mass ∧ type_of% Dynamics.nitrogenVelocityAtMass_injective ∧
    type_of% Dynamics.integer_mass_changes_actual_velocity :=
  ⟨atomicMassRuntime_sourceCertificate.1, atomicMassRuntime_sourceCertificate.2.massFraction,
    atomicMassRuntime_sourceCertificate.2.conversionError,
    atomicMassRuntime_sourceCertificate.2.reconstructedMass, atomicMassRuntime_sourceCertificate.2.preparedMass,
    atomicMassRuntime_sourceCertificate.2.actualTarget, atomicMassRuntime_sourceCertificate.2.actualKinetic,
    atomicMassRuntime_sourceCertificate.2.actualEnergy, atomicMassRuntime_sourceCertificate.2.massSensitive,
    atomicMassRuntime_sourceCertificate.2.integerHostile⟩

theorem atomicMassRuntime_materialRecognition :
    type_of% (atomicMassRuntimeFace_factorizes atomicMassRuntimeSeed (.component .material)) ∧
    generatedAtomicMassMaterial.preparation = Source.preparation ∧
    generatedAtomicMassMaterial.species = isotopeFace ∧
    generatedAtomicMassMaterial.relativeMasses = Source.relativeMass ∧
    generatedAtomicMassMaterial.massNumberResiduals = Source.massNumberResidual ∧
    generatedAtomicMassMaterial.conversionResiduals = Source.conversionResidual ∧
    generatedAtomicMassMaterial.reconstructedMasses = Source.reconstructedMass ∧
    generatedAtomicMassMaterial.atomicFibres = atomEquivIsotopeResidual ∧
    generatedAtomicMassMaterial.nuclearReference = Dynamics.reconstructedReference ∧
    generatedAtomicMassMaterial.targetKinetic = Dynamics.reconstructedKinetic :=
  ⟨atomicMassRuntimeFace_factorizes atomicMassRuntimeSeed (.component .material),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem atomicMassRuntime_actualMass (runtime : LivingRuntimeState atomicMassRuntimeProcess) :
    type_of% (atomicMassRuntimeFace_factorizes runtime (.component .material)) ∧
    generatedAtomicMassMaterial.reconstructedMasses =
      (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.masses := by
  refine ⟨atomicMassRuntimeFace_factorizes runtime (.component .material), ?_⟩
  rw [atomicMassRuntime_response]
  exact Source.reconstructedMass_eq_actual

end
end LAlanine40K2025.AtomicMass.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
