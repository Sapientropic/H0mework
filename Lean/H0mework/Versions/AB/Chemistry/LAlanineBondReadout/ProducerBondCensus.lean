import H0mework.Versions.AB.Chemistry.LAlanineBondReadout.RepresentationBondConsumerKernel

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.Calculation

open LAlanine40K2025.Interface Consumers

theorem registeredSearch_complete_account :
    Source.calculation.heavyAtomCount = 6 ∧ Source.calculation.heavyPairCount = 15 ∧
    Source.calculation.registeredSeedCount = 675 ∧ Source.calculation.candidateCount = 5 ∧
    Source.calculation.admittedSeedCount = 311 ∧ Source.calculation.notAdmittedSeedCount = 364 ∧
    Source.calculation.admittedSeedCount + Source.calculation.notAdmittedSeedCount =
      Source.calculation.registeredSeedCount ∧ Source.calculation.positiveBCPCount = 5 := by
  decide +kernel

theorem sameDensity_energy_and_electrons :
    Source.calculation.sameDensityEnergyNanohartree = -323457454913 ∧
    Source.calculation.electronCountMicro = 48000000 ∧
    Source.calculation.independentAtomElectronCountMicro = 48000000 := by decide +kernel

theorem derivative_receipt :
    Source.calculation.maxGradientDerivativeErrorTrillion = 1398 ∧
    Source.calculation.maxHessianDerivativeErrorTrillion = 2459 := by decide +kernel

theorem everyBCP_positive_and_stable : ∀ pair, bcpIncidence pair = true →
    0 < (Source.pairReadoutAt pair).bcpDensityNano ∧
    0 < (Source.pairReadoutAt pair).bcpDensityDeltaNano ∧
    0 < (Source.pairReadoutAt pair).lineIntegralDensityDeltaNanoAngstrom ∧
    (Source.pairReadoutAt pair).pathEndpointsStable = true := by
  intro pair
  cases pair <;> decide +kernel

theorem independentAtomTopology_eq_actual : Source.independentAtomTopologyAt = bcpIncidence := by
  funext pair
  cases pair <;> rfl

theorem actualTopology_eq_retainedInitial :
    bcpIncidence = LAlanine40K2025.Calculation.bcpIncidence := by
  funext pair
  cases pair <;> rfl

theorem nonbond_midpoint_is_not_stationary :
    bcpIncidence .n003O001 = false ∧
    (Source.pairReadoutAt .n003O001).midpointGradientNormNano = 159664836 := by
  decide +kernel

theorem retainedGraph_does_not_fix_density_or_laplacian :
    (LAlanine40K2025.Source.pairReadoutAt .c004C005).bcpDensityNano = 247272356 ∧
    (Source.pairReadoutAt .c004C005).bcpDensityNano = 247259833 ∧
    0 < (LAlanine40K2025.Source.pairReadoutAt .c004O002).bcpLaplacianNano ∧
    (Source.pairReadoutAt .c004O002).bcpLaplacianNano < 0 := by
  decide +kernel

end LAlanine40K2025.BondReadout.Calculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
