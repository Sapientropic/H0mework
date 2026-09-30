import H0mework.Chemistry.LAlanineBondReadout.ProducerBondCensus

/-! `false` and `true` select the retained initial source and actual M3, not arbitrary states. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.HistoryConsumers

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open LAlanine40K2025.Interface

noncomputable section

def retainedOccurrenceGraph : Bool → ASUHeavyPair → Bool
  | false => LAlanine40K2025.Calculation.bcpIncidence
  | true => Consumers.bcpIncidence

def retainedOccurrenceDensity : Bool → Nat
  | false => (LAlanine40K2025.Source.pairReadoutAt .c004C005).bcpDensityNano
  | true => (Source.pairReadoutAt .c004C005).bcpDensityNano

def retainedOccurrenceEnergy : Bool → Int
  | false => LAlanine40K2025.Source.calculation.scfEnergyNanohartree
  | true => Source.calculation.sameDensityEnergyNanohartree

def densityRead : IndependentReadout Bool where
  Output := Nat
  read := retainedOccurrenceDensity

def energyRead : IndependentReadout Bool where
  Output := Int
  read := retainedOccurrenceEnergy

theorem graphProjection_kernelStrictlyCoarser :
    FaceKernelEscapeAt retainedOccurrenceGraph densityRead := by
  refine ⟨false, true, Calculation.actualTopology_eq_retainedInitial.symm, ?_⟩
  change (247272356 : Nat) ≠ 247259833
  decide +kernel

theorem graphProjection_energyEscape :
    FaceKernelEscapeAt retainedOccurrenceGraph energyRead := by
  refine ⟨false, true, Calculation.actualTopology_eq_retainedInitial.symm, ?_⟩
  change (-323451651859 : Int) ≠ -323457454913
  decide +kernel

theorem registeredGraph_cannotMint_density :
    ¬ Function.FactorsThrough retainedOccurrenceDensity retainedOccurrenceGraph :=
  graphProjection_kernelStrictlyCoarser.not_factorsThrough

theorem registeredGraph_cannotMint_energy :
    ¬ Function.FactorsThrough retainedOccurrenceEnergy retainedOccurrenceGraph :=
  graphProjection_energyEscape.not_factorsThrough

end
end LAlanine40K2025.BondReadout.HistoryConsumers
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
