import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Producer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Inverse

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Current
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def donorOrbit : Sym2 Basis := s(Spectrum.firstIndex,Spectrum.firstIndex)

theorem donor_resolvents : donorBlockResolvents donorOrbit :=
  source_isolation_resolvents Spectrum.firstIndex (source_top_pair_isolation Producer.actual_top_pair)

theorem donor_support :
    ∀ i j, pcOrbit i ≠ donorOrbit ∨ pcOrbit j ≠ donorOrbit → Source.donor i j = 0 :=
  original_donor_one_block donorOrbit donor_resolvents

theorem donor_preserves : Preserves pcOrbit Source.donor :=
  original_donor_preserves donorOrbit donor_resolvents

theorem inverse_preserves :
    Preserves pceOrbit (Measurement.sourceOutputObservable Load.Source.loadTotalHamiltonian) :=
  original_inverseObservable_preserves donor_preserves

theorem effect_preserves :
    Preserves pceOrbit (Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian) :=
  original_effect_preserves donor_preserves

theorem effect_root (k : Sym2 Basis) :
    restrict pceOrbit k (CFC.sqrt (Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian)) =
      CFC.sqrt (restrict pceOrbit k (Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian)) :=
  original_effect_block_root donor_preserves k

theorem complement_root (k : Sym2 Basis) :
    restrict pceOrbit k (CFC.sqrt (1 - Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian)) =
      CFC.sqrt (restrict pceOrbit k (1 - Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian)) :=
  original_complement_block_root donor_preserves k

theorem measurement_scale :
    Measurement.measurementScale (Measurement.sourceOutputObservable Load.Source.loadTotalHamiltonian) =
      1 + ‖fun k : Sym2 Basis => restrict pceOrbit k
        (Measurement.sourceOutputObservable Load.Source.loadTotalHamiltonian)‖ :=
  original_measurementScale_blocks donor_preserves

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Current
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
