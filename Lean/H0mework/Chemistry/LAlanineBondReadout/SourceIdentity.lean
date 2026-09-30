import H0mework.Chemistry.LAlanineBondReadout.SourceSourceBoundBondReadout

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.Source

theorem physicalTime_eq_parent : physicalTime = Runtime.bondParentTime := by
  rw [Runtime.bondParent_clock, Propagation.Producer.nativeClockStep_exact]
  change (46875000000000 : ℚ) / 36212777618028463 =
    3 * ((15625000000000 : ℚ) / 36212777618028463)
  norm_num

theorem no_extra_physical_step : physicalElapsedTime = 0 := by decide +kernel

end LAlanine40K2025.BondReadout.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
