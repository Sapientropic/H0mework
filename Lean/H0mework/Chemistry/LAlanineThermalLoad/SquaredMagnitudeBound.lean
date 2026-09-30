import H0mework.Chemistry.LAlanineThermalLoad.Block0
import H0mework.Chemistry.LAlanineThermalLoad.Block1
import H0mework.Chemistry.LAlanineThermalLoad.Block2
import H0mework.Chemistry.LAlanineThermalLoad.Block3
import H0mework.Chemistry.LAlanineThermalLoad.Block4
import H0mework.Chemistry.LAlanineThermalLoad.Block5
import H0mework.Chemistry.LAlanineThermalLoad.Block6

/-! # All original Hamiltonian entries consume their seven bounded square certificates -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer.StrictThermal

theorem sourceSquaredMagnitude_bound :
    sourceSquaredMagnitude ≤ 1600 * 1000000000000000 ^ 2 := by
  rw [sourceSquaredMagnitude_blocks]
  have rowBound (b : Fin 7) :
      sourceSquaredBlock b ≤ (![400, 400, 250, 125, 150, 125, 50] b : ℤ) *
        1000000000000000 ^ 2 := by
    fin_cases b
    · exact sourceSquaredBlock0_bound
    · exact sourceSquaredBlock1_bound
    · exact sourceSquaredBlock2_bound
    · exact sourceSquaredBlock3_bound
    · exact sourceSquaredBlock4_bound
    · exact sourceSquaredBlock5_bound
    · exact sourceSquaredBlock6_bound
  have combined := Finset.sum_le_sum (s := Finset.univ) (fun b _ => rowBound b)
  norm_num [Fin.sum_univ_succ] at combined ⊢
  linarith

end LAlanine40K2025.Thermal.Load.Producer.StrictThermal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
