import H0mework.Chemistry.LAlanineRefillRows.Block0
import H0mework.Chemistry.LAlanineRefillRows.Block1
import H0mework.Chemistry.LAlanineRefillRows.Block2
import H0mework.Chemistry.LAlanineRefillRows.Block3
import H0mework.Chemistry.LAlanineRefillRows.Block4
import H0mework.Chemistry.LAlanineRefillRows.Block5
import H0mework.Chemistry.LAlanineRefillRows.Block6

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.SourcePrimitive

open Propagation.Interface

theorem sourceRows_cache_exact (i : Basis) :
    sourceCachedGershDiagonal i = sourceGershDiagonal i ∧
      sourceCachedDensityRowMass i = sourceDensityRowMass i := by
  obtain ⟨⟨block, offset⟩, rfl⟩ := (finProdFinEquiv : Fin 7 × Fin 14 ≃ Fin 98).surjective i
  fin_cases block
  · exact sourceRowCacheBlock0 offset
  · exact sourceRowCacheBlock1 offset
  · exact sourceRowCacheBlock2 offset
  · exact sourceRowCacheBlock3 offset
  · exact sourceRowCacheBlock4 offset
  · exact sourceRowCacheBlock5 offset
  · exact sourceRowCacheBlock6 offset

noncomputable def sourceGershShiftedNumerator : ℤ :=
  ∑ i : Basis, (sourceGershDiagonal i + 8 * 1000000000000000) * sourceDensityRowMass i

set_option maxRecDepth 4096 in
theorem sourceCachedGershShifted_exact :
    (∑ i : Basis, (sourceCachedGershDiagonal i + 8 * 1000000000000000) * sourceCachedDensityRowMass i) =
      58032657897527496672781307966405294620160 := by decide

theorem sourceGershShiftedNumerator_positive : 0 < sourceGershShiftedNumerator := by
  have exactRows : sourceGershShiftedNumerator =
      ∑ i : Basis, (sourceCachedGershDiagonal i + 8 * 1000000000000000) * sourceCachedDensityRowMass i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(sourceRows_cache_exact i).1, (sourceRows_cache_exact i).2]
  rw [exactRows, sourceCachedGershShifted_exact]
  norm_num

set_option maxRecDepth 4096 in
theorem sourceCachedGramMass_exact :
    (∑ i : Basis, sourceCachedDensityRowMass i) = 95999999999993451236866761 := by decide

theorem sourceGramIntegerMass_exact :
    (∑ i : Basis, sourceDensityRowMass i) = 95999999999993451236866761 := by
  have equality : (∑ i : Basis, sourceDensityRowMass i) = ∑ i : Basis, sourceCachedDensityRowMass i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (sourceRows_cache_exact i).2.symm
  rw [equality, sourceCachedGramMass_exact]

end LAlanine40K2025.Thermal.Recovery.SourcePrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
