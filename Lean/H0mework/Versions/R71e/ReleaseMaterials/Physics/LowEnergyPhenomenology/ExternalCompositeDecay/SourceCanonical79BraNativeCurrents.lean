import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNativeCurrentRows0
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNativeCurrentRows1
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNativeCurrentRows2
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNativeCurrentRows3
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79NativeCurrentData
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79SourceSparseSums
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators

private theorem raw_sparse_current (i j : Fin 79) :
    (∑a : Fin 97,∑b : Fin 97,
      sourceMapPoint true i a * ActualCandidateBra.primalPairPoint a b *
        sourceMapPoint false j b) = sparseCurrentPoint i j := by
  simp only [sourceMapPoint,actual_source_sparse_rows]
  exact source_sparse_pair (sourcePolynomialPoint true) (sourcePolynomialPoint false)
    i j ActualCandidateBra.primalPairPoint

private theorem native_heavy_current (i : Fin 48) (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint (nativeIndex79 i) j = primalCurrentPoint (nativeIndex79 i) j := by
  fin_cases i
  · exact actual_native_heavy_current_row0 j heavy
  · exact actual_native_heavy_current_row1 j heavy
  · exact actual_native_heavy_current_row2 j heavy
  · exact actual_native_heavy_current_row3 j heavy
  · exact actual_native_heavy_current_row4 j heavy
  · exact actual_native_heavy_current_row5 j heavy
  · exact actual_native_heavy_current_row6 j heavy
  · exact actual_native_heavy_current_row7 j heavy
  · exact actual_native_heavy_current_row8 j heavy
  · exact actual_native_heavy_current_row9 j heavy
  · exact actual_native_heavy_current_row10 j heavy
  · exact actual_native_heavy_current_row11 j heavy
  · exact actual_native_heavy_current_row12 j heavy
  · exact actual_native_heavy_current_row13 j heavy
  · exact actual_native_heavy_current_row14 j heavy
  · exact actual_native_heavy_current_row15 j heavy
  · exact actual_native_heavy_current_row16 j heavy
  · exact actual_native_heavy_current_row17 j heavy
  · exact actual_native_heavy_current_row18 j heavy
  · exact actual_native_heavy_current_row19 j heavy
  · exact actual_native_heavy_current_row20 j heavy
  · exact actual_native_heavy_current_row21 j heavy
  · exact actual_native_heavy_current_row22 j heavy
  · exact actual_native_heavy_current_row23 j heavy
  · exact actual_native_heavy_current_row24 j heavy
  · exact actual_native_heavy_current_row25 j heavy
  · exact actual_native_heavy_current_row26 j heavy
  · exact actual_native_heavy_current_row27 j heavy
  · exact actual_native_heavy_current_row28 j heavy
  · exact actual_native_heavy_current_row29 j heavy
  · exact actual_native_heavy_current_row30 j heavy
  · exact actual_native_heavy_current_row31 j heavy
  · exact actual_native_heavy_current_row32 j heavy
  · exact actual_native_heavy_current_row33 j heavy
  · exact actual_native_heavy_current_row34 j heavy
  · exact actual_native_heavy_current_row35 j heavy
  · exact actual_native_heavy_current_row36 j heavy
  · exact actual_native_heavy_current_row37 j heavy
  · exact actual_native_heavy_current_row38 j heavy
  · exact actual_native_heavy_current_row39 j heavy
  · exact actual_native_heavy_current_row40 j heavy
  · exact actual_native_heavy_current_row41 j heavy
  · exact actual_native_heavy_current_row42 j heavy
  · exact actual_native_heavy_current_row43 j heavy
  · exact actual_native_heavy_current_row44 j heavy
  · exact actual_native_heavy_current_row45 j heavy
  · exact actual_native_heavy_current_row46 j heavy
  · exact actual_native_heavy_current_row47 j heavy

theorem actual_native_sparse_current (i : Fin 48) (j : Fin 79) :
    sparseCurrentPoint (nativeIndex79 i) j = primalCurrentPoint (nativeIndex79 i) j := by
  by_cases hj : j.val < 48
  · let j' : Fin 48 := ⟨j.val,hj⟩
    have heq : nativeIndex79 j' = j := Fin.ext rfl
    rw [←heq]
    calc
      _ = ∑a : Fin 97,∑b : Fin 97,
          sourceMapPoint true (nativeIndex79 i) a * ActualCandidateBra.primalPairPoint a b *
            sourceMapPoint false (nativeIndex79 j') b :=
        (raw_sparse_current (nativeIndex79 i) (nativeIndex79 j')).symm
      _ = ActualCandidateBra.primalPairPoint (sourceIndex97 i) (sourceIndex97 j') :=
        raw_current_native_both ActualCandidateBra.primalPairPoint true false i j'
      _ = primalCurrentPoint (nativeIndex79 i) (nativeIndex79 j') :=
        actual_native_current_data i j'
  · exact native_heavy_current i j (Nat.le_of_not_lt hj)

end LowEnergy.ActualCanonical79Imaginary
