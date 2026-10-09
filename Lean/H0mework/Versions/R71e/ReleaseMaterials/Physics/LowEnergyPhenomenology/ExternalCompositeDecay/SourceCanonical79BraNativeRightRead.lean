import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraCurrentFunctionFold
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79NativeSourceRows
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79SourceSparseSums
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators

theorem sparse_current_native_right (i : Fin 79) (j : Fin 48) :
    sparseCurrentPoint i (nativeIndex79 j) =
      ∑s : Fin 8,sourceWeight (sourcePolynomialPoint true) i s *
        ActualCandidateBra.primalPairPoint (sourceField i s) (sourceIndex97 j) := by
  have h := raw_current_native_right ActualCandidateBra.primalPairPoint true false i j
  simp only [sourceMapPoint,actual_source_sparse_rows] at h
  rw [source_sparse_pair,source_sparse_sum_left] at h
  exact h

end LowEnergy.ActualCanonical79Imaginary
