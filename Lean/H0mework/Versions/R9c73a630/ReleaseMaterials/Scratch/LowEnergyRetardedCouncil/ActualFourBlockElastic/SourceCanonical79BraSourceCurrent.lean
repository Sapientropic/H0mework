import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairs
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79SourceSparseRows
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79SourceSparseSums
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79SourceConjugate
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraCurrents
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators

theorem actual_primal_pair_symmetric (a b : Fin 97) :
    ActualCandidateBra.primalPairPoint a b = ActualCandidateBra.primalPairPoint b a := by
  rw [← ActualCandidateBra.actual_entry_pair a b,← ActualCandidateBra.actual_entry_pair b a]
  exact ActualCandidateBra.actual_tensor_symmetric _ _

theorem actual_primal_source_current (i j : Fin 79) :
    (∑a : Fin 97,∑b : Fin 97,sourceMapPoint true i a *
      ActualCandidateBra.primalPairPoint a b * sourceMapPoint false j b) =
        primalCurrentPoint i j := by
  simp only [sourceMapPoint,actual_source_sparse_rows]
  rw [source_sparse_pair]
  exact actual_sparse_current i j

theorem actual_source_current (dual : Bool) (i j : Fin 79) :
    (∑a : Fin 97,∑b : Fin 97,sourceMapPoint true i a *
      ActualCandidateBra.pairPoint dual a b * sourceMapPoint false j b) =
        currentPoint dual i j := by
  cases dual
  · change (∑a : Fin 97,∑b : Fin 97,sourceMapPoint true i a *
      ActualCandidateBra.primalPairPoint a b * sourceMapPoint false j b) =
        primalCurrentPoint i j
    exact actual_primal_source_current i j
  · change (∑a : Fin 97,∑b : Fin 97,sourceMapPoint true i a *
      star (ActualCandidateBra.primalPairPoint a b) * sourceMapPoint false j b) =
        star (primalCurrentPoint j i)
    rw [← actual_primal_source_current j i]
    simpa only [actual_source_point_star] using
      conjugate_source_current (sourceMapPoint false) ActualCandidateBra.primalPairPoint
        actual_primal_pair_symmetric i j

end LowEnergy.ActualCanonical79Imaginary
