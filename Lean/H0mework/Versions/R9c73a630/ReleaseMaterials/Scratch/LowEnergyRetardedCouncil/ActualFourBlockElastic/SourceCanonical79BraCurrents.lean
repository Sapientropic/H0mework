import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraNativeCurrents
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraHeavyCurrents
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

theorem actual_sparse_current (i j : Fin 79) :
    sparseCurrentPoint i j = primalCurrentPoint i j := by
  by_cases h : i.val < 48
  · let n : Fin 48 := ⟨i.val,h⟩
    have hn : nativeIndex79 n = i := by
      apply Fin.ext
      rfl
    rw [← hn]
    exact actual_native_sparse_current n j
  · let b : Fin 31 := ⟨i.val-48,by omega⟩
    have hb : heavyIndex79 b = i := by
      apply Fin.ext
      dsimp [heavyIndex79,b]
      omega
    rw [← hb]
    exact actual_heavy_sparse_current b j

end LowEnergy.ActualCanonical79Imaginary
