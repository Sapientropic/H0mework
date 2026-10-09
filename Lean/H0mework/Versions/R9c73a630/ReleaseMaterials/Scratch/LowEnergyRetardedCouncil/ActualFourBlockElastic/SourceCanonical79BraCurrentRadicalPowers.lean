import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairBasis
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

theorem current_sqrt2_cube : (Real.sqrt 2 : ℂ)^3 = 2*(Real.sqrt 2 : ℂ) := by
  calc
    _ = (Real.sqrt 2 : ℂ)^2*(Real.sqrt 2 : ℂ) := by ring
    _ = _ := by rw [ActualCandidateBra.sqrt2_square]

theorem current_sqrt15_cube : (Real.sqrt 15 : ℂ)^3 = 15*(Real.sqrt 15 : ℂ) := by
  calc
    _ = (Real.sqrt 15 : ℂ)^2*(Real.sqrt 15 : ℂ) := by ring
    _ = _ := by rw [ActualCandidateBra.sqrt15_square]

end LowEnergy.ActualCanonical79Imaginary
