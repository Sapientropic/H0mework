import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockImaginaryPoint
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

def denominatorPoint (a : Fin 10) : ℂ :=
  ![(5089223228363110042136892361/146411471711750400000000), (880674872209406859519368641/7403720841127526400000000), (880674872209406859519368641/7403720841127526400000000), (-65124842331217710284987/9037745167392000), (-341/216), (-341/216), (-341/216), (-341/216), (-341/216), (-341/216)] a

theorem actual_denominator_point (a : Fin 10) :
    MixedSpectatorCanonical79Data.denominator Complex.I 0 a = denominatorPoint a := by
  fin_cases a <;>
    norm_num [MixedSpectatorCanonical79Data.denominator, denominatorPoint,
      Complex.I_pow_eq_pow_mod, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals norm_num [Complex.I_sq]

end LowEnergy.ActualCanonical79Imaginary
