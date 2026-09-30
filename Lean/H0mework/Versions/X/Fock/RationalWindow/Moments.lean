import H0mework.Versions.X.Fock.RationalWindow.Columns

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRationalWindowReadout

def mass (bound scale : Nat) (second : Fin (bound + 1)) (samples : Samples bound scale) : ℚ :=
  ((scale : ℚ)^2 - 1)⁻¹ *
    (column bound scale samples second (Fin.last scale) - column bound scale samples 0 0 -
      column bound scale samples 0 (Fin.last scale))

def clock (bound scale : Nat) (second : Fin (bound + 1)) (samples : Samples bound scale) : ℚ :=
  (scale : ℚ)⁻¹ * (column bound scale samples 0 (Fin.last scale) - mass bound scale second samples) -
    (scale : ℚ) * mass bound scale second samples

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem mass_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Samples (inventoryBound runtime + steps) (index.val + 1)) :
    (mass (inventoryBound runtime + steps) (index.val + 1)
      (SourceOperatorObservationAcquisition.secondColumn runtime index nonunit steps) samples : ℂ) =
        SourceOperatorObservationAcquisition.massRead runtime index nonunit steps (embed runtime index steps samples) := by
  simp only [mass, Rat.cast_mul, Rat.cast_inv, Rat.cast_sub, Rat.cast_pow, Rat.cast_natCast, Rat.cast_one,
    column_source, SourceOperatorObservationAcquisition.massRead, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]

theorem clock_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Samples (inventoryBound runtime + steps) (index.val + 1)) :
    (clock (inventoryBound runtime + steps) (index.val + 1)
      (SourceOperatorObservationAcquisition.secondColumn runtime index nonunit steps) samples : ℂ) =
        SourceOperatorObservationAcquisition.clockRead runtime index nonunit steps (embed runtime index steps samples) := by
  simp only [clock, Rat.cast_mul, Rat.cast_inv, Rat.cast_sub, Rat.cast_natCast, column_source, mass_source,
    SourceOperatorObservationAcquisition.clockRead, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]

end
end SourceRationalWindowReadout
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
