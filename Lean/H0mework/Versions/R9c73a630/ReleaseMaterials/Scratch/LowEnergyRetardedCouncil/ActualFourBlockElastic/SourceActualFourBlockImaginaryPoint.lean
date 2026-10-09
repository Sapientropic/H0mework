import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.MixedSpectatorFourBlockSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.ActualFourBlockElastic
open ActualFourBlockSource MixedSpectatorPairedSourceFrame
open scoped BigOperators

theorem zero_signed_radius : signedRadius (0 : Fin 3 → ℝ) = 0 := by
  simp [signedRadius, spatialRadius,
    SaturationMonoid.PhysicsCore.LowEnergy.Rotation.momentumRadius]

theorem actual_imaginary_canonical_regular :
    MixedSpectatorCanonical79Exchange.RegularMomentum Complex.I 0 := by
  intro a
  rw [zero_signed_radius]
  fin_cases a <;>
    norm_num [MixedSpectatorCanonical79Data.denominator, Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]

theorem actual_imaginary_dual_regular :
    MixedSpectatorDual24Exchange.RegularMomentum Complex.I 0 := by
  intro a
  rw [zero_signed_radius]
  fin_cases a <;>
    norm_num [MixedSpectatorDual24Data.denominator, Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]

def imaginaryTransferTime : ℂ := (6 * (Real.sqrt 15 : ℂ) / 25) * Complex.I

private theorem transfer_time_sq : imaginaryTransferTime^2 = -108/125 := by
  have h : (Real.sqrt 15 : ℂ)^2 = 15 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  simp only [imaginaryTransferTime, mul_pow, div_pow]
  rw [h, Complex.I_sq]
  norm_num

private theorem transfer_time_four : imaginaryTransferTime^4 = 11664/15625 := by
  calc
    _ = (imaginaryTransferTime^2)^2 := by ring
    _ = _ := by rw [transfer_time_sq]; norm_num

private theorem transfer_time_six : imaginaryTransferTime^6 = -1259712/1953125 := by
  calc
    _ = (imaginaryTransferTime^2)^3 := by ring
    _ = _ := by rw [transfer_time_sq]; norm_num

theorem actual_imaginary_scalar_denominator :
    MixedSpectatorScalar61Exchange.denominator (worldTransfer Complex.I 0) =
      (-444011091/97656250 : ℂ) * (Real.sqrt 30 : ℂ) := by
  have h : worldTransfer Complex.I 0 = ![imaginaryTransferTime,0,0,0] := by
    ext a
    fin_cases a <;> norm_num [worldTransfer, imaginaryTransferTime]
  rw [h]
  norm_num [MixedSpectatorScalar61Exchange.denominator, transfer_time_sq,
    transfer_time_four, transfer_time_six, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem actual_imaginary_scalar_regular :
    MixedSpectatorScalar61Exchange.denominator (worldTransfer Complex.I 0) ≠ 0 := by
  rw [actual_imaginary_scalar_denominator]
  apply mul_ne_zero (by norm_num)
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 30)))

/-- The actual common regular point is generated internally, before the
four-block source acts on the fixed candidate. -/
def imaginaryKinematics : Kinematics where
  x := Complex.I
  k := 0
  pLeft := 0
  pRight := 0
  canonicalRegular := actual_imaginary_canonical_regular
  dualRegular := actual_imaginary_dual_regular
  scalarRegular := actual_imaginary_scalar_regular

end LowEnergy.ActualFourBlockElastic
