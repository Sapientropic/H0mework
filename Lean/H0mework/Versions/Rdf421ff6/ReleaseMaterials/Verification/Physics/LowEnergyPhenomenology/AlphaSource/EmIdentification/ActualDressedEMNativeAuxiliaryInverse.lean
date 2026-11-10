import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeAuxiliaryBlocks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open scoped Matrix BigOperators

private theorem lie_reader_scale (r : ℂ) (v : Fin 12 → ℂ) :
    auxiliaryLieReader (fun a => r*v a)=fun a => r*auxiliaryLieReader v a := by
  funext a
  unfold auxiliaryLieReader
  split_ifs <;> ring

private theorem lie_inverse_scale (r : ℂ) (v : Fin 12 → ℂ) :
    auxiliaryLieInverse (fun a => r*v a)=fun a => r*auxiliaryLieInverse v a := by
  funext a
  unfold auxiliaryLieInverse
  split_ifs <;> ring

private theorem lie_inverse_sub (u v : Fin 12 → ℂ) :
    auxiliaryLieInverse (u-v)=auxiliaryLieInverse u-auxiliaryLieInverse v := by
  funext a
  simp only [Pi.sub_apply]
  unfold auxiliaryLieInverse
  split_ifs <;> simp only [Pi.sub_apply] <;> ring1

private theorem native_auxiliary_weight_nonzero (p : Fin 6) : nativeAuxiliaryWeight p≠0 := by
  have nonzero : (lapse : ℂ)≠0:=Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  unfold nativeAuxiliaryWeight
  split_ifs <;> exact div_ne_zero (by simp [nonzero]) (by norm_num)

/-- The source colour metric and the six original lapse weights determine the auxiliary inverse. -/
def nativeAuxiliaryInverse (v : (Fin 6 × Fin 12) → ℂ) : (Fin 6 × Fin 12) → ℂ :=
  fun i => (nativeAuxiliaryWeight i.1)⁻¹*auxiliaryLieInverse (fun a => v (i.1,a)) i.2

theorem actual_native_auxiliary_inverse_left (p : Fin 4 → ℂ) (v : (Fin 6 × Fin 12) → ℂ) :
    nativeAuxiliaryInverse (originalGaugeAuxiliaryPencil p*ᵥv)=v := by
  rw [actual_native_auxiliary_reader]
  funext i
  change (nativeAuxiliaryWeight i.1)⁻¹*
    auxiliaryLieInverse (fun a => nativeAuxiliaryWeight i.1*
      auxiliaryLieReader (fun b => v (i.1,b)) a) i.2=v i
  rw [lie_inverse_scale,auxiliary_lie_inverse_left]
  simp [native_auxiliary_weight_nonzero]

theorem actual_native_auxiliary_inverse_right (p : Fin 4 → ℂ) (v : (Fin 6 × Fin 12) → ℂ) :
    originalGaugeAuxiliaryPencil p*ᵥnativeAuxiliaryInverse v=v := by
  rw [actual_native_auxiliary_reader]
  funext i
  change nativeAuxiliaryWeight i.1*
    auxiliaryLieReader (fun a => (nativeAuxiliaryWeight i.1)⁻¹*
      auxiliaryLieInverse (fun b => v (i.1,b)) a) i.2=v i
  rw [lie_reader_scale,auxiliary_lie_inverse_right]
  simp [native_auxiliary_weight_nonzero]

theorem native_auxiliary_inverse_sub (u v : (Fin 6 × Fin 12) → ℂ) :
    nativeAuxiliaryInverse (u-v)=nativeAuxiliaryInverse u-nativeAuxiliaryInverse v := by
  funext i
  change (nativeAuxiliaryWeight i.1)⁻¹*
    auxiliaryLieInverse ((fun a => u (i.1,a))-(fun a => v (i.1,a))) i.2=_
  rw [lie_inverse_sub]
  simp only [nativeAuxiliaryInverse,Pi.sub_apply,mul_sub]

end LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
