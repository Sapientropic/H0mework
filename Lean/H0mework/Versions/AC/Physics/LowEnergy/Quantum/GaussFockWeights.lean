import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussNativeMatter

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussFockWeights
open GaussNativeMatter SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
attribute [local instance] SourceRealScalarFock.branchOrder
open scoped BigOperators

theorem native_number_commute (a : NativeLie) : Commute fiberNumber (nativeFock a) := by
  show fiberNumber * nativeFock a = nativeFock a * fiberNumber
  apply ContinuousLinearMap.ext
  intro psi
  apply fiberCoordinates.injective
  change SourceFockRaising.total
      (SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize (nativeFull a) (fiberCoordinates psi)) =
    SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize (nativeFull a)
      (SourceFockRaising.total (fiberCoordinates psi))
  exact LinearMap.congr_fun (SourceFockRaising.quantize_preserves_number (nativeFull a)) (fiberCoordinates psi)

def matrixEntry (a : NativeLie) (output input : Occupation) : ℂ :=
  nativeFock a (EuclideanSpace.single input 1) output

theorem entry_number_zero (a : NativeLie) (output input : Occupation)
    (different : output.card ≠ input.card) : matrixEntry a output input = 0 := by
  have hn : fiberNumber (EuclideanSpace.single input 1) = (input.card : ℂ) • EuclideanSpace.single input 1 := by
    ext word
    rw [fiberNumber_apply]
    by_cases h : word = input
    · subst word; simp
    · simp [EuclideanSpace.single, h]
  have h := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (EuclideanSpace.single input 1) output)
    (native_number_commute a).eq
  change fiberNumber (nativeFock a (EuclideanSpace.single input 1)) output =
    nativeFock a (fiberNumber (EuclideanSpace.single input 1)) output at h
  rw [fiberNumber_apply, hn, map_smul] at h
  change (output.card : ℂ) * matrixEntry a output input = (input.card : ℂ) * matrixEntry a output input at h
  have hz : ((output.card : ℂ) - (input.card : ℂ)) * matrixEntry a output input = 0 := by
    linear_combination h
  have hc : (output.card : ℂ) - (input.card : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast different)
  exact (mul_eq_zero.mp hz).resolve_left hc

def weight (c : ℕ → ℂ) : FockFiber →L[ℂ] FockFiber :=
  LinearMap.toContinuousLinearMap
    { toFun := fun psi => WithLp.toLp 2 (fun word => c word.card * psi word)
      map_add' := by
        intro psi phi
        apply PiLp.ext
        intro word
        exact mul_add _ _ _
      map_smul' := by
        intro z psi
        apply PiLp.ext
        intro word
        change c word.card * (z * psi word) = z * (c word.card * psi word)
        ring }

theorem weight_apply (c : ℕ → ℂ) (psi : FockFiber) (word : Occupation) :
    weight c psi word = c word.card * psi word := rfl

theorem weight_basis (c : ℕ → ℂ) (input : Occupation) :
    weight c (EuclideanSpace.single input 1) = c input.card • EuclideanSpace.single input 1 := by
  apply PiLp.ext
  intro word
  rw [weight_apply]
  by_cases h : word = input
  · subst word; simp
  · simp [EuclideanSpace.single, h]

theorem native_weight_commute (c : ℕ → ℂ) (a : NativeLie) : Commute (weight c) (nativeFock a) := by
  show weight c * nativeFock a = nativeFock a * weight c
  apply ContinuousLinearMap.ext
  intro psi
  have expansion : psi = ∑ word : Occupation, psi word • EuclideanSpace.single word 1 := by
    apply PiLp.ext
    intro word
    simp [WithLp.ofLp_sum, Finset.sum_apply, EuclideanSpace.single, Pi.single_apply]
  have hsingle (input : Occupation) :
      weight c (nativeFock a (EuclideanSpace.single input 1)) =
        nativeFock a (weight c (EuclideanSpace.single input 1)) := by
    rw [weight_basis, map_smul]
    apply PiLp.ext
    intro output
    rw [weight_apply]
    change c output.card * matrixEntry a output input = c input.card * matrixEntry a output input
    by_cases h : output.card = input.card
    · rw [h]
    · rw [entry_number_zero a output input h, mul_zero, mul_zero]
  change weight c (nativeFock a psi) = nativeFock a (weight c psi)
  rw [expansion, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [map_smul, map_smul, map_smul, map_smul, hsingle]

theorem native_weighted_skew (c : ℕ → ℂ) (a : NativeLie) (psi phi : FockFiber) :
    inner ℂ (weight c (nativeFock a psi)) phi + inner ℂ (weight c psi) (nativeFock a phi) = 0 := by
  have h := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T psi) (native_weight_commute c a).eq
  change weight c (nativeFock a psi) = nativeFock a (weight c psi) at h
  rw [h]
  exact nativeFock_skew a (weight c psi) phi

#print axioms native_number_commute
#print axioms native_weight_commute
#print axioms native_weighted_skew
end LowEnergy.GaussFockWeights
