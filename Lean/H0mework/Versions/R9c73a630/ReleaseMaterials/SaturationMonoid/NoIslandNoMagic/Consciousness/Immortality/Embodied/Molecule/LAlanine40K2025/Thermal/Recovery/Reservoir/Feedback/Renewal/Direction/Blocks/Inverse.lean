import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Norm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Donor

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
theorem mask_eq_self {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) : mask label A = A := by
  ext i j
  by_cases same : label i = label j
  · exact if_pos same
  · simpa only [mask, if_neg same] using (kept i j same).symm

omit [Fintype ι] [DecidableEq ι] in
theorem mask_zero (label : ι → κ) : mask label (0 : Matrix ι ι ℂ) = 0 := by
  ext i j
  simp [mask]

omit [DecidableEq ι] in
theorem mask_trace (label : ι → κ) (A : Matrix ι ι ℂ) :
    (mask label A).trace = A.trace := by
  simp [Matrix.trace, Matrix.diag, mask]

omit [Fintype ι] [DecidableEq ι] in
theorem mask_add (label : ι → κ) (A B : Matrix ι ι ℂ) :
    mask label (A+B) = mask label A + mask label B := by
  ext i j
  by_cases same : label i = label j <;> simp [mask, same]

omit [Fintype ι] [DecidableEq ι] in
theorem mask_sub (label : ι → κ) (A B : Matrix ι ι ℂ) :
    mask label (A-B) = mask label A - mask label B := by
  ext i j
  by_cases same : label i = label j <;> simp [mask, same]

omit [Fintype ι] [DecidableEq ι] in
theorem mask_smul (label : ι → κ) (A : Matrix ι ι ℂ) (c : ℂ) :
    mask label (c • A) = c • mask label A := by
  ext i j
  by_cases same : label i = label j <;> simp [mask, same]

omit [DecidableEq ι] in
theorem mask_mul_left {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (B : Matrix ι ι ℂ) :
    mask label (A*B) = A * mask label B := by
  ext i j
  by_cases same : label i = label j
  · simp only [mask, if_pos same, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro x _
    by_cases inside : label x = label j
    · rw [if_pos inside]
    · rw [kept i x (fun equal => inside (equal.symm.trans same)), zero_mul, zero_mul]
  · simp only [mask, if_neg same, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro x _
    by_cases inside : label x = label j
    · rw [kept i x (fun equal => same (equal.trans inside)), zero_mul]
    · rw [if_neg inside, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem mask_star (label : ι → κ) (A : Matrix ι ι ℂ) :
    mask label Aᴴ = (mask label A)ᴴ := by
  ext i j
  by_cases same : label i = label j
  · simp only [mask, Matrix.conjTranspose_apply, if_pos same, if_pos same.symm]
  · simp only [mask, Matrix.conjTranspose_apply, if_neg same, if_neg (Ne.symm same), star_zero]

omit [DecidableEq ι] in
theorem mask_mul_right {label : ι → κ} {B : Matrix ι ι ℂ}
    (kept : Preserves label B) (A : Matrix ι ι ℂ) :
    mask label (A*B) = mask label A * B := by
  have dual := congrArg Matrix.conjTranspose (mask_mul_left (preserves_star kept) Aᴴ)
  simpa only [← mask_star, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using dual

theorem mask_conjugation {label : ι → κ} (U : Matrix.unitaryGroup ι ℂ)
    (kept : Preserves label (U : Matrix ι ι ℂ)) (rho : Matrix ι ι ℂ) :
    mask label (Quantum.conjugation U rho) = Quantum.conjugation U (mask label rho) := by
  simp only [Quantum.conjugation_apply, Matrix.star_eq_conjTranspose]
  rw [mask_mul_right (preserves_star kept), mask_mul_left kept]

omit [DecidableEq ι] in
theorem trace_ignores_cross {label : ι → κ} {O : Matrix ι ι ℂ}
    (kept : Preserves label O) (rho : Matrix ι ι ℂ) :
    (O*rho).trace = (O*mask label rho).trace := by
  rw [← mask_mul_left kept, mask_trace]

theorem systemNext_mask {label : ι → κ} {tau : Matrix ι ι ℂ}
    (kept : Preserves label tau) (rho : Matrix ι ι ℂ) (c s : ℝ) :
    systemNext (mask label rho) tau c s = mask label (systemNext rho tau c s) := by
  rw [systemNext_full, systemNext_full, mask_add, mask_add]
  simp only [mask_smul, mask_sub, mask_mul_left kept, mask_mul_right kept,
    mask_eq_self kept, mask_trace]

section Spectator
variable {η : Type*} [Fintype η] [DecidableEq η]

omit [DecidableEq ι] [Fintype ι] [Fintype η] [DecidableEq η] in
theorem slice_mask (label : ι → κ) (rho : Matrix (ι × η) (ι × η) ℂ) (e f : η) :
    BodyKernel.slice (mask (fun i => label i.1) rho) e f = mask label (BodyKernel.slice rho e f) := rfl

theorem bodyExchange_mask {label : ι → κ} {tau : Matrix ι ι ℂ}
    (kept : Preserves label tau) (rho : Matrix (ι × η) (ι × η) ℂ) (angle : ℝ) :
    BodyKernel.bodyExchange (mask (fun i => label i.1) rho) tau angle =
      mask (fun i => label i.1) (BodyKernel.bodyExchange rho tau angle) := by
  ext i j
  have sliced : BodyKernel.slice
      (BodyKernel.bodyExchange (mask (fun i => label i.1) rho) tau angle) i.2 j.2 =
      BodyKernel.slice (mask (fun i => label i.1) (BodyKernel.bodyExchange rho tau angle)) i.2 j.2 := by
    rw [BodyKernel.bodyExchange_slice, slice_mask, slice_mask,
      BodyKernel.bodyExchange_slice, systemNext_mask kept]
  exact congrArg (fun A => A i.1 j.1) sliced
end Spectator

omit [Fintype ι] [DecidableEq ι] in
theorem inverse_commutes_mask (label : ι → κ)
    (L : Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ)
    (forward : ∀ rho, L (mask label rho) = mask label (L rho)) (rho : Matrix ι ι ℂ) :
    L.symm (mask label rho) = mask label (L.symm rho) := by
  apply L.injective
  rw [LinearEquiv.apply_symm_apply, forward, LinearEquiv.apply_symm_apply]

omit [Fintype ι] in
theorem mask_single_off {label : ι → κ} (i j : ι) (outside : label i ≠ label j) :
    mask label (Matrix.single i j (1 : ℂ)) = 0 := by
  ext a b
  by_cases left : a = i
  · subst a
    by_cases right : b = j
    · subst b
      simp [mask, outside]
    · simp [mask, Matrix.single, Ne.symm right]
  · simp [mask, Matrix.single, Ne.symm left]

theorem inverseTrace_preserves {label : ι → κ}
    (L : Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ)
    (forward : ∀ rho, L (mask label rho) = mask label (L rho))
    (O : Matrix ι ι ℂ) (kept : Preserves label O) :
    Preserves label (Measurement.inverseTraceObservable L O) := by
  intro i j separated
  change (O * L.symm (Matrix.single j i 1)).trace = 0
  rw [trace_ignores_cross kept, ← inverse_commutes_mask label L forward,
    mask_single_off j i (Ne.symm separated), map_zero, Matrix.mul_zero, Matrix.trace_zero]

set_option maxRecDepth 4096

open Propagation.Interface Load.Source

theorem original_channel_mask (donorKept : Preserves pcOrbit Source.donor) (rho : LoadedJoint) :
    BodyKernel.sourceBodyChannel (mask pceOrbit rho) = mask pceOrbit (BodyKernel.sourceBodyChannel rho) := by
  rw [BodyKernel.sourceBodyChannel_factor, BodyKernel.sourceBodyChannel_factor]
  have exchange := bodyExchange_mask donorKept rho (Real.pi / 2 - (Propagation.Producer.nativeClockStep : ℝ))
  change BodyKernel.bodyExchange (mask pceOrbit rho) Source.donor _ =
    mask pceOrbit (BodyKernel.bodyExchange rho Source.donor _) at exchange
  rw [exchange]
  symm
  apply mask_conjugation
  exact preserves_tensor_left (source_free_pc_preserves _) _

theorem original_inverseObservable_preserves (donorKept : Preserves pcOrbit Source.donor) :
    Preserves pceOrbit (Measurement.sourceOutputObservable Load.Source.loadTotalHamiltonian) := by
  apply inverseTrace_preserves Measurement.sourceChannelEquiv
  · intro rho
    simpa only [Measurement.sourceChannelEquiv_apply] using original_channel_mask donorKept rho
  · exact source_load_preserves

theorem original_effect_preserves (donorKept : Preserves pcOrbit Source.donor) :
    Preserves pceOrbit (Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian) :=
  preserves_add (preserves_smul (preserves_one pceOrbit) ((1/2 : ℝ) : ℂ))
    (preserves_smul (original_inverseObservable_preserves donorKept) _)

theorem original_effect_block_root (donorKept : Preserves pcOrbit Source.donor) (k : Sym2 Basis) :
    restrict pceOrbit k (CFC.sqrt (Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian)) =
      CFC.sqrt (restrict pceOrbit k (Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian)) :=
  restrict_sqrt (original_effect_preserves donorKept)
    (Measurement.sourceMeasurement_lawful _ Load.Source.loadTotalHamiltonian_hermitian).1 k

theorem original_complement_block_root (donorKept : Preserves pcOrbit Source.donor) (k : Sym2 Basis) :
    restrict pceOrbit k (CFC.sqrt (1 - Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian)) =
      CFC.sqrt (restrict pceOrbit k (1 - Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian)) :=
  restrict_sqrt (preserves_sub (preserves_one pceOrbit) (original_effect_preserves donorKept))
    (Measurement.sourceMeasurement_lawful _ Load.Source.loadTotalHamiltonian_hermitian).2 k

theorem original_measurementScale_blocks (donorKept : Preserves pcOrbit Source.donor) :
    Measurement.measurementScale (Measurement.sourceOutputObservable Load.Source.loadTotalHamiltonian) =
      1 + ‖fun k : Sym2 Basis => restrict pceOrbit k
        (Measurement.sourceOutputObservable Load.Source.loadTotalHamiltonian)‖ := by
  unfold Measurement.measurementScale
  rw [norm_eq_block_norm (original_inverseObservable_preserves donorKept)]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
