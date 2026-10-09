import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Source

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble

open Collision SourceGeneratedWorkInformation SourceGeneratedConditionalWork
open scoped Matrix ComplexOrder
noncomputable section

def spectralFrame : Matrix.unitaryGroup Current.FullIndex ℂ :=
  star contrast_hermitian.eigenvectorUnitary

def measured0 : PMF Current.FullIndex :=
  Quantum.diagonalPMF (Quantum.conjugation spectralFrame rho0)
    (Quantum.conjugation_posSemidef spectralFrame rho0 rho0_positive)
    ((Quantum.conjugation_trace spectralFrame rho0).trans rho0_trace)

def measured1 : PMF Current.FullIndex :=
  Quantum.diagonalPMF (Quantum.conjugation spectralFrame rho1)
    (Quantum.conjugation_posSemidef spectralFrame rho1 rho1_positive)
    ((Quantum.conjugation_trace spectralFrame rho1).trans rho1_trace)

private theorem conjugation_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ) (p : ℝ) :
    Quantum.conjugation U ((p : ℂ) • M) =
      (p : ℂ) • Quantum.conjugation U M := by
  simp only [Quantum.conjugation_apply, Matrix.mul_smul, Matrix.smul_mul]

private theorem diagonal_smul_real {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (p : ℝ) (i : ι) :
    (((p : ℂ) • M) i i).re = p * (M i i).re := by
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem left_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (i : ι) :
    (((blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) * joint *
      star (blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)) (Sum.inl i) (Sum.inl i)).re =
      ((Quantum.conjugation U joint.toBlocks₁₁) i i).re :=
  congrArg (fun M : Matrix ι ι ℂ => (M i i).re)
    (blockUnitary_conjugation_diagonal_left U U joint)

private theorem right_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (i : ι) :
    (((blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) * joint *
      star (blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)) (Sum.inr i) (Sum.inr i)).re =
      ((Quantum.conjugation U joint.toBlocks₂₂) i i).re :=
  congrArg (fun M : Matrix ι ι ℂ => (M i i).re)
    (blockUnitary_conjugation_diagonal_right U U joint)

theorem source_index_left (i : Current.FullIndex) :
    (sourcePMF (Sum.inl i)).toReal = p0 * (measured0 i).toReal := by
  have hun : (p0 : ℂ) • rho0 = sigma0 := weighted_unnormalize sigma0 p0 p0_pos
  calc
    (sourcePMF (Sum.inl i)).toReal =
        ((Born.jointRead contrast contrast_hermitian receivedState) (Sum.inl i) (Sum.inl i)).re :=
      Born.distribution_toReal contrast contrast_hermitian receivedState (Sum.inl i)
    _ = ((Quantum.conjugation spectralFrame sigma0) i i).re := by
      simpa only [Born.jointRead, Born.frame, Quantum.conjugation_apply,
        spectralFrame, sigma0, Resource.loadBlock] using
        left_diagonal (star contrast_hermitian.eigenvectorUnitary) receivedState.joint i
    _ = p0 * (measured0 i).toReal := by
      rw [← hun, conjugation_smul, diagonal_smul_real]
      exact congrArg (p0 * ·) (Quantum.diagonalPMF_toReal _ _ _ i).symm

theorem source_index_right (i : Current.FullIndex) :
    (sourcePMF (Sum.inr i)).toReal = p1 * (measured1 i).toReal := by
  have hun : (p1 : ℂ) • rho1 = sigma1 := weighted_unnormalize sigma1 p1 p1_pos
  calc
    (sourcePMF (Sum.inr i)).toReal =
        ((Born.jointRead contrast contrast_hermitian receivedState) (Sum.inr i) (Sum.inr i)).re :=
      Born.distribution_toReal contrast contrast_hermitian receivedState (Sum.inr i)
    _ = ((Quantum.conjugation spectralFrame sigma1) i i).re := by
      simpa only [Born.jointRead, Born.frame, Quantum.conjugation_apply,
        spectralFrame, sigma1, Resource.suppliedBlock] using
        right_diagonal (star contrast_hermitian.eigenvectorUnitary) receivedState.joint i
    _ = p1 * (measured1 i).toReal := by
      rw [← hun, conjugation_smul, diagonal_smul_real]
      exact congrArg (p1 * ·) (Quantum.diagonalPMF_toReal _ _ _ i).symm

attribute [local irreducible] measured0 measured1 p0 p1 valueRead

local instance : MeasurableSpace PointerIndex := ⊤
local instance : MeasurableSingletonClass PointerIndex := ⟨fun _ => trivial⟩
local instance : MeasurableSpace Value := ⊤
local instance : MeasurableSingletonClass Value := ⟨fun _ => trivial⟩

def read0 (i : Current.FullIndex) : Value := valueRead (Sum.inl i)
def read1 (i : Current.FullIndex) : Value := valueRead (Sum.inr i)
def observed0 : PMF Value := measured0.map read0
def observed1 : PMF Value := measured1.map read1

attribute [local irreducible] read0 read1

private theorem cell_sum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (source : PMF A) (read : A → B) (value : B) :
    (source.map read value).toReal =
      ∑ atom : A, (source atom).toReal * (if read atom = value then 1 else 0) := by
  have original := Quantum.sum_map_read source read (fun other => if other = value then 1 else 0)
  simpa [mul_ite] using original

theorem source_joint_left_value (value : Value) :
    (joint (0, value)).toReal = p0 * (observed0 value).toReal := by
  have original := cell_sum sourcePMF
    (fun atom => (Born.pointer atom, valueRead atom)) (0, value)
  have conditional := cell_sum measured0 read0 value
  change (joint (0, value)).toReal = _ at original
  rw [original, Fintype.sum_sum_type]
  simp only [Born.pointer, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq, true_and]
  simp only [show (1 : Fin 2) ≠ 0 by decide, false_and, ite_false,
    mul_zero, Finset.sum_const_zero, add_zero]
  change _ = p0 * ((measured0.map read0 value).toReal)
  rw [conditional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [read0]
  rw [source_index_left i]
  simp only [mul_assoc]

theorem source_joint_right_value (value : Value) :
    (joint (1, value)).toReal = p1 * (observed1 value).toReal := by
  have original := cell_sum sourcePMF
    (fun atom => (Born.pointer atom, valueRead atom)) (1, value)
  have conditional := cell_sum measured1 read1 value
  change (joint (1, value)).toReal = _ at original
  rw [original, Fintype.sum_sum_type]
  simp only [Born.pointer, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq, true_and]
  simp only [show (0 : Fin 2) ≠ 1 by decide, false_and, ite_false,
    mul_zero, Finset.sum_const_zero, zero_add]
  change _ = p1 * ((measured1.map read1 value).toReal)
  rw [conditional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [read1]
  rw [source_index_right i]
  simp only [mul_assoc]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
