import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Recovery
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Marginal

/-! The conditional decoder reads each original unnormalized pointer block in the same observable frame. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Collision Quantum
open scoped ComplexOrder

noncomputable section

theorem diagonal_branch_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (observable : Matrix ι ι ℂ) (hermitian : observable.IsHermitian)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (∑ index : ι ⊕ ι, (conjugation (blockUnitary (star hermitian.eigenvectorUnitary)
      (star hermitian.eigenvectorUnitary)) joint index index).re *
        (if Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) index = 0 then
          Sum.elim hermitian.eigenvalues hermitian.eigenvalues index else 0)) =
      energy observable joint.toBlocks₁₁ := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, mul_zero,
    Finset.sum_const_zero, add_zero]
  let rotated := conjugation (blockUnitary (star hermitian.eigenvectorUnitary)
    (star hermitian.eigenvectorUnitary)) joint
  change (∑ index, (rotated.toBlocks₁₁ index index).re * hermitian.eigenvalues index) = _
  have block : rotated.toBlocks₁₁ = conjugation (star hermitian.eigenvectorUnitary) joint.toBlocks₁₁ := by
    simp only [rotated, conjugation_apply, blockUnitary_conjugation_diagonal_left]
  rw [block]
  exact spectral_first_moment observable joint.toBlocks₁₁ hermitian

theorem diagonal_branch_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (observable : Matrix ι ι ℂ) (hermitian : observable.IsHermitian)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (∑ index : ι ⊕ ι, (conjugation (blockUnitary (star hermitian.eigenvectorUnitary)
      (star hermitian.eigenvectorUnitary)) joint index index).re *
        (if Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) index = 1 then
          Sum.elim hermitian.eigenvalues hermitian.eigenvalues index else 0)) =
      energy observable joint.toBlocks₂₂ := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.zero_ne_one, ite_false, ite_true, mul_zero,
    Finset.sum_const_zero, zero_add]
  let rotated := conjugation (blockUnitary (star hermitian.eigenvectorUnitary)
    (star hermitian.eigenvectorUnitary)) joint
  change (∑ index, (rotated.toBlocks₂₂ index index).re * hermitian.eigenvalues index) = _
  have block : rotated.toBlocks₂₂ = conjugation (star hermitian.eigenvectorUnitary) joint.toBlocks₂₂ := by
    simp only [rotated, conjugation_apply, blockUnitary_conjugation_diagonal_right]
  rw [block]
  exact spectral_first_moment observable joint.toBlocks₂₂ hermitian

local instance : MeasurableSpace PointerIndex := ⊤
local instance : MeasurableSingletonClass PointerIndex := ⟨fun _ => trivial⟩

variable (observable : Current.FullJoint) (hermitian : observable.IsHermitian) (current : Live.State)

theorem decoder_weighted (atom : Fin 2) :
    (((distribution observable hermitian current).map pointer) atom).toReal *
      (bestDecoder observable hermitian current atom).re =
        ∑ index : PointerIndex, (distribution observable hermitian current index).toReal *
          (if pointer index = atom then outcome observable hermitian index else 0) := by
  have weighted := congrArg Complex.re
    (SourceWeightedRecovery.weighted_optimal (distribution observable hermitian current) pointer
      (task observable hermitian) atom)
  simpa only [Complex.re_sum, Complex.smul_re, smul_eq_mul, apply_ite, task,
    Complex.ofReal_re, Complex.zero_re, bestDecoder, SourceWeightedRecovery.observed] using weighted

theorem zero_weighted_mean : zeroRead current.joint * (bestDecoder observable hermitian current 0).re =
    energy observable current.joint.toBlocks₁₁ := by
  have weighted := decoder_weighted observable hermitian current 0
  rw [pointer_zero_read] at weighted
  simp only [distribution_toReal] at weighted
  exact weighted.trans (diagonal_branch_zero observable hermitian current.joint)

theorem one_weighted_mean : oneRead current.joint * (bestDecoder observable hermitian current 1).re =
    energy observable current.joint.toBlocks₂₂ := by
  have weighted := decoder_weighted observable hermitian current 1
  rw [pointer_one_read] at weighted
  simp only [distribution_toReal] at weighted
  exact weighted.trans (diagonal_branch_one observable hermitian current.joint)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
