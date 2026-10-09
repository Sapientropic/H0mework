import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.InstrumentFrame

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem approximated_root_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A R : Matrix ι ι ℂ) (bounded : A ≤ 1) (paid : ‖CFC.sqrt A-R‖ ≤ (2/10^7 : ℝ)) : ‖R‖ ≤ 2 := by
  have root := root_norm_le_one A bounded
  have triangle := norm_sub_le_norm_sub_add_norm_sub R (CFC.sqrt A) 0
  simp only [sub_zero] at triangle
  rw [norm_sub_rev] at paid
  linarith

theorem source_roots_norm : ‖SquareRoot.Full.sourceRoot‖ ≤ 2 ∧ ‖SquareRoot.Full.sourceComplement‖ ≤ 2 :=
  ⟨approximated_root_norm _ _ (sub_nonneg.mp SquareRoot.original_finite_effect_positive.2) SquareRoot.Full.source_whole_roots_error.1,
    approximated_root_norm _ _ (sub_le_self _ SquareRoot.original_finite_effect_positive.1) SquareRoot.Full.source_whole_roots_error.2⟩

def rotatedRoot (R : LoadedJoint) : LoadedJoint := Phase.freePolynomial*R*star Phase.freePolynomial

theorem root_rotation_error (R : LoadedJoint) (bounded : ‖R‖ ≤ 2) :
    ‖Quantum.conjugation numericFree R-rotatedRoot R‖ ≤ (13/10^18 : ℝ) := by
  have normV := Input.approximated_unitary_norm numericFree Phase.freePolynomial _ Phase.numeric_free_polynomial_error
  have paid := Input.raw_conjugation_error numericFree Phase.freePolynomial R
  exact paid.trans ((mul_le_mul (mul_le_mul (add_le_add le_rfl normV) bounded (norm_nonneg _) (by norm_num))
    Phase.numeric_free_polynomial_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem body_root_rotation_error (R : LoadedJoint) (bounded : ‖R‖ ≤ 2) :
    ‖Incidence.bodyObservable (Quantum.conjugation numericFree R)-Incidence.bodyObservable (rotatedRoot R)‖ ≤ (13/10^18 : ℝ) := by
  rw [← bodyObservable_sub]
  exact (body_observable_norm _).trans (root_rotation_error R bounded)

def finiteSourcePointer : PointerJoint :=
  SquareRoot.rawDilation (Incidence.bodyObservable (rotatedRoot SquareRoot.Full.sourceRoot))
    (Incidence.bodyObservable (rotatedRoot SquareRoot.Full.sourceComplement))

theorem original_finite_source_pointer_error : ‖calculatedSourcePointer-finiteSourcePointer‖ ≤ (3/10^17 : ℝ) := by
  rw [original_source_pointer_coordinates,finiteSourcePointer]
  exact (SquareRoot.raw_dilation_error _ _ _ _).trans
    ((add_le_add (body_root_rotation_error SquareRoot.Full.sourceRoot source_roots_norm.1)
      (body_root_rotation_error SquareRoot.Full.sourceComplement source_roots_norm.2)).trans (by norm_num))

theorem calculated_source_pointer_norm : ‖calculatedSourcePointer‖ ≤ 1+(4/10^7 : ℝ) := by
  have same : ‖calculatedSourcePointer‖=‖SquareRoot.Full.sourcePointer‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ PointerJoint pointerFrame) SquareRoot.Full.sourcePointer
  rw [same]
  exact SquareRoot.approximated_pointer_norm SquareRoot.Full.sourceRoot SquareRoot.Full.sourceComplement
    SquareRoot.Full.source_whole_roots_error.1 SquareRoot.Full.source_whole_roots_error.2

theorem finite_source_pointer_norm : ‖finiteSourcePointer‖ ≤ 2 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub finiteSourcePointer calculatedSourcePointer 0
  simp only [sub_zero] at triangle
  have paid := original_finite_source_pointer_error
  rw [norm_sub_rev] at paid
  linarith [calculated_source_pointer_norm]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
