import H0mework.Chemistry.LAlanineWholeBandCell2.SourceMaterial

/-! Actual orbitals and the full matrix precede report recognition and the original parametric RHS consumer. -/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Source

open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceFields WholeBandSource
open WholeBandMatrix IntervalParameterMap ContinuousGradient
noncomputable section

theorem material_matrix_calculation : RowsCertificate material.rows material.ao := Call128.matrixCertificate

theorem material_actual_orbitals : AOContains material.box material.ao :=
  fun j b x inside => Call128.actual_orbitals j b x inside

theorem material_full_bilinear (j k : LowJet) :
    calculatedBilinear material.rows j k = bilinearPair (material.ao j) (material.ao k) material.density :=
  bilinear_commutes material.rows material.ao material_matrix_calculation j k

theorem material_calculated_field (x : Point) (inside : InRectangle material.box x) :
    FieldHolds material.computed x := Call128.calculated_field_holds x inside

theorem material_actual_values (x : Point) (inside : InRectangle material.box x) :
    (∀ axis, Holds (material.computed.gradient axis) (material.actualGradient x axis)) ∧
    (∀ axis direction, Holds (material.computed.hessian axis direction) (material.actualHessian x axis direction)) :=
  material_calculated_field x inside

theorem material_report_recognition (i : Fin 2) :
    (∀ axis, material.computed.gradient axis = (material.reported i).gradient axis) ∧
    (∀ axis direction, material.computed.hessian axis direction = (material.reported i).hessian axis direction) := by
  fin_cases i <;> exact ⟨Call128.matrix_gradient_report, Call128.matrix_hessian_report⟩

theorem material_registered_field (i : Fin 2) (x : Point) (inside : InRectangle material.box x) :
    FieldHolds (material.reported i) x := by
  fin_cases i <;> exact Call128.actual_field x inside

theorem material_rhs_contains (state : JetBox) (x : Point) (J : Point →L[ℝ] Point)
    (inside : InRectangle material.box x) (input : JetHolds state x J) :
    JetHolds (rhs material.computed state) (material.actualGradient x) ((sourceHessianLinear x).comp J) :=
  rhs_contains material.computed state x J input (material_calculated_field x inside)

structure InitialFieldClosure : Prop where
  restrictions : type_of% same_original_restrictions
  addresses : type_of% call_addresses_injective
  nonemptyBox : type_of% box_nonempty
  matrixCalculation : type_of% material_matrix_calculation
  actualOrbitals : type_of% material_actual_orbitals
  fullBilinear : type_of% material_full_bilinear
  calculatedField : type_of% material_calculated_field
  actualValues : type_of% material_actual_values
  reportRecognition : type_of% material_report_recognition
  registeredField : type_of% material_registered_field
  parametricRhs : type_of% material_rhs_contains

theorem sourceGeneratedInitialFieldClosure : InitialFieldClosure :=
  ⟨same_original_restrictions, call_addresses_injective, box_nonempty, material_matrix_calculation,
    material_actual_orbitals, material_full_bilinear, material_calculated_field, material_actual_values,
    material_report_recognition, material_registered_field, material_rhs_contains⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell2.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
