import H0mework.Versions.R2.Physics.MotherProgrammesFormationMatter.ActionBasis

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions

open DiracExteriorMatterAction MotherCoordinateCompletion MotherFamilyOccurrence
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Stage9C.Revision
open scoped Matrix

noncomputable section

abbrev Carrier := Completed coordinateCount
abbrev FullMatrix := Matrix Index Index ℂ

def matrix (value : Carrier) : FullMatrix := fun row column =>
  (coordinates coordinateCount value (address (row, column, 0)) : ℂ) +
    (coordinates coordinateCount value (address (row, column, 1)) : ℂ) * complexUnit

def operator (value : Carrier) : Module.End ℂ DiracExteriorMatterCarrier := by
  classical
  exact Matrix.toLin matterBasis matterBasis (matrix value)

def readMatrix (action : Module.End ℂ DiracExteriorMatterCarrier) : FullMatrix := by
  classical
  exact LinearMap.toMatrix matterBasis matterBasis action

theorem operator_matrix (value : Carrier) : readMatrix (operator value) = matrix value := by
  classical
  exact LinearMap.toMatrix_toLin matterBasis matterBasis (matrix value)

/-- The action is on the entire 252-dimensional matter carrier. -/
theorem actual_action (value : Carrier) (matter : DiracExteriorMatterCarrier) :
    (matterBasis.repr (operator value matter) : Index → ℂ) =
      matrix value *ᵥ matterBasis.repr matter := by
  classical
  exact Matrix.repr_toLin matterBasis matterBasis (matrix value) matter

theorem actual_entry (value : Carrier) (row column : Index) :
    matterBasis.repr (operator value (matterBasis column)) row = matrix value row column := by
  classical
  rw [← operator_matrix]
  exact (LinearMap.toMatrix_apply matterBasis matterBasis (operator value) row column).symm

def matrixCoordinates (data : FullMatrix) : Fin coordinateCount → ℝ := fun slot =>
  let pair := address.symm slot
  Fin.cases (data pair.1 pair.2.1).re (fun _ => (data pair.1 pair.2.1).im) pair.2.2

theorem coordinates_recovered (value : Carrier) :
    matrixCoordinates (matrix value) = coordinates coordinateCount value := by
  funext slot
  obtain ⟨⟨row, column, part⟩, rfl⟩ := address.surjective slot
  fin_cases part <;> simp [matrixCoordinates, matrix, complex_unit]
  rfl

theorem matrix_restored (data : FullMatrix) :
    matrix ((realEquiv coordinateCount).symm (matrixCoordinates data)) = data := by
  have restored : coordinates coordinateCount ((realEquiv coordinateCount).symm
      (matrixCoordinates data)) = matrixCoordinates data :=
    (realEquiv coordinateCount).apply_symm_apply _
  funext row column
  unfold matrix
  rw [restored]
  simp only [matrixCoordinates, Equiv.symm_apply_apply]
  change ((data row column).re : ℂ) + ((data row column).im : ℂ) * complexUnit = data row column
  rw [complex_unit]
  exact Complex.re_add_im _

def operatorEquiv : Carrier ≃ Module.End ℂ DiracExteriorMatterCarrier where
  toFun := operator
  invFun action := (realEquiv coordinateCount).symm (matrixCoordinates (readMatrix action))
  left_inv value := by
    change (realEquiv coordinateCount).symm (matrixCoordinates (readMatrix (operator value))) = value
    rw [operator_matrix, coordinates_recovered]
    exact (realEquiv coordinateCount).symm_apply_apply value
  right_inv action := by
    classical
    change Matrix.toLin matterBasis matterBasis
      (matrix ((realEquiv coordinateCount).symm (matrixCoordinates (readMatrix action)))) = action
    rw [matrix_restored]
    exact Matrix.toLin_toMatrix matterBasis matterBasis action

theorem every_operator (action : Module.End ℂ DiracExteriorMatterCarrier) :
    ∃! value : Carrier, operator value = action := by
  refine ⟨operatorEquiv.symm action, operatorEquiv.apply_symm_apply action, ?_⟩
  intro value generated
  exact operatorEquiv.injective (generated.trans (operatorEquiv.apply_symm_apply action).symm)

def finiteData (visit : MotherVisit) : Carrier := (fromVisit coordinateCount visit : Carrier)
def operatorAt (visit : MotherVisit) : Module.End ℂ DiracExteriorMatterCarrier := operator (finiteData visit)

theorem finite_matrix (visit : MotherVisit) (row column : Index) :
    readMatrix (operatorAt visit) row column =
      (RationalSourceFormation.sourceTrace (StageEightDiscreteFormation.sourceAtVisit
        (sample coordinateCount visit (address (row, column, 0)))) : ℂ) +
      (RationalSourceFormation.sourceTrace (StageEightDiscreteFormation.sourceAtVisit
        (sample coordinateCount visit (address (row, column, 1)))) : ℂ) * complexUnit := by
  rw [operatorAt, operator_matrix]
  exact congrArg₂ (fun real imag : ℝ => (real : ℂ) + (imag : ℂ) * complexUnit)
    (finite_native_read coordinateCount visit (address (row, column, 0)))
    (finite_native_read coordinateCount visit (address (row, column, 1)))

theorem finite_samples_are_past (visit : MotherVisit) (row column : Index) (part : Fin 2) :
    temporalDepth (sample coordinateCount visit (address (row, column, part))).history ≤
      temporalDepth visit.history :=
  sample_is_past coordinateCount visit (address (row, column, part))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions
