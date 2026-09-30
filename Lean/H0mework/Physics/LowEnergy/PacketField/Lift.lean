import H0mework.Physics.LowEnergy.PacketField.CircleBound

/-! Native finite circle tables act on the same primitive pole columns. Their
coefficient bounds generate field bounds before any current contraction. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
noncomputable section
variable {ι : Type*} [Fintype ι]

abbrev CircleData (ι : Type*) := Fin 9 → Matrix ι ι ℝ

def circleMatrix (data : CircleData ι) (parameter : ℝ) (row column : ι) : ℂ :=
  circleEntry (fun degree => (data degree row column : ℂ)) parameter

def circleAction (data : CircleData ι) (parameter : ℝ) (field : ι → ℂ) (row : ι) : ℂ :=
  ∑ column, circleMatrix data parameter row column*field column

def transportedBound (data : CircleData ι) (bound : ι → ℝ) (row : ι) : ℝ :=
  ∑ column, (∑ degree, |data degree row column|)*bound column

theorem circleAction_bound (data : CircleData ι) (parameter : ℝ) (field : ι → ℂ)
    (bound : ι → ℝ) (bounded : ∀ column, ‖field column‖≤bound column) (row : ι) :
    ‖circleAction data parameter field row‖≤transportedBound data bound row := by
  unfold circleAction transportedBound
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro column _
  rw [norm_mul]
  have coefficient : ‖circleMatrix data parameter row column‖≤∑ degree, |data degree row column| := by
    simpa only [circleMatrix,Complex.norm_real,Real.norm_eq_abs] using
      circleEntry_bound (fun degree => (data degree row column : ℂ)) parameter
  exact mul_le_mul coefficient (bounded column) (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem circleAction_measurable {X : Type*} [MeasurableSpace X] (data : CircleData ι)
    (parameter : X → ℝ) (parameterMeasurable : Measurable parameter)
    (field : X → ι → ℂ) (fieldMeasurable : ∀ column, Measurable (fun point => field point column)) (row : ι) :
    Measurable (fun point => circleAction data (parameter point) (field point) row) := by
  unfold circleAction circleMatrix
  exact Finset.measurable_sum _ (fun column _ =>
    (((circleEntry_continuous (fun degree => (data degree row column : ℂ))).measurable.comp parameterMeasurable).mul
      (fieldMeasurable column)))

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
