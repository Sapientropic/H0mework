import H0mework.Physics.LowEnergy.FullQuantum.StateGreen.Preparation

/-! Exact two-time matrix evolution, retaining the inverse second leg and
never commuting the prepared occupation through the source Hamiltonian. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateGreen
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open YangMills.FullPairing
noncomputable section
attribute [local instance] Fermion.fullIndexOrder

abbrev SourceMatrix := Matrix Quantum.Index Quantum.Index ℂ

def U (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) : SourceMatrix :=
  primalMatrix actual point momentum time

def generator (point : BasePoint) (momentum : Fin 3 → ℝ) : SourceMatrix :=
  Quantum.operatorMatrix (drift actual point momentum)

theorem U_entry (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) (i j : Quantum.Index) :
    U point momentum time i j=Quantum.coordinates (primal actual point momentum time (Quantum.wholeBasis j)) i := by
  let _ : DecidableEq Quantum.Index := Classical.decEq _
  rw [U,primalMatrix,Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply]
  rfl

theorem U_zero (point : BasePoint) (momentum : Fin 3 → ℝ) : U point momentum 0=1 := by
  ext i j
  rw [U_entry,primal_zero]
  by_cases same : i=j
  · subst j
    simp [Quantum.coordinates]
  · simp [Quantum.coordinates,same,Ne.symm same]

theorem U_inverse (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) :
    U point momentum time*U point momentum (-time)=1 :=
  primalMatrix_inverse actual point momentum time

private theorem coordinate_derivative (point : BasePoint) (momentum : Fin 3 → ℝ)
    (time : ℝ) (v : DiracExteriorMatterCarrier) :
    HasDerivAt (fun t => Quantum.coordinates (primal actual point momentum t v))
      (Quantum.coordinates (drift actual point momentum (primal actual point momentum time v))) time := by
  let read : Hilbert →L[ℂ] (Quantum.Index → ℂ) :=
    (Quantum.coordinates.toLinearMap.comp naturalCoordinates.symm.toLinearMap).toContinuousLinearMap
  have generated := (read.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time
    (primal_derivative actual point momentum time v)
  have read_value (w : DiracExteriorMatterCarrier) : read (naturalCoordinates w)=Quantum.coordinates w := by simp [read]
  change HasDerivAt (fun t => read (naturalCoordinates (primal actual point momentum t v)))
    (read (naturalCoordinates (drift actual point momentum (primal actual point momentum time v)))) time at generated
  simpa only [read_value] using generated

theorem U_derivative (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) :
    HasDerivAt (U point momentum) (generator point momentum*U point momentum time) time := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have component := hasDerivAt_pi.mp (coordinate_derivative point momentum time (Quantum.wholeBasis j)) i
  rw [← Quantum.matrix_action] at component
  simpa only [Matrix.mul_apply,U_entry,generator,Matrix.mulVec,dotProduct] using component

theorem U_continuous (point : BasePoint) (momentum : Fin 3 → ℝ) : Continuous (U point momentum) :=
  continuous_iff_continuousAt.mpr fun t => (U_derivative point momentum t).continuousAt

theorem U_commutes (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) :
    U point momentum time*generator point momentum=generator point momentum*U point momentum time := by
  have mother : (primal actual point momentum time).comp (drift actual point momentum)=
      (drift actual point momentum).comp (primal actual point momentum time) := by
    apply LinearMap.ext
    intro v
    exact primal_drift_commute actual point momentum time v
  have generated := congrArg Quantum.operatorMatrix mother
  simpa only [U,primalMatrix,generator,Quantum.matrix_composition] using generated

private theorem matrix_mul_const_derivative (curve : ℝ → SourceMatrix) (derivative B : SourceMatrix)
    (time : ℝ) (hasDerivative : HasDerivAt curve derivative time) :
    HasDerivAt (fun t => curve t*B) (derivative*B) time := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have generated := HasDerivAt.fun_sum (u := Finset.univ)
    (fun l _ => (hasDerivAt_pi.mp (hasDerivAt_pi.mp hasDerivative i) l).mul_const (B l j))
  simpa only [Matrix.mul_apply] using generated

private theorem matrix_const_mul_derivative (A : SourceMatrix) (curve : ℝ → SourceMatrix) (derivative : SourceMatrix)
    (time : ℝ) (hasDerivative : HasDerivAt curve derivative time) :
    HasDerivAt (fun t => A*curve t) (A*derivative) time := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have generated := HasDerivAt.fun_sum (u := Finset.univ)
    (fun l _ => (hasDerivAt_pi.mp (hasDerivAt_pi.mp hasDerivative l) j).const_mul (A i l))
  simpa only [Matrix.mul_apply] using generated

def legs (point : BasePoint) (momentum : Fin 3 → ℝ) (middle : SourceMatrix) (t s : ℝ) : SourceMatrix :=
  U point momentum t*middle*U point momentum (-s)

theorem legs_left_derivative (point : BasePoint) (momentum : Fin 3 → ℝ)
    (middle : SourceMatrix) (t s : ℝ) :
    HasDerivAt (fun time => legs point momentum middle time s)
      (generator point momentum*legs point momentum middle t s) t := by
  have generated := matrix_mul_const_derivative _ _ (U point momentum (-s)) t
    (matrix_mul_const_derivative _ _ middle t (U_derivative point momentum t))
  simpa only [legs,Matrix.mul_assoc] using generated

theorem legs_right_derivative (point : BasePoint) (momentum : Fin 3 → ℝ)
    (middle : SourceMatrix) (t s : ℝ) :
    HasDerivAt (fun time => legs point momentum middle t time)
      (-(legs point momentum middle t s*generator point momentum)) s := by
  have inverse := (U_derivative point momentum (-s)).scomp s (hasDerivAt_neg s)
  have generated := matrix_const_mul_derivative (U point momentum t*middle) _ _ s inverse
  convert! generated using 1
  simp only [neg_one_smul,Matrix.mul_neg]
  rw [← U_commutes]
  simp only [legs,Matrix.mul_assoc]

theorem legs_left_continuous (point : BasePoint) (momentum : Fin 3 → ℝ)
    (middle : SourceMatrix) (s : ℝ) : Continuous (fun t => legs point momentum middle t s) :=
  continuous_iff_continuousAt.mpr fun t => (legs_left_derivative point momentum middle t s).continuousAt

theorem legs_right_continuous (point : BasePoint) (momentum : Fin 3 → ℝ)
    (middle : SourceMatrix) (t : ℝ) : Continuous (fun s => legs point momentum middle t s) :=
  continuous_iff_continuousAt.mpr fun s => (legs_right_derivative point momentum middle t s).continuousAt

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateGreen
