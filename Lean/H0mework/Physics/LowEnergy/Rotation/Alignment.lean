import H0mework.Physics.LowEnergy.Rotation.Hodge
import H0mework.Physics.LowEnergy.Rotation.Circle

/-! Constructive alignment of every nonzero real spatial momentum by the same two rotation circles. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Rotation
open ProofFreeRicherAnholonomicSource
open scoped Matrix
noncomputable section

def momentumRadius (momentum : Fin 3 → ℝ) : ℝ :=
  Real.sqrt ((momentum 0)^2+(momentum 1)^2+(momentum 2)^2)

def transverseRadius (momentum : Fin 3 → ℝ) : ℝ :=
  Real.sqrt ((momentum 0)^2+(momentum 1)^2)

theorem momentumRadius_square (momentum : Fin 3 → ℝ) :
    (momentumRadius momentum)^2=(momentum 0)^2+(momentum 1)^2+(momentum 2)^2 :=
  Real.sq_sqrt (by positivity)

theorem transverseRadius_square (momentum : Fin 3 → ℝ) :
    (transverseRadius momentum)^2=(momentum 0)^2+(momentum 1)^2 :=
  Real.sq_sqrt (by positivity)

theorem momentumRadius_positive (momentum : Fin 3 → ℝ) (nonzero : momentum ≠ 0) :
    0 < momentumRadius momentum := by
  apply Real.sqrt_pos.2
  by_contra failed
  have zero0 : momentum 0=0 := by nlinarith [sq_nonneg (momentum 1), sq_nonneg (momentum 2)]
  have zero1 : momentum 1=0 := by nlinarith [sq_nonneg (momentum 0), sq_nonneg (momentum 2)]
  have zero2 : momentum 2=0 := by nlinarith [sq_nonneg (momentum 0), sq_nonneg (momentum 1)]
  apply nonzero
  funext index
  fin_cases index <;> simp [zero0, zero1, zero2]

theorem first_alignment (momentum : Fin 3 → ℝ) :
    ∃ c s : ℝ, c^2+s^2=1 ∧
      rotateZ c s *ᵥ ![0,momentum 0,momentum 1,momentum 2] =
        ![0,transverseRadius momentum,0,momentum 2] := by
  by_cases zero : transverseRadius momentum = 0
  · have sq := transverseRadius_square momentum
    have zero0 : momentum 0=0 := by nlinarith [sq_nonneg (momentum 1)]
    have zero1 : momentum 1=0 := by nlinarith [sq_nonneg (momentum 0)]
    refine ⟨1,0,by norm_num,?_⟩
    ext row
    fin_cases row <;> simp [rotateZ, Matrix.mulVec, dotProduct, Fin.sum_univ_four, zero, zero0, zero1]
  · refine ⟨momentum 0/transverseRadius momentum,momentum 1/transverseRadius momentum,?_,?_⟩
    · have sq := transverseRadius_square momentum
      field_simp
      nlinarith [sq]
    · ext row
      fin_cases row <;> simp [rotateZ, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      · field_simp
        exact (transverseRadius_square momentum).symm
      · ring

theorem second_alignment (momentum : Fin 3 → ℝ) (nonzero : momentum ≠ 0) :
    (momentum 2/momentumRadius momentum)^2+(transverseRadius momentum/momentumRadius momentum)^2=1 ∧
      rotateY (momentum 2/momentumRadius momentum) (transverseRadius momentum/momentumRadius momentum) *ᵥ
        ![0,transverseRadius momentum,0,momentum 2] = ![0,0,0,momentumRadius momentum] := by
  have positive := momentumRadius_positive momentum nonzero
  have norm_nonzero := ne_of_gt positive
  have sq := momentumRadius_square momentum
  have transverse := transverseRadius_square momentum
  constructor
  · field_simp
    nlinarith
  · ext row
    fin_cases row <;> simp [rotateY, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    · ring
    · field_simp
      nlinarith

theorem momentum_alignment (momentum : Fin 3 → ℝ) (nonzero : momentum ≠ 0) :
    ∃ y z : ℝ,
      let rotation := rotateY (circleCos y) (circleSin y)*rotateZ (circleCos z) (circleSin z)
      rotation.transpose*rotation=1 ∧ rotation.det=1 ∧
        rotation *ᵥ ![0,momentum 0,momentum 1,momentum 2] = ![0,0,0,momentumRadius momentum] := by
  obtain ⟨c,s,unit,first⟩ := first_alignment momentum
  obtain ⟨z,zc,zs⟩ := circle_surjective c s unit
  obtain ⟨yunit,second⟩ := second_alignment momentum nonzero
  obtain ⟨y,yc,ys⟩ := circle_surjective (momentum 2/momentumRadius momentum)
    (transverseRadius momentum/momentumRadius momentum) yunit
  refine ⟨y,z,?_,?_,?_⟩
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (rotateY _ _).transpose,
      rotateY_orthogonal _ _ (circle_unit y), Matrix.one_mul,
      rotateZ_orthogonal _ _ (circle_unit z)]
  · rw [Matrix.det_mul, rotateY_det _ _ (circle_unit y), rotateZ_det _ _ (circle_unit z), one_mul]
  · rw [← Matrix.mulVec_mulVec, zc, zs, first, yc, ys]
    exact second

theorem zero_momentum_rotation :
    (1 : LorentzianCoframe) *ᵥ (![0,0,0,0] : LorentzianIndex → ℝ) = ![0,0,0,0] ∧
      momentumRadius (0 : Fin 3 → ℝ)=0 := by
  simp [momentumRadius]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Rotation
