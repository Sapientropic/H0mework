import H0mework.Versions.R71e.Physics.LowEnergy.PacketField.Circle

/-! The same two native rotation circles admit a specified Borel alignment.
No global continuous choice of spin frame is needed for the spatial field. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open Rotation ProofFreeRicherAnholonomicSource
noncomputable section

def firstCosine (momentum : Fin 3 → ℝ) : ℝ :=
  if transverseRadius momentum=0 then 1 else momentum 0/transverseRadius momentum

def firstSine (momentum : Fin 3 → ℝ) : ℝ :=
  if transverseRadius momentum=0 then 0 else momentum 1/transverseRadius momentum

theorem specified_first_alignment (momentum : Fin 3 → ℝ) :
    (firstCosine momentum)^2+(firstSine momentum)^2=1 ∧
      rotateZ (firstCosine momentum) (firstSine momentum) *ᵥ ![0,momentum 0,momentum 1,momentum 2]=
        ![0,transverseRadius momentum,0,momentum 2] := by
  by_cases zero : transverseRadius momentum=0
  · have sq := transverseRadius_square momentum
    have zero0 : momentum 0=0 := by nlinarith [sq_nonneg (momentum 1)]
    have zero1 : momentum 1=0 := by nlinarith [sq_nonneg (momentum 0)]
    constructor
    · simp [firstCosine,firstSine,zero]
    · ext row
      fin_cases row <;> simp [firstCosine,firstSine,rotateZ,Matrix.mulVec,dotProduct,Fin.sum_univ_four,zero,zero0,zero1]
  · simp only [firstCosine,firstSine,if_neg zero]
    constructor
    · have sq := transverseRadius_square momentum
      field_simp
      nlinarith [sq]
    · ext row
      fin_cases row <;> simp [rotateZ,Matrix.mulVec,dotProduct,Fin.sum_univ_four]
      · field_simp
        exact (transverseRadius_square momentum).symm
      · ring

def borelParameters (momentum : Fin 3 → ℝ) : ℝ×ℝ :=
  (circleParameter (momentum 2/momentumRadius momentum) (transverseRadius momentum/momentumRadius momentum),
    circleParameter (firstCosine momentum) (firstSine momentum))

def borelRotation (momentum : Fin 3 → ℝ) : LorentzianCoframe :=
  rotateY (circleCos (borelParameters momentum).1) (circleSin (borelParameters momentum).1)*
    rotateZ (circleCos (borelParameters momentum).2) (circleSin (borelParameters momentum).2)

theorem borelRotation_generated (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) :
    (borelRotation momentum).transpose*borelRotation momentum=1 ∧ (borelRotation momentum).det=1 ∧
      borelRotation momentum *ᵥ ![0,momentum 0,momentum 1,momentum 2]=![0,0,0,momentumRadius momentum] := by
  obtain ⟨firstUnit,first⟩ := specified_first_alignment momentum
  obtain ⟨zc,zs⟩ := circleParameter_correct (firstCosine momentum) (firstSine momentum) firstUnit
  obtain ⟨secondUnit,second⟩ := second_alignment momentum nonzero
  obtain ⟨yc,ys⟩ := circleParameter_correct _ _ secondUnit
  unfold borelRotation borelParameters
  refine ⟨?_,?_,?_⟩
  · rw [Matrix.transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc (rotateY _ _).transpose,
      rotateY_orthogonal _ _ (circle_unit _),Matrix.one_mul,rotateZ_orthogonal _ _ (circle_unit _)]
  · rw [Matrix.det_mul,rotateY_det _ _ (circle_unit _),rotateZ_det _ _ (circle_unit _),one_mul]
  · rw [← Matrix.mulVec_mulVec,zc,zs,first,yc,ys]
    exact second

theorem borelParameters_measurable : Measurable borelParameters := by
  have radius : Measurable momentumRadius := by unfold momentumRadius; fun_prop
  have transverse : Measurable transverseRadius := by unfold transverseRadius; fun_prop
  have firstC : Measurable firstCosine :=
    Measurable.ite (measurableSet_eq_fun transverse measurable_const) measurable_const
      ((measurable_pi_apply 0).div transverse)
  have firstS : Measurable firstSine :=
    Measurable.ite (measurableSet_eq_fun transverse measurable_const) measurable_const
      ((measurable_pi_apply 1).div transverse)
  exact (circleParameter_measurable.comp (((measurable_pi_apply 2).div radius).prodMk (transverse.div radius))).prodMk
    (circleParameter_measurable.comp (firstC.prodMk firstS))

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
