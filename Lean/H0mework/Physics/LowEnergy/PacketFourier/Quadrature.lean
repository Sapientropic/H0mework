import H0mework.Physics.LowEnergy.PacketFourier.Current

/-! The real cosine and sine quadratures are generated from the paired complex
currents; the cosine is the already constructed original time current. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace PacketNoise PacketDynamics GaugeHistory Stage9C.Material.SpinPair
noncomputable section
attribute [local irreducible] freeAction

theorem phaseForward_cosine (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    (1/2 : ℂ) • (phaseForwardLinear transfer time field+phaseForwardLinear (-transfer) time field)=
      timeForwardLinear transfer time field := by
  let outside := boundaryAction.comp (spatialFlow 0 (-time))
  let value := sourceHamiltonian (flowDomain time field)
  change (1/2 : ℂ) • (outside (phaseShift transfer value)+outside (phaseShift (-transfer) value))=
    outside ((1/2 : ℂ) • (phaseShift transfer value+phaseShift (-transfer) value))
  rw [map_smul,map_add]

theorem phaseBackward_cosine (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    (1/2 : ℂ) • (phaseBackwardLinear transfer time field+phaseBackwardLinear (-transfer) time field)=
      timeBackwardLinear transfer time field := by
  let input := adjointDomain (-time) (boundaryDomain field)
  let outside := (adjointFlow time).toLinearMap.comp conjugateHamiltonianLinear
  change (1/2 : ℂ) • (outside (phaseDomain transfer input)+outside (phaseDomain (-transfer) input))=
    outside (cosineDomain transfer input)
  rw [cosineDomain_phases,map_smul,map_add]

attribute [local irreducible] phaseForwardLinear phaseBackwardLinear timeForwardLinear timeBackwardLinear

theorem phaseCurrent_cosine (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    (1/2 : ℂ) • (phaseCurrentField transfer time field+phaseCurrentField (-transfer) time field)=
      timeCurrentField transfer time field := by
  change (1/2 : ℂ) •
      ((((lapse^2)⁻¹ : ℝ) : ℂ) • (phaseForwardLinear transfer time field+phaseBackwardLinear transfer time field)+
        (((lapse^2)⁻¹ : ℝ) : ℂ) • (phaseForwardLinear (-transfer) time field+phaseBackwardLinear (-transfer) time field))=
    (((lapse^2)⁻¹ : ℝ) : ℂ) • (timeForwardLinear transfer time field+timeBackwardLinear transfer time field)
  calc
    _ = (((lapse^2)⁻¹ : ℝ) : ℂ) •
        ((1/2 : ℂ) • (phaseForwardLinear transfer time field+phaseForwardLinear (-transfer) time field)+
          (1/2 : ℂ) • (phaseBackwardLinear transfer time field+phaseBackwardLinear (-transfer) time field)) := by module
    _ = _ := by rw [phaseForward_cosine,phaseBackward_cosine]

def sineCurrentLinear (transfer : Position) (time : ℝ) :
    Quantum.Generator.domain freeAction →ₗ[ℂ] FullMatterL2 :=
  (2*Complex.I)⁻¹ • (phaseCurrentLinear transfer time-phaseCurrentLinear (-transfer) time)

def sineCurrentField (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  sineCurrentLinear transfer time field

theorem sineCurrentField_apply (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    sineCurrentField transfer time field=(2*Complex.I)⁻¹ •
      (phaseCurrentField transfer time field-phaseCurrentField (-transfer) time field) := rfl

theorem sineCurrentField_add (transfer : Position) (time : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    sineCurrentField transfer time (left+right)=
      sineCurrentField transfer time left+sineCurrentField transfer time right := map_add _ _ _

theorem sineCurrentField_smul (transfer : Position) (time : ℝ) (scale : ℂ)
    (field : Quantum.Generator.domain freeAction) :
    sineCurrentField transfer time (scale • field)=scale • sineCurrentField transfer time field := map_smul _ _ _

attribute [local irreducible] phaseCurrentField

theorem sineCurrentField_pair (transfer : Position) (time : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (sineCurrentField transfer time left) right.val=
      inner ℂ left.val (sineCurrentField transfer time right) := by
  rw [sineCurrentField_apply,sineCurrentField_apply,inner_smul_left,inner_smul_right,
    inner_sub_left,inner_sub_right]
  have coefficient : (starRingEnd ℂ) ((2*Complex.I)⁻¹)= -((2*Complex.I)⁻¹) := by
    simp only [map_inv₀,map_mul,map_ofNat,Complex.conj_I,mul_neg,inv_neg]
  rw [coefficient]
  have opposite := phaseCurrentField_pair (-transfer) time left right
  rw [neg_neg] at opposite
  have difference := congrArg₂ (fun first second : ℂ => first-second)
    (phaseCurrentField_pair transfer time left right) opposite
  calc
    _ = -((2*Complex.I)⁻¹)*
        (inner ℂ left.val (phaseCurrentField (-transfer) time right)-
          inner ℂ left.val (phaseCurrentField transfer time right)) := congrArg _ difference
    _ = _ := by ring

def sineCurrentMean (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) : ℂ :=
  inner ℂ field.val (sineCurrentField transfer time field)

theorem sineCurrentMean_real (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    star (sineCurrentMean transfer time field)=sineCurrentMean transfer time field := by
  change (starRingEnd ℂ) (inner ℂ field.val (sineCurrentField transfer time field))=
    inner ℂ field.val (sineCurrentField transfer time field)
  rw [inner_conj_symm,sineCurrentField_pair]

theorem phaseCurrent_reconstruct (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    phaseCurrentField transfer time field=
      timeCurrentField transfer time field+Complex.I • sineCurrentField transfer time field := by
  rw [← phaseCurrent_cosine,sineCurrentField_apply,smul_smul]
  have coefficient : Complex.I*(2*Complex.I)⁻¹=(1/2 : ℂ) := by field_simp
  rw [coefficient]
  module

theorem sineCurrentField_zero_transfer (time : ℝ) (field : Quantum.Generator.domain freeAction) :
    sineCurrentField 0 time field=0 := by
  rw [sineCurrentField_apply,neg_zero,sub_self,smul_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
