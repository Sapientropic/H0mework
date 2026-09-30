import H0mework.Physics.LowEnergy.PacketDynamics.Domains
import H0mework.Physics.LowEnergy.PacketNoise.Current

/-! The original boundary weight remains to the left of the inverse evolution.
The second term reverses the whole first term on their common source domain. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace PacketNoise GaugeHistory Stage9C.Material.SpinPair
noncomputable section
attribute [local irreducible] freeAction

def timeForwardLinear (transfer : Position) (time : ℝ) :
    Quantum.Generator.domain freeAction →ₗ[ℂ] FullMatterL2 :=
  boundaryAction.toLinearMap.comp ((spatialFlow 0 (-time)).toLinearMap.comp
    ((cosineShift transfer).toLinearMap.comp
      (sourceHamiltonianLinear.comp (flowDomainLinear time))))

def timeBackwardLinear (transfer : Position) (time : ℝ) :
    Quantum.Generator.domain freeAction →ₗ[ℂ] FullMatterL2 :=
  (adjointFlow time).toLinearMap.comp
    (conjugateHamiltonianLinear.comp ((cosineDomainLinear transfer).comp
      ((adjointDomainLinear (-time)).comp boundaryDomainLinear)))

private theorem flow_pair (time : ℝ) (left right : FullMatterL2) :
    inner ℂ (spatialFlow 0 time left) right=inner ℂ left (adjointFlow time right) := by
  rw [adjointFlow_original]
  exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

theorem timeForward_pair (transfer : Position) (time : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (timeForwardLinear transfer time left) right.val=
      inner ℂ left.val (timeBackwardLinear transfer time right) := by
  change inner ℂ (boundaryAction (spatialFlow 0 (-time)
      (cosineShift transfer (sourceHamiltonian (flowDomain time left))))) right.val=
    inner ℂ left.val (adjointFlow time (conjugateHamiltonian
      (cosineDomain transfer (adjointDomain (-time) (boundaryDomain right)))))
  rw [boundaryAction_symmetric,flow_pair,cosine_symmetric]
  have source := sourceHamiltonian_pair (flowDomain time left)
    (cosineDomain transfer (adjointDomain (-time) (boundaryDomain right)))
  change inner ℂ (sourceHamiltonian (flowDomain time left))
      (cosineShift transfer (adjointFlow (-time) (boundaryAction right.val)))=
    inner ℂ (spatialFlow 0 time left.val) (conjugateHamiltonian
      (cosineDomain transfer (adjointDomain (-time) (boundaryDomain right)))) at source
  rw [source,flow_pair]

theorem timeBackward_pair (transfer : Position) (time : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (timeBackwardLinear transfer time left) right.val=
      inner ℂ left.val (timeForwardLinear transfer time right) := by
  have source := congrArg (starRingEnd ℂ) (timeForward_pair transfer time right left)
  simpa only [inner_conj_symm] using source.symm

def timeCurrentLinear (transfer : Position) (time : ℝ) :
    Quantum.Generator.domain freeAction →ₗ[ℂ] FullMatterL2 :=
  (((lapse^2)⁻¹ : ℝ) : ℂ) • (timeForwardLinear transfer time+timeBackwardLinear transfer time)

def timeCurrentField (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  timeCurrentLinear transfer time field

theorem timeCurrentField_apply (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    timeCurrentField transfer time field=(((lapse^2)⁻¹ : ℝ) : ℂ) •
      (boundaryAction (spatialFlow 0 (-time) (cosineShift transfer
        (sourceHamiltonian (flowDomain time field))))+
        adjointFlow time (conjugateHamiltonian
          (cosineDomain transfer (adjointDomain (-time) (boundaryDomain field))))) := rfl

theorem timeCurrentField_add (transfer : Position) (time : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    timeCurrentField transfer time (left+right)=
      timeCurrentField transfer time left+timeCurrentField transfer time right := map_add _ _ _

theorem timeCurrentField_smul (transfer : Position) (time : ℝ) (scale : ℂ)
    (field : Quantum.Generator.domain freeAction) :
    timeCurrentField transfer time (scale • field)=scale • timeCurrentField transfer time field := map_smul _ _ _

attribute [local irreducible] timeForwardLinear timeBackwardLinear

theorem timeCurrentField_pair (transfer : Position) (time : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (timeCurrentField transfer time left) right.val=
      inner ℂ left.val (timeCurrentField transfer time right) := by
  change inner ℂ ((((lapse^2)⁻¹ : ℝ) : ℂ) •
      (timeForwardLinear transfer time left+timeBackwardLinear transfer time left)) right.val=
    inner ℂ left.val ((((lapse^2)⁻¹ : ℝ) : ℂ) •
      (timeForwardLinear transfer time right+timeBackwardLinear transfer time right))
  rw [inner_smul_left,inner_smul_right,inner_add_left,inner_add_right]
  have real : (starRingEnd ℂ) (((lapse^2)⁻¹ : ℝ) : ℂ)=(((lapse^2)⁻¹ : ℝ) : ℂ) := by simp
  rw [real]
  have pieces := congrArg₂ (fun first second : ℂ => first+second)
    (timeForward_pair transfer time left right) (timeBackward_pair transfer time left right)
  exact congrArg (fun value : ℂ => (((lapse^2)⁻¹ : ℝ) : ℂ)*value)
    (pieces.trans (add_comm _ _))

theorem timeCurrentField_zero (transfer : Position) (field : Quantum.Generator.domain freeAction) :
    timeCurrentField transfer 0 field=PacketNoise.currentField transfer field := by
  rw [timeCurrentField_apply,currentField_apply,neg_zero,flowDomain_zero,
    spatialFlow_zero,adjointDomain_zero,adjointFlow_zero]

def timeCurrentMean (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) : ℂ :=
  inner ℂ field.val (timeCurrentField transfer time field)

theorem timeCurrentMean_real (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    star (timeCurrentMean transfer time field)=timeCurrentMean transfer time field := by
  change (starRingEnd ℂ) (inner ℂ field.val (timeCurrentField transfer time field))=
    inner ℂ field.val (timeCurrentField transfer time field)
  rw [inner_conj_symm,timeCurrentField_pair]

theorem timeCurrentMean_im (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    (timeCurrentMean transfer time field).im=0 :=
  Complex.conj_eq_iff_im.mp (timeCurrentMean_real transfer time field)

theorem timeCurrentMean_re_cast (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    ((timeCurrentMean transfer time field).re : ℂ)=timeCurrentMean transfer time field := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im,timeCurrentMean_im]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
