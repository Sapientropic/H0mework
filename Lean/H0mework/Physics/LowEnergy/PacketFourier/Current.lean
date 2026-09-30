import H0mework.Physics.LowEnergy.PacketFourier.Domains

/-! Both terms use the same Fourier phase. Their complete adjoint therefore
returns the opposite momentum current, retaining the original boundary order. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace PacketNoise PacketDynamics GaugeHistory Stage9C.Material.SpinPair
noncomputable section
attribute [local irreducible] freeAction

def phaseForwardLinear (transfer : Position) (time : ℝ) :
    Quantum.Generator.domain freeAction →ₗ[ℂ] FullMatterL2 :=
  boundaryAction.toLinearMap.comp ((spatialFlow 0 (-time)).toLinearMap.comp
    ((phaseShift transfer).toLinearMap.comp
      (sourceHamiltonianLinear.comp (flowDomainLinear time))))

def phaseBackwardLinear (transfer : Position) (time : ℝ) :
    Quantum.Generator.domain freeAction →ₗ[ℂ] FullMatterL2 :=
  (adjointFlow time).toLinearMap.comp
    (conjugateHamiltonianLinear.comp ((phaseDomainLinear transfer).comp
      ((adjointDomainLinear (-time)).comp boundaryDomainLinear)))

private theorem flow_pair (time : ℝ) (left right : FullMatterL2) :
    inner ℂ (spatialFlow 0 time left) right=inner ℂ left (adjointFlow time right) := by
  rw [adjointFlow_original]
  exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

theorem phaseForward_pair (transfer : Position) (time : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (phaseForwardLinear transfer time left) right.val=
      inner ℂ left.val (phaseBackwardLinear (-transfer) time right) := by
  change inner ℂ (boundaryAction (spatialFlow 0 (-time)
      (phaseShift transfer (sourceHamiltonian (flowDomain time left))))) right.val=
    inner ℂ left.val (adjointFlow time (conjugateHamiltonian
      (phaseDomain (-transfer) (adjointDomain (-time) (boundaryDomain right)))))
  rw [boundaryAction_symmetric,flow_pair,phase_pair]
  have source := sourceHamiltonian_pair (flowDomain time left)
    (phaseDomain (-transfer) (adjointDomain (-time) (boundaryDomain right)))
  change inner ℂ (sourceHamiltonian (flowDomain time left))
      (phaseShift (-transfer) (adjointFlow (-time) (boundaryAction right.val)))=
    inner ℂ (spatialFlow 0 time left.val) (conjugateHamiltonian
      (phaseDomain (-transfer) (adjointDomain (-time) (boundaryDomain right)))) at source
  rw [source,flow_pair]

theorem phaseBackward_pair (transfer : Position) (time : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (phaseBackwardLinear transfer time left) right.val=
      inner ℂ left.val (phaseForwardLinear (-transfer) time right) := by
  have source := congrArg (starRingEnd ℂ) (phaseForward_pair (-transfer) time right left)
  simpa only [inner_conj_symm,neg_neg] using source.symm

def phaseCurrentLinear (transfer : Position) (time : ℝ) :
    Quantum.Generator.domain freeAction →ₗ[ℂ] FullMatterL2 :=
  (((lapse^2)⁻¹ : ℝ) : ℂ) • (phaseForwardLinear transfer time+phaseBackwardLinear transfer time)

def phaseCurrentField (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  phaseCurrentLinear transfer time field

theorem phaseCurrentField_apply (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    phaseCurrentField transfer time field=(((lapse^2)⁻¹ : ℝ) : ℂ) •
      (boundaryAction (spatialFlow 0 (-time) (phaseShift transfer
        (sourceHamiltonian (flowDomain time field))))+
        adjointFlow time (conjugateHamiltonian
          (phaseDomain transfer (adjointDomain (-time) (boundaryDomain field))))) := rfl

theorem phaseCurrentField_add (transfer : Position) (time : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    phaseCurrentField transfer time (left+right)=
      phaseCurrentField transfer time left+phaseCurrentField transfer time right := map_add _ _ _

theorem phaseCurrentField_smul (transfer : Position) (time : ℝ) (scale : ℂ)
    (field : Quantum.Generator.domain freeAction) :
    phaseCurrentField transfer time (scale • field)=scale • phaseCurrentField transfer time field := map_smul _ _ _

attribute [local irreducible] phaseForwardLinear phaseBackwardLinear

theorem phaseCurrentField_pair (transfer : Position) (time : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (phaseCurrentField transfer time left) right.val=
      inner ℂ left.val (phaseCurrentField (-transfer) time right) := by
  change inner ℂ ((((lapse^2)⁻¹ : ℝ) : ℂ) •
      (phaseForwardLinear transfer time left+phaseBackwardLinear transfer time left)) right.val=
    inner ℂ left.val ((((lapse^2)⁻¹ : ℝ) : ℂ) •
      (phaseForwardLinear (-transfer) time right+phaseBackwardLinear (-transfer) time right))
  rw [inner_smul_left,inner_smul_right,inner_add_left,inner_add_right]
  have real : (starRingEnd ℂ) (((lapse^2)⁻¹ : ℝ) : ℂ)=(((lapse^2)⁻¹ : ℝ) : ℂ) := by simp
  rw [real]
  have pieces := congrArg₂ (fun first second : ℂ => first+second)
    (phaseForward_pair transfer time left right) (phaseBackward_pair transfer time left right)
  exact congrArg (fun value : ℂ => (((lapse^2)⁻¹ : ℝ) : ℂ)*value)
    (pieces.trans (add_comm _ _))

def phaseCurrentMean (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) : ℂ :=
  inner ℂ field.val (phaseCurrentField transfer time field)

theorem phaseCurrentMean_conj (transfer : Position) (time : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    star (phaseCurrentMean transfer time field)=phaseCurrentMean (-transfer) time field := by
  change (starRingEnd ℂ) (inner ℂ field.val (phaseCurrentField transfer time field))=
    inner ℂ field.val (phaseCurrentField (-transfer) time field)
  rw [inner_conj_symm,phaseCurrentField_pair]

theorem phaseCurrentField_zero (transfer : Position) (field : Quantum.Generator.domain freeAction) :
    phaseCurrentField transfer 0 field=(((lapse^2)⁻¹ : ℝ) : ℂ) •
      (boundaryAction (phaseShift transfer (sourceHamiltonian field))+
        conjugateHamiltonian (phaseDomain transfer (boundaryDomain field))) := by
  rw [phaseCurrentField_apply,neg_zero,flowDomain_zero,
    spatialFlow_zero,adjointDomain_zero,adjointFlow_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
