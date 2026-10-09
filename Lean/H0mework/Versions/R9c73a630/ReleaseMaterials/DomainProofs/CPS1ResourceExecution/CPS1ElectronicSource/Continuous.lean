import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Projection

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open scoped Matrix InnerProductSpace
open CPS1ElectronicEvolution
variable {frame : CPS1Recycling.Frame}

def continuousAction (state : State frame) : SpinSpace →L[ℂ] SpinSpace :=
  ∑ i, ∑ j, state.hamiltonian i j •
    (innerSL ℂ (basis state.geometry j)).smulRight (basis state.geometry i)

theorem continuous_action_exact (state : State frame) :
    (continuousAction state).toLinearMap = projectedAction state := by
  apply LinearMap.ext
  intro field
  change continuousAction state field =
    ∑ i, (∑ j, state.hamiltonian i j * inner ℂ (basis state.geometry j) field) • basis state.geometry i
  simp only [continuousAction,sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,smul_smul,Finset.sum_smul]

theorem actual_continuous_midpoint (state : State frame) (time : ℝ) (slot : ElectronIndex state.geometry) :
    let updated := occupiedUpdate state.hamiltonian (time/2) state.occupied
    let before := fields (basis state.geometry) state.occupied slot
    let after := fields (basis state.geometry) updated slot
    after + (Complex.I * ((time/2 : ℝ) : ℂ)) • continuousAction state after =
      before - (Complex.I * ((time/2 : ℝ) : ℂ)) • continuousAction state before := by
  have action : ∀ field, continuousAction state field = projectedAction state field :=
    fun field => congrArg (fun operator : SpinSpace →ₗ[ℂ] SpinSpace => operator field)
      (continuous_action_exact state)
  simpa only [action] using projected_midpoint state time slot

end
end CPS1ElectronicSource
