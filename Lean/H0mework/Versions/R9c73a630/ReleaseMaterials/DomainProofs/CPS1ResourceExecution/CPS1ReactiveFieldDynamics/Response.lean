import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Fock
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.WholeBasisResponse

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace CPS1ReactiveFieldDynamics
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace Matrix Topology

def responseCoordinates (state : Snapshot) (time : ℝ) : Matrix (BasisIndex state) state.ElectronIndex ℂ :=
  CPS1ElectronicEvolution.occupiedUpdate (fullFock state) (time/2) (coordinates state)

def response (state : Snapshot) (time : ℝ) : Snapshot :=
  withOccupation state (increment state (responseCoordinates state time))

def fullAction (state : Snapshot) : SpinSpace →L[ℂ] SpinSpace :=
  ∑ first, ∑ second, fullFock state first second •
    (innerSL ℂ (basis state second)).smulRight (basis state first)

theorem full_action_fields (state : Snapshot) (coefficients : Matrix (BasisIndex state) state.ElectronIndex ℂ)
    (slot : state.ElectronIndex) :
    fullAction state (CPS1ElectronicEvolution.fields (basis state) coefficients slot) =
      CPS1ElectronicEvolution.fields (basis state) (fullFock state * coefficients) slot := by
  simp only [fullAction,sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,CPS1ElectronicEvolution.fields,(basis_orthonormal state).inner_right_fintype,
    Matrix.mul_apply,smul_smul,Finset.sum_smul]

theorem response_fields (state : Snapshot) (time : ℝ) (slot : state.ElectronIndex) :
    (response state time).fields slot = CPS1ElectronicEvolution.fields (basis state)
      (responseCoordinates state time) slot := increment_fields state _ slot

theorem response_good (state : Snapshot) (good : state.Good) (time : ℝ) : (response state time).Good := by
  have fields : (response state time).fields =
      CPS1ElectronicEvolution.fields (basis state) (responseCoordinates state time) :=
    funext (response_fields state time)
  rw [CPS1ReactiveField.Carried.Snapshot.Good,fields]
  exact CPS1ElectronicEvolution.updated_fields _ (basis_orthonormal state) _
    (full_fock_hermitian state) _ _ (coordinates_gram state good)

theorem response_coordinates_zero (state : Snapshot) : responseCoordinates state 0 = coordinates state := by
  simp only [responseCoordinates,zero_div,CPS1ElectronicEvolution.occupiedUpdate,
    CPS1ElectronicEvolution.zero_time,Matrix.one_mul]

theorem response_zero (state : Snapshot) : response state 0 = state := by
  unfold response
  rw [response_coordinates_zero,increment_current]
  cases state
  rfl

theorem response_source (state : Snapshot) (time : ℝ) :
    (response state time).primitive = state.primitive ∧
    (response state time).nuclei = state.nuclei ∧
    (response state time).waterOrigins = state.waterOrigins ∧
    (response state time).electronInertia = state.electronInertia ∧
    (response state time).Ne = state.Ne ∧ (response state time).reserve = state.reserve :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem response_equation (state : Snapshot) (time : ℝ) :
    CPS1ElectronicEvolution.denominator (fullFock state) (time/2) * responseCoordinates state time =
      (1-CPS1ElectronicEvolution.generator (fullFock state) (time/2))*coordinates state := by
  unfold responseCoordinates CPS1ElectronicEvolution.occupiedUpdate
  rw [← Matrix.mul_assoc,CPS1ElectronicEvolution.actual_equation _ (full_fock_hermitian state)]

theorem response_midpoint (state : Snapshot) (time : ℝ) (slot : state.ElectronIndex) :
    (response state time).fields slot + (Complex.I*((time/2 : ℝ) : ℂ)) •
      fullAction state ((response state time).fields slot) =
      state.fields slot - (Complex.I*((time/2 : ℝ) : ℂ)) • fullAction state (state.fields slot) := by
  have equation := response_equation state time
  have matrixEq : responseCoordinates state time + (Complex.I*((time/2 : ℝ) : ℂ)) •
      (fullFock state * responseCoordinates state time) =
      coordinates state - (Complex.I*((time/2 : ℝ) : ℂ)) • (fullFock state * coordinates state) := by
    simpa only [CPS1ElectronicEvolution.denominator,CPS1ElectronicEvolution.generator,
      Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul] using equation
  have readout := congrArg (fun matrix => CPS1ElectronicEvolution.fields (basis state) matrix slot) matrixEq
  have scalar (value : ℂ) (matrix : Matrix (BasisIndex state) state.ElectronIndex ℂ)
      (index : BasisIndex state) (electron : state.ElectronIndex) :
      (value • matrix) index electron = value * matrix index electron := rfl
  rw [response_fields,← current_coordinates state slot,full_action_fields,full_action_fields]
  simpa only [CPS1ElectronicEvolution.fields,Matrix.add_apply,Matrix.sub_apply,scalar,
    add_smul,sub_smul,smul_smul,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.smul_sum] using readout

def sourceDensity (state : Snapshot) : Matrix (BasisIndex state) (BasisIndex state) ℂ :=
  coordinates state * (coordinates state).conjTranspose

def responseDensity (state : Snapshot) (time : ℝ) : Matrix (BasisIndex state) (BasisIndex state) ℂ :=
  responseCoordinates state time * (responseCoordinates state time).conjTranspose

theorem response_density (state : Snapshot) (time : ℝ) :
    responseDensity state time = CPS1ElectronicEvolution.densityUpdate (fullFock state) (time/2)
      (sourceDensity state) := by
  simp only [responseDensity,responseCoordinates,CPS1ElectronicEvolution.occupiedUpdate,
    CPS1ElectronicEvolution.densityUpdate,sourceDensity,Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem response_coordinates_continuous (state : Snapshot) (point : ℝ) :
    ContinuousAt (responseCoordinates state) point := by
  exact CPS1PositivePulse.occupied_update_continuousAt (fun _ : ℝ => fullFock state)
    (fun time : ℝ => time/2) (fun _ : ℝ => coordinates state) point continuousAt_const
    (continuous_id.div_const 2).continuousAt continuousAt_const (full_fock_hermitian state)

theorem response_occupation_continuous (state : Snapshot) (point : ℝ) :
    ContinuousAt (fun time : ℝ => increment state (responseCoordinates state time)) point := by
  have difference : ContinuousAt (fun time : ℝ => responseCoordinates state time-coordinates state) point :=
    (response_coordinates_continuous state point).sub
      (continuousAt_const (y := coordinates state))
  have generated := CPS1PositivePulse.matrix_mul_continuousAt (fun _ : ℝ => sourceCoefficient state)
    (fun time => responseCoordinates state time-coordinates state) point continuousAt_const difference
  exact (continuousAt_const (y := state.occupied)).add generated

end
end CPS1ReactiveFieldDynamics
