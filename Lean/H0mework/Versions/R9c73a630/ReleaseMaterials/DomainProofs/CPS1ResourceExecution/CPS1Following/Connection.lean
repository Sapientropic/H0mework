import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Translation
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open scoped Matrix InnerProductSpace BigOperators
open CPS1ElectronicEvolution
variable {frame : CPS1Recycling.Frame}

def sourceConnection (state : CPS1ElectronicSource.State frame) (velocity : Point) :
    Matrix (CPS1ElectronicSource.SpinIndex state.geometry) (CPS1ElectronicSource.SpinIndex state.geometry) ℂ :=
  fun first second => inner ℂ (CPS1ElectronicSource.basis state.geometry first) (basisRate state 0 velocity second)

def sourceMomentum (state : CPS1ElectronicSource.State frame) (velocity : Point) :
    Matrix (CPS1ElectronicSource.SpinIndex state.geometry) (CPS1ElectronicSource.SpinIndex state.geometry) ℂ :=
  fun first second => Complex.I * sourceConnection state velocity first second

theorem source_connection_skew (state : CPS1ElectronicSource.State frame) (velocity : Point)
    (first second : CPS1ElectronicSource.SpinIndex state.geometry) :
    sourceConnection state velocity first second + star (sourceConnection state velocity second first) = 0 := by
  have motion : HasDerivAt (fun time : ℝ => time • velocity) velocity 0 := by
    simpa only [one_smul,id_eq] using! (hasDerivAt_id (0 : ℝ)).smul_const velocity
  have each (mode : CPS1ElectronicSource.SpinIndex state.geometry) :=
    moving_basis_curve state (fun time : ℝ => time • velocity) velocity 0 motion mode
  have differentiated := (each first).inner ℂ (each second)
  have fixed : HasDerivAt (fun time : ℝ =>
      inner ℂ (movingBasis state (time • velocity) first) (movingBasis state (time • velocity) second))
      (0 : ℂ) 0 := by
    have same : (fun time : ℝ =>
        inner ℂ (movingBasis state (time • velocity) first) (movingBasis state (time • velocity) second)) =
        fun _ => inner ℂ (CPS1ElectronicSource.basis state.geometry first)
          (CPS1ElectronicSource.basis state.geometry second) := by
      funext time
      exact translate_inner (time • velocity) _ _
    rw [same]
    exact hasDerivAt_const _ _
  have zero := differentiated.unique fixed
  have simplified : inner ℂ (CPS1ElectronicSource.basis state.geometry first) (basisRate state 0 velocity second) +
      inner ℂ (basisRate state 0 velocity first) (CPS1ElectronicSource.basis state.geometry second) = 0 := by
    simpa only [movingBasis,zero_smul,translate_zero] using zero
  have swapped := inner_conj_symm (𝕜 := ℂ) (basisRate state 0 velocity first)
    (CPS1ElectronicSource.basis state.geometry second)
  change star (inner ℂ (CPS1ElectronicSource.basis state.geometry second) (basisRate state 0 velocity first)) =
    inner ℂ (basisRate state 0 velocity first) (CPS1ElectronicSource.basis state.geometry second) at swapped
  change inner ℂ (CPS1ElectronicSource.basis state.geometry first) (basisRate state 0 velocity second) +
    star (inner ℂ (CPS1ElectronicSource.basis state.geometry second) (basisRate state 0 velocity first)) = 0
  rw [swapped]
  exact simplified

theorem source_momentum_hermitian (state : CPS1ElectronicSource.State frame) (velocity : Point) :
    (sourceMomentum state velocity).IsHermitian := by
  apply Matrix.ext
  intro first second
  change star (Complex.I * sourceConnection state velocity second first) =
    Complex.I * sourceConnection state velocity first second
  have swapped : star (sourceConnection state velocity second first) =
      -sourceConnection state velocity first second := by
    apply eq_neg_iff_add_eq_zero.mpr
    rw [add_comm]
    exact source_connection_skew state velocity first second
  have imaginary : star (Complex.I) = -Complex.I := by simp
  rw [star_mul,imaginary,swapped]
  ring

def followingHamiltonian (state : CPS1ElectronicSource.State frame) (velocity : Point) :=
  state.hamiltonian-sourceMomentum state velocity

theorem following_hamiltonian_hermitian (state : CPS1ElectronicSource.State frame) (velocity : Point) :
    (followingHamiltonian state velocity).IsHermitian :=
  (CPS1ElectronicSource.source_hamiltonian_hermitian state).sub (source_momentum_hermitian state velocity)

def followingOccupied (state : CPS1ElectronicSource.State frame) (velocity : Point) (time : ℝ) :=
  occupiedUpdate (followingHamiltonian state velocity) (time/2) state.occupied

def followingAction (state : CPS1ElectronicSource.State frame) (velocity : Point) : SpinSpace →L[ℂ] SpinSpace :=
  ∑ first, ∑ second, followingHamiltonian state velocity first second •
    (innerSL ℂ (CPS1ElectronicSource.basis state.geometry second)).smulRight
      (CPS1ElectronicSource.basis state.geometry first)

theorem following_action_fields (state : CPS1ElectronicSource.State frame) (velocity : Point)
    (occupied : Matrix (CPS1ElectronicSource.SpinIndex state.geometry) (CPS1ElectronicSource.ElectronIndex state.geometry) ℂ)
    (slot : CPS1ElectronicSource.ElectronIndex state.geometry) :
    followingAction state velocity (fields (CPS1ElectronicSource.basis state.geometry) occupied slot) =
      fields (CPS1ElectronicSource.basis state.geometry) (followingHamiltonian state velocity * occupied) slot := by
  simp only [followingAction,sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,CPS1ElectronicEvolution.fields,
    (CPS1ElectronicEvolution.Source.basis_orthonormal state.geometry).inner_right_fintype,
    Matrix.mul_apply,smul_smul,Finset.sum_smul]

theorem following_midpoint (state : CPS1ElectronicSource.State frame) (velocity : Point) (time : ℝ)
    (slot : CPS1ElectronicSource.ElectronIndex state.geometry) :
    let before := fields (CPS1ElectronicSource.basis state.geometry) state.occupied slot
    let after := fields (CPS1ElectronicSource.basis state.geometry) (followingOccupied state velocity time) slot
    after + (Complex.I * ((time/2 : ℝ) : ℂ)) • followingAction state velocity after =
      before - (Complex.I * ((time/2 : ℝ) : ℂ)) • followingAction state velocity before := by
  dsimp only
  have matrix := congrArg (fun operator => operator * state.occupied)
    (actual_equation (followingHamiltonian state velocity) (following_hamiltonian_hermitian state velocity) (time/2))
  have paid : followingOccupied state velocity time +
      (Complex.I * ((time/2 : ℝ) : ℂ)) • (followingHamiltonian state velocity * followingOccupied state velocity time) =
      state.occupied-(Complex.I * ((time/2 : ℝ) : ℂ)) • (followingHamiltonian state velocity * state.occupied) := by
    simpa only [denominator,generator,Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,
      Matrix.mul_assoc,occupiedUpdate,followingOccupied] using matrix
  have continuous := congrArg (fun occupied => fields (CPS1ElectronicSource.basis state.geometry) occupied slot) paid
  rw [CPS1ElectronicSource.fields_add,CPS1ElectronicSource.fields_sub,
    CPS1ElectronicSource.fields_smul,CPS1ElectronicSource.fields_smul] at continuous
  rw [following_action_fields,following_action_fields]
  exact continuous

def movingAction (state : CPS1ElectronicSource.State frame) (centre velocity : Point) : SpinSpace →L[ℂ] SpinSpace :=
  (translate centre).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((followingAction state velocity).comp (translate (-centre)).toContinuousLinearEquiv.toContinuousLinearMap)

theorem moving_action_translated (state : CPS1ElectronicSource.State frame) (centre velocity : Point)
    (field : SpinSpace) :
    movingAction state centre velocity (translate centre field) =
      translate centre (followingAction state velocity field) := by
  change translate centre (followingAction state velocity (translate (-centre) (translate centre field))) = _
  rw [translate_inverse]

theorem moving_midpoint (state : CPS1ElectronicSource.State frame) (beforeCentre afterCentre velocity : Point)
    (time : ℝ) (slot : CPS1ElectronicSource.ElectronIndex state.geometry) :
    let before := translate beforeCentre (fields (CPS1ElectronicSource.basis state.geometry) state.occupied slot)
    let after := translate afterCentre (fields (CPS1ElectronicSource.basis state.geometry) (followingOccupied state velocity time) slot)
    let transported := translate (afterCentre-beforeCentre) before
    after + (Complex.I * ((time/2 : ℝ) : ℂ)) • movingAction state afterCentre velocity after =
      transported - (Complex.I * ((time/2 : ℝ) : ℂ)) • movingAction state afterCentre velocity transported := by
  dsimp only
  rw [translate_add,sub_add_cancel]
  have paid := congrArg (translate afterCentre) (following_midpoint state velocity time slot)
  simpa only [map_add,map_sub,map_smul,moving_action_translated] using paid

theorem following_occupation_gram (state : CPS1ElectronicSource.State frame) (velocity : Point) (time : ℝ) :
    (followingOccupied state velocity time).conjTranspose * followingOccupied state velocity time =
      state.occupied.conjTranspose * state.occupied :=
  occupied_gram _ (following_hamiltonian_hermitian state velocity) _ _

end
end CPS1Following
