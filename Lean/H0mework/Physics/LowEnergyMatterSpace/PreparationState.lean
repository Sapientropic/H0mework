import H0mework.Physics.LowEnergyMatterSpace.PreparationHistory
import H0mework.Physics.LowEnergyActive.Triplet
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-! The generated preparation map transports the original finite source vector to a spatial state. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace ComplexOrder
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open ActiveSector Stage9C.Material.SpinPair InnerProductSpace
noncomputable section
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def sourcePrepared : MatterFiber :=
  WithLp.toLp 2 (fun index : SourceIndex => originalTripletCoefficients 1 1 index.1 index.2 / 2)

theorem sourcePrepared_inner : inner ℂ sourcePrepared sourcePrepared=1 := by
  rw [PiLp.inner_apply]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_three]
  norm_num [sourcePrepared,originalTripletCoefficients]

theorem sourcePrepared_norm : ‖sourcePrepared‖=1 := by
  have real := congrArg Complex.re sourcePrepared_inner
  change RCLike.re (inner ℂ sourcePrepared sourcePrepared)=1 at real
  rw [inner_self_eq_norm_sq] at real
  nlinarith [norm_nonneg sourcePrepared]

theorem sourcePrepared_actual_origin :
    actual.matter 0=(2 : ℂ) • tripletMatter (fun spin color => sourcePrepared (spin,color)) := by
  change spinPairMatter (upperPhase 0) (lowerPhase 0)=_
  rw [upperPhase,lowerPhase,phase_zero,phase_zero,original_matter_triplet]
  unfold tripletMatter
  funext spin
  simp only [Pi.smul_apply,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro color _
  congr 1
  change originalTripletCoefficients 1 1 spin color=2*(originalTripletCoefficients 1 1 spin color/2)
  ring

def spatialPreparation (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) : MatterL2 :=
  preparationMap force continuousForce t sourcePrepared

def transportedDensity (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) : MatterL2 →L[ℂ] MatterL2 :=
  (preparationMap force continuousForce t).comp
    ((rankOne ℂ sourcePrepared sourcePrepared).comp (preparationMap force continuousForce t).adjoint)

theorem transportedDensity_generated (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) :
    transportedDensity force continuousForce t=
      rankOne ℂ (spatialPreparation force continuousForce t) (spatialPreparation force continuousForce t) := by
  apply ContinuousLinearMap.ext
  intro v
  change preparationMap force continuousForce t
      (inner ℂ sourcePrepared ((preparationMap force continuousForce t).adjoint v) • sourcePrepared)=
    inner ℂ (preparationMap force continuousForce t sourcePrepared) v •
      preparationMap force continuousForce t sourcePrepared
  rw [map_smul,ContinuousLinearMap.adjoint_inner_right]

theorem transportedDensity_positive (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) : 0≤transportedDensity force continuousForce t := by
  rw [transportedDensity_generated,ContinuousLinearMap.nonneg_iff_isPositive]
  exact isPositive_rankOne_self _

def spatialResponse (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) : (MatterL2 →L[ℂ] MatterL2) →L[ℂ] ℂ :=
  (innerSL ℂ (spatialPreparation force continuousForce t)).comp
    (ContinuousLinearMap.apply ℂ MatterL2 (spatialPreparation force continuousForce t))

theorem spatialResponse_source_pullback (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (A : MatterL2 →L[ℂ] MatterL2) :
    spatialResponse force continuousForce t A=
      inner ℂ sourcePrepared ((preparationMap force continuousForce t).adjoint
        (A (preparationMap force continuousForce t sourcePrepared))) := by
  change inner ℂ (preparationMap force continuousForce t sourcePrepared)
    (A (preparationMap force continuousForce t sourcePrepared))=_
  exact (ContinuousLinearMap.adjoint_inner_right (preparationMap force continuousForce t)
    sourcePrepared (A (preparationMap force continuousForce t sourcePrepared))).symm

theorem spatialResponse_square (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (A : MatterL2 →L[ℂ] MatterL2) :
    spatialResponse force continuousForce t (A.adjoint.comp A)=
      ((‖A (spatialPreparation force continuousForce t)‖^2 : ℝ) : ℂ) := by
  change inner ℂ (spatialPreparation force continuousForce t)
    (A.adjoint (A (spatialPreparation force continuousForce t)))=_
  rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
  norm_cast

theorem original_preparation_amplitude (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (A : MatterL2 →L[ℂ] MatterL2) :
    inner ℂ (preparationMap force continuousForce t ((2 : ℂ) • sourcePrepared))
      (A (preparationMap force continuousForce t ((2 : ℂ) • sourcePrepared)))=
      4*spatialResponse force continuousForce t A := by
  rw [map_smul,map_smul,inner_smul_left,inner_smul_right]
  change star (2 : ℂ)*(2*spatialResponse force continuousForce t A)=_
  norm_num
  ring

def spatialFunctional (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) : (MatterL2 →L[ℂ] MatterL2) →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (spatialResponse force continuousForce t).toLinearMap
    (fun A positive => (ContinuousLinearMap.nonneg_iff_isPositive A).mp positive |>.inner_nonneg_right _)

theorem spatialFunctional_one (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) :
    spatialFunctional force continuousForce t 1=((‖spatialPreparation force continuousForce t‖^2 : ℝ) : ℂ) := by
  change inner ℂ (spatialPreparation force continuousForce t) (spatialPreparation force continuousForce t)=_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

def normalizedPreparation (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) : MatterL2 :=
  ((‖spatialPreparation force continuousForce t‖⁻¹ : ℝ) : ℂ) • spatialPreparation force continuousForce t

theorem normalizedPreparation_norm (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (nonzero : spatialPreparation force continuousForce t≠0) :
    ‖normalizedPreparation force continuousForce t‖=1 := by
  rw [normalizedPreparation,norm_smul,Complex.norm_real,Real.norm_of_nonneg
    (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr nonzero)]

def normalizedFunctional (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) : (MatterL2 →L[ℂ] MatterL2) →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((innerSL ℂ (normalizedPreparation force continuousForce t)).comp
      (ContinuousLinearMap.apply ℂ MatterL2 (normalizedPreparation force continuousForce t))).toLinearMap
    (fun A positive => (ContinuousLinearMap.nonneg_iff_isPositive A).mp positive |>.inner_nonneg_right _)

theorem normalizedFunctional_one (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (nonzero : spatialPreparation force continuousForce t≠0) :
    normalizedFunctional force continuousForce t 1=1 := by
  change inner ℂ (normalizedPreparation force continuousForce t)
    (normalizedPreparation force continuousForce t)=1
  rw [inner_self_eq_norm_sq_to_K,normalizedPreparation_norm force continuousForce t nonzero]
  norm_num

def preparedOccupation (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) : MatterL2 →L[ℂ] MatterL2 :=
  rankOne ℂ (normalizedPreparation force continuousForce t) (normalizedPreparation force continuousForce t)

theorem preparedOccupation_projection (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (nonzero : spatialPreparation force continuousForce t≠0) :
    IsStarProjection (preparedOccupation force continuousForce t) :=
  isStarProjection_rankOne_self (normalizedPreparation_norm force continuousForce t nonzero)

theorem preparedOccupation_bounds (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (nonzero : spatialPreparation force continuousForce t≠0) :
    0≤preparedOccupation force continuousForce t ∧ preparedOccupation force continuousForce t≤1 :=
  ⟨(preparedOccupation_projection force continuousForce t nonzero).nonneg,
    (preparedOccupation_projection force continuousForce t nonzero).le_one⟩

theorem normalizedPreparation_evolution_norm (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t elapsed : ℝ)
    (nonzero : spatialPreparation force continuousForce t≠0) :
    ‖spatialUnitary elapsed (normalizedPreparation force continuousForce t)‖=1 := by
  rw [spatialUnitary_norm,normalizedPreparation_norm force continuousForce t nonzero]

theorem normalizedPreparation_evolution_response (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t elapsed : ℝ) (A : MatterL2 →L[ℂ] MatterL2) :
    inner ℂ (spatialUnitary elapsed (normalizedPreparation force continuousForce t))
      (A (spatialUnitary elapsed (normalizedPreparation force continuousForce t)))=
      normalizedFunctional force continuousForce t
        ((spatialUnitary elapsed).toContinuousLinearEquiv.toContinuousLinearMap.adjoint.comp
          (A.comp (spatialUnitary elapsed).toContinuousLinearEquiv.toContinuousLinearMap)) := by
  exact (ContinuousLinearMap.adjoint_inner_right
    (spatialUnitary elapsed).toContinuousLinearEquiv.toContinuousLinearMap
    (normalizedPreparation force continuousForce t)
    (A (spatialUnitary elapsed (normalizedPreparation force continuousForce t)))).symm

theorem source_history_generates_normalized_state (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (atTime : ℝ) (nonzero : force atTime sourcePrepared≠0) :
    ∃ t, normalizedFunctional force continuousForce t 1=1 ∧
      IsStarProjection (preparedOccupation force continuousForce t) := by
  obtain ⟨t,generated⟩ := preparationMap_nonzero_some_time force continuousForce sourcePrepared atTime nonzero
  exact ⟨t,normalizedFunctional_one force continuousForce t generated,
    preparedOccupation_projection force continuousForce t generated⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
