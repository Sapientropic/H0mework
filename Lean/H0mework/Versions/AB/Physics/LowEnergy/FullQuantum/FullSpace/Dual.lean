import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.FullSpace.Flow

/-! The original independent dual transports by the full inverse, with its C0 factor retained. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
open YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open StageNineCurrentCoframeMatterTemporalPrincipal
noncomputable section

def principal (point : BasePoint) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (operator (currentCoframeMatterTemporalPrincipal (actual.coframe point))).compLpL 2 volume

def inversePrincipal (point : BasePoint) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))).compLpL 2 volume

theorem inversePrincipal_left (point : BasePoint) (field : FullMatterL2) :
    inversePrincipal point (principal point field)=field := by
  apply Lp.ext
  filter_upwards [(operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))).coeFn_compLpL (principal point field),
    (operator (currentCoframeMatterTemporalPrincipal (actual.coframe point))).coeFn_compLpL field] with x outer inner
  erw [outer,inner]
  obtain ⟨v,equality⟩ := naturalCoordinates.surjective (field x)
  rw [← equality,operator_coordinates,operator_coordinates,
    currentCoframeMatterTemporalPrincipalInverse_left _ (actual_noncharacteristic point)]

theorem inversePrincipal_right (point : BasePoint) (field : FullMatterL2) :
    principal point (inversePrincipal point field)=field := by
  apply Lp.ext
  filter_upwards [(operator (currentCoframeMatterTemporalPrincipal (actual.coframe point))).coeFn_compLpL (inversePrincipal point field),
    (operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))).coeFn_compLpL field] with x outer inner
  erw [outer,inner]
  obtain ⟨v,equality⟩ := naturalCoordinates.surjective (field x)
  rw [← equality,operator_coordinates,operator_coordinates,
    currentCoframeMatterTemporalPrincipalInverse_right _ (actual_noncharacteristic point)]

def dualMomentumFlow (point : BasePoint) (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (spatialFlow point (-time)).adjoint

theorem momentum_pair_preserved (point : BasePoint) (time : ℝ) (dual field : FullMatterL2) :
    inner ℂ (dualMomentumFlow point time dual) (spatialFlow point time field)=inner ℂ dual field := by
  rw [dualMomentumFlow,ContinuousLinearMap.adjoint_inner_left,spatialFlow_inverse]

def originalDualFlow (point : BasePoint) (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (inversePrincipal point).adjoint.comp
    ((dualMomentumFlow point time).comp (principal point).adjoint)

theorem original_pair_preserved (point : BasePoint) (time : ℝ) (dual field : FullMatterL2) :
    inner ℂ (originalDualFlow point time dual) (principal point (spatialFlow point time field))=
      inner ℂ dual (principal point field) := by
  change inner ℂ ((inversePrincipal point).adjoint (dualMomentumFlow point time ((principal point).adjoint dual)))
    (principal point (spatialFlow point time field))=_
  rw [ContinuousLinearMap.adjoint_inner_left,inversePrincipal_left,momentum_pair_preserved,
    ContinuousLinearMap.adjoint_inner_left]

theorem original_pair_integral (point : BasePoint) (time : ℝ) (dual field : FullMatterL2) :
    (∫ x, inner ℂ (originalDualFlow point time dual x) (principal point (spatialFlow point time field) x))=
      ∫ x, inner ℂ (dual x) (principal point field x) := by
  rw [← L2.inner_def,← L2.inner_def]
  exact original_pair_preserved point time dual field

theorem dualMomentumFlow_norm (point : BasePoint) (time : ℝ) :
    ‖dualMomentumFlow point time‖≤1+|time| * sourceRate point := by
  rw [dualMomentumFlow,ContinuousLinearMap.adjoint.norm_map]
  simpa only [abs_neg] using spatialFlow_norm point (-time)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
