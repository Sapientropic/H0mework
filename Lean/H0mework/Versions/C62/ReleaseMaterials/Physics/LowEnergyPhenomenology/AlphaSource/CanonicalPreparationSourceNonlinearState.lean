import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCausalState
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNonlinearPreparedLaplace

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourcePreparedResponse
open PreparationVacuumSourcePreparedState PreparationVacuumCausalFieldResponse PreparationVacuumNonlinearLaplace
open PreparationVacuumFieldPerturbation PreparationVacuumDampedFieldPerturbation
open GaussCoreHilbert GaussComposite GaussComposite.SourceGraph
open CanonicalPhysicalSpatial CanonicalGradedSpatialSource PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open FullYSourceCutoffVolterra SourceFamilyOperator SourceFiniteUnitary GaussUnitaryHistory
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation
open PreparationChartGuard PreparationScalarCoordinates
open scoped Topology InnerProductSpace
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

def sourceProfile (epsilon : ℝ) (precision : 0<epsilon) : Profile :=
  zeroLocalizedProfile actualNativeLocalizer (sourceCausalState epsilon precision).point.val

def preparedLaplace (epsilon : ℝ) (precision : 0<epsilon) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping : ℝ) (positive : 0<damping)
    (left right : Bool) (lc ls rc rs : Fin 2) (r : ℝ) : ℂ :=
  SourceGraph.response (sourceNonlinearLaplace cut f g phi psi p frequency damping positive r)
    left right lc ls rc rs (sourceProfile epsilon precision) (sourceProfile epsilon precision)

def preparedLaplaceFirst (epsilon : ℝ) (precision : 0<epsilon) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping : ℝ) (positive : 0<damping)
    (left right : Bool) (lc ls rc rs : Fin 2) : ℂ :=
  SourceGraph.response (sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive)
    left right lc ls rc rs (sourceProfile epsilon precision) (sourceProfile epsilon precision)

theorem preparedLaplace_derivative (epsilon : ℝ) (precision : 0<epsilon) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping : ℝ) (positive : 0<damping) (left right : Bool) (lc ls rc rs : Fin 2) :
    HasDerivAt (preparedLaplace epsilon precision cut f g phi psi p frequency damping positive left right lc ls rc rs)
      (preparedLaplaceFirst epsilon precision cut f g phi psi p frequency damping positive left right lc ls rc rs) 0 :=
  (original_prepared_nonlinear_laplace (sourceCausalState epsilon precision).point.val p cut f g phi psi frequency damping
    positive left right lc ls rc rs).2

theorem preparedLaplace_remainder (epsilon : ℝ) (precision : 0<epsilon) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) (left right : Bool) (lc ls rc rs : Fin 2) :
    ‖preparedLaplace epsilon precision cut f g phi psi p frequency damping positive left right lc ls rc rs r-
      preparedLaplace epsilon precision cut f g phi psi p frequency damping positive left right lc ls rc rs 0-
      r • preparedLaplaceFirst epsilon precision cut f g phi psi p frequency damping positive left right lc ls rc rs‖ ≤
      legBound^2*((nonlinearRemainderScale cut f g phi psi p damping*laplaceMass damping)*‖r‖^2)*
        ‖sourceProfile epsilon precision‖*‖sourceProfile epsilon precision‖ := by
  have same : preparedLaplace epsilon precision cut f g phi psi p frequency damping positive left right lc ls rc rs r-
      preparedLaplace epsilon precision cut f g phi psi p frequency damping positive left right lc ls rc rs 0-
      r • preparedLaplaceFirst epsilon precision cut f g phi psi p frequency damping positive left right lc ls rc rs=
      SourceGraph.response (sourceNonlinearLaplace cut f g phi psi p frequency damping positive r-
        sourceNonlinearLaplace cut f g phi psi p frequency damping positive 0-
        r • sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive)
        left right lc ls rc rs (sourceProfile epsilon precision) (sourceProfile epsilon precision) := by
    simp only [preparedLaplace,preparedLaplaceFirst,SourceGraph.response,sub_apply,smul_apply,inner_sub_right,inner_smul_right_eq_smul]
  rw [same]
  apply (SourceGraph.response_bound _ left right lc ls rc rs _ _).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sourceNonlinearLaplace_remainder cut f g phi psi p frequency damping r positive small)
      (sq_nonneg _)) (norm_nonneg _)) (norm_nonneg _)

structure NonlinearState (epsilon : ℝ) extends CausalState epsilon where
  laplaceDerivative :
    let u:=zeroLocalizedProfile actualNativeLocalizer point.val
    ∀ (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
      (frequency damping : ℝ) (positive : 0<damping) (left right : Bool) (lc ls rc rs : Fin 2),
      HasDerivAt (fun r : ℝ=>SourceGraph.response (sourceNonlinearLaplace cut f g phi psi p frequency damping positive r)
        left right lc ls rc rs u u)
        (SourceGraph.response (sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive) left right lc ls rc rs u u) 0
  laplaceRemainder :
    let u:=zeroLocalizedProfile actualNativeLocalizer point.val
    ∀ (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
      (frequency damping r : ℝ) (positive : 0<damping) (_small : |r|≤nonlinearRadius g psi p cut damping)
      (left right : Bool) (lc ls rc rs : Fin 2),
      ‖SourceGraph.response (sourceNonlinearLaplace cut f g phi psi p frequency damping positive r) left right lc ls rc rs u u-
        SourceGraph.response (sourceNonlinearLaplace cut f g phi psi p frequency damping positive 0) left right lc ls rc rs u u-
        r • SourceGraph.response (sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive) left right lc ls rc rs u u‖ ≤
        legBound^2*((nonlinearRemainderScale cut f g phi psi p damping*laplaceMass damping)*‖r‖^2)*‖u‖*‖u‖

def sourceNonlinearState (epsilon : ℝ) (precision : 0<epsilon) : NonlinearState epsilon where
  toCausalState:=sourceCausalState epsilon precision
  laplaceDerivative:=preparedLaplace_derivative epsilon precision
  laplaceRemainder:=preparedLaplace_remainder epsilon precision

theorem sourceNonlinearState_same_preparation (epsilon : ℝ) (precision : 0<epsilon) :
    (sourceNonlinearState epsilon precision).toCausalState.toSourcePreparation=sourcePreparation epsilon precision := rfl

end LowEnergy.PreparationVacuumSourcePreparedResponse
