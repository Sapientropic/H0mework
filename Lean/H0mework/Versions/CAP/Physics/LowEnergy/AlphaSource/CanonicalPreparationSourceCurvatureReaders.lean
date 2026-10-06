import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNonlinearState
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldFormConsumer

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourcePreparedResponse
open PreparationVacuumSourcePreparedState PreparationVacuumCausalFieldResponse PreparationVacuumNonlinearLaplace
open PreparationVacuumFieldPerturbation PreparationVacuumDampedFieldPerturbation PreparationVacuumFieldConstraintResponse
open GaussCoreHilbert GaussComposite GaussComposite.SourceGraph
open CanonicalPhysicalSpatial CanonicalGradedSpatialSource PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open FullYSourceCutoffVolterra SourceFamilyOperator SourceFiniteUnitary GaussUnitaryHistory
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation
open PreparationChartGuard PreparationScalarCoordinates
open scoped Topology InnerProductSpace

variable (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4 → ℂ) (row : Fin 36)
  (cut : ℕ) (receiver : Field289) (phi psi : Localizer) (p : PhysicalMomentum)
  (frequency damping : ℝ) (positive : 0<damping) (left right : Bool) (lc ls rc rs : Fin 2)

-- Original 36-row real/imaginary restrictions, read on one generated state.
-- Subtracting the imaginary branch's base value is the original curvature
-- curve convention and leaves its first derivative unchanged.
def curvatureLaplaceCurve (r : ℝ) : ℂ :=
  preparedLaplace epsilon precision cut receiver (readerReal sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs r+
    Complex.I*(preparedLaplace epsilon precision cut receiver (readerImag sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs r-
      preparedLaplace epsilon precision cut receiver (readerImag sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs 0)

def curvatureLaplaceFirst : ℂ :=
  preparedLaplaceFirst epsilon precision cut receiver (readerReal sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs+
    Complex.I*preparedLaplaceFirst epsilon precision cut receiver (readerImag sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs

theorem curvatureLaplace_derivative :
    HasDerivAt (curvatureLaplaceCurve epsilon precision sourceMomentum row cut receiver phi psi p frequency damping positive left right lc ls rc rs)
      (curvatureLaplaceFirst epsilon precision sourceMomentum row cut receiver phi psi p frequency damping positive left right lc ls rc rs) 0 := by
  have realPart:=preparedLaplace_derivative epsilon precision cut receiver (readerReal sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs
  have imagPart:=preparedLaplace_derivative epsilon precision cut receiver (readerImag sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs
  exact realPart.add ((imagPart.sub_const _).const_mul Complex.I)

theorem curvatureLaplace_remainder (r : ℝ)
    (realSmall : |r|≤nonlinearRadius (readerReal sourceMomentum row) psi p cut damping)
    (imagSmall : |r|≤nonlinearRadius (readerImag sourceMomentum row) psi p cut damping) :
    ‖curvatureLaplaceCurve epsilon precision sourceMomentum row cut receiver phi psi p frequency damping positive left right lc ls rc rs r-
      curvatureLaplaceCurve epsilon precision sourceMomentum row cut receiver phi psi p frequency damping positive left right lc ls rc rs 0-
      r • curvatureLaplaceFirst epsilon precision sourceMomentum row cut receiver phi psi p frequency damping positive left right lc ls rc rs‖ ≤
      legBound^2*((nonlinearRemainderScale cut receiver (readerReal sourceMomentum row) phi psi p damping+
        nonlinearRemainderScale cut receiver (readerImag sourceMomentum row) phi psi p damping)*laplaceMass damping*‖r‖^2)*
          ‖sourceProfile epsilon precision‖*‖sourceProfile epsilon precision‖ := by
  let A:=preparedLaplace epsilon precision cut receiver (readerReal sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs
  let B:=preparedLaplace epsilon precision cut receiver (readerImag sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs
  let DA:=preparedLaplaceFirst epsilon precision cut receiver (readerReal sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs
  let DB:=preparedLaplaceFirst epsilon precision cut receiver (readerImag sourceMomentum row) phi psi p frequency damping positive left right lc ls rc rs
  have split : curvatureLaplaceCurve epsilon precision sourceMomentum row cut receiver phi psi p frequency damping positive left right lc ls rc rs r-
      curvatureLaplaceCurve epsilon precision sourceMomentum row cut receiver phi psi p frequency damping positive left right lc ls rc rs 0-
      r • curvatureLaplaceFirst epsilon precision sourceMomentum row cut receiver phi psi p frequency damping positive left right lc ls rc rs=
      (A r-A 0-r • DA)+Complex.I*(B r-B 0-r • DB) := by
    change (A r+Complex.I*(B r-B 0))-(A 0+Complex.I*(B 0-B 0))-r • (DA+Complex.I*DB)=_
    simp only [Complex.real_smul]
    ring
  rw [split]
  apply (norm_add_le _ _).trans
  rw [norm_mul,Complex.norm_I,one_mul]
  exact (add_le_add
    (preparedLaplace_remainder epsilon precision cut receiver (readerReal sourceMomentum row) phi psi p frequency damping r positive realSmall left right lc ls rc rs)
    (preparedLaplace_remainder epsilon precision cut receiver (readerImag sourceMomentum row) phi psi p frequency damping r positive imagSmall left right lc ls rc rs)).trans_eq (by ring)

-- The same profile also consumes the literal source curvature form, including
-- its primal/gauge/coframe/constraint slots, before any pole operation.
theorem source_curvature_form_first (F : Index) :
    HasDerivAt (curvatureReducedPreparedCurve sourceMomentum row p F left right lc ls rc rs
      (sourceProfile epsilon precision) (sourceProfile epsilon precision))
      (((fieldJets (readerReal sourceMomentum row) p
        (sourceTestApprox F (completedLeg left lc ls (sourceProfile epsilon precision)))
        (sourceTestApprox F (completedLeg right rc rs (sourceProfile epsilon precision)))).first 0)+
        Complex.I*((fieldJets (readerImag sourceMomentum row) p
        (sourceTestApprox F (completedLeg left lc ls (sourceProfile epsilon precision)))
        (sourceTestApprox F (completedLeg right rc rs (sourceProfile epsilon precision)))).first 0)) 0 :=
  original_curvature_reduced_prepared_first sourceMomentum row p F left right lc ls rc rs
    (sourceProfile epsilon precision) (sourceProfile epsilon precision)

theorem curvature_profile_same_state :
    sourceProfile epsilon precision=zeroLocalizedProfile actualNativeLocalizer (sourceNonlinearState epsilon precision).point.val := rfl

end LowEnergy.PreparationVacuumSourcePreparedResponse
