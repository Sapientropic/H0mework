import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeCurrentTime
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeChargeRead
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeSeed

/-! The original charged source legs consume the complete configuration
current family before differentiation. No N1 projection is inserted. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open GaussCoreHilbert GaussCoreDifferential SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates CanonicalGradedCurrent CanonicalGradedLocalCurrent
open GaussUnitaryHistory (HistorySpace inclusion reader sourceFilter)
open SourceFamilyOperator
open scoped InnerProductSpace Topology
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem grade_zero_history_pair (x y : HistorySpace) :
    inner ℂ (reader gradeZeroProjection x) y=inner ℂ x (reader gradeZeroProjection y) :=
  lift_pair sourceFilter (constant gradeZeroProjection) (constant gradeZeroProjection)
    (fun _ => grade_zero_projection_pair) x y

theorem source_leg_grade_zero_fixed (addition : Bool) (channel spin : Fin 2) (f : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    reader gradeZeroProjection (inclusion (leg addition channel spin f)) =
      inclusion (leg addition channel spin f) := by
  rw [GaussUnitaryHistory.reader_inclusion]
  have hg : GaussYukawaGrade.grade (leg addition channel spin f)=0 := by
    rw [leg_source_grade,original_seed_section_grade f profile sameSource,map_zero]
  rw [grade_zero_fixed _ hg]

def compositeCurrent (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter time : ℝ) (leftAddition rightAddition : Bool)
    (leftChannel leftSpin rightChannel rightSpin : Fin 2) (f g : QuantumTest) : ℂ :=
  inner ℂ (inclusion (leg leftAddition leftChannel leftSpin f))
    (fullCurrent phi psi mu nu a b cut parameter time (inclusion (leg rightAddition rightChannel rightSpin g)))

theorem composite_current_return (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter time : ℝ) (leftAddition rightAddition : Bool)
    (leftChannel leftSpin rightChannel rightSpin : Fin 2) (f g : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    compositeCurrent phi psi mu nu a b cut parameter time leftAddition rightAddition
      leftChannel leftSpin rightChannel rightSpin f g =
    inner ℂ (inclusion (leg leftAddition leftChannel leftSpin f))
      (currentOperator phi psi mu nu a b parameter time (inclusion (leg rightAddition rightChannel rightSpin g))) := by
  unfold compositeCurrent
  rw [full_current_return]
  change inner ℂ (inclusion (leg leftAddition leftChannel leftSpin f))
    (reader gradeZeroProjection (currentOperator phi psi mu nu a b parameter time
      (inclusion (leg rightAddition rightChannel rightSpin g)))) = _
  rw [←grade_zero_history_pair,source_leg_grade_zero_fixed leftAddition leftChannel leftSpin f profile sameSource]

theorem composite_current_derivative (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (time : ℝ) (leftAddition rightAddition : Bool)
    (leftChannel leftSpin rightChannel rightSpin : Fin 2) (f g : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    HasDerivAt (fun parameter : ℝ => compositeCurrent phi psi mu nu a b cut parameter time
      leftAddition rightAddition leftChannel leftSpin rightChannel rightSpin f g)
      (inner ℂ (inclusion (leg leftAddition leftChannel leftSpin f))
        (currentDerivative phi psi mu nu a b time (inclusion (leg rightAddition rightChannel rightSpin g)))) 0 := by
  simp only [composite_current_return phi psi mu nu a b cut _ time leftAddition rightAddition
    leftChannel leftSpin rightChannel rightSpin f g profile sameSource]
  have h := ((ContinuousLinearMap.apply ℂ HistorySpace
    (inclusion (leg rightAddition rightChannel rightSpin g))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (currentOperator_derivative phi psi mu nu a b time)
  convert (hasDerivAt_const (0 : ℝ) (inclusion (leg leftAddition leftChannel leftSpin f))).inner ℂ h using 1
  all_goals first | rfl | (simp only [inner_zero_left,add_zero]; rfl)

theorem composite_current_cutoff_independent (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut first : ℕ) (parameter time : ℝ) (leftAddition rightAddition : Bool)
    (leftChannel leftSpin rightChannel rightSpin : Fin 2) (f g : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    compositeCurrent phi psi mu nu a b cut parameter time leftAddition rightAddition
      leftChannel leftSpin rightChannel rightSpin f g =
    compositeCurrent phi psi mu nu a b first parameter time leftAddition rightAddition
      leftChannel leftSpin rightChannel rightSpin f g := by
  rw [composite_current_return _ _ _ _ _ _ cut _ _ _ _ _ _ _ _ _ _ profile sameSource,
    composite_current_return _ _ _ _ _ _ first _ _ _ _ _ _ _ _ _ _ profile sameSource]

end LowEnergy.GaussComposite
