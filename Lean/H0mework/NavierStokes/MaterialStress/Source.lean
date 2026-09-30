import H0mework.NavierStokes.MaterialStress.Functional
import H0mework.NavierStokes.MaterialAction.SourceAdjoint

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeSourceCoframeStress

open PhysicsCore DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction StageNineCoframeSectorStress
open StageNineDiracDualYukawaSpinJurisdiction SU7ExteriorBreakingYukawa
open MeasureTheory Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open NativeCoframeInverseAction NativeMatterCoframeStress NativeMaterialMomentumJet
open NativePauliCoframeAction NativeMaterialJetAction NativeSourceMaterialJet
open NativePhysicalFourier NativePhysicalSource

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def current (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) : LorentzianCoframe :=
  kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity) (covariantDerivative velocity derivative)

theorem original_sector_yukawa_zero (velocity : PhysicalSpace) :
    chiralExteriorYukawaAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
      (NativeCanonicalFluidCoframe.matter velocity) = 0 := by
  change diracMatrixMatterAction leftChiralityProjector (diracMatrixMatterAction (diracGamma 0)
    (diracDualRightChiralYukawaAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
      (NativeCanonicalFluidCoframe.matter velocity))) = 0
  rw [NativeSourceMaterialAdjoint.source_yukawa_zero, map_zero, map_zero]

def responseCovector (velocity : PhysicalSpace) (coefficients : LorentzianCoframe) : LorentzianCoframe →L[ℝ] ℝ :=
  volumeFactor velocity • (pairing coefficients).comp
    (inverseDerivative (NativeCanonicalFluidCoframe.coframe velocity))

def stress (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) : LorentzianCoframe →L[ℝ] ℝ :=
  responseCovector velocity (current velocity derivative)

theorem responseCovector_single (velocity : PhysicalSpace) (coefficients : LorentzianCoframe) (internal coordinate : Fin 4) :
    responseCovector velocity coefficients (Matrix.single internal coordinate 1) =
      -(volumeFactor velocity /
        (NativeCanonicalFluidCoframe.diagonal velocity internal * NativeCanonicalFluidCoframe.diagonal velocity coordinate)) *
          coefficients internal coordinate := by
  have sparse : (NativeCanonicalFluidCoframe.coframe velocity)⁻¹ * Matrix.single internal coordinate 1 *
      (NativeCanonicalFluidCoframe.coframe velocity)⁻¹ =
      Matrix.single internal coordinate ((NativeCanonicalFluidCoframe.diagonal velocity internal)⁻¹ *
        (NativeCanonicalFluidCoframe.diagonal velocity coordinate)⁻¹) := by
    rw [NativeCanonicalFluidCoframe.coframe_inv]
    ext row column
    by_cases sameRow : row = internal <;> by_cases sameColumn : column = coordinate <;>
      simp_all [Matrix.mul_diagonal, Matrix.single_apply]
    all_goals aesop
  simp only [responseCovector, smul_apply, ContinuousLinearMap.comp_apply, inverseDerivative_apply,
    sparse, map_neg, pairing_apply]
  simp [Matrix.single_apply, mul_ite, ite_and]
  ring

theorem stress_single (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (internal coordinate : Fin 4) :
    stress velocity derivative (Matrix.single internal coordinate 1) =
      -(volumeFactor velocity /
        (NativeCanonicalFluidCoframe.diagonal velocity internal * NativeCanonicalFluidCoframe.diagonal velocity coordinate)) *
          current velocity derivative internal coordinate :=
  responseCovector_single velocity (current velocity derivative) internal coordinate

/-- All nine spatial entries of the true coframe-variation response are generated from the same covariant jet. -/
theorem responseCovector_spatial (velocity : PhysicalSpace) (coefficients : LorentzianCoframe) (internal coordinate : Fin 3) :
    responseCovector velocity coefficients (Matrix.single internal.succ coordinate.succ 1) =
      -NativeCanonicalFluidCoframe.scale velocity * coefficients internal.succ coordinate.succ := by
  rw [responseCovector_single]
  have diagonal (direction : Fin 3) : NativeCanonicalFluidCoframe.diagonal velocity direction.succ =
      (NativeCanonicalFluidCoframe.scale velocity)⁻¹ := by
    fin_cases direction <;> rfl
  rw [diagonal, diagonal]
  simp only [volumeFactor, NativeCanonicalFluidCoframe.coframe_volume]
  field_simp [(NativeCanonicalFluidCoframe.scale_pos velocity).ne']

theorem spatial_stress (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (internal coordinate : Fin 3) :
    stress velocity derivative (Matrix.single internal.succ coordinate.succ 1) =
      -NativeCanonicalFluidCoframe.scale velocity * current velocity derivative internal.succ coordinate.succ :=
  responseCovector_spatial velocity (current velocity derivative) internal coordinate

theorem responseCovector_add (velocity : PhysicalSpace) (first second : LorentzianCoframe) :
    responseCovector velocity (first + second) = responseCovector velocity first + responseCovector velocity second := by
  ext direction
  simp only [responseCovector, smul_apply, ContinuousLinearMap.comp_apply, add_apply,
    pairing_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, smul_eq_mul]

/-- The source equation supplies the zero inner density; the stress is the actual Fréchet derivative. -/
theorem receipt_stress_hasFDerivAt {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus,
      HasFDerivAt (density (current (receiptField receipt time point) (receiptJet receipt time point)) 0)
        (stress (receiptField receipt time point) (receiptJet receipt time point))
        (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point)) := by
  filter_upwards [receipt_kineticVector_zero receipt time] with point source
  apply density_hasFDerivAt_of_inner_zero _ _ _ (NativeCanonicalFluidCoframe.coframe_nondegenerate _)
  rw [add_zero, current, pairing_eq_kinetic]
  change (NativeCanonicalFluidCoframe.dual _ (gaugeVectorAt _ _)).re = 0
  rw [source, map_zero, Complex.zero_re]

/-- Every complete point-field extension of the generated matter data has this same original-sector stress. -/
theorem receipt_stress_eq_mother_restriction {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T)
    (source : SmoothUnifiedSource) (motherPoint : ProofFreeRicherAnholonomicSource.BasePoint) :
    ∀ᵐ point : Torus, ∀ field : StageNineContinuumPointField,
      field.coframe = NativeCanonicalFluidCoframe.coframe (receiptField receipt time point) →
      field.conjugateMatter = NativeCanonicalFluidCoframe.dual (receiptField receipt time point) →
      field.matterCovariantDerivative = covariantDerivative (receiptField receipt time point) (receiptJet receipt time point) →
      field.scalar = sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource →
      field.matter = NativeCanonicalFluidCoframe.matter (receiptField receipt time point) →
      coframeMatterSectorStressCovector source motherPoint field =
        stress (receiptField receipt time point) (receiptJet receipt time point) := by
  filter_upwards [receipt_stress_hasFDerivAt receipt time] with point derivative field frame dual jet scalar matter
  have functions : density (current (receiptField receipt time point) (receiptJet receipt time point)) 0 =
      coframeMatterSectorLocalDensity source motherPoint field := by
    funext candidate
    rw [← density_eq_mother]
    simp only [currentCoefficients, dual, jet, massCoefficient, scalar, matter,
      sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply,
      original_sector_yukawa_zero, map_zero, Complex.zero_re]
    rfl
  rw [coframeMatterSectorStressCovector, frame, ← functions]
  exact derivative.fderiv

end
end SaturationMonoid.NavierStokes.NativeSourceCoframeStress
