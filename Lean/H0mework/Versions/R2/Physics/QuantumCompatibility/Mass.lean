import H0mework.Versions.R2.Physics.QuantumCompatibility.DualResponse
import H0mework.Versions.R2.Physics.SpinPair.Scalar

/-! The occupied sector is in the source Yukawa kernel. The full mass map,
its source vacuum and its nonzero generation-mixing entries remain present
as independent readouts of the very same accepted actual. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource
open StageNineHolonomicField StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineDiracDualYukawaSpinJurisdiction
open SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum SU7ExteriorMatterRepresentation
open Stage9C.Material.SpinPair

noncomputable section

def actualVacuum (point : BasePoint) : ExteriorBreakingScalarCarrier :=
  scalarCoordinateEquiv.symm (actual.scalar point)

theorem actualVacuum_source (point : BasePoint) :
    actualVacuum point = sourceGeneratedVacuumBase positiveSmoothUnifiedSource := by
  unfold actualVacuum
  rw [actual_scalar]
  exact scalarCoordinateEquiv.symm_apply_apply _

theorem actualVacuum_stageEight (point : BasePoint) :
    actualVacuum point = finiteGenerationJointBreakingScalar := by
  rw [actualVacuum_source, positive_sourceGeneratedVacuumBase]

def fullMass (point : BasePoint) :
    ExteriorDegreeTwoMatterCarrier →ₗ[ℂ] ExteriorDegreeSixMatterCarrier :=
  exteriorYukawaMassMap (actualVacuum point)

theorem fullMass_source (point : BasePoint) :
    fullMass point = exteriorYukawaMassMap (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) := by
  rw [fullMass, actualVacuum_source]

theorem fullMass_nonzero (point : BasePoint) : fullMass point ≠ 0 := by
  rw [fullMass_source]
  exact Stage9C.Material.firstAssemblyCartanActual_sourceYukawaMass_nonzero

def massMatrix (point : BasePoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  finiteGenerationMassMatrixOfScalar (actualVacuum point)

theorem massMatrix_stageEight (point : BasePoint) :
    massMatrix point = finiteGenerationJointMassMatrix := by
  rw [massMatrix, actualVacuum_stageEight]
  rfl

theorem massMatrix_entry_nonzero (point : BasePoint) (output input : Fin 2) :
    massMatrix point output input ≠ 0 := by
  rw [massMatrix_stageEight]
  exact finiteGenerationJointMassMatrix_entry_ne_zero output input

theorem fullMass_su7_covariant (point : BasePoint) (frame : SU7MotherGroup)
    (matter : ExteriorDegreeTwoMatterCarrier) :
    exteriorYukawaMassMap (exteriorBreakingScalarRepresentation frame (actualVacuum point))
      (su7ExteriorPowerRepresentation 2 frame matter) =
      su7ExteriorPowerRepresentation 6 frame (fullMass point matter) :=
  exteriorYukawaMassMap_su7_equivariant _ _ _

def yukawaAction (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  diracDualRightChiralYukawaAction (actualVacuum point)

theorem occupied_yukawa_zero (point : BasePoint) :
    yukawaAction point (actual.matter point) = 0 := by
  have original := actual_yukawaVector_zero point
  unfold StageNineDiracDualYukawaLocalSpinDensity.generatedContinuumDiracDualYukawaVector at original
  change diracDualRightChiralYukawaAction
    (scalarCoordinateEquiv.symm (scalarFrameRelativeCoordinates positiveSmoothUnifiedSource 0 point
      (actual.scalar point)))
    (StageNineGlobalIntegratedAction.matterFrameRelative positiveSmoothUnifiedSource 0 point
      (actual.matter point)) = 0 at original
  simpa only [yukawaAction, actualVacuum,
    StageNineP286GaugeConnectionVariationDensity.scalarFrameRelativeCoordinates_zeroChart,
    StageNineP286GaugeConnectionVariationDensity.matterFrameRelative_zeroChart] using original

theorem occupied_yukawa_quantum_zero (point : BasePoint) :
    vectorRead point (responseMatrix (yukawaAction point)) = 0 := by
  have observed := actual_action_quantumResponse point (yukawaAction point)
  rw [occupied_yukawa_zero, map_zero] at observed
  have nonzero : 4 * (spinScale : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt spinScale_pos)
  exact (mul_eq_zero.mp observed.symm).resolve_left nonzero

theorem complete_mass_readout (point : BasePoint) :
    fullMass point ≠ 0 ∧
    (∀ output input, massMatrix point output input ≠ 0) ∧
    yukawaAction point (actual.matter point) = 0 ∧
    vectorRead point (responseMatrix (yukawaAction point)) = 0 :=
  ⟨fullMass_nonzero point, massMatrix_entry_nonzero point,
    occupied_yukawa_zero point, occupied_yukawa_quantum_zero point⟩

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility
