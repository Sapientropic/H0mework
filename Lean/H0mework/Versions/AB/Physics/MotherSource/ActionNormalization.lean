import H0mework.Versions.AB.Physics.MotherSource.StaticHamiltonian.Legendre
import H0mework.Versions.AB.Physics.MotherSource.CanonicalMatter.Time

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.ActionNormalization
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open StageNineGlobalIntegratedAction StageNineMatterPointwiseEquation StageNineEnrichedProofFreeSource
open StageNineDiracDualFormNativeMotherAction Stage10.StaticHamiltonian Stage10.CanonicalMatter
open Stage9C.Material.SpinPair
open scoped InnerProductSpace
noncomputable section

def phaseMomentum : ℝ :=
  matterDifferentialMomentum Runtime.source preparedConfiguration
    (matterCoordinateEquiv ((-Complex.I) • preparedConfiguration.matter 0)) 0 0

theorem phaseMomentum_source : phaseMomentum = 4*spinScale := prepared_action_time_momentum 0
theorem phaseMomentum_positive : 0 < phaseMomentum := by rw [phaseMomentum_source]; exact mul_pos (by norm_num) spinScale_pos

def actionScale : ℝ := phaseMomentum⁻¹

theorem actionScale_source : actionScale = (4*spinScale)⁻¹ := by rw [actionScale, phaseMomentum_source]
theorem actionScale_positive : 0 < actionScale := inv_pos.mpr phaseMomentum_positive

theorem source_unit_phase (point : BasePoint) :
    actionScale*matterDifferentialMomentum Runtime.source preparedConfiguration
      (matterCoordinateEquiv ((-Complex.I) • preparedConfiguration.matter point)) 0 point = 1 := by
  rw [prepared_action_time_momentum, actionScale_source, inv_mul_cancel₀ (mul_pos (by norm_num) spinScale_pos).ne']

theorem unique_phase_normalization (scale : ℝ) (unit : scale*phaseMomentum = 1) : scale = actionScale := by
  unfold actionScale
  apply mul_right_cancel₀ phaseMomentum_positive.ne'
  rw [unit, inv_mul_cancel₀ phaseMomentum_positive.ne']

/-- The single source-generated factor scales every component of the complete mother density. -/
def density (point : BasePoint) (field : StageNineContinuumPointField) : ℝ :=
  actionScale*sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Runtime.source 0 point field

def hamiltonian (configuration : StageNineHolonomicConfiguration) (point : BasePoint) : ℝ :=
  deriv (fun rate : ℝ => density point (toContinuumPointField (timeStretch configuration point rate) point)) 0-
    density point (toContinuumPointField configuration point)

theorem source_legendre (configuration : StageNineHolonomicConfiguration) (smooth : configuration.Smooth) (point : BasePoint) :
    HasDerivAt (fun rate : ℝ => density point (toContinuumPointField (timeStretch configuration point rate) point))
      (actionScale*ordinaryTimePairing Runtime.source configuration point) 0 :=
  (source_time_legendre Runtime.source configuration smooth point).const_mul actionScale

theorem source_hamiltonian (configuration : StageNineHolonomicConfiguration) (smooth : configuration.Smooth) (point : BasePoint) :
    hamiltonian configuration point = actionScale*hamiltonianDensity Runtime.source configuration point := by
  rw [hamiltonian, (source_legendre configuration smooth point).deriv]
  unfold density hamiltonianDensity
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.ActionNormalization
