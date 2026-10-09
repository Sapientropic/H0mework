import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.GammaIntegrals
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.MotionBudget
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Account

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open BasinRefinement SourceGaussianModel
noncomputable section

def positionMeter (phase : Phase) (second : ℝ) (i : Coordinate) : ℝ :=
  SIWork.lengthMeter*position phase (second/SIWork.timeSecond) i
def velocityMeterPerSecond (phase : Phase) (second : ℝ) (i : Coordinate) : ℝ :=
  SIWork.lengthMeter/SIWork.timeSecond*velocity phase (second/SIWork.timeSecond) i

theorem position_equation_si (phase : Phase) (second : ℝ) (i : Coordinate) :
    HasDerivAt (fun s => positionMeter phase s i) (velocityMeterPerSecond phase second i) second := by
  have generated := ((position_equation phase (second/SIWork.timeSecond) i).comp second
    ((hasDerivAt_id second).div_const SIWork.timeSecond)).const_mul SIWork.lengthMeter
  unfold positionMeter velocityMeterPerSecond
  convert generated using 1 <;> first | rfl | ring

theorem position_integral_si (phase : Phase) (i : Coordinate) :
    positionMeter phase SIWork.segmentSeconds i-positionMeter phase 0 i=
      ∫ second in (0 : ℝ)..SIWork.segmentSeconds, velocityMeterPerSecond phase second i := by
  have regular : Continuous (fun s => velocityMeterPerSecond phase s i) :=
    continuous_const.mul ((velocity_differentiable phase i).continuous.comp (continuous_id.div_const _))
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => position_equation_si phase t i) (regular.intervalIntegrable 0 SIWork.segmentSeconds)).symm

theorem actual_displacement_meter (i : Coordinate) :
    positionMeter .leave SIWork.segmentSeconds i-positionMeter .enter 0 i=SIWork.lengthMeter*displacement i := by
  simp only [positionMeter,SIWork.segmentSeconds,mul_div_cancel_right₀ _ SIWork.time_positive.ne',
    zero_div,target_position,source_position,generated_position,displacement,Rat.cast_add,Rat.cast_mul]
  ring

theorem actual_meter_nonreturning :
    0 < positionMeter .leave SIWork.segmentSeconds (0,0)-positionMeter .enter 0 (0,0) := by
  rw [actual_displacement_meter]
  apply mul_pos SIWork.length_positive
  simpa [displacement,axisQ] using (Rat.cast_pos.mpr displacement_positive : (0 : ℝ)<(displacementQ : ℝ))

theorem motion_budget_joule (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ duration) :
    SIWork.energyJoule*nuclearKinetic (fun i => mass i*shiftRate .drive t i)<
      SIWork.energyJoule*(input.reserve : ℝ)/2 := by
  have paid := mul_lt_mul_of_pos_left (translation_kinetic_paid t lo hi) SIWork.energy_positive
  linarith only [paid]

def spatialGammaSI (phase : Phase) (second : ℝ) (x y : Point) : ℂ :=
  movingGamma phase (second/SIWork.timeSecond) x y

theorem spatial_gamma_equation_si (phase : Phase) (second : ℝ) (x y : Point) :
    HasDerivAt (fun s => spatialGammaSI phase s x y)
      ((1/SIWork.timeSecond : ℝ) • spatialGammaRate phase (second/SIWork.timeSecond) x y) second := by
  have raw := (spatial_gamma_equation phase (second/SIWork.timeSecond) x y).scomp second
    ((hasDerivAt_id second).div_const SIWork.timeSecond)
  simpa only [spatialGammaSI,Function.comp_def,id_eq] using! raw

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
