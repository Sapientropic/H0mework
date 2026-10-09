import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.Rotation.Alignment
import H0mework.Physics.LowEnergy.LightModes.Native
import H0mework.Physics.LowEnergy.LightModes.MetricPole

/-! The actual axial roots and metric residues are consumed at the radius of every nonzero spatial momentum. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightSpace
open Stage9C.Material.SpinPair Filter Topology
noncomputable section

def radialMomentum (momentum : Fin 3 → ℝ) : ℝ := Rotation.momentumRadius momentum/spinScale

theorem radial_square (momentum : Fin 3 → ℝ) :
    (radialMomentum momentum)^2=((momentum 0)^2+(momentum 1)^2+(momentum 2)^2)/2 := by
  rw [radialMomentum,div_pow,Rotation.momentumRadius_square,spinScale_sq]

def sourceExponent (branch : LightModes.Branch) (momentum : Fin 3 → ℝ) : ℂ :=
  LightModes.physicalExponent branch (radialMomentum momentum)

theorem radial_positive (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) : 0<radialMomentum momentum :=
  div_pos (Rotation.momentumRadius_positive momentum nonzero) spinScale_pos

theorem radial_small (momentum : Fin 3 → ℝ)
    (small : Rotation.momentumRadius momentum≤ spinScale*LightModes.momentumRadius) :
    |radialMomentum momentum|≤LightModes.momentumRadius := by
  unfold radialMomentum
  have nonnegative : 0≤Rotation.momentumRadius momentum := Real.sqrt_nonneg _
  rw [abs_of_nonneg (div_nonneg nonnegative spinScale_pos.le)]
  apply (div_le_iff₀ spinScale_pos).mpr
  exact small.trans_eq (mul_comm _ _)

theorem source_exponent_nonzero (branch : LightModes.Branch) (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) :
    sourceExponent branch momentum≠0 :=
  LightModes.source_native_nonzero branch _ (radial_positive momentum nonzero).ne'

theorem generated_radial_roots (branch : LightModes.Branch) (momentum : Fin 3 → ℝ)
    (nonzero : momentum≠0) (small : Rotation.momentumRadius momentum≤ spinScale*LightModes.momentumRadius) :
    LightModes.sourceFactor branch ((LightModes.sourceWave branch (radialMomentum momentum))^2)
      ((radialMomentum momentum : ℂ)^2)=0 ∧
    LightModes.sourceFactor branch ((-LightModes.sourceWave branch (radialMomentum momentum))^2)
      ((radialMomentum momentum : ℂ)^2)=0 ∧
    LightModes.sourceWave branch (radialMomentum momentum)≠ -LightModes.sourceWave branch (radialMomentum momentum) :=
  LightModes.source_two_time_roots branch _ (radial_small momentum small) (radial_positive momentum nonzero).ne'

theorem generated_metric_pole (momentum : Fin 3 → ℝ) (nonzero : momentum≠0)
    (small : Rotation.momentumRadius momentum≤ spinScale*LightModes.momentumRadius) :
    Tendsto (fun z : ℂ => (z-LightModes.sourceWave .axialPhase (radialMomentum momentum))*
      (LightModes.metricNumerator z (radialMomentum momentum)/
        LightModes.sourceFactor .axialPhase (z^2) ((radialMomentum momentum : ℂ)^2)))
      (𝓝[≠] (LightModes.sourceWave .axialPhase (radialMomentum momentum)))
      (𝓝 (LightModes.metricNumerator (LightModes.sourceWave .axialPhase (radialMomentum momentum)) (radialMomentum momentum)/
        LightModes.axialTimeDerivative (radialMomentum momentum))) ∧
    LightModes.metricNumerator (LightModes.sourceWave .axialPhase (radialMomentum momentum)) (radialMomentum momentum)/
      LightModes.axialTimeDerivative (radialMomentum momentum)≠0 :=
  LightModes.original_metric_true_pole _ (radial_small momentum small) (radial_positive momentum nonzero).ne'

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightSpace
