import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.BosonCausal.State
import H0mework.Versions.R3bbcbd59.Physics.LowEnergySpectrum.Spectrum
import H0mework.Physics.LowEnergy.BosonCausal.Convolution

/-! The source coframe/metric read of the generated five-state trajectory.
All constants refer to the original lapse and spin scale. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
open Stage9C.Material.SpinPair
noncomputable section

theorem source_lapse_closed : lapse=3*Real.sqrt 30/25 := by
  have root := Real.sq_sqrt (show (0 : ℝ)≤30 by norm_num)
  have positive := Real.sqrt_nonneg (30 : ℝ)
  nlinarith [lapse_sq,lapse_pos]

theorem source_oscillation_rate : oscillation=Spectrum.geometryFrequency := by
  apply (sq_eq_sq₀ oscillation_positive.le Spectrum.geometryFrequency_positive.le).mp
  rw [oscillation_squared,Spectrum.geometryFrequency_squared]

theorem source_growth_rate : growth=Spectrum.gaugeGrowthRate := by
  apply (sq_eq_sq₀ growth_positive.le Spectrum.gaugeGrowthRate_positive.le).mp
  rw [growth_squared,Spectrum.gaugeGrowthRate_squared]

theorem source_physical_time_factor : lapse*spinScale=2*frequency*(5/6 : ℝ) := by
  unfold frequency gaugeScale
  ring

def metricFromState (source : ℝ → ℂ) (t : ℝ) : ℂ :=
  -2*(lapse : ℂ)*((6/25)*source t+(lapse : ℂ)*geometricPosition source t+
    (lapse : ℂ)*(10*(spinScale : ℂ)/3)*gaugePosition source t)

theorem metricFromState_response (source : ℝ → ℂ) (t : ℝ) :
    metricFromState source t=responseTo source t := by
  have nonzero : (lapse : ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  have nsq : (lapse : ℂ)^2=(54/125 : ℂ) := by rw [← Complex.ofReal_pow,lapse_sq]; norm_num
  have ssq : (spinScale : ℂ)^2=2 := by rw [← Complex.ofReal_pow,spinScale_sq]; norm_num
  have c : contact= -12*(lapse : ℂ)/25 := by rw [source_lapse_closed]; unfold contact; push_cast; ring
  have a : oscillationWeight= -1944*(lapse : ℂ)/15625 := by rw [source_lapse_closed]; unfold oscillationWeight; push_cast; ring
  have b : growthWeight= -64*(lapse : ℂ)/5 := by rw [source_lapse_closed]; unfold growthWeight; push_cast; ring
  rw [responseTo,c,a,b]
  unfold metricFromState geometricPosition gaugePosition
  field_simp [nonzero]
  ring_nf
  simp only [nsq,ssq]
  ring

theorem metricFromState_causal (source : ℝ → ℂ) (regular : Continuous source) (t : ℝ) :
    metricFromState source t=contact*source t+
      ∫ s : ℝ in (0 : ℝ)..t, memory (t-s)*source s := by
  rw [metricFromState_response,responseTo_convolution _ regular]

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
