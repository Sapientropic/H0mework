import H0mework.Physics.LowEnergy.PacketPairResponse.Fixed
import H0mework.Physics.LowEnergy.PacketPairResponse.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The source light band has a genuine finite feedback integral. Rescaling the
actual causal branches generates its continuous quadratic-time quotient. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open PacketFourier
noncomputable section
attribute [local irreducible] slopeFeedback

def fourierDensity : ℝ := 1/(2*Real.pi)^3

def bandResponse (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) : ℝ :=
  fourierDensity*∫ point : LightBand, fixedFeedback energy damping positive point time ∂bandMeasure

def bandSlopeResponse (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) : ℝ :=
  fourierDensity*∫ point : LightBand, slopeFeedback energy damping positive point time ∂bandMeasure

def bandLeading (energy damping : ℝ) (positive : 0 < damping) : ℝ :=
  fourierDensity*∫ point : LightBand, (bandCoupling true point+bandCoupling false point)*
    oppositeNoise energy damping positive (bandShift point) 0 ∂bandMeasure

theorem slopeFeedback_integrable (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    Integrable (fun point : LightBand => slopeFeedback energy damping positive point time) bandMeasure := by
  have continuous := (slopeFeedback_continuous energy damping positive).comp
    ((continuous_id : Continuous (id : LightBand → LightBand)).prodMk (continuous_const (y := time)))
  simpa only [IntegrableOn,Measure.restrict_univ,Function.comp_def,Function.uncurry,id_eq] using
    continuous.continuousOn.integrableOn_compact (μ := bandMeasure) isCompact_univ

theorem fixedFeedback_integrable (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    Integrable (fun point : LightBand => fixedFeedback energy damping positive point time) bandMeasure := by
  simp_rw [fixedFeedback_slope]
  exact (slopeFeedback_integrable energy damping positive time).const_mul (time^2)

theorem bandSlopeResponse_continuous (energy damping : ℝ) (positive : 0 < damping) :
    Continuous (bandSlopeResponse energy damping positive) := by
  change Continuous (fun time : ℝ => fourierDensity*
    ∫ point : LightBand, slopeFeedback energy damping positive point time ∂bandMeasure)
  have joint : Continuous (fun pair : ℝ×LightBand => slopeFeedback energy damping positive pair.2 pair.1) :=
    (slopeFeedback_continuous energy damping positive).comp continuous_swap
  have generated := continuous_parametric_integral_of_continuous (μ := bandMeasure)
    (f := fun time point => slopeFeedback energy damping positive point time) joint isCompact_univ
  simpa only [Measure.restrict_univ] using generated.const_mul fourierDensity

theorem bandResponse_slope (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    bandResponse energy damping positive time=time^2*bandSlopeResponse energy damping positive time := by
  unfold bandResponse bandSlopeResponse
  simp_rw [fixedFeedback_slope]
  rw [integral_const_mul]
  ring

theorem bandSlopeResponse_initial (energy damping : ℝ) (positive : 0 < damping) :
    bandSlopeResponse energy damping positive 0=bandLeading energy damping positive := by
  unfold bandSlopeResponse bandLeading
  simp_rw [slopeFeedback_initial]

theorem bandLeading_integrable (energy damping : ℝ) (positive : 0 < damping) :
    Integrable (fun point : LightBand => (bandCoupling true point+bandCoupling false point)*
      oppositeNoise energy damping positive (bandShift point) 0) bandMeasure := by
  simpa only [slopeFeedback_initial] using slopeFeedback_integrable energy damping positive 0

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
