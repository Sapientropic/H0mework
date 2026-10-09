import H0mework.Physics.LowEnergy.PacketField.Contraction
import H0mework.Physics.LowEnergy.PacketField.ReflectionIntegral

/-! The complete spatial integral of one physical field equals the certified
two-order average. Both orientations already occur in the full momentum ball. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace PacketPairResponse VertexTensor
noncomputable section
attribute [local irreducible] phaseBranch

def forwardFeedback (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (point : LightBand) : ℝ :=
  orientedFeedback (bandCoupling true point) (bandCoupling false point) energy damping positive (bandShift point) time

theorem bandCoupling_reflection (same : Bool) (point : LightBand) :
    bandCoupling same (reflectPoint point)=bandCoupling same point := by
  have momentum : bandMomentum (reflectPoint point)= -bandMomentum point := by funext j; rfl
  unfold bandCoupling
  rw [momentum]
  simp only [fixedMomentumCoupling,radial_opposite,Pi.neg_apply,neg_sq]

theorem bandShift_reflection (point : LightBand) : bandShift (reflectPoint point)= -(bandShift point) := by
  change (2*Real.pi)⁻¹ • (-point.val)= -((2*Real.pi)⁻¹ • point.val)
  exact smul_neg _ _

theorem forwardFeedback_continuous (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    Continuous (forwardFeedback energy damping positive time) := by
  have plus := branchOnBand_continuous energy damping positive true time
  have minus := branchOnBand_continuous energy damping positive false time
  have same := bandCoupling_continuous true
  have opposite := bandCoupling_continuous false
  change Continuous (fun point : LightBand => fourGram (bandCoupling true point) (bandCoupling false point)
    (fun sign => branchOnBand energy damping positive sign time point))
  simp_rw [fourGram_coordinates]
  exact continuous_const.mul
    ((((same.sub opposite).div_const 2).mul ((plus.sub minus).norm.pow 2)).add
      (((same.add opposite).div_const 2).mul ((plus.add minus).norm.pow 2)))

theorem forwardFeedback_integrable (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    Integrable (forwardFeedback energy damping positive time) bandMeasure := by
  simpa only [IntegrableOn,Measure.restrict_univ] using!
    (forwardFeedback_continuous energy damping positive time).continuousOn.integrableOn_compact
      (μ := bandMeasure) isCompact_univ

theorem fixedFeedback_average (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (point : LightBand) :
    fixedFeedback energy damping positive point time=
      (forwardFeedback energy damping positive time point+forwardFeedback energy damping positive time (reflectPoint point))/2 := by
  unfold fixedFeedback oppositeFeedback forwardFeedback
  rw [bandCoupling_reflection,bandCoupling_reflection,bandShift_reflection]

theorem forwardFeedback_integral (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    fourierDensity*(∫ point : LightBand, forwardFeedback energy damping positive time point ∂bandMeasure)=
      bandResponse energy damping positive time := by
  have reverse : Integrable (fun point => forwardFeedback energy damping positive time (reflectPoint point)) bandMeasure := by
    simpa only [IntegrableOn,Measure.restrict_univ] using!
      ((forwardFeedback_continuous energy damping positive time).comp reflectPoint_continuous).continuousOn.integrableOn_compact
        (μ := bandMeasure) isCompact_univ
  rw [bandResponse]
  simp_rw [fixedFeedback_average]
  rw [integral_div,integral_add (forwardFeedback_integrable energy damping positive time) reverse,band_reflection]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
