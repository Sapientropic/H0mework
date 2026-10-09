import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberFieldLeft

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedLeftFreeJet
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumGradedTransport
open ActualDressedNumberField ActualDressedNumberZero
open Filter
open scoped Topology InnerProductSpace
abbrev FreeOp := H→L[ℂ]H
local instance freeRealAlgebra : NormedAlgebra ℝ FreeOp := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointCompression jointCResolvent physicalTime gradeZeroProjection

/-- Direction of the actual compression field family, with all 289 force entries retained. -/
def freeCompressionCurrent (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) : FreeOp := fderiv ℝ (jointCompression p F) 0 force

theorem free_compression_base (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    jointCompression p F 0=CanonicalPhysicalSpatial.compression p F := by
  have source:=(jointCompression_ray (0:Field289) p F).self_of_nhds
  simp only [zero_smul] at source
  exact source.trans (transportedCompression_zero 0 p F)

theorem free_compression_direction (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) :
    HasDerivAt (fun r : ℝ=>jointCompression p F (r • force)) (freeCompressionCurrent p F force) 0 := by
  have source:=(jointCompression_C2 p F).differentiableAt (by norm_num) |>.hasFDerivAt
  exact source.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp only [zero_smul])

def freeTimeSlope (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (t : ℝ) : FreeOp :=
  CanonicalGradedVariation.variation (CanonicalPhysicalSpatial.compression p F)
    (freeCompressionCurrent p F force) t

attribute [local irreducible] freeCompressionCurrent freeTimeSlope

/-- Differentiate the actual nonlinear compression family, rather than an equality only at zero. -/
theorem free_time_direction (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>SourceFiniteUnitary.time (jointCompression p F (r • force)) t)
      (freeTimeSlope p F force t) 0 := by
  have source:=PreparationVacuumActionDecomposition.nonlinear_time_derivative
    (jointCompression p F 0) (freeCompressionCurrent p F force)
    (fun r : ℝ=>jointCompression p F (r • force)-jointCompression p F 0)
    (by simp only [zero_smul,sub_self]) ((free_compression_direction p F force).sub_const _) t
  simpa only [add_sub_cancel,free_compression_base,freeTimeSlope] using source

theorem free_time_slope_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (t : ℝ) :
    ‖freeTimeSlope p F force t‖≤|t| * ‖freeCompressionCurrent p F force‖ := by
  unfold freeTimeSlope
  exact CanonicalGradedVariation.variation_bound _ _ (CanonicalPhysicalSpatial.compression_selfAdjoint p F) t

theorem free_green_base (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointCResolvent p F z 0=CanonicalPhysicalResolvent.finiteResolvent p F z := by
  unfold jointCResolvent CanonicalPhysicalResolvent.finiteResolvent FullYSourceResolventGraphSplice.resolvent
  rw [free_compression_base]

theorem free_green_direction (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (force : Field289) :
    HasDerivAt (fun r : ℝ=>jointCResolvent p F z (r • force))
      (-(jointCResolvent p F z 0*freeCompressionCurrent p F force*jointCResolvent p F z 0)) 0 := by
  have source:=(free_compression_direction p F force).sub_const (z • (1:FreeOp))
  have unit:=(actual_joint_free_units_near_zero p F z nonreal).self_of_nhds
  have inverse:=inverse_curve_derivative (fun r : ℝ=>jointCompression p F (r • force)-z • (1:FreeOp))
    0 (freeCompressionCurrent p F force) source (by simpa only [zero_smul] using unit)
  simpa only [zero_smul,jointCResolvent] using inverse

private theorem insertion_price {A : Type*} [NormedRing A] (U B : A) :
    ‖-(U*B*U)‖≤‖U‖^2*‖B‖ := by
  rw [norm_neg]
  calc
    _≤(‖U‖*‖B‖)*‖U‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _=‖U‖^2*‖B‖ := by ring

theorem free_green_slope_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (force : Field289) :
    ‖-(jointCResolvent p F z 0*freeCompressionCurrent p F force*jointCResolvent p F z 0)‖≤
      ‖jointCResolvent p F z 0‖^2*‖freeCompressionCurrent p F force‖ :=
  insertion_price _ _

theorem free_green_source_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (force : Field289) :
    ‖-(jointCResolvent p F z 0*freeCompressionCurrent p F force*jointCResolvent p F z 0)‖≤
      (1/|z.im|)^2*‖freeCompressionCurrent p F force‖ := by
  have source : ‖jointCResolvent p F z 0‖≤1/|z.im| := by
    rw [free_green_base]
    exact CanonicalPhysicalResolvent.finite_bound p F z nonreal
  exact (free_green_slope_price p F z force).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) source 2) (norm_nonneg _))

/-- The actual grade-zero left time family consumes the generated free jet. -/
theorem actual_left_time_direction (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>gradeZeroProjection*physicalTime p F t (r • force))
      (gradeZeroProjection*freeTimeSlope p F force t) 0 := by
  have free:=(free_time_direction p F force t).const_mul gradeZeroProjection
  exact free.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun r=>actual_joint_time_grade_zero_left p F t (r • force)))

/-- The near-zero actual resolvent identity transports the same generated free jet. -/
theorem actual_left_green_direction (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (force : Field289) :
    HasDerivAt (fun r : ℝ=>gradeZeroProjection*jointResolvent p F z (r • force))
      (gradeZeroProjection*(-(jointCResolvent p F z 0*freeCompressionCurrent p F force*jointCResolvent p F z 0))) 0 := by
  have free:=(free_green_direction p F z nonreal force).const_mul gradeZeroProjection
  have ray : Tendsto (fun r : ℝ=>r • force) (𝓝 0) (𝓝 (0:Field289)) := by
    have continuous : Continuous (fun r : ℝ=>r • force) := continuous_id.smul continuous_const
    simpa only [zero_smul] using continuous.tendsto (0:ℝ)
  exact free.congr_of_eventuallyEq (ray.eventually (actual_joint_resolvent_grade_zero_left p F z nonreal))

end LowEnergy.GaussComposite.ActualDressedLeftFreeJet
