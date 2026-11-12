import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticCurrentCircuit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedStaticFeedback
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalStaticSpatialCouplingReturn PreparationVacuumStaticPoleResponse
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedCorrectedElectronRead
open ActualDressedOrderedStatic ActualDressedZeroDamping ActualDressedEMTensorClock
open ActualCompositeFieldCurrent Filter Set
open scoped Matrix BigOperators Topology

/-- This is the paid zero-clock read of the complete feedback-plus-nine circuit, not a separately chosen matching constant. -/
def zeroFeedbackNullRead (event : DressedEvent) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (kappa : staticDomain) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : ℂ :=
  zeroClockProbeRead event (Real.sqrt kappa.val) n pd ps dL dR sL sR-
    nativeCurrentRead n unit kappa pd ps dL dR sL sR

def sourceFeedbackNullCoefficient (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  sourceOrderedProbeCoefficient event n pd ps dL dR sL sR-nativeCurrentCoefficient pd ps dL dR sL sR

private theorem static_ir_tendsto :
    Tendsto (fun kappa : staticDomain => Real.sqrt kappa.val) staticApproach (nhdsWithin 0 ({0}ᶜ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · simpa only [Real.sqrt_zero,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp staticVal_tendsto
  · filter_upwards with kappa
    simpa only [mem_compl_iff,mem_singleton_iff] using (Real.sqrt_pos.mpr kappa.property.1).ne'

/-- The original ordered source chart supplies every actual inverse and the limit of the complete feedback/null sum. -/
theorem actual_feedback_null_damping_return (event : DressedEvent) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (nonzero : irClockDeterminant event n≠0)
    (factor : Polynomial.X^sourceClockOrder event n∣irClockProbeNumerator event n pd ps dL dR sL sR) :
    ∀ᶠ kappa : staticDomain in staticApproach,
      Tendsto (fun sigma : ℝ => feedbackCurrentRead event n unit kappa sigma pd ps dL dR sL sR+
          nullCurrentRead event n kappa sigma pd ps dL dR sL sR)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroFeedbackNullRead event n unit kappa pd ps dL dR sL sR)) := by
  filter_upwards [static_ir_tendsto.eventually (source_ordered_original_chart event n nonzero)] with kappa chart
  have full:=actual_zero_clock_probe event (Real.sqrt kappa.val) n pd ps dL dR sL sR chart.1 factor
  have combined:=full.sub (tendsto_const_nhds (x:=nativeCurrentRead n unit kappa pd ps dL dR sL sR))
  apply Tendsto.congr' _ combined
  filter_upwards [chart.2.2] with sigma regular
  have circuit:=actual_static_current_circuit event n unit kappa sigma regular.1 regular.2 pd ps dL dR sL sR
  linear_combination circuit

/-- The whole native coefficient and the generated feedback/nine coefficient retain all same-order long-range terms. -/
theorem actual_feedback_null_spatial_return (event : DressedEvent) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (nonzero : irClockDeterminant event n≠0) (clock : ClockFinite event n pd ps dL dR sL sR)
    (emBounded : ∀mu nu,LowEnergy.ActualDressedVisiblePole.poleOrder (zeroClockEMFraction event n mu nu) 0≤4)
    (probeBounded : LowEnergy.ActualDressedVisiblePole.poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0≤4) :
    Tendsto (fun kappa : staticDomain => -(kappa.val : ℂ)^2*zeroFeedbackNullRead event n unit kappa pd ps dL dR sL sR)
      staticApproach (𝓝 (sourceFeedbackNullCoefficient event n pd ps dL dR sL sR)) := by
  have full:=(actual_ordered_coulomb_return event n pd ps dL dR sL sR nonzero clock emBounded probeBounded).2.2
  have restricted:=full.comp (tendsto_comap : Tendsto (Subtype.val : staticDomain→ℝ) staticApproach (nhdsWithin 0 (Ioi 0)))
  have combined:=restricted.sub (actual_native_current_spatial_return n unit pd ps dL dR sL sR)
  simpa only [staticApproach,Function.comp_def,zeroFeedbackNullRead,sourceFeedbackNullCoefficient,mul_sub] using combined

def sourceFeedbackNullPrice (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℝ :=
  1+‖sourceFeedbackNullCoefficient event n pd ps dL dR sL sR‖

theorem actual_feedback_null_source_price (event : DressedEvent) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (nonzero : irClockDeterminant event n≠0) (clock : ClockFinite event n pd ps dL dR sL sR)
    (emBounded : ∀mu nu,LowEnergy.ActualDressedVisiblePole.poleOrder (zeroClockEMFraction event n mu nu) 0≤4)
    (probeBounded : LowEnergy.ActualDressedVisiblePole.poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0≤4) :
    ∀ᶠ kappa : staticDomain in staticApproach,
      ‖-(kappa.val : ℂ)^2*zeroFeedbackNullRead event n unit kappa pd ps dL dR sL sR‖≤
        sourceFeedbackNullPrice event n pd ps dL dR sL sR := by
  have paid:=actual_feedback_null_spatial_return event n unit pd ps dL dR sL sR nonzero clock emBounded probeBounded
  have price:=paid.norm.eventually_lt_const (show
    ‖sourceFeedbackNullCoefficient event n pd ps dL dR sL sR‖<sourceFeedbackNullPrice event n pd ps dL dR sL sR from by
      unfold sourceFeedbackNullPrice; linarith)
  filter_upwards [price] with kappa bound
  exact bound.le

/-- A finite source branch supplies this actual two-step return; singular and pole branches retain their original source data. -/
structure SourceLongrangeReturn (event : DressedEvent) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) where
  branch : OrderedStaticReturn event n pd ps dL dR sL sR
  actualReturn : match branch with
    | .finite _ _ _ _ _ _ =>
      (∀ᶠ kappa : staticDomain in staticApproach,
        Tendsto (fun sigma : ℝ => feedbackCurrentRead event n unit kappa sigma pd ps dL dR sL sR+
            nullCurrentRead event n kappa sigma pd ps dL dR sL sR)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroFeedbackNullRead event n unit kappa pd ps dL dR sL sR))) ∧
        Tendsto (fun kappa : staticDomain => -(kappa.val : ℂ)^2*zeroFeedbackNullRead event n unit kappa pd ps dL dR sL sR)
          staticApproach (𝓝 (sourceFeedbackNullCoefficient event n pd ps dL dR sL sR))
    | _ => True

/-- Source-owned determinant, divisibility and pole decisions are consumed internally; no scalar/radial response is supplied by the caller. -/
def sourceLongrangeReturn (event : DressedEvent) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : SourceLongrangeReturn event n unit pd ps dL dR sL sR := by
  match sourceOrderedStaticReturn event n pd ps dL dR sL sR with
  | .singular zero => exact ⟨.singular zero,True.intro⟩
  | .clockPrincipal nonzero clock pole => exact ⟨.clockPrincipal nonzero clock pole,True.intro⟩
  | .higherSpatial nonzero clock higher => exact ⟨.higherSpatial nonzero clock higher,True.intro⟩
  | .finite nonzero clock emBounded probeBounded emReturn probeReturn =>
    exact ⟨.finite nonzero clock emBounded probeBounded emReturn probeReturn,
      actual_feedback_null_damping_return event n unit pd ps dL dR sL sR nonzero clock.2,
      actual_feedback_null_spatial_return event n unit pd ps dL dR sL sR nonzero clock emBounded probeBounded⟩

theorem actual_longrange_coefficient_balance (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    sourceOrderedProbeCoefficient event n pd ps dL dR sL sR=
      nativeCurrentCoefficient pd ps dL dR sL sR+sourceFeedbackNullCoefficient event n pd ps dL dR sL sR := by
  unfold sourceFeedbackNullCoefficient
  ring

end LowEnergy.GaussComposite.ActualDressedStaticFeedback
