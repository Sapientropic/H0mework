import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.Projection
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance projectionActionComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


/-- The literal source programme uses the complete actual P profile before its mean readout. -/
def actualPhysicalMovingWindow (raw : ℝ → ℂ) (t : ℝ) : ℂ :=
  (2 * Real.exp (-t / 2) : ℂ) * ∫ x in -(Real.exp t / 4)..Real.exp t / 4, raw x

def actualPhysicalPairedMovingWindow (h t : ℝ) : ℂ :=
  actualPhysicalMovingWindow (actualPhysicalPairedRaw observation nontrivial half h) t

def actualPhysicalSiblingMovingWindow (h t : ℝ) : ℂ :=
  actualPhysicalMovingWindow (actualPhysicalSiblingRaw observation nontrivial half h) t

private theorem projection_raw_even (value : BurnolL2) (raw : ℝ → ℂ) (x : ℝ) :
    burnolEvenProjectionRaw value raw (-x) = burnolEvenProjectionRaw value raw x := by
  unfold burnolEvenProjectionRaw burnolEvenRaw
  simp only [neg_neg]
  ring

private theorem projection_source_outer_continuousAt
    (value : BurnolL2) (raw : ℝ → ℂ) (outside : ContinuousOn (burnolEvenProjectionPositiveOuterRaw value raw) (Ioi 0))
    (x : ℝ) (large : 1/4 < x) : ContinuousAt (burnolEvenProjectionRaw value raw) x := by
  have source : burnolEvenProjectionRaw value raw =ᶠ[𝓝 x] burnolEvenProjectionPositiveOuterRaw value raw := by
    filter_upwards [Ioi_mem_nhds large] with y hy
    exact burnolEvenProjectionRaw_eq_positiveOuter value raw hy
  exact (outside.continuousAt (Ioi_mem_nhds (by linarith : 0 < x))).congr_of_eventuallyEq source

private theorem source_window_hasDerivAt (raw : ℝ → ℂ) (sourceLp : MemLp raw 2 volume)
    (even : ∀ x, raw (-x) = raw x) (t : ℝ) (endpoint : ContinuousAt raw (Real.exp t / 4)) :
    HasDerivAt (actualPhysicalMovingWindow raw)
      (-(actualPhysicalMovingWindow raw t)/2 + (Real.exp (t/2) : ℂ)*raw (Real.exp t/4)) t := by
  let a := Real.exp t / 4
  have interval : IntervalIntegrable raw volume (-a) a := by
    have : IsFiniteMeasure (volume.restrict (uIcc (-a) a)) := by
      change IsFiniteMeasure (volume.restrict (Icc (min (-a) a) (max (-a) a)))
      infer_instance
    have restricted : MemLp raw 2 (volume.restrict (uIcc (-a) a)) := sourceLp.restrict _
    have on : IntegrableOn raw (uIcc (-a) a) volume := restricted.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    exact on.intervalIntegrable
  have left : ContinuousAt raw (-a) := by
    have atPositive : ContinuousAt raw (-(-a)) := by simpa only [neg_neg] using endpoint
    have twin : ContinuousAt (fun x : ℝ => raw (-x)) (-a) :=
      atPositive.comp continuous_neg.continuousAt
    simpa only [even] using twin
  have ends : HasDerivAt (fun s : ℝ => (- (Real.exp s / 4), Real.exp s / 4)) (-a, a) t :=
    ((Real.hasDerivAt_exp t).div_const 4).neg.prodMk ((Real.hasDerivAt_exp t).div_const 4)
  have integralAction := (intervalIntegral.integral_hasFDerivAt interval
    sourceLp.aestronglyMeasurable.stronglyMeasurableAtFilter
    sourceLp.aestronglyMeasurable.stronglyMeasurableAtFilter left endpoint).comp_hasDerivAt t ends
  have integralPrice : HasDerivAt (fun s : ℝ => ∫ x in -(Real.exp s / 4)..Real.exp s / 4, raw x)
      ((Real.exp t / 2 : ℝ) • raw a) t := by
    have price : ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (raw a) -
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (raw (-a))) (-a, a) =
        (Real.exp t / 2 : ℝ) • raw a := by
      change a • raw a - (-a) • raw (-a) = (Real.exp t / 2 : ℝ) • raw a
      rw [even]
      simp only [real_smul]
      dsimp [a]
      push_cast
      ring
    rw [price] at integralAction
    exact integralAction
  have weight := (((hasDerivAt_id t).neg.div_const 2).exp.ofReal_comp).const_mul (2 : ℂ)
  have action := weight.mul integralPrice
  have price : (2 * (Real.exp (-t/2)*(-1/2) : ℝ) * (∫ x in -(Real.exp t/4)..Real.exp t/4, raw x)) +
      (2*(Real.exp (-t/2) : ℂ))*((Real.exp t/2 : ℝ) • raw a) =
      -(actualPhysicalMovingWindow raw t)/2 + (Real.exp (t/2) : ℂ)*raw a := by
    simp only [actualPhysicalMovingWindow, real_smul]
    have exponents : Real.exp (-t/2) * Real.exp t = Real.exp (t/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have exponentsC := congrArg (fun x : ℝ => (x : ℂ)) exponents
    push_cast at exponentsC ⊢
    rw [← exponentsC]
    ring
  change HasDerivAt (actualPhysicalMovingWindow raw)
    ((2 * (Real.exp (-t/2)*(-1/2) : ℝ) * (∫ x in -(Real.exp t/4)..Real.exp t/4, raw x)) +
      (2*(Real.exp (-t/2) : ℂ))*((Real.exp t/2 : ℝ) • raw a)) t at action
  rw [price] at action
  exact action

/-- The actual paired/sibling positive-annulus action is generated from source P profiles; no pointwise L² trace enters as an input. -/
theorem actual_physical_moving_window_action (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (t : ℝ) (positive : 0 < t) :
    HasDerivAt (actualPhysicalPairedMovingWindow observation nontrivial half h)
      (-(actualPhysicalPairedMovingWindow observation nontrivial half h t)/2 +
        (Real.exp (t/2) : ℂ) * actualPhysicalPairedOuterRaw observation nontrivial half h (Real.exp t/4)) t ∧
    HasDerivAt (actualPhysicalSiblingMovingWindow observation nontrivial half h)
      (-(actualPhysicalSiblingMovingWindow observation nontrivial half h t)/2 +
        (Real.exp (t/2) : ℂ) * actualPhysicalSiblingOuterRaw observation nontrivial half h (Real.exp t/4)) t := by
  have qualification := actual_physical_pair_sibling_source_raw observation nontrivial half h nonnegative bounded
  have pairLp := (Lp.memLp ((P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) : BurnolL2))).ae_eq qualification.1
  have siblingLp := (Lp.memLp ((P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) : BurnolL2))).ae_eq qualification.2
  have radius : 1/4 < Real.exp t/4 := by
    have ex := Real.one_lt_exp_iff.mpr positive
    linarith
  have outside := actual_physical_source_outer_continuous observation nontrivial half h
  have pairAction := source_window_hasDerivAt _ pairLp
    (projection_raw_even _ _) t (projection_source_outer_continuousAt _ _ outside.1 _ radius)
  have siblingAction := source_window_hasDerivAt _ siblingLp
    (projection_raw_even _ _) t (projection_source_outer_continuousAt _ _ outside.2 _ radius)
  have actualOuter := actual_physical_source_outer observation nontrivial half h (Real.exp t/4) radius
  exact ⟨by simpa only [actualPhysicalPairedMovingWindow, actualOuter.1] using! pairAction,
    by simpa only [actualPhysicalSiblingMovingWindow, actualOuter.2] using! siblingAction⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
