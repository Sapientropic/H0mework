import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedRationalFourier

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedStaticPole
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil PreparationVacuumFieldPerturbation
open SourcePropagationNoetherTime SourcePropagationResolvent SourcePropagationAlgebraicResponse
open SourcePropagationConstrainedPoleReturn
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualDressedHistoryKernel ActualDressedClockMoment ActualDressedFrequencyHalf
open ActualDressedFrequencyInverse
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
attribute [local irreducible] sourceInverse polynomialResolvent sourcePoleRegularOperator sourceLeadingPole
  sourcePoleOrder planeNoetherInverse sourceMaterialMap sourceContactMap rawInitial driveOperator

def staticPoleRegularOperator (q : PhysicalResponsePoint) (reader force : Field289) (lambda : ℂ) : ResponseOp :=
  lambda^sourcePoleOrder q 0 • sourcePoleRegularOperator q 0 lambda
    (sourceMaterialMap q reader force+sourceContactMap q reader force)+
  sourcePoleRegularOperator q 0 lambda
    (driveOperator q force (sourcePoleRegularOperator q 0 lambda (rawInitial q reader)))

def staticPoleLeadingOperator (q : PhysicalResponsePoint) (reader force : Field289) : ResponseOp :=
  sourceLeadingPole q 0 (driveOperator q force (sourceLeadingPole q 0 (rawInitial q reader)))

attribute [local irreducible] staticPoleRegularOperator staticPoleLeadingOperator

private theorem double_inverse_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R D : E→L[ℂ]E) (M C A : E) (z : ℂ) :
    z^2 • (R M+R (C+D (R A)))=
      z • (z • R) (M+C)+(z • R) (D ((z • R) A)) := by
  simp only [smul_apply,map_add,map_smul,smul_add,smul_smul,pow_two,add_assoc]

/-- The same source pole regularization retains all three original preparation/contact/drive terms. -/
theorem static_plane_pole_regularized (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    lambda^(2*sourcePoleOrder q 0) • planeNoetherInverse q reader force 0 lambda=
      staticPoleRegularOperator q reader force lambda := by
  have nonzero : lambda≠0 := by
    intro zero
    have realzero:=congrArg Complex.re zero
    simp only [Complex.zero_re] at realzero
    linarith
  have removed := sourcePole_removed q 0 lambda nonzero
  have future := polynomialResolvent_future q lambda positive
  have regularized : lambda^sourcePoleOrder q 0 • sourceInverse q lambda=sourcePoleRegularOperator q 0 lambda := by
    simpa only [sub_zero,future] using! removed
  have scale := double_inverse_scale (sourceInverse q lambda) (driveOperator q force)
    (sourceMaterialMap q reader force) (sourceContactMap q reader force) (rawInitial q reader)
    (lambda^sourcePoleOrder q 0)
  have shifted : planeNoetherInverse q reader force 0 lambda=
      sourceInverse q lambda (sourceMaterialMap q reader force)+
      sourceInverse q lambda (sourceContactMap q reader force+
        driveOperator q force (sourceInverse q lambda (rawInitial q reader))) := by
    unfold planeNoetherInverse
    exact congrArg (fun S : SourcePropagationResolvent.TransferOp=>
      sourceInverse q lambda (sourceMaterialMap q reader force)+
        S (sourceContactMap q reader force+driveOperator q force (sourceInverse q lambda (rawInitial q reader))))
      (congrArg (sourceInverse q) (sub_zero lambda))
  have first : lambda^(2*sourcePoleOrder q 0) • planeNoetherInverse q reader force 0 lambda=
      (lambda^sourcePoleOrder q 0)^2 • (sourceInverse q lambda (sourceMaterialMap q reader force)+
        sourceInverse q lambda (sourceContactMap q reader force+
          driveOperator q force (sourceInverse q lambda (rawInitial q reader)))) := by
    have power : lambda^(2*sourcePoleOrder q 0)=(lambda^sourcePoleOrder q 0)^2 := by rw [←pow_mul];congr 1;omega
    exact congrArg₂ (fun z : ℂ=>fun A : ResponseOp=>z • A) power shifted
  have replace:=congrArg
    (fun S : SourcePropagationResolvent.TransferOp=>lambda^sourcePoleOrder q 0 •
      S (sourceMaterialMap q reader force+sourceContactMap q reader force)+
      S (driveOperator q force (S (rawInitial q reader)))) regularized
  unfold staticPoleRegularOperator
  exact first.trans (scale.trans replace)

private theorem regularized_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : ℂ→E→L[ℂ]E) (D : E→L[ℂ]E) (M C A : E) (z : ℂ→ℂ)
    (point : ℂ) (hR : ContinuousAt R point) (hz : ContinuousAt z point) :
    ContinuousAt (fun l=>z l • R l (M+C)+R l (D (R l A))) point := by
  have first:=hR.clm_apply (continuousAt_const : ContinuousAt (fun _ : ℂ=>M+C) point)
  have inner:=hR.clm_apply (continuousAt_const : ContinuousAt (fun _ : ℂ=>A) point)
  have drive:=D.continuous.continuousAt.comp inner
  exact (hz.smul first).add (hR.clm_apply drive)

theorem static_regular_operator_continuous (q : PhysicalResponsePoint) (reader force : Field289) :
    ContinuousAt (staticPoleRegularOperator q reader force) 0 := by
  unfold staticPoleRegularOperator
  exact regularized_continuous (sourcePoleRegularOperator q 0) (driveOperator q force)
    (sourceMaterialMap q reader force) (sourceContactMap q reader force) (rawInitial q reader)
    (fun lambda : ℂ=>lambda^sourcePoleOrder q 0) 0 (sourcePoleRegular_continuousAt q 0)
    (continuous_id.pow _).continuousAt

theorem static_regular_operator_origin (q : PhysicalResponsePoint) (reader force : Field289)
    (pole : 0<sourcePoleOrder q 0) :
    staticPoleRegularOperator q reader force 0=staticPoleLeadingOperator q reader force := by
  unfold staticPoleRegularOperator staticPoleLeadingOperator sourceLeadingPole
  have zeroPower : (0:ℂ)^sourcePoleOrder q 0=0 := zero_pow (ne_of_gt pole)
  have remove:=congrArg
    (fun z : ℂ=>z • sourcePoleRegularOperator q 0 0
      (sourceMaterialMap q reader force+sourceContactMap q reader force)+
      sourcePoleRegularOperator q 0 0
        (driveOperator q force (sourcePoleRegularOperator q 0 0 (rawInitial q reader)))) zeroPower
  exact remove.trans ((congrArg
    (fun A : ResponseOp=>A+sourcePoleRegularOperator q 0 0
      (driveOperator q force (sourcePoleRegularOperator q 0 0 (rawInitial q reader))))
    (zero_smul ℂ (sourcePoleRegularOperator q 0 0 (sourceMaterialMap q reader force+sourceContactMap q reader force))))
      |>.trans (zero_add _))

end LowEnergy.GaussComposite.ActualDressedStaticPole
