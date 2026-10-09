import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPoleKernel

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
attribute [local irreducible] dressedEulerObserver dressedStaticPolarization frequencyHalfPolarization
  staticPoleRegularOperator staticPoleLeadingOperator dressedKinematicPoint

def dressedStaticPoleOrder (event : DressedEvent) : ℕ := sourcePoleOrder (dressedKinematicPoint event 0) 0

def dressedStaticPoleRegular (event : DressedEvent) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>dressedEulerObserver event (staticPoleRegularOperator (dressedKinematicPoint event 0)
    (fieldUnit i) (fieldUnit j) lambda)

def dressedStaticPoleLeading (event : DressedEvent) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>dressedEulerObserver event (staticPoleLeadingOperator (dressedKinematicPoint event 0)
    (fieldUnit i) (fieldUnit j))

attribute [local irreducible] dressedStaticPoleOrder dressedStaticPoleRegular dressedStaticPoleLeading

theorem dressed_static_pole_order_positive (event : DressedEvent) : 0<dressedStaticPoleOrder event := by
  unfold dressedStaticPoleOrder
  exact zero_transfer_sourcePoleOrder (dressedKinematicPoint event 0)
    (by simp only [dressedKinematicPoint,neg_zero])

private theorem observed_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (observer : E→L[ℂ]ℂ) (c : ℂ) (x : E) : observer (c • x)=c*observer x := by
  rw [map_smul,smul_eq_mul]

/-- All actual static quantum entries have a generated regularized source object. -/
theorem dressed_static_polarization_regularized (event : DressedEvent) (lambda : ℂ)
    (positive : 0<lambda.re) (i j : Fin 289) :
    lambda^(2*dressedStaticPoleOrder event)*dressedStaticPolarization event 0 lambda i j=
      dressedStaticPoleRegular event lambda i j := by
  have off : sourceClockGrowth (fun _ : Fin 4=>(0:ℂ))<lambda.re := by
    simpa only [sourceClockGrowth,Complex.zero_re,max_self] using positive
  have actual:=dressed_frequency_half_inverse event 0 (fun _ : Fin 4=>(0:ℂ)) lambda off i j
  have staticRead:=dressed_static_polarization_actual event 0 (fun _ : Fin 4=>(0:ℂ)) rfl lambda positive i j
  have staticInverse : dressedStaticPolarization event 0 lambda i j=
      dressedEulerObserver event (planeNoetherInverse (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j) 0 lambda) := by
    have original : dressedSignalHalfOperator event 0 (fun _ : Fin 4=>(0:ℂ)) lambda (Pi.single j 1) i=
        dressedEulerObserver event (planeNoetherInverse (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j) 0 lambda) := by
      simpa only [frequencyHalfPolarization] using! actual
    exact staticRead.symm.trans original
  have generated:=static_plane_pole_regularized (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j) lambda positive
  have observed:=congrArg (dressedEulerObserver event) generated
  have regular : lambda^(2*dressedStaticPoleOrder event)*
      dressedEulerObserver event (planeNoetherInverse (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j) 0 lambda)=
      dressedStaticPoleRegular event lambda i j := by
    simpa only [observed_scale,dressedStaticPoleOrder,dressedStaticPoleRegular] using! observed
  exact (congrArg (fun z : ℂ=>lambda^(2*dressedStaticPoleOrder event)*z) staticInverse).trans regular

theorem dressed_static_pole_regular_continuous (event : DressedEvent) :
    ContinuousAt (dressedStaticPoleRegular event) 0 := by
  apply continuousAt_pi.2
  intro i
  apply continuousAt_pi.2
  intro j
  unfold dressedStaticPoleRegular
  exact (dressedEulerObserver event).continuous.continuousAt.comp
    (static_regular_operator_continuous (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j))

theorem dressed_static_pole_regular_origin (event : DressedEvent) :
    dressedStaticPoleRegular event 0=dressedStaticPoleLeading event := by
  funext i j
  unfold dressedStaticPoleRegular dressedStaticPoleLeading
  exact congrArg (dressedEulerObserver event)
    (static_regular_operator_origin (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j)
      (by simpa only [dressedStaticPoleOrder] using dressed_static_pole_order_positive event))

/-- The actual positive damping limit returns the complete generated coefficient, including possible observed cancellation. -/
theorem dressed_static_pole_leading_limit (event : DressedEvent) (i j : Fin 289) :
    Tendsto (fun sigma : ℝ=>(sigma:ℂ)^(2*dressedStaticPoleOrder event)*
      dressedStaticPolarization event 0 (sigma:ℂ) i j) (nhdsWithin 0 (Ioi (0:ℝ)))
      (𝓝 (dressedStaticPoleLeading event i j)) := by
  have embedding : Tendsto (fun sigma : ℝ=>(sigma:ℂ)) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (0:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have regular:=((continuous_apply j).continuousAt.tendsto.comp
    ((continuous_apply i).continuousAt.tendsto.comp
      (dressed_static_pole_regular_continuous event).tendsto)).comp embedding
  have origin : dressedStaticPoleRegular event 0 i j=dressedStaticPoleLeading event i j :=
    congrFun (congrFun (dressed_static_pole_regular_origin event) i) j
  rw [origin] at regular
  apply Tendsto.congr' _ regular
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  exact (dressed_static_polarization_regularized event (sigma:ℂ) positive i j).symm

end LowEnergy.GaussComposite.ActualDressedStaticPole
