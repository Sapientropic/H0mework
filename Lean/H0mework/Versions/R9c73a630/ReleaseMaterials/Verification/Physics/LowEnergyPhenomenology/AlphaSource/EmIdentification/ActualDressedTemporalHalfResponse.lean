import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalReaderGerm

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalHalf
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField
open PreparationVacuumNoetherChart PreparationVacuumGaugeSourceInjection
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil
open PreparationVacuumTemporalCharge PreparationVacuumSourceChargeWard
open SourcePropagationResolvent SourcePropagationFieldFeedback SourcePropagationNearFieldTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedSylvester
open ActualDressedNonlinearHalf
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
local instance : NormedAlgebra ℝ ResponseOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ SourcePropagationResolvent.TransferOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ SourcePropagationResolvent.TransferOp := ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ SourcePropagationResolvent.TransferOp := by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=SourcePropagationResolvent.TransferOp)) using 1
local instance : ContinuousSMul ℝ SourcePropagationResolvent.TransferOp := by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=SourcePropagationResolvent.TransferOp)) using 1
local instance : ContinuousENorm SourcePropagationResolvent.TransferOp := by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=SourcePropagationResolvent.TransferOp)) using 1
attribute [local irreducible] noetherReader noetherBackgroundInitial noetherBackgroundOperator
  physicalBackgroundMap jointResolvent noetherNonlinearHalf fieldInverse fieldPencil sourceInverse

def temporalGaussInitial (q : PhysicalResponsePoint) (a : Fin 12) (h : Field289) : ResponseOp :=
  jointResolvent (q.p+q.k) q.F q.z h*(-temporalGaussReader q.F a)*jointResolvent q.p q.F q.w h

/-- Both original physical-time legs propagate the same weighted Gauss and normal-pair insertion. -/
def temporalGaussHalf (q : PhysicalResponsePoint) (a : Fin 12) (lambda : ℂ) (h : Field289) : ResponseOp :=
  ∫t in Ioi (0:ℝ),laplaceWeight lambda t • physicalBackgroundMap q h t (temporalGaussInitial q a h)

theorem temporal_gauss_initial_generated (q : PhysicalResponsePoint) (a : Fin 12) (h : Field289)
    (small : ‖h‖<temporalFrameRadius q.F) :
    noetherBackgroundInitial q (temporalField a) h=temporalGaussInitial q a h :=by
  unfold noetherBackgroundInitial temporalGaussInitial
  rw [temporal_reader_gauss q.F h small a q.p]

theorem temporal_gauss_half_generated (q : PhysicalResponsePoint) (a : Fin 12) (lambda : ℂ) (h : Field289)
    (small : ‖h‖<temporalFrameRadius q.F) :
    noetherNonlinearHalf q (temporalField a) lambda h=temporalGaussHalf q a lambda h :=by
  unfold noetherNonlinearHalf temporalGaussHalf
  rw [temporal_gauss_initial_generated q a h small]

theorem temporal_gauss_half_integrable (q : PhysicalResponsePoint) (a : Fin 12) (lambda : ℂ)
    (positive : 0<lambda.re) (h : Field289) (small : ‖h‖<temporalFrameRadius q.F)
    (inside : h∈timeDomain q lambda) :
    IntegrableOn (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t (temporalGaussInitial q a h))
      (Ioi (0:ℝ)) :=by
  simpa only [temporal_gauss_initial_generated q a h small] using!
    noether_nonlinear_half_integrable q (temporalField a) lambda positive h inside

/-- The source supplies one positive field ball for all twelve original temporal currents and their genuine halfline endpoint equation. -/
theorem temporal_half_source_neighborhood (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    ∃radius : ℝ,0<radius ∧ ∀h : Field289,‖h‖<radius →
      ‖h‖<temporalFrameRadius q.F ∧ h∈timeDomain q lambda ∧
      ∀a : Fin 12,
        noetherNonlinearHalf q (temporalField a) lambda h=temporalGaussHalf q a lambda h ∧
        fieldPencil q lambda h (temporalGaussHalf q a lambda h)=temporalGaussInitial q a h :=by
  have readers : ∀ᶠh : Field289 in 𝓝 0,∀a : Fin 12,
      noetherNonlinearHalf q (temporalField a) lambda h=noetherBackgroundOperator q (temporalField a) lambda h :=
    Filter.eventually_all.2 (fun a=>noether_nonlinear_half_background q (temporalField a) lambda positive)
  have endpoints : ∀ᶠh : Field289 in 𝓝 0,∀a : Fin 12,
      fieldPencil q lambda h (noetherBackgroundOperator q (temporalField a) lambda h)=
        noetherBackgroundInitial q (temporalField a) h :=
    Filter.eventually_all.2 (fun a=>noether_background_operator_pencil q (temporalField a) lambda (ne_of_gt positive))
  have frame : ∀ᶠh : Field289 in 𝓝 0,‖h‖<temporalFrameRadius q.F :=
    (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using temporal_frame_radius_positive q.F))
  have all : ∀ᶠh : Field289 in 𝓝 0,
      ‖h‖<temporalFrameRadius q.F ∧ h∈timeDomain q lambda ∧
      ∀a : Fin 12,
        noetherNonlinearHalf q (temporalField a) lambda h=temporalGaussHalf q a lambda h ∧
        fieldPencil q lambda h (temporalGaussHalf q a lambda h)=temporalGaussInitial q a h :=by
    filter_upwards [frame,timeDomain_source_near q lambda positive,readers,endpoints] with h small inside read endpoint
    refine ⟨small,inside,fun a=>⟨temporal_gauss_half_generated q a lambda h small,?_⟩⟩
    rw [←temporal_gauss_half_generated q a lambda h small,read a,endpoint a]
    exact temporal_gauss_initial_generated q a h small
  rcases Metric.mem_nhds_iff.mp all with ⟨radius,positiveRadius,ball⟩
  refine ⟨radius,positiveRadius,fun h small=>ball ?_⟩
  simpa only [Metric.mem_ball,dist_zero_right] using small

/-- The same actual creation-minus-background nonlinear source consumes the weighted Gauss operator before differentiation. -/
theorem temporal_actual_half_source (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12)
    (lambda : ℂ) (positive : 0<lambda.re) (h : Field289)
    (small : ‖h‖<temporalFrameRadius event.frame)
    (inside : h∈timeDomain (dressedKinematicPoint event transfer) lambda) :
    dressedNoetherHalfSource event transfer lambda h (gaugeSlot 0 a)=
      dressedEulerObserver event (temporalGaussHalf (dressedKinematicPoint event transfer) a lambda h) :=by
  have paid:=dressed_noether_half_read event transfer lambda positive h inside (gaugeSlot 0 a)
  have slot : fieldUnit (gaugeSlot 0 a)=temporalField a:=rfl
  rw [slot] at paid
  exact paid.trans (congrArg (dressedEulerObserver event)
    (temporal_gauss_half_generated (dressedKinematicPoint event transfer) a lambda h small))

end LowEnergy.GaussComposite.ActualDressedTemporalHalf
