import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFrequencyMemory

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFrequencyInverse
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil PreparationVacuumFieldPerturbation
open SourcePropagationNoetherTime SourcePropagationResolvent
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualDressedHistoryKernel ActualDressedClockMoment ActualDressedFrequencyHalf
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
local instance : NormedAlgebra ℝ ResponseOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ ResponseOp:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ SourcePropagationResolvent.TransferOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ SourcePropagationResolvent.TransferOp:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedSpace ℝ SourcePropagationResolvent.TransferOp:=ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ SourcePropagationResolvent.TransferOp:=by
  convert! NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=SourcePropagationResolvent.TransferOp) using 1
local instance : ContinuousSMul ℝ SourcePropagationResolvent.TransferOp:=by
  convert! IsBoundedSMul.continuousSMul (α:=ℝ) (β:=SourcePropagationResolvent.TransferOp) using 1
local instance : ContinuousENorm SourcePropagationResolvent.TransferOp:=by
  convert! SeminormedAddGroup.toContinuousENorm (E:=SourcePropagationResolvent.TransferOp) using 1
attribute [local irreducible] noetherMemoryMap rawInitial twoTimeMap driveOperator sourceInverse laplaceWeight

private def sourceApply : SourcePropagationResolvent.TransferOp→L[ℝ] ResponseOp→L[ℝ] ResponseOp :=
  ((ContinuousLinearMap.apply ℂ ResponseOp).flip).bilinearRestrictScalars ℝ

theorem source_inverse_applied_integrable (q : PhysicalResponsePoint) (lambda : ℂ)
    (positive : 0<lambda.re) (A : ResponseOp) :
    IntegrableOn (fun t=>laplaceWeight lambda t • twoTimeMap q t A) (Ioi (0:ℝ)) := by
  have paid:=sourceInverse_integrable q lambda positive
  unfold IntegrableOn at paid ⊢
  have applied:=Integrable.apply_continuousLinearMap
    (𝕜:=ℂ) (𝕜':=ℂ) (σ:=RingHom.id ℂ) (H:=ResponseOp) (E:=ResponseOp) paid A
  simpa only [ContinuousLinearMap.apply_apply,smul_apply] using! applied

theorem source_inverse_applied_read (q : PhysicalResponsePoint) (lambda : ℂ)
    (positive : 0<lambda.re) (A : ResponseOp) :
    (∫t in Ioi (0:ℝ),laplaceWeight lambda t • twoTimeMap q t A)=sourceInverse q lambda A := by
  unfold sourceInverse
  exact (ContinuousLinearMap.integral_apply (sourceInverse_integrable q lambda positive) A).symm

private theorem source_weight_split (clock lambda : ℂ) (t s : ℝ) :
    laplaceWeight lambda t*Complex.exp ((s:ℂ)*clock)=
      laplaceWeight (lambda-clock) s*laplaceWeight lambda (t-s) := by
  unfold laplaceWeight
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem weighted_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E→L[ℂ]E) (x : E) (a b c d : ℂ) (weights : a*b=c*d) :
    a • (b • A x)=(c • A) (d • x) := by
  simp only [smul_apply,map_smul,smul_smul]
  exact congrArg (fun z : ℂ=>z • A x) (weights.trans (mul_comm c d))

theorem noether_memory_weighted (q : PhysicalResponsePoint) (reader force : Field289)
    (clock lambda : ℂ) (t s : ℝ) :
    laplaceWeight lambda t • (Complex.exp ((s:ℂ)*clock) • noetherMemoryMap q reader t s force)=
      (laplaceWeight (lambda-clock) s • twoTimeMap q s)
        (laplaceWeight lambda (t-s) • driveOperator q force (twoTimeMap q (t-s) (rawInitial q reader))) := by
  have actual:=congrArg
    (fun A : ResponseOp=>laplaceWeight lambda t • (Complex.exp ((s:ℂ)*clock) • A))
    (noether_memory_convolution q reader force t s)
  exact actual.trans (weighted_apply (twoTimeMap q s)
    (driveOperator q force (twoTimeMap q (t-s) (rawInitial q reader)))
    (laplaceWeight lambda t) (Complex.exp ((s:ℂ)*clock))
    (laplaceWeight (lambda-clock) s) (laplaceWeight lambda (t-s))
    (source_weight_split clock lambda t s))

def planeNoetherMemory (q : PhysicalResponsePoint) (reader force : Field289) (clock : ℂ) (t : ℝ) : ResponseOp :=
  ∫s in (0:ℝ)..t,Complex.exp ((s:ℂ)*clock) • noetherMemoryMap q reader t s force

attribute [local irreducible] planeNoetherMemory

private theorem plane_memory_convolution (q : PhysicalResponsePoint) (reader force : Field289)
    (clock lambda : ℂ) (t : ℝ) :
    laplaceWeight lambda t • planeNoetherMemory q reader force clock t=
      ∫s in (0:ℝ)..t,sourceApply (laplaceWeight (lambda-clock) s • twoTimeMap q s)
        (laplaceWeight lambda (t-s) • driveOperator q force (twoTimeMap q (t-s) (rawInitial q reader))) := by
  have distribute:=intervalIntegral.integral_smul (μ:=volume) (a:=(0:ℝ)) (b:=t)
    (laplaceWeight lambda t) (fun s=>Complex.exp ((s:ℂ)*clock) • noetherMemoryMap q reader t s force)
  have pointwise : (∫s in (0:ℝ)..t,laplaceWeight lambda t •
      (Complex.exp ((s:ℂ)*clock) • noetherMemoryMap q reader t s force))=
      ∫s in (0:ℝ)..t,sourceApply (laplaceWeight (lambda-clock) s • twoTimeMap q s)
        (laplaceWeight lambda (t-s) • driveOperator q force (twoTimeMap q (t-s) (rawInitial q reader))) := by
    apply intervalIntegral.integral_congr
    intro s _
    exact noether_memory_weighted q reader force clock lambda t s
  unfold planeNoetherMemory
  exact distribute.symm.trans pointwise

private theorem memory_drive_integrable (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    IntegrableOn (fun t=>laplaceWeight lambda t • driveOperator q force (twoTimeMap q t (rawInitial q reader)))
      (Ioi (0:ℝ)) := by
  have paid:=source_inverse_applied_integrable q lambda positive (rawInitial q reader)
  unfold IntegrableOn at paid ⊢
  simpa only [map_smul] using!
    (driveOperator q force).integrable_comp paid

private theorem forward_convolution_integrable {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℝ→E) (g : ℝ→G) (L : E→L[ℝ] G→L[ℝ]G)
    (fi : IntegrableOn f (Ioi (0:ℝ))) (gi : IntegrableOn g (Ioi (0:ℝ))) :
    IntegrableOn (fun t=>∫s in (0:ℝ)..t,L (f s) (g (t-s))) (Ioi (0:ℝ)) := by
  have whole : IntegrableOn (posConvolution f g L) (Ioi (0:ℝ)):=
    (integrable_posConvolution fi gi L).integrableOn
  apply whole.congr
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  rw [posConvolution,indicator_of_mem ht]

private theorem forward_convolution_integral {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f : ℝ→E) (g : ℝ→G) (L : E→L[ℝ] G→L[ℝ]G)
    (fi : IntegrableOn f (Ioi (0:ℝ))) (gi : IntegrableOn g (Ioi (0:ℝ))) :
    (∫t in Ioi (0:ℝ),∫s in (0:ℝ)..t,L (f s) (g (t-s)))=
      L (∫s in Ioi (0:ℝ),f s) (∫s in Ioi (0:ℝ),g s) :=
  integral_posConvolution (μ:=volume) (ν:=volume) fi gi L

theorem plane_noether_memory_integrable (q : PhysicalResponsePoint) (reader force : Field289)
    (clock lambda : ℂ) (positive : 0<lambda.re) (shifted : 0<(lambda-clock).re) :
    IntegrableOn (fun t=>laplaceWeight lambda t • planeNoetherMemory q reader force clock t) (Ioi (0:ℝ)) := by
  let f : ℝ→SourcePropagationResolvent.TransferOp:=fun t=>laplaceWeight (lambda-clock) t • twoTimeMap q t
  let g : ℝ→ResponseOp:=fun t=>laplaceWeight lambda t • driveOperator q force (twoTimeMap q t (rawInitial q reader))
  have fi : IntegrableOn f (Ioi (0:ℝ)):=sourceInverse_integrable q (lambda-clock) shifted
  have gi : IntegrableOn g (Ioi (0:ℝ)):=memory_drive_integrable q reader force lambda positive
  have whole:=forward_convolution_integrable f g sourceApply fi gi
  have same : (fun t=>laplaceWeight lambda t • planeNoetherMemory q reader force clock t)=
      (fun t=>∫s in (0:ℝ)..t,sourceApply (f s) (g (t-s))) :=
    funext (plane_memory_convolution q reader force clock lambda)
  rw [same]
  exact whole

/-- Fubini retains the shifted outer inverse and the original unshifted preparation inverse. -/
theorem plane_noether_memory_inverse (q : PhysicalResponsePoint) (reader force : Field289)
    (clock lambda : ℂ) (positive : 0<lambda.re) (shifted : 0<(lambda-clock).re) :
    (∫t in Ioi (0:ℝ),laplaceWeight lambda t • planeNoetherMemory q reader force clock t)=
      sourceInverse q (lambda-clock)
        (driveOperator q force (sourceInverse q lambda (rawInitial q reader))) := by
  let f : ℝ→SourcePropagationResolvent.TransferOp:=fun t=>laplaceWeight (lambda-clock) t • twoTimeMap q t
  let g : ℝ→ResponseOp:=fun t=>laplaceWeight lambda t • driveOperator q force (twoTimeMap q t (rawInitial q reader))
  have fi : IntegrableOn f (Ioi (0:ℝ)):=sourceInverse_integrable q (lambda-clock) shifted
  have gi : IntegrableOn g (Ioi (0:ℝ)):=memory_drive_integrable q reader force lambda positive
  have generated:=forward_convolution_integral f g sourceApply fi gi
  have driven : (∫t in Ioi (0:ℝ),laplaceWeight lambda t • driveOperator q force (twoTimeMap q t (rawInitial q reader)))=
      driveOperator q force (sourceInverse q lambda (rawInitial q reader)) := by
    have read:=(driveOperator q force).integral_comp_comm
      (source_inverse_applied_integrable q lambda positive (rawInitial q reader))
    simpa only [map_smul,source_inverse_applied_read q lambda positive (rawInitial q reader)] using! read
  have same : (fun t=>laplaceWeight lambda t • planeNoetherMemory q reader force clock t)=
      (fun t=>∫s in (0:ℝ)..t,sourceApply (f s) (g (t-s))) :=
    funext (plane_memory_convolution q reader force clock lambda)
  have integralSame:=congrArg (fun h : ℝ→ResponseOp=>∫t in Ioi (0:ℝ),h t) same
  have firstRead : (∫t in Ioi (0:ℝ),f t)=sourceInverse q (lambda-clock) := by
    unfold f sourceInverse
    rfl
  have applied := congrArg₂ (fun A : SourcePropagationResolvent.TransferOp=>fun x : ResponseOp=>sourceApply A x)
    firstRead driven
  calc
    _=∫t in Ioi (0:ℝ),∫s in (0:ℝ)..t,sourceApply (f s) (g (t-s)) := integralSame
    _=sourceApply (∫t in Ioi (0:ℝ),f t) (∫t in Ioi (0:ℝ),g t) := generated
    _=sourceApply (sourceInverse q (lambda-clock))
        (driveOperator q force (sourceInverse q lambda (rawInitial q reader))) := applied
    _=_ := rfl

end LowEnergy.GaussComposite.ActualDressedFrequencyInverse
