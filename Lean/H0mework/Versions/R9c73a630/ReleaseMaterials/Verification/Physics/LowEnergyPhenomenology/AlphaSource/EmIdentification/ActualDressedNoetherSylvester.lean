import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationInverse
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNoetherHistoryResponse

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSylvester
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumNoetherChart
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil
open SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime SourcePropagationResolvent
open Set MeasureTheory
open scoped Topology BigOperators
abbrev ResponseOp := H→L[ℂ]H
local instance : NormedAlgebra ℝ ResponseOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : ContinuousENorm SourcePropagationResolvent.TransferOp := by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=SourcePropagationResolvent.TransferOp)) using 1
attribute [local irreducible] noetherHistoryOperatorJet sourceInverse propagationPencil
  slopeHalf rawHalf noetherReaderContact rawReaderContact jointResolvent

/-- The fixed-canonical-momentum contact increment is retained before taking the halfline. -/
def noetherStaticContact (q : PhysicalResponsePoint) (reader force : Field289) : ResponseOp :=
  jointResolvent (q.p+q.k) q.F q.z 0*
    (noetherReaderContact reader force q.p q.F-rawReaderContact reader force q.p q.F)*
      jointResolvent q.p q.F q.w 0

def noetherStaticInitial (q : PhysicalResponsePoint) (reader force : Field289) : ResponseOp :=
  slopeInitial q reader force+noetherStaticContact q reader force

/-- This is the original complete Noether history, not a projected matter inverse. -/
def noetherStaticHalf (q : PhysicalResponsePoint) (reader force : Field289) (lambda : ℂ) : ResponseOp :=
  ∫t in Ioi (0:ℝ),laplaceWeight lambda t •
    (noetherHistoryOperatorJet q reader (fun _=>⟨force,0,0⟩) t).value

attribute [local irreducible] noetherStaticContact noetherStaticInitial noetherStaticHalf
  rawInitial slopeInitial leftCurrent rightCurrent

theorem noether_static_flow (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) :
    (noetherHistoryOperatorJet q reader (fun _=>⟨force,0,0⟩) t).value=
      slopeFlow q reader force t+twoTimeMap q t (noetherStaticContact q reader force) := by
  rw [noetherHistoryOperatorJet_value,historyOperator_constant,twoTimeMap_apply]
  simp only [slopeFlow,noetherStaticContact,mul_assoc]

private theorem correction_integrable (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    IntegrableOn (fun t=>laplaceWeight lambda t •
      twoTimeMap q t (noetherStaticContact q reader force)) (Ioi (0:ℝ)) := by
  have paid:=sourceInverse_integrable q lambda positive
  unfold IntegrableOn at *
  with_reducible_and_instances
    have source:=Integrable.apply_continuousLinearMap (𝕜:=ℂ) (𝕜':=ℂ)
      (σ:=RingHom.id ℂ)
      (H:=ResponseOp) (E:=ResponseOp) paid (noetherStaticContact q reader force)
    simpa only [ContinuousLinearMap.apply_apply,smul_apply] using! source

theorem noether_static_half_integrable (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    IntegrableOn (fun t=>laplaceWeight lambda t •
      (noetherHistoryOperatorJet q reader (fun _=>⟨force,0,0⟩) t).value) (Ioi (0:ℝ)) := by
  have first:=slopeFlow_integrable q reader force lambda positive
  have second:=correction_integrable q reader force lambda positive
  unfold IntegrableOn at *
  with_reducible_and_instances
    simpa only [noether_static_flow,smul_add] using!
      Integrable.add (ε':=ResponseOp) first second

private theorem correction_half (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    (∫t in Ioi (0:ℝ),laplaceWeight lambda t •
      twoTimeMap q t (noetherStaticContact q reader force))=
        sourceInverse q lambda (noetherStaticContact q reader force) := by
  unfold sourceInverse
  simpa only [smul_apply] using
    (ContinuousLinearMap.integral_apply (sourceInverse_integrable q lambda positive)
      (noetherStaticContact q reader force)).symm

theorem noether_static_half_return (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    noetherStaticHalf q reader force lambda=slopeHalf q reader force lambda+
      sourceInverse q lambda (noetherStaticContact q reader force) := by
  unfold noetherStaticHalf
  simp_rw [noether_static_flow,smul_add]
  rw [integral_add (slopeFlow_integrable q reader force lambda positive)
    (correction_integrable q reader force lambda positive),correction_half q reader force lambda positive]
  unfold slopeHalf
  rfl

private theorem corrected_initial_algebra {A : Type*} [AddCommGroup A] (S D L R : A) :
    (S-L+R)+D=(S+D)-L+R := by abel

theorem noether_static_half_pencil (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    propagationPencil q lambda (noetherStaticHalf q reader force lambda)=
      noetherStaticInitial q reader force-leftCurrent q force*rawHalf q reader lambda+
        rawHalf q reader lambda*rightCurrent q force := by
  have correction:=congrArg (fun L : SourcePropagationResolvent.TransferOp=>
    L (noetherStaticContact q reader force)) (sourceInverse_left q lambda positive)
  simp only [mul_apply_eq_comp,one_apply_eq_self] at correction
  calc
    _=propagationPencil q lambda (slopeHalf q reader force lambda)+
        propagationPencil q lambda (sourceInverse q lambda (noetherStaticContact q reader force)) := by
      exact (congrArg (propagationPencil q lambda)
        (noether_static_half_return q reader force lambda positive)).trans
          ((propagationPencil q lambda).map_add _ _)
    _=(slopeInitial q reader force-leftCurrent q force*rawHalf q reader lambda+
        rawHalf q reader lambda*rightCurrent q force)+noetherStaticContact q reader force := by
      exact congrArg₂ (fun A B : ResponseOp=>A+B)
        (slopeHalf_pencil q reader force lambda positive) correction
    _=_ := by
      unfold noetherStaticInitial
      exact corrected_initial_algebra _ _ _ _

/-- The full joint propagation inverse consumes the corrected current initial and both driven legs. -/
theorem noether_static_half_inverse (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    noetherStaticHalf q reader force lambda=sourceInverse q lambda
      (noetherStaticInitial q reader force-
        leftCurrent q force*sourceInverse q lambda (rawInitial q reader)+
          sourceInverse q lambda (rawInitial q reader)*rightCurrent q force) := by
  have equation:=congrArg (sourceInverse q lambda)
    (noether_static_half_pencil q reader force lambda positive)
  have cancel:=congrArg (fun L : SourcePropagationResolvent.TransferOp=>
    L (noetherStaticHalf q reader force lambda)) (sourceInverse_right q lambda positive)
  rw [rawHalf_true_inverse q reader lambda positive] at equation
  simpa only [mul_apply_eq_comp,one_apply_eq_self] using cancel.symm.trans equation

end LowEnergy.GaussComposite.ActualDressedSylvester
