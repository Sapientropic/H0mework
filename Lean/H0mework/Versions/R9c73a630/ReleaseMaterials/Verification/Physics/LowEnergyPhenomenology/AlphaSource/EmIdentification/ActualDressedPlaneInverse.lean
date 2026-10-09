import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFrequencyConvolution

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
attribute [local irreducible] noetherInitialMap noetherContactMap noetherMemoryMap
  sourceMaterialMap sourceContactMap rawInitial twoTimeMap driveOperator sourceInverse laplaceWeight planeNoetherMemory

/-- Positive Fourier construction of the complete preparation, contact and two-memory operator. -/
def planeNoetherOperator (q : PhysicalResponsePoint) (reader force : Field289) (clock : ℂ) (t : ℝ) : ResponseOp :=
  noetherInitialMap q reader t force+Complex.exp ((t:ℂ)*clock) • noetherContactMap q reader t force+
    planeNoetherMemory q reader force clock t

def planeNoetherInverse (q : PhysicalResponsePoint) (reader force : Field289) (clock lambda : ℂ) : ResponseOp :=
  sourceInverse q lambda (sourceMaterialMap q reader force)+
    sourceInverse q (lambda-clock) (sourceContactMap q reader force+
      driveOperator q force (sourceInverse q lambda (rawInitial q reader)))

attribute [local irreducible] planeNoetherOperator planeNoetherInverse

private theorem plane_initial_weighted (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (t : ℝ) :
    laplaceWeight lambda t • noetherInitialMap q reader t force=
      laplaceWeight lambda t • twoTimeMap q t (sourceMaterialMap q reader force) := by
  unfold noetherInitialMap twoTimeMap
  rfl

private theorem plane_contact_weighted (q : PhysicalResponsePoint) (reader force : Field289)
    (clock lambda : ℂ) (t : ℝ) :
    laplaceWeight lambda t • (Complex.exp ((t:ℂ)*clock) • noetherContactMap q reader t force)=
      laplaceWeight (lambda-clock) t • twoTimeMap q t (sourceContactMap q reader force) := by
  have weight : laplaceWeight lambda t*Complex.exp ((t:ℂ)*clock)=laplaceWeight (lambda-clock) t := by
    unfold laplaceWeight
    rw [←Complex.exp_add]
    congr 1
    ring
  have first : laplaceWeight lambda t • (Complex.exp ((t:ℂ)*clock) • noetherContactMap q reader t force)=
      laplaceWeight (lambda-clock) t • noetherContactMap q reader t force :=
    (smul_smul (laplaceWeight lambda t) (Complex.exp ((t:ℂ)*clock))
      (noetherContactMap q reader t force)).trans (congrArg (fun z : ℂ=>z • noetherContactMap q reader t force) weight)
  have contact : noetherContactMap q reader t force=twoTimeMap q t (sourceContactMap q reader force) := by
    unfold noetherContactMap twoTimeMap
    rfl
  exact first.trans (congrArg (fun A : ResponseOp=>laplaceWeight (lambda-clock) t • A) contact)

theorem plane_noether_operator_integrable (q : PhysicalResponsePoint) (reader force : Field289)
    (clock lambda : ℂ) (positive : 0<lambda.re) (shifted : 0<(lambda-clock).re) :
    IntegrableOn (fun t=>laplaceWeight lambda t • planeNoetherOperator q reader force clock t) (Ioi (0:ℝ)) := by
  have initial : IntegrableOn (fun t=>laplaceWeight lambda t • noetherInitialMap q reader t force) (Ioi (0:ℝ)) := by
    simpa only [plane_initial_weighted] using!
      source_inverse_applied_integrable q lambda positive (sourceMaterialMap q reader force)
  have contact : IntegrableOn (fun t=>laplaceWeight lambda t •
      (Complex.exp ((t:ℂ)*clock) • noetherContactMap q reader t force)) (Ioi (0:ℝ)) := by
    simpa only [plane_contact_weighted] using!
      source_inverse_applied_integrable q (lambda-clock) shifted (sourceContactMap q reader force)
  have memory:=plane_noether_memory_integrable q reader force clock lambda positive shifted
  unfold IntegrableOn at initial contact memory ⊢
  with_reducible_and_instances
    simpa only [planeNoetherOperator,smul_add] using!
      Integrable.add (ε':=ResponseOp) (Integrable.add (ε':=ResponseOp) initial contact) memory

private theorem integral_three {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f g h : ℝ→E) (fi : IntegrableOn f (Ioi (0:ℝ))) (gi : IntegrableOn g (Ioi (0:ℝ)))
    (hi : IntegrableOn h (Ioi (0:ℝ))) :
    (∫t in Ioi (0:ℝ),f t+g t+h t)=
      (∫t in Ioi (0:ℝ),f t)+(∫t in Ioi (0:ℝ),g t)+(∫t in Ioi (0:ℝ),h t) := by
  unfold IntegrableOn at fi gi hi
  have outer:=integral_add (fi.add gi) hi
  have inner:=integral_add fi gi
  have first : (∫t in Ioi (0:ℝ),f t+g t+h t)=
      (∫t in Ioi (0:ℝ),f t+g t)+(∫t in Ioi (0:ℝ),h t) := by
    simpa only [Pi.add_apply] using! outer
  exact first.trans (congrArg (fun z : E=>z+(∫t in Ioi (0:ℝ),h t)) inner)

private theorem combine_images {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E→L[ℂ] E) (x y z : E) : z+A x+A y=z+A (x+y) := by
  rw [map_add,add_assoc]

/-- The two source inverse clocks follow from the original ordered histories, without a new inverse premise. -/
theorem plane_noether_operator_inverse (q : PhysicalResponsePoint) (reader force : Field289)
    (clock lambda : ℂ) (positive : 0<lambda.re) (shifted : 0<(lambda-clock).re) :
    (∫t in Ioi (0:ℝ),laplaceWeight lambda t • planeNoetherOperator q reader force clock t)=
      planeNoetherInverse q reader force clock lambda := by
  have initial := source_inverse_applied_integrable q lambda positive (sourceMaterialMap q reader force)
  have contact := source_inverse_applied_integrable q (lambda-clock) shifted (sourceContactMap q reader force)
  have memory:=plane_noether_memory_integrable q reader force clock lambda positive shifted
  have distribute:=integral_three
    (fun t=>laplaceWeight lambda t • twoTimeMap q t (sourceMaterialMap q reader force))
    (fun t=>laplaceWeight (lambda-clock) t • twoTimeMap q t (sourceContactMap q reader force))
    (fun t=>laplaceWeight lambda t • planeNoetherMemory q reader force clock t) initial contact memory
  have source : (∫t in Ioi (0:ℝ),laplaceWeight lambda t • planeNoetherOperator q reader force clock t)=
      (∫t in Ioi (0:ℝ),laplaceWeight lambda t • twoTimeMap q t (sourceMaterialMap q reader force))+
      (∫t in Ioi (0:ℝ),laplaceWeight (lambda-clock) t • twoTimeMap q t (sourceContactMap q reader force))+
      (∫t in Ioi (0:ℝ),laplaceWeight lambda t • planeNoetherMemory q reader force clock t) := by
    simpa only [planeNoetherOperator,smul_add,plane_initial_weighted,plane_contact_weighted] using! distribute
  have initialRead:=source_inverse_applied_read q lambda positive (sourceMaterialMap q reader force)
  have contactRead:=source_inverse_applied_read q (lambda-clock) shifted (sourceContactMap q reader force)
  have memoryRead:=plane_noether_memory_inverse q reader force clock lambda positive shifted
  have read:=congrArg₂ (fun x y : ResponseOp=>x+y)
    (congrArg₂ (fun x y : ResponseOp=>x+y) initialRead contactRead) memoryRead
  have combined : sourceInverse q lambda (sourceMaterialMap q reader force)+
      sourceInverse q (lambda-clock) (sourceContactMap q reader force)+
      sourceInverse q (lambda-clock) (driveOperator q force (sourceInverse q lambda (rawInitial q reader)))=
      planeNoetherInverse q reader force clock lambda := by
    unfold planeNoetherInverse
    exact combine_images (sourceInverse q (lambda-clock)) (sourceContactMap q reader force)
      (driveOperator q force (sourceInverse q lambda (rawInitial q reader)))
      (sourceInverse q lambda (sourceMaterialMap q reader force))
  exact source.trans (read.trans combined)

private theorem plane_memory_continuous (q : PhysicalResponsePoint) (reader force : Field289)
    (clock : ℂ) (t : ℝ) : Continuous (fun s : ℝ=>Complex.exp ((s:ℂ)*clock) • noetherMemoryMap q reader t s force) := by
  have exponential : Continuous (fun s : ℝ=>Complex.exp ((s:ℂ)*clock)) := by fun_prop
  have raw : Continuous (fun s : ℝ=>twoTimeMap q (t-s) (rawInitial q reader)) :=
    (ContinuousLinearMap.apply ℂ ResponseOp (rawInitial q reader)).continuous.comp
      ((twoTimeMap_continuous q).comp (continuous_const.sub continuous_id))
  have drive := (driveOperator q force).continuous.comp raw
  have memory := (twoTimeMap_continuous q).clm_apply drive
  have same : (fun s : ℝ=>noetherMemoryMap q reader t s force)=
      (fun s=>twoTimeMap q s (driveOperator q force (twoTimeMap q (t-s) (rawInitial q reader)))) :=
    funext (noether_memory_convolution q reader force t)
  have weightedSame := congrArg
    (fun h : ℝ→ResponseOp=>fun s : ℝ=>Complex.exp ((s:ℂ)*clock) • h s) same
  exact (exponential.smul memory).congr (fun s=>congrFun weightedSame.symm s)

theorem plane_noether_observer (q : PhysicalResponsePoint) (reader force : Field289)
    (observer : ResponseOp→L[ℂ]ℂ) (clock : ℂ) (t : ℝ) :
    observer (planeNoetherOperator q reader force clock t)=
      observer (noetherInitialMap q reader t force)+
        Complex.exp ((t:ℂ)*clock)*observer (noetherContactMap q reader t force)+
        ∫s in (0:ℝ)..t,Complex.exp ((s:ℂ)*clock)*observer (noetherMemoryMap q reader t s force) := by
  have read:=observer.intervalIntegral_comp_comm
    ((plane_memory_continuous q reader force clock t).intervalIntegrable (μ:=volume) 0 t)
  unfold planeNoetherOperator planeNoetherMemory
  simp only [map_add,map_smul,smul_eq_mul]
  exact congrArg (fun z : ℂ=>observer (noetherInitialMap q reader t force)+
    Complex.exp ((t:ℂ)*clock)*observer (noetherContactMap q reader t force)+z)
      (by simpa only [map_smul,smul_eq_mul] using! read.symm)

end LowEnergy.GaussComposite.ActualDressedFrequencyInverse
