import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeFields
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeComplex
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativePreparedWard

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNullNative
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumFullFieldRiesz PreparationVacuumNoetherChart
open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction
open PreparationVacuumSourceFieldFamily PreparationVacuumOriginalDensity
open PreparationVacuumPropagationPencil
open SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSourcePreparation ActualDressedLockedWard
open scoped Matrix BigOperators
attribute [local irreducible] dressedEulerObserver jointResolvent physicalTime jointCurrent nativeWardHistory
  nativeReader nativeReaderContact nativeDeviationReader nativeDeviationReaderContact

/-- The uncontracted original remainder retains every matter, independent-dual, BF, and simplicity slot. -/
def originalNullRemainder (p : Fin 4→ℝ) (n : Fin 9) : Field289:=
  originalNullReal p n-nativeSourceColumn n 1 p

theorem original_null_remainder_state (p : Fin 4→ℝ) (n : Fin 9) :
    fieldDirection (originalNullRemainder p n)=0 :=by
  change fieldDirectionLinear (originalNullReal p n-nativeSourceColumn n 1 p)=0
  rw [map_sub]
  change fieldDirection (originalNullReal p n)-fieldDirection (nativeSourceColumn n 1 p)=0
  rw [original_null_native_state,nativeSourceColumn_state,sub_self]

private theorem state_gradient_part (n : Fin 9) (gradient : Fin 4→ℝ) (s : ActionState) :
    stateVariation n 1 gradient s-stateVariation n 1 0 s=stateVariation n 0 gradient s :=by
  apply Prod.ext
  · change ((1:ℝ) • nativeFrameGenerator n)*s.1-((1:ℝ) • nativeFrameGenerator n)*s.1=((0:ℝ) • nativeFrameGenerator n)*s.1
    simp only [one_smul,zero_smul,zero_mul,sub_self]
  apply Prod.ext
  · funext mu
    change ((1:ℝ) • (nativeMatterGenerator n*s.2.1 mu-s.2.1 mu*nativeMatterGenerator n)-gradient mu • nativeMatterGenerator n)-
      ((1:ℝ) • (nativeMatterGenerator n*s.2.1 mu-s.2.1 mu*nativeMatterGenerator n)-(0:ℝ) • nativeMatterGenerator n)=
      (0:ℝ) • (nativeMatterGenerator n*s.2.1 mu-s.2.1 mu*nativeMatterGenerator n)-gradient mu • nativeMatterGenerator n
    simp only [one_smul,zero_smul,sub_zero,zero_sub]
    abel
  · change ((1:ℝ) • (nativeMatterGenerator n*s.2.2-s.2.2*nativeMatterGenerator n))-
      ((1:ℝ) • (nativeMatterGenerator n*s.2.2-s.2.2*nativeMatterGenerator n))=
      (0:ℝ) • (nativeMatterGenerator n*s.2.2-s.2.2*nativeMatterGenerator n)
    simp only [one_smul,zero_smul,sub_self]

/-- Fourier imaginary coefficients carry zero parameter value and the imaginary parameter gradient. -/
theorem original_null_imaginary_state (p : Fin 4→ℂ) (n : Fin 9) :
    fieldDirection (fun row=>(originalNullColumn p n row).im)=
      stateVariation n 0 (fun mu=>(p mu).im) (sourceState sourcePoint.val) :=by
  rw [original_null_imaginary_part]
  change fieldDirectionLinear (_-_)=_
  rw [map_sub]
  change fieldDirection (originalNullReal (fun mu=>(p mu).im) n)-fieldDirection (originalNullReal 0 n)=_
  rw [original_null_native_state,original_null_native_state,state_gradient_part]

private theorem noether_reader_congr (f g : Field289) (same : fieldDirection f=fieldDirection g)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : noetherReader f p F=noetherReader g p F :=by
  have density (base candidate : ActionState) :
      transportedDensity f base candidate=transportedDensity g base candidate :=by
    funext i
    simp only [transportedDensity,densityVariation,lowerVariation,principalVariation,same]
  funext h
  simp only [noetherReader,noetherForm,noetherSample,noetherFiber,transportedRawSymbol,density]

/-- The complete original source column and the native reference variation have the same actual transported reader, on the whole configuration family. -/
theorem original_null_noether_reader (gradient : Fin 4→ℝ) (n : Fin 9)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader (originalNullReal gradient n) p F=noetherReader (nativeSourceColumn n 1 gradient) p F :=by
  exact noether_reader_congr _ _ ((original_null_native_state gradient n).trans
    (nativeSourceColumn_state n 1 gradient).symm) p F

theorem original_null_imaginary_noether_reader (clock : Fin 4→ℂ) (n : Fin 9)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader (fun row=>(originalNullColumn clock n row).im) p F=
      noetherReader (nativeSourceColumn n 0 (fun mu=>(clock mu).im)) p F :=by
  exact noether_reader_congr _ _ ((original_null_imaginary_state clock n).trans
    (nativeSourceColumn_state n 0 (fun mu=>(clock mu).im)).symm) p F

theorem original_null_noether_contact (gradient : Fin 4→ℝ) (n : Fin 9) (force : Field289)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReaderContact (originalNullReal gradient n) force p F=
      noetherReaderContact (nativeSourceColumn n 1 gradient) force p F :=by
  rw [noetherReaderContact,original_null_noether_reader,noetherReaderContact]

private theorem history_contact_algebra {A : Type*} [Ring A]
    (dl dr l r tl tr cl cr j old next : A) :
    (dl*(l*j*r)*tr+tl*((-cl)*j*r+l*old*r+l*j*(-cr))*tr+tl*(l*j*r)*dr)+
      tl*l*(next-old)*r*tr=
    dl*(l*j*r)*tr+tl*((-cl)*j*r+l*next*r+l*j*(-cr))*tr+tl*(l*j*r)*dr :=by
  simp only [mul_sub,sub_mul,mul_add,add_mul,mul_assoc]
  abel

private theorem history_native_layout (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    (noetherHistoryOperatorJet q reader signal t).value=
      nativeWardHistory q (noetherReader reader q.p q.F 0)
        (fun force=>noetherReaderContact reader force q.p q.F) (fun s=>(signal s).value) t :=by
  rw [noetherHistoryOperatorJet_value]
  simp only [historyOperator,historyMiddle,rawInitial,nativeWardHistory,noetherReader_source]
  exact history_contact_algebra _ _ _ _ _ _ _ _ _ _ _

/-- The opposite-clock consumer may use this before applying its same actual quantum observer. -/
theorem original_null_imaginary_history (q : PhysicalResponsePoint) (clock : Fin 4→ℂ)
    (n : Fin 9) (signal : ℝ→SourceJet Field289) (t : ℝ) :
    (noetherHistoryOperatorJet q (fun row=>(originalNullColumn clock n row).im) signal t).value=
      (noetherHistoryOperatorJet q (nativeSourceColumn n 0 (fun mu=>(clock mu).im)) signal t).value :=by
  rw [history_native_layout,history_native_layout,original_null_imaginary_noether_reader]
  simp only [noetherReaderContact,original_null_imaginary_noether_reader]

/-- Same actual creation-minus-background observation, with both ordered legs, the initial variation and read contact retained. -/
theorem original_null_actual_history (event : DressedEvent) (transfer : PhysicalMomentum)
    (n : Fin 9) (gradient : Fin 4→ℝ) (signal : ℝ→SourceJet Field289) (t : ℝ) :
    dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer)
        (originalNullReal gradient n) signal t).value=
    dressedEulerObserver event
      (nativeWardHistory (dressedKinematicPoint event transfer)
        (nativeReader n 1 gradient event.momentum event.frame 0)
        (fun force=>nativeReaderContact n 1 gradient force event.momentum event.frame)
        (fun s=>(signal s).value) t)-
    dressedEulerObserver event
      (nativeWardHistory (dressedKinematicPoint event transfer)
        (nativeDeviationReader n 1 event.momentum event.frame 0)
        (fun force=>nativeDeviationReaderContact n 1 force event.momentum event.frame)
        (fun s=>(signal s).value) t) :=by
  have same : (noetherHistoryOperatorJet (dressedKinematicPoint event transfer)
      (originalNullReal gradient n) signal t).value=
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer)
        (nativeSourceColumn n 1 gradient) signal t).value :=by
    rw [history_native_layout,history_native_layout,original_null_noether_reader]
    simp_rw [original_null_noether_contact]
  rw [same]
  exact native_reference_actual_history event transfer n 1 gradient signal t

end LowEnergy.GaussComposite.ActualDressedNullNative
