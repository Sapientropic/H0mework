import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeDeviationReader
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherAction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedLockedWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumFullFieldRiesz PreparationVacuumNoetherChart
open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction
open PreparationVacuumPropagationPencil
open SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSourcePreparation
open Filter
open scoped Matrix BigOperators InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] dressedEulerObserver jointResolvent noetherReader rawReader rawReaderContact
  physicalTime timeSlope jointCurrent noetherReaderContact nativeReader nativeReaderContact
  nativeDeviationReader nativeDeviationReaderContact noetherHistoryOperatorJet nativeSourceColumn
 def nativeDeviationPreparedKernel (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ)
    (h : Field289) (age : ℝ) : Operator:=
  physicalTime (q.p+q.k) q.F (-age) h*jointResolvent (q.p+q.k) q.F q.z h*
    nativeDeviationReader n theta q.p q.F h*jointResolvent q.p q.F q.w h*physicalTime q.p q.F age h

 def nativeDeviationPreparedFive (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ)
    (force : Field289) (age : ℝ) : Operator:=
  (((timeSlope force (q.p+q.k) q.F (-age)*jointResolvent (q.p+q.k) q.F q.z 0+
      physicalTime (q.p+q.k) q.F (-age) 0*(-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 force*jointResolvent (q.p+q.k) q.F q.z 0)))*
        nativeDeviationReader n theta q.p q.F 0+
      (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0)*
        nativeDeviationReaderContact n theta force q.p q.F)*jointResolvent q.p q.F q.w 0+
      (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0*
        nativeDeviationReader n theta q.p q.F 0)*(-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 force*jointResolvent q.p q.F q.w 0)))*physicalTime q.p q.F age 0+
    (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0*
      nativeDeviationReader n theta q.p q.F 0*jointResolvent q.p q.F q.w 0)*timeSlope force q.p q.F age

 theorem nativeDeviationPreparedFive_generated (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ)
    (force : Field289) (age : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>nativeDeviationPreparedKernel q n theta (r • force) age)
      (nativeDeviationPreparedFive q n theta force age) 0 :=by
  have tl:=physicalTime_direction force (q.p+q.k) q.F (-age)
  have rl:=inverse_direction (q.p+q.k) q.F q.z hz force
  have j:=native_deviation_reader_generated n theta force q.p q.F
  have rr:=inverse_direction q.p q.F q.w hw force
  have tr:=physicalTime_direction force q.p q.F age
  have actual:=((((tl.mul rl).mul j).mul rr).mul tr)
  convert! actual using 1
  simp only [nativeDeviationPreparedKernel,nativeDeviationPreparedFive,Pi.mul_apply,zero_smul]


private theorem product_five_contact {A : Type*} [Ring A]
    (a b c d e da db dc dd de raw : A) :
    (((da*b+a*db)*c+(a*b)*dc)*d+((a*b)*c)*dd)*e+(((a*b)*c)*d)*de=
      (da*b*c*d*e+a*db*c*d*e+a*b*raw*d*e+a*b*c*dd*e+a*b*c*d*de)+
        a*b*(dc-raw)*d*e := by
  simp only [add_mul,mul_sub,sub_mul]
  abel


theorem native_reference_original_operator_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) (reader : Field289) :
    HasDerivAt (fun r : ℝ=>dressedNoetherKernel event transfer reader age (r • force))
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) reader
        (fun _=>⟨force,0,0⟩) age).value 0 := by
  have tl:=physicalTime_direction force (event.momentum-transfer) event.frame (-age)
  have rl:=inverse_direction (event.momentum-transfer) event.frame event.energy event.nonreal force
  have readpaid:=noetherReader_generated reader force event.momentum event.frame
  have rr:=inverse_direction event.momentum event.frame event.energy event.nonreal force
  have tr:=physicalTime_direction force event.momentum event.frame age
  have generated:=(((tl.mul rl).mul readpaid).mul rr).mul tr
  simp only [Pi.mul_apply,zero_smul,noetherReader_source] at generated
  have value:=noetherHistoryOperatorJet_value (dressedKinematicPoint event transfer) reader
    (fun _=>⟨force,0,0⟩) age
  rw [historyOperator_constant] at value
  have algebra:=product_five_contact
    (physicalTime (event.momentum-transfer) event.frame (-age) 0)
    (jointResolvent (event.momentum-transfer) event.frame event.energy 0)
    (rawReader reader event.momentum event.frame 0)
    (jointResolvent event.momentum event.frame event.energy 0)
    (physicalTime event.momentum event.frame age 0)
    (timeSlope force (event.momentum-transfer) event.frame (-age))
    (-(jointResolvent (event.momentum-transfer) event.frame event.energy 0*
      jointCurrent (event.momentum-transfer) event.frame event.energy 0 force*
      jointResolvent (event.momentum-transfer) event.frame event.energy 0))
    (noetherReaderContact reader force event.momentum event.frame)
    (-(jointResolvent event.momentum event.frame event.energy 0*
      jointCurrent event.momentum event.frame event.energy 0 force*
      jointResolvent event.momentum event.frame event.energy 0))
    (timeSlope force event.momentum event.frame age)
    (rawReaderContact reader force event.momentum event.frame)
  have corrected:=generated.congr_deriv (show _=
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) reader
        (fun _=>⟨force,0,0⟩) age).value from by
    rw [value]
    simpa only [dressedKinematicPoint,sub_eq_add_neg,fiveDerivative] using! algebra)
  simpa only [dressedNoetherKernel,Pi.mul_apply] using! corrected


private theorem product_middle_sub {A : Type*} [Ring A] (a b x y c d : A) :
    a*b*(x-y)*c*d=a*b*x*c*d-a*b*y*c*d := by
  simp only [mul_sub,sub_mul]

/-- The same actual N2 creation and unchanged source background observe both complete two-leg kernels. -/
theorem native_reference_actual_kernel (event : DressedEvent) (transfer : PhysicalMomentum)
    (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) (age : ℝ) :
    (fun h=>dressedEulerObserver event
      (dressedNoetherKernel event transfer (nativeSourceColumn n theta gradient) age h))=ᶠ[𝓝 0]
    fun h=>dressedEulerObserver event
      (nativePreparedKernel (dressedKinematicPoint event transfer) n theta gradient h age-
        nativeDeviationPreparedKernel (dressedKinematicPoint event transfer) n theta h age) := by
  filter_upwards [native_reference_reader_germ n theta gradient event.momentum event.frame] with h paid
  simp only [dressedNoetherKernel,nativePreparedKernel,nativeDeviationPreparedKernel,dressedKinematicPoint]
  rw [paid]
  simpa only [sub_eq_add_neg] using congrArg (dressedEulerObserver event)
    (product_middle_sub (physicalTime (event.momentum-transfer) event.frame (-age) h)
      (jointResolvent (event.momentum-transfer) event.frame event.energy h)
      (nativeReader n theta gradient event.momentum event.frame h)
      (nativeDeviationReader n theta event.momentum event.frame h)
      (jointResolvent event.momentum event.frame event.energy h)
      (physicalTime event.momentum event.frame age h))

/-- Full five-term differentiation retains both physical-time legs, both resolvents and the generated mixed contact. -/
theorem native_reference_actual_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>dressedEulerObserver event
      (dressedNoetherKernel event transfer (nativeSourceColumn n theta gradient) age (r • force)))
      (dressedEulerObserver event
        (nativePreparedFive (dressedKinematicPoint event transfer) n theta gradient force age-
          nativeDeviationPreparedFive (dressedKinematicPoint event transfer) n theta force age)) 0 := by
  have native:=nativePreparedFive_generated (dressedKinematicPoint event transfer) n theta gradient force age
    event.nonreal event.nonreal
  have deviation:=nativeDeviationPreparedFive_generated (dressedKinematicPoint event transfer) n theta force age
    event.nonreal event.nonreal
  have observed:=((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (native.sub deviation)
  exact observed.congr_of_eventuallyEq ((native_reference_actual_kernel event transfer n theta gradient age).comp_tendsto
    (by simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto))


/-- The original full Noether response on this symmetry column returns the source-native response minus its generated preparation/configuration term. -/
theorem native_reference_actual_noether (event : DressedEvent) (transfer : PhysicalMomentum)
    (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) (force : Field289) (age : ℝ) :
    dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer)
        (nativeSourceColumn n theta gradient) (fun _=>⟨force,0,0⟩) age).value=
      dressedEulerObserver event
        (nativePreparedFive (dressedKinematicPoint event transfer) n theta gradient force age)-
      dressedEulerObserver event
        (nativeDeviationPreparedFive (dressedKinematicPoint event transfer) n theta force age) := by
  have original:=native_reference_original_operator_derivative event transfer force age (nativeSourceColumn n theta gradient)
  have observed:=((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 original
  have returned:=observed.unique (native_reference_actual_derivative event transfer n theta gradient force age)
  simpa only [map_sub,ContinuousLinearMap.coe_restrictScalars'] using returned


/-- The exact original causal layout: initial material variation, reading-time contact, and the two ordered time legs. -/
def nativeWardHistory (q : PhysicalResponsePoint) (reader : Operator) (contact : Field289→Operator)
    (history : ℝ→Field289) (t : ℝ) : Operator :=
  orderedDual q history t*(jointResolvent (q.p+q.k) q.F q.z 0*reader*jointResolvent q.p q.F q.w 0)*
      physicalTime q.p q.F t 0+
  physicalTime (q.p+q.k) q.F (-t) 0*
    ((-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 (history 0)*jointResolvent (q.p+q.k) q.F q.z 0))*
      reader*jointResolvent q.p q.F q.w 0+
    jointResolvent (q.p+q.k) q.F q.z 0*contact (history t)*jointResolvent q.p q.F q.w 0+
    jointResolvent (q.p+q.k) q.F q.z 0*reader*
      (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 (history 0)*jointResolvent q.p q.F q.w 0)))*
      physicalTime q.p q.F t 0+
  physicalTime (q.p+q.k) q.F (-t) 0*
    (jointResolvent (q.p+q.k) q.F q.z 0*reader*jointResolvent q.p q.F q.w 0)*orderedPrimal q history t

private theorem history_contact_algebra {A : Type*} [Ring A]
    (dl dr l r tl tr cl cr j old next : A) :
    (dl*(l*j*r)*tr+tl*((-cl)*j*r+l*old*r+l*j*(-cr))*tr+tl*(l*j*r)*dr)+
      tl*l*(next-old)*r*tr=
    dl*(l*j*r)*tr+tl*((-cl)*j*r+l*next*r+l*j*(-cr))*tr+tl*(l*j*r)*dr := by
  simp only [mul_sub,sub_mul,mul_add,add_mul,mul_assoc]
  abel

private theorem original_history_contact (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    (noetherHistoryOperatorJet q reader signal t).value=
      nativeWardHistory q (noetherReader reader q.p q.F 0)
        (fun force=>noetherReaderContact reader force q.p q.F) (fun s=>(signal s).value) t := by
  rw [noetherHistoryOperatorJet_value]
  simp only [historyOperator,historyMiddle,rawInitial,nativeWardHistory,noetherReader_source]
  exact history_contact_algebra _ _ _ _ _ _ _ _ _ _ _

private theorem history_sub_algebra {A : Type*} [Ring A]
    (dl dr l r tl tr cl cr x y c d : A) :
    dl*(l*(x-y)*r)*tr+tl*((-cl)*(x-y)*r+l*(c-d)*r+l*(x-y)*(-cr))*tr+
      tl*(l*(x-y)*r)*dr=
    (dl*(l*x*r)*tr+tl*((-cl)*x*r+l*c*r+l*x*(-cr))*tr+tl*(l*x*r)*dr)-
    (dl*(l*y*r)*tr+tl*((-cl)*y*r+l*d*r+l*y*(-cr))*tr+tl*(l*y*r)*dr) := by
  noncomm_ring

private theorem nativeWardHistory_sub (q : PhysicalResponsePoint) (A B : Operator)
    (C D : Field289→Operator) (history : ℝ→Field289) (t : ℝ) :
    nativeWardHistory q (A-B) (fun force=>C force-D force) history t=
      nativeWardHistory q A C history t-nativeWardHistory q B D history t := by
  unfold nativeWardHistory
  exact history_sub_algebra _ _ _ _ _ _ _ _ _ _ _ _

/-- The configuration/source preparation term is retained in the original arbitrary-history response, rather than inferred to vanish from background locking. -/
theorem native_reference_actual_history (event : DressedEvent) (transfer : PhysicalMomentum)
    (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) (signal : ℝ→SourceJet Field289) (t : ℝ) :
    dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer)
        (nativeSourceColumn n theta gradient) signal t).value=
    dressedEulerObserver event
      (nativeWardHistory (dressedKinematicPoint event transfer)
        (nativeReader n theta gradient event.momentum event.frame 0)
        (fun force=>nativeReaderContact n theta gradient force event.momentum event.frame)
        (fun s=>(signal s).value) t)-
    dressedEulerObserver event
      (nativeWardHistory (dressedKinematicPoint event transfer)
        (nativeDeviationReader n theta event.momentum event.frame 0)
        (fun force=>nativeDeviationReaderContact n theta force event.momentum event.frame)
        (fun s=>(signal s).value) t) := by
  have reader:=native_reference_reader n theta gradient event.momentum event.frame
  have contact : (fun force=>noetherReaderContact (nativeSourceColumn n theta gradient) force event.momentum event.frame)=
      fun force=>nativeReaderContact n theta gradient force event.momentum event.frame-
        nativeDeviationReaderContact n theta force event.momentum event.frame :=
    funext (fun force=>native_reference_reader_contact n theta gradient force event.momentum event.frame)
  have replaced := congrArg₂
    (fun (A : Operator) (C : Field289→Operator)=>nativeWardHistory (dressedKinematicPoint event transfer)
      A C (fun s=>(signal s).value) t) reader contact
  have split:=nativeWardHistory_sub (dressedKinematicPoint event transfer)
    (nativeReader n theta gradient event.momentum event.frame 0)
    (nativeDeviationReader n theta event.momentum event.frame 0)
    (fun force=>nativeReaderContact n theta gradient force event.momentum event.frame)
    (fun force=>nativeDeviationReaderContact n theta force event.momentum event.frame)
    (fun s=>(signal s).value) t
  have original:=congrArg (dressedEulerObserver event)
    (original_history_contact (dressedKinematicPoint event transfer) (nativeSourceColumn n theta gradient) signal t)
  exact original.trans ((congrArg (dressedEulerObserver event) (replaced.trans split)).trans
    ((dressedEulerObserver event).map_sub _ _))

end LowEnergy.GaussComposite.ActualDressedLockedWard
