import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceCurrentTimeTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronFullNoetherMixedSoft
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumNoetherOrdinaryWard
open ActualEMJointCurrentMomentum ActualElectronPhysicalJointInverse ActualElectronWholeChargeSoft
open PreparationVacuumNoetherChart PreparationVacuumGaugeSourceInjection
open ActualElectronWholeNoetherObserver ActualDressedFullCoulomb ActualDressedNoether
open SourceFamilyHilbert SourceFamilyOperator Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] actualFullNoetherVariation jointResolvent jointCurrent jointHessian
  physicalTime noetherReader noetherReaderContact rawReaderContact timeSlope mixedVertex

/-- All five original derivative factors vary through their actual momentum producers. -/
theorem actual_complete_J_transfer_continuous (event : DressedEvent) (reader force : Field289) (age : ℝ) :
    Continuous (fun k : PhysicalMomentum=>actualFullNoetherVariation event (-k) reader force age) := by
  have momentum : Continuous (fun k : PhysicalMomentum=>event.momentum+k):=
    (continuous_const (y:=event.momentum)).add continuous_id
  have tl :=(actual_noether_physical_time_momentum_continuous event.frame (-age)).comp momentum
  have l :=(actual_electron_physical_resolvent_continuous event.frame event.energy event.nonreal).comp momentum
  have dtl :=(actual_full_time_slope_momentum_continuous event.frame force (-age)).comp momentum
  have current :=(joint_current_momentum_continuous event.frame event.energy).clm_apply (continuous_const (y:=force))
  have dl :=((l.mul (current.comp momentum)).mul l).neg
  have dJ : Continuous (fun _ : PhysicalMomentum=>noetherReaderContact reader force event.momentum event.frame):=continuous_const
  have J : Continuous (fun _ : PhysicalMomentum=>noetherReader reader event.momentum event.frame 0):=continuous_const
  have R : Continuous (fun _ : PhysicalMomentum=>jointResolvent event.momentum event.frame event.energy 0):=continuous_const
  have dR : Continuous (fun _ : PhysicalMomentum=>-(jointResolvent event.momentum event.frame event.energy 0*
      jointCurrent event.momentum event.frame event.energy 0 force*jointResolvent event.momentum event.frame event.energy 0)):=continuous_const
  have TR : Continuous (fun _ : PhysicalMomentum=>physicalTime event.momentum event.frame age 0):=continuous_const
  have dTR : Continuous (fun _ : PhysicalMomentum=>timeSlope force event.momentum event.frame age):=continuous_const
  have generated:=(((((dtl.mul l).add (tl.mul dl)).mul J).add ((tl.mul l).mul dJ)).mul R |>.add
    (((tl.mul l).mul J).mul dR)).mul TR |>.add ((((tl.mul l).mul J).mul R).mul dTR)
  simpa only [actualFullNoetherVariation,sub_neg_eq_add,Function.comp_def,Pi.mul_apply,Pi.add_apply,Pi.neg_apply] using! generated

/-- The two original current words and the mixed Hessian contact are retained on the actual joint family. -/
theorem actual_original_mixed_transfer_continuous (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z w : ℂ) (hz : z.im≠0) (f g : Field289) :
    Continuous (fun k : PhysicalMomentum=>mixedVertex f g p k F z w) := by
  have momentum : Continuous (fun k : PhysicalMomentum=>p+k):=(continuous_const (y:=p)).add continuous_id
  have L :=(actual_electron_physical_resolvent_continuous F z hz).comp momentum
  have current :=(joint_current_momentum_continuous F z).clm_apply (continuous_const (y:=f))
  have first :=(((L.mul (current.comp momentum)).mul L).mul_const (jointCurrent p F w 0 g)).mul_const (jointResolvent p F w 0)
  have second :=(((L.mul_const (jointCurrent p F w 0 g)).mul_const (jointResolvent p F w 0)).mul_const
    (jointCurrent p F w 0 f)).mul_const (jointResolvent p F w 0)
  have contact :=(L.mul_const (jointHessian p F w f g)).mul_const (jointResolvent p F w 0)
  simpa only [mixedVertex,Function.comp_def,Pi.mul_apply,Pi.add_apply,Pi.sub_apply] using! (first.add second).sub contact

/-- The original corrected contact keeps its raw subtraction, both physical times and both actual inverses. -/
def actualCorrectedContact (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (age : ℝ) : H→L[ℂ]H :=
  physicalTime (event.momentum-transfer) event.frame (-age) 0*
    jointResolvent (event.momentum-transfer) event.frame event.energy 0*
      (noetherReaderContact reader force event.momentum event.frame-rawReaderContact reader force event.momentum event.frame)*
    jointResolvent event.momentum event.frame event.energy 0*physicalTime event.momentum event.frame age 0

attribute [local irreducible] actualCorrectedContact

theorem actual_corrected_contact_original (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (age : ℝ) :
    actualCorrectedContact event transfer reader force age=
      (correctedContactJet (dressedKinematicPoint event transfer) reader force age).value := by
  simp only [actualCorrectedContact,correctedContactJet,jetMul,jetConst,physicalTimeJet,timeJet,
    physicalTime,dressedKinematicPoint,sub_eq_add_neg,neg_one_mul,one_mul,add_zero]

theorem actual_corrected_contact_transfer_continuous (event : DressedEvent) (reader force : Field289) (age : ℝ) :
    Continuous (fun k : PhysicalMomentum=>actualCorrectedContact event (-k) reader force age) := by
  have momentum : Continuous (fun k : PhysicalMomentum=>event.momentum+k):=
    (continuous_const (y:=event.momentum)).add continuous_id
  have TL :=(actual_noether_physical_time_momentum_continuous event.frame (-age)).comp momentum
  have L :=(actual_electron_physical_resolvent_continuous event.frame event.energy event.nonreal).comp momentum
  have generated:=((TL.mul L).mul_const
    (noetherReaderContact reader force event.momentum event.frame-rawReaderContact reader force event.momentum event.frame)).mul_const
    (jointResolvent event.momentum event.frame event.energy 0) |>.mul_const (physicalTime event.momentum event.frame age 0)
  simpa only [actualCorrectedContact,sub_neg_eq_add,Function.comp_def,Pi.mul_apply] using! generated

private theorem simultaneous_modulus {P E : Type*} [NormedAddCommGroup P] [NormedAddCommGroup E]
    (f g h : P→E) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃radius : ℝ,0<radius ∧ ∀k : P,‖k‖<radius→
      ‖f k-f 0‖<epsilon ∧ ‖g k-g 0‖<epsilon ∧ ‖h k-h 0‖<epsilon := by
  obtain ⟨rf,pf,bf⟩:=Metric.continuousAt_iff.mp hf.continuousAt epsilon positive
  obtain ⟨rg,pg,bg⟩:=Metric.continuousAt_iff.mp hg.continuousAt epsilon positive
  obtain ⟨rh,ph,bh⟩:=Metric.continuousAt_iff.mp hh.continuousAt epsilon positive
  refine ⟨min rf (min rg rh),lt_min pf (lt_min pg ph),fun k small=>⟨?_,?_,?_⟩⟩
  · simpa only [dist_eq_norm] using bf (x:=k) (by
      simpa only [dist_eq_norm,sub_zero] using small.trans_le (min_le_left rf (min rg rh)))
  · simpa only [dist_eq_norm] using bg (x:=k) (by
      simpa only [dist_eq_norm,sub_zero] using small.trans_le ((min_le_right rf (min rg rh)).trans (min_le_left rg rh)))
  · simpa only [dist_eq_norm] using bh (x:=k) (by
      simpa only [dist_eq_norm,sub_zero] using small.trans_le ((min_le_right rf (min rg rh)).trans (min_le_right rg rh)))

/-- A simultaneous source-generated modulus covers the full response, true mixed contact and corrected-minus-raw contact. -/
theorem actual_complete_response_modulus (event : DressedEvent) (reader force : Field289) (age epsilon : ℝ)
    (positive : 0<epsilon) : ∃radius : ℝ,0<radius ∧ ∀k : PhysicalMomentum,‖k‖<radius→
      ‖actualFullNoetherVariation event (-k) reader force age-actualFullNoetherVariation event 0 reader force age‖<epsilon ∧
      ‖mixedVertex force reader event.momentum k event.frame event.energy event.energy-
        mixedVertex force reader event.momentum 0 event.frame event.energy event.energy‖<epsilon ∧
      ‖actualCorrectedContact event (-k) reader force age-actualCorrectedContact event 0 reader force age‖<epsilon := by
  have generated:=simultaneous_modulus
    (fun k : PhysicalMomentum=>actualFullNoetherVariation event (-k) reader force age)
    (fun k : PhysicalMomentum=>mixedVertex force reader event.momentum k event.frame event.energy event.energy)
    (fun k : PhysicalMomentum=>actualCorrectedContact event (-k) reader force age)
    (actual_complete_J_transfer_continuous event reader force age)
    (actual_original_mixed_transfer_continuous event.momentum event.frame event.energy event.energy event.nonreal force reader)
    (actual_corrected_contact_transfer_continuous event reader force age) epsilon positive
  simpa only [neg_zero] using! generated

end LowEnergy.GaussComposite.ActualElectronFullNoetherMixedSoft
