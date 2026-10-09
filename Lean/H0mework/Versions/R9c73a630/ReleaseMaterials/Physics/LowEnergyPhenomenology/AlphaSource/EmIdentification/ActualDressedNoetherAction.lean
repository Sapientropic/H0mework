import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherResponse

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNoether
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumFullFieldRiesz
open PreparationVacuumNoetherChart SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime
open ActualDressedFullCoulomb
open ActualDressedSourcePreparation PreparationVacuumSourcePreparedResponse GaussComposite.SourceGraph
open scoped Matrix BigOperators InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] dressedEulerObserver jointResolvent noetherReader rawReader rawReaderContact
  physicalTime timeSlope jointCurrent noetherReaderContact noetherHistoryOperatorJet historyOperator dressedNoetherJet

private theorem product_five_contact {A : Type*} [Ring A]
    (a b c d e da db dc dd de raw : A) :
    (((da*b+a*db)*c+(a*b)*dc)*d+((a*b)*c)*dd)*e+(((a*b)*c)*d)*de=
      (da*b*c*d*e+a*db*c*d*e+a*b*raw*d*e+a*b*c*dd*e+a*b*c*d*de)+
        a*b*(dc-raw)*d*e := by
  simp only [add_mul,mul_sub,sub_mul]
  abel

/-- The actual nonlinear Noether insertion uses the original uncut retainer and physical time. -/
def dressedNoetherKernel (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) (h : Field289) : H→L[ℂ]H :=
  physicalTime (event.momentum-transfer) event.frame (-age) h*
    jointResolvent (event.momentum-transfer) event.frame event.energy h*
      noetherReader reader event.momentum event.frame h*
    jointResolvent event.momentum event.frame event.energy h*
  physicalTime event.momentum event.frame age h

theorem dressed_noether_history_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (age : ℝ) (i : Fin 289) :
    (dressedNoetherJet event transfer signal age i).value=
      dressedEulerObserver event
        (historyOperator (dressedKinematicPoint event transfer) (fieldUnit i)
          (fun t=>(signal t).value) age)+
      dressedEulerObserver event
        (physicalTime (event.momentum-transfer) event.frame (-age) 0*
          jointResolvent (event.momentum-transfer) event.frame event.energy 0*
          (noetherReaderContact (fieldUnit i) (signal age).value event.momentum event.frame-
            rawReaderContact (fieldUnit i) (signal age).value event.momentum event.frame)*
          jointResolvent event.momentum event.frame event.energy 0*
          physicalTime event.momentum event.frame age 0) := by
  rw [dressed_noether_jet_original]
  have original:=congrArg (dressedEulerObserver event)
    (noetherHistoryOperatorJet_value (dressedKinematicPoint event transfer) (fieldUnit i) signal age)
  simpa only [map_add,dressedKinematicPoint,sub_eq_add_neg] using! original

private theorem dressed_noether_operator_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) (i : Fin 289) :
    HasDerivAt (fun r : ℝ=>dressedNoetherKernel event transfer (fieldUnit i) age (r • force))
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i)
        (fun _=>⟨force,0,0⟩) age).value 0 := by
  have tl:=physicalTime_direction force (event.momentum-transfer) event.frame (-age)
  have rl:=inverse_direction (event.momentum-transfer) event.frame event.energy event.nonreal force
  have reader:=noetherReader_generated (fieldUnit i) force event.momentum event.frame
  have rr:=inverse_direction event.momentum event.frame event.energy event.nonreal force
  have tr:=physicalTime_direction force event.momentum event.frame age
  have generated:=(((tl.mul rl).mul reader).mul rr).mul tr
  simp only [Pi.mul_apply,zero_smul,noetherReader_source] at generated
  have value:=noetherHistoryOperatorJet_value (dressedKinematicPoint event transfer) (fieldUnit i)
    (fun _=>⟨force,0,0⟩) age
  rw [historyOperator_constant] at value
  have algebra:=product_five_contact
    (physicalTime (event.momentum-transfer) event.frame (-age) 0)
    (jointResolvent (event.momentum-transfer) event.frame event.energy 0)
    (rawReader (fieldUnit i) event.momentum event.frame 0)
    (jointResolvent event.momentum event.frame event.energy 0)
    (physicalTime event.momentum event.frame age 0)
    (timeSlope force (event.momentum-transfer) event.frame (-age))
    (-(jointResolvent (event.momentum-transfer) event.frame event.energy 0*
      jointCurrent (event.momentum-transfer) event.frame event.energy 0 force*
      jointResolvent (event.momentum-transfer) event.frame event.energy 0))
    (noetherReaderContact (fieldUnit i) force event.momentum event.frame)
    (-(jointResolvent event.momentum event.frame event.energy 0*
      jointCurrent event.momentum event.frame event.energy 0 force*
      jointResolvent event.momentum event.frame event.energy 0))
    (timeSlope force event.momentum event.frame age)
    (rawReaderContact (fieldUnit i) force event.momentum event.frame)
  have corrected:=generated.congr_deriv (show _=
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i)
        (fun _=>⟨force,0,0⟩) age).value from by
    rw [value]
    simpa only [dressedKinematicPoint,sub_eq_add_neg,fiveDerivative] using! algebra)
  simpa only [dressedNoetherKernel,Pi.mul_apply] using! corrected

/-- The complete five-term quantum response is a derivative of this same actual insertion. -/
theorem dressed_noether_action_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) (i : Fin 289) :
    HasDerivAt (fun r : ℝ=>dressedEulerObserver event
        (dressedNoetherKernel event transfer (fieldUnit i) age (r • force)))
      (dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) age i).value 0 := by
  have original:=dressed_noether_operator_derivative event transfer force age i
  have observed:=((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 original
  rw [dressed_noether_jet_original]
  exact observed

end LowEnergy.GaussComposite.ActualDressedNoether
