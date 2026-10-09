import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberFieldBackground

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberField
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open PreparationVacuumNoetherChart
open ActualDressedNoether ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedNumberZero
open GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open Filter
open scoped Topology InnerProductSpace
local instance noetherFieldReal : NormedAlgebra ℝ ActualDressedNumberZero.Op:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] dressedNoetherKernel dressedEulerObserver physicalTime jointResolvent noetherReader sourceDressedUnit
  jointCompression jointCResolvent jointN1GreenWords jointN2GreenWords
  prepared sourceProfile

/-- Same original field read: left C(h), right finite Green words, original right time, complete reader and original background. -/
def numberFieldRead (event : DressedEvent) (transfer : PhysicalMomentum) (reader : Field289) (age : ℝ) (h : Field289) : ℂ :=
  -inner ℂ (sourceDressedUnit event.epsilon event.precision)
    (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-age)
      (jointCResolvent (event.momentum-transfer) event.frame event.energy h
        (noetherReader reader event.momentum event.frame h
          (jointN2GreenWords event.momentum event.frame event.energy h
            (physicalTime event.momentum event.frame age h (sourceDressedUnit event.epsilon event.precision))))))+
  inner ℂ (prepared (sourceProfile event.epsilon event.precision))
    (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-age)
      (jointCResolvent (event.momentum-transfer) event.frame event.energy h
        (noetherReader reader event.momentum event.frame h
          (jointN1GreenWords event.momentum event.frame event.energy h
            (physicalTime event.momentum event.frame age h (prepared (sourceProfile event.epsilon event.precision)))))))

attribute [local irreducible] numberFieldRead

private theorem left_word (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ)
    (t : ℝ) (h : Field289)
    (green : gradeZeroProjection*jointResolvent p F z h=gradeZeroProjection*jointCResolvent p F z h) :
    gradeZeroProjection*physicalTime p F t h*jointResolvent p F z h=
      gradeZeroProjection*SourceFiniteUnitary.time (jointCompression p F h) t*jointCResolvent p F z h := by
  have commute:=SourceFiniteUnitary.time_commutes _ _ (actual_joint_C_grade_zero p F h) t
  calc
    _=gradeZeroProjection*SourceFiniteUnitary.time (jointCompression p F h) t*jointResolvent p F z h := by
      rw [actual_joint_time_grade_zero_left]
    _=SourceFiniteUnitary.time (jointCompression p F h) t*(gradeZeroProjection*jointResolvent p F z h) := by
      rw [commute.eq,mul_assoc]
    _=SourceFiniteUnitary.time (jointCompression p F h) t*(gradeZeroProjection*jointCResolvent p F z h) := by rw [green]
    _=SourceFiniteUnitary.time (jointCompression p F h) t*gradeZeroProjection*jointCResolvent p F z h := by rw [mul_assoc]
    _=_ := by rw [commute.symm.eq]

private theorem left_pair (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ)
    (t : ℝ) (h : Field289) (x y : H) (fixed : gradeZeroProjection x=x)
    (green : gradeZeroProjection*jointResolvent p F z h=gradeZeroProjection*jointCResolvent p F z h) :
    inner ℂ x (physicalTime p F t h (jointResolvent p F z h y))=
      inner ℂ x (SourceFiniteUnitary.time (jointCompression p F h) t (jointCResolvent p F z h y)) := by
  have original:=congrArg (fun A : ActualDressedNumberZero.Op=>inner ℂ x (A y)) (left_word p F z t h green)
  simpa only [mul_apply_eq_comp,←grade_zero_projection_pair,fixed] using original

/-- The complete actual observer has this same-source field germ, uniformly in original ages and all reader directions. -/
theorem actual_noether_number_field_germ (event : DressedEvent) (transfer : PhysicalMomentum) :
    ∀ᶠh : Field289 in 𝓝 0,∀(age : ℝ) (reader : Field289),
    dressedEulerObserver event (dressedNoetherKernel event transfer reader age h)=numberFieldRead event transfer reader age h := by
  have conditions:=(actual_joint_resolvent_grade_zero_left (event.momentum-transfer) event.frame event.energy event.nonreal).and
    ((actual_joint_created_inverse_time_return event.momentum event.frame event.energy event.nonreal event.epsilon event.precision).and
      (actual_joint_background_inverse_time_return event.momentum event.frame event.energy event.nonreal
        (sourceProfile event.epsilon event.precision)))
  apply conditions.mono
  intro h conditions
  obtain ⟨left,created,background⟩:=conditions
  intro age reader
  rw [dressed_euler_observer_original]
  unfold dressedNoetherKernel numberFieldRead
  simp only [mul_apply_eq_comp]
  rw [created age,background age]
  have created_pair:=left_pair (event.momentum-transfer) event.frame event.energy (-age) h
    (sourceDressedUnit event.epsilon event.precision)
    (noetherReader reader event.momentum event.frame h
      (jointN2GreenWords event.momentum event.frame event.energy h
        (physicalTime event.momentum event.frame age h (sourceDressedUnit event.epsilon event.precision))))
    (actual_created_unit_grade_zero_fixed event.epsilon event.precision) left
  have background_pair:=left_pair (event.momentum-transfer) event.frame event.energy (-age) h
    (prepared (sourceProfile event.epsilon event.precision))
    (noetherReader reader event.momentum event.frame h
      (jointN1GreenWords event.momentum event.frame event.energy h
        (physicalTime event.momentum event.frame age h (prepared (sourceProfile event.epsilon event.precision)))))
    (actual_background_grade_zero_fixed (sourceProfile event.epsilon event.precision)) left
  exact congrArg₂ (fun a b : ℂ=>-a+b) created_pair background_pair

/-- Original full five-term constant-field quantum response directly consumes the generated field germ, including contact and both time variations. -/
theorem actual_number_field_quantum_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) (i : Fin 289) :
    HasDerivAt (fun r : ℝ=>numberFieldRead event transfer (PreparationVacuumActionFieldLift.fieldUnit i) age (r • force))
      (dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) age i).value 0 := by
  have curve : Tendsto (fun r : ℝ=>r • force) (𝓝 0) (𝓝 0) := by
    simpa only [id_eq, zero_smul] using ((hasDerivAt_id (0:ℝ)).smul_const force).continuousAt.tendsto
  have along:=curve.eventually (actual_noether_number_field_germ event transfer)
  have source:=dressed_noether_action_derivative event transfer force age i
  exact source.congr_of_eventuallyEq (along.mono (fun r returned=>(returned age _).symm))

end LowEnergy.GaussComposite.ActualDressedNumberField
