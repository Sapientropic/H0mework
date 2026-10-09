import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherHistory
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSignalCausalResponse

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSignal
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open SourcePropagationMotherEulerKernel SourcePropagationNativeEulerHistory SourcePropagationNoetherTime
open SourcePropagationMotherResidualDirections
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSourcePreparation
open PreparationVacuumSourcePreparedResponse
open SourceGraph MeasureTheory Filter Set
open scoped Matrix BigOperators Topology InnerProductSpace Interval
attribute [local irreducible] sourceProfile sourceDressedUnit dressedEulerObserver dressedNoetherJet
  sourceHistoryOperator noetherHistoryOperatorJet

private theorem unit_inner_read_price (v : H) (unit : ‖v‖=1) (A : H→L[ℂ]H) :
    ‖inner ℂ v (A v)‖ ≤ ‖A‖ := by
  refine (norm_inner_le_norm v (A v)).trans ?_
  simpa only [unit,one_mul,mul_one] using A.le_opNorm v

/-- The price uses the actual two unit states, independently of the historical q observer. -/
theorem dressed_euler_observer_price (event : DressedEvent) : ‖dressedEulerObserver event‖ ≤ 2 := by
  have background : ‖prepared (sourceProfile event.epsilon event.precision)‖=1 := by
    rw [sourceProfile]
    exact (sourceCausalState event.epsilon event.precision).unit
  apply (dressedEulerObserver event).opNorm_le_bound (by norm_num)
  intro A
  rw [dressed_euler_observer_original]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  have created:=unit_inner_read_price _ (source_dressed_unit_norm event.epsilon event.precision) A
  have vacuum:=unit_inner_read_price _ background A
  nlinarith

/-- Every original Noether row is observed by the same actual creation minus background. -/
def dressedSignalOperator (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) : SignalAmplitude→L[ℝ] (Fin 289→ℂ) :=
  ContinuousLinearMap.pi (fun i=>
    ((dressedEulerObserver event).restrictScalars ℝ).comp
      (sourceHistoryOperator (dressedKinematicPoint event transfer) (fieldUnit i) p t))

theorem dressed_signal_operator_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    dressedSignalOperator event transfer p t a=
      fun i=>(dressedNoetherJet event transfer (nativeTimeSignal (sourceRealSignal p a)) t i).value := by
  funext i
  rw [dressedSignalOperator,ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars',sourceHistoryOperator_actual]
  exact (dressed_noether_jet_original event transfer (nativeTimeSignal (sourceRealSignal p a)) t i).symm

theorem dressed_signal_operator_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) : Continuous (dressedSignalOperator event transfer p) := by
  apply continuous_clm_apply.2
  intro a
  have actual : (fun t=>dressedSignalOperator event transfer p t a)=
      fun t i=>(dressedNoetherJet event transfer (nativeTimeSignal (sourceRealSignal p a)) t i).value :=
    funext (fun t=>dressed_signal_operator_actual event transfer p t a)
  rw [actual]
  exact continuous_pi (fun i=>(dressed_noether_jet_continuous event transfer _
    (sourceTimeSignal_continuous p a) i).1)

/-- Both genuine real Fourier histories are retained, with no polarization average. -/
def dressedSignalQuadrature (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) : SignalAmplitude→L[ℝ] (Fin 289→ℂ) :=
  dressedSignalOperator event transfer p t+
    Complex.I • (dressedSignalOperator event transfer p t).comp sourceQuadratureOperator

theorem dressed_signal_quadrature_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    dressedSignalQuadrature event transfer p t a=
      (fun i=>(dressedNoetherJet event transfer (nativeTimeSignal (sourceRealSignal p a)) t i).value)+
        Complex.I • (fun i=>(dressedNoetherJet event transfer
          (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t i).value) := by
  rw [dressedSignalQuadrature,add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,dressed_signal_operator_actual,sourceQuadratureOperator,
    smul_apply,ContinuousLinearMap.id_apply,dressed_signal_operator_actual]
  rfl

theorem dressed_signal_quadrature_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) : Continuous (dressedSignalQuadrature event transfer p) :=
  (dressed_signal_operator_continuous event transfer p).add
    (((dressed_signal_operator_continuous event transfer p).clm_comp continuous_const).const_smul Complex.I)

private theorem quadrature_phase {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G] (A : E→L[ℝ]G) (x : E) :
    A (Complex.I • x)+Complex.I • A ((-Complex.I) • (Complex.I • x))=
      Complex.I • (A x+Complex.I • A ((-Complex.I) • x)) := by
  simp only [smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul,smul_add,neg_smul,
    map_neg,smul_neg]
  abel

/-- Complex phase transport follows from the two real source histories. -/
theorem dressed_signal_quadrature_phase (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    dressedSignalQuadrature event transfer p t (Complex.I • a)=
      Complex.I • dressedSignalQuadrature event transfer p t a := by
  simpa only [dressedSignalQuadrature,add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,sourceQuadratureOperator,ContinuousLinearMap.id_apply]
    using quadrature_phase (dressedSignalOperator event transfer p t) a

/-- The duration is produced by the original nonlinear family for both quadratures. -/
def dressedSignalDuration (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (a : SignalAmplitude) : ℝ :=
  sourceSignalDuration (dressedKinematicPoint event transfer) p a

theorem dressed_signal_duration_positive (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (a : SignalAmplitude) : 0<dressedSignalDuration event transfer p a :=
  sourceSignalDuration_positive _ _ _

/-- This family changes the original source field before differentiating the preparation. -/
def dressedSignalNonlinear (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (a : SignalAmplitude) (r t : ℝ) : Fin 289→ℂ :=
  fun i=>dressedNonlinearSource event transfer (nativeTimeSignal (sourceRealSignal p a))
    (motherHistoryRegular _ (sourceRealSignal_smooth p a)) r t i+
    Complex.I*dressedNonlinearSource event transfer
      (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a)))
      (motherHistoryRegular _ (sourceRealSignal_smooth p (sourceQuadrature a))) r t i

theorem dressed_signal_nonlinear_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) (future : 0≤t)
    (inside : t<dressedSignalDuration event transfer p a) (i : Fin 289) :
    HasDerivAt (fun r=>dressedSignalNonlinear event transfer p a r t i)
      (dressedSignalQuadrature event transfer p t a i) 0 := by
  have left:=dressed_nonlinear_source_generated event transfer (nativeTimeSignal (sourceRealSignal p a))
    (motherHistoryRegular _ (sourceRealSignal_smooth p a)) t future (lt_min_iff.mp inside).1 i
  have right:=dressed_nonlinear_source_generated event transfer
    (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a)))
    (motherHistoryRegular _ (sourceRealSignal_smooth p (sourceQuadrature a))) t future
      (lt_min_iff.mp inside).2 i
  simpa only [dressedSignalNonlinear,dressed_signal_quadrature_actual,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul] using! left.add (right.const_mul Complex.I)

end LowEnergy.GaussComposite.ActualDressedSignal
