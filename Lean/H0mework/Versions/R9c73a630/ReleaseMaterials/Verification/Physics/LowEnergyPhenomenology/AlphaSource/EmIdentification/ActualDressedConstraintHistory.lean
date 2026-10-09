import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintTranspose
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderContactBasis
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeColumn

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedConstraintWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open SourcePropagationNativeActionHessian SourcePropagationNoetherTime SourcePropagationNativeEulerHistory
open SourcePropagationMotherEulerKernel
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open ActualDressedConstraintRead ActualDressedNullNative
open MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] originalChange originalReadback originalJacobi dressedWindowPolarization
  nativeHessian dressedEulerObserver noetherHistoryOperatorJet dressedSignalQuadrature

/-- A complex reader is the two distinct real source field insertions. -/
def dressedComplexReader (event : DressedEvent) (transfer : PhysicalMomentum) (V : SignalAmplitude)
    (signal : ℝ→SourceJet Field289) (t : ℝ) : ℂ :=
  dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fun k=>(V k).re) signal t).value+
    Complex.I*dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fun k=>(V k).im) signal t).value

theorem dressed_complex_reader_actual (event : DressedEvent) (transfer : PhysicalMomentum) (V : SignalAmplitude)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    dressedComplexReader event transfer V signal t=
      ∑j : Fin 289,V j*(dressedNoetherJet event transfer signal t j).value :=
  actual_complex_noether_contraction event transfer V signal t

/-- Both actual real histories and both actual real readers remain in this quantum contraction. -/
def dressedQuantumReader (event : DressedEvent) (transfer : PhysicalMomentum) (V : SignalAmplitude)
    (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) : ℂ :=
  dressedComplexReader event transfer V (nativeTimeSignal (sourceRealSignal p a)) t+
    Complex.I*dressedComplexReader event transfer V
      (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t

theorem dressed_quantum_reader_actual (event : DressedEvent) (transfer : PhysicalMomentum) (V : SignalAmplitude)
    (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) :
    dressedQuantumReader event transfer V p a t=dotProduct V (dressedSignalQuadrature event transfer p t a) := by
  rw [dressedQuantumReader,dressed_complex_reader_actual,dressed_complex_reader_actual,
    dressed_signal_quadrature_actual]
  simp only [dotProduct,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply congrArg₂ (·+·) rfl
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The full finite quantum constraint is the original opposite-momentum Noether history read. -/
theorem source_constraint_quantum_history (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (lambda : ℂ) (T : ℝ) (a : SignalAmplitude) (n : Fin 9) :
    sourceCokernel p (dressedWindowPolarization event transfer p lambda T*ᵥa) n=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*
        dressedQuantumReader event transfer (originalNullColumn (-p) n) p a t := by
  rw [original_null_cokernel,←dressed_window_polarization_actual,dressed_signal_window_actual]
  simp_rw [dressed_quantum_reader_actual]
  let V : SignalAmplitude:=originalNullColumn (-p) n
  have quad : ∀j,Continuous (fun t=>dressedSignalQuadrature event transfer p t a j) := by
    intro j
    exact (continuous_apply j).comp
      ((dressed_signal_quadrature_continuous event transfer p).clm_apply continuous_const)
  have weighted : ∀j,IntervalIntegrable
      (fun t=>V j*(laplaceWeight lambda t*dressedSignalQuadrature event transfer p t a j)) volume 0 T := by
    intro j
    have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
    exact ((weight.mul (quad j)).const_mul (V j)).intervalIntegrable 0 T
  change (∑j,V j*(∫t in (0:ℝ)..T,laplaceWeight lambda t*dressedSignalQuadrature event transfer p t a j))=
    ∫t in (0:ℝ)..T,laplaceWeight lambda t*(∑j,V j*dressedSignalQuadrature event transfer p t a j)
  simp_rw [←intervalIntegral.integral_const_mul]
  rw [←intervalIntegral.integral_finsetSum (fun j _=>weighted j)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The nine rows of the original nonlinear residual generate that same full quantum history on its actual window. -/
theorem source_constraint_nonlinear_history (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (lambda : ℂ) (T : ℝ) (future : 0 ≤ T) (a : SignalAmplitude)
    (inside : T<dressedSignalDuration event transfer p a) (n : Fin 9) :
    sourceCokernel p
      (fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*deriv (fun r=>dressedSignalRawEuler event transfer p a r t i) 0) n=
      -(∫t in (0:ℝ)..T,laplaceWeight lambda t*
        dressedQuantumReader event transfer (originalNullColumn (-p) n) p a t) := by
  rw [dressed_native_window_pencil_generated event transfer p lambda T future a inside,
    source_cokernel_actual_pencil]
  exact congrArg Neg.neg (source_constraint_quantum_history event transfer p lambda T a n)

/-- The actual source term and all nine remaining Schur rows consume the original Noether history. -/
theorem source_constraint_schur_history (event : DressedEvent) (T : ℝ) (forcing : SignalAmplitude)
    (initial : Fin 9→ℂ) (n : Fin 9) :
    (anchorSchur event T*ᵥinitial-anchorSchurSource event T forcing) n=
      sourceCokernel anchorInput forcing n+
        ∫t in (0:ℝ)..T,laplaceWeight 3 t*
          dressedQuantumReader (anchorEvent event) 0 (originalNullColumn (-anchorInput) n)
            anchorInput (anchorResponseNine event T forcing initial) t := by
  rw [←anchor_schur_generated,map_add]
  exact congrArg (fun x : ℂ=>sourceCokernel anchorInput forcing n+x)
    (source_constraint_quantum_history (anchorEvent event) 0 anchorInput 3 T
      (anchorResponseNine event T forcing initial) n)

end LowEnergy.GaussComposite.ActualDressedConstraintWard
