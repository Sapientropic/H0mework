import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorColumn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorWard

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNativeQuantumWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumCurrentSignalOperator
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open SourcePropagationNoetherTime SourcePropagationNativeEulerHistory
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedConstraintWard ActualDressedNativeConstraint ActualDressedNullNative ActualEMDressedSchur
open MeasureTheory
open scoped Matrix BigOperators Interval
attribute [local irreducible] originalNullColumn dressedQuantumReader dressedSignalQuadrature

private def bilinearRead (D : SignalAmplitude) : SignalAmplitude→ₗ[ℂ]ℂ where
  toFun V:=dotProduct V D
  map_add' V W:=by simp only [dotProduct,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' c V:=by
    simp only [dotProduct,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc,Finset.mul_sum]

/-- The same original native constraint is its retained background Ward plus the actual gauge-current divergence. -/
theorem native_color_constraint_current (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (g : Fin 3) (v : SignalAmplitude) (t : ℝ) :
    nativeConstraintHistory event transfer p (Fin.castAdd 6 g) v t-
      nativeConstraintDeviation event transfer p (Fin.castAdd 6 g) v t=
    dressedQuantumReader event transfer (originalNullColumn 0 (Fin.castAdd 6 g)) p v t+
      ∑a : Fin 12,∑mu : Fin 4,(p mu*(gaugeColorRaw g a:ℂ))*
        dressedQuantumReader event transfer (fun row=>(gaugeField mu a row:ℂ)) p v t :=by
  rw [←native_constraint_quadratures]
  simp_rw [dressed_quantum_reader_actual]
  have source:=congrArg (bilinearRead (dressedSignalQuadrature event transfer p t v))
    (original_color_column_gradient (-p) g)
  simpa only [map_sub,map_sum,map_smul,bilinearRead,LinearMap.coe_mk,AddHom.coe_mk,
    smul_eq_mul,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib,sub_neg_eq_add] using source

/-- Full finite C9Pi consumes the original gauge four-current and the original full289 zero-covector column. -/
theorem source_color_constraint_current (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (v : SignalAmplitude) (g : Fin 3) :
    sourceCokernel p (dressedWindowPolarization event transfer p lambda T*ᵥv) (Fin.castAdd 6 g)=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*
        (dressedQuantumReader event transfer (originalNullColumn 0 (Fin.castAdd 6 g)) p v t+
          ∑a : Fin 12,∑mu : Fin 4,(p mu*(gaugeColorRaw g a:ℂ))*
            dressedQuantumReader event transfer (fun row=>(gaugeField mu a row:ℂ)) p v t) :=by
  rw [source_constraint_native_history]
  simp_rw [native_color_constraint_current event transfer p g v]

/-- The actual original nonlinear residual generates exactly these retained-background and current terms on its own source window. -/
theorem source_color_constraint_nonlinear (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (future : 0 ≤ T) (v : SignalAmplitude)
    (inside : T<dressedSignalDuration event transfer p v) (g : Fin 3) :
    sourceCokernel p
      (fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*deriv (fun r=>dressedSignalRawEuler event transfer p v r t i) 0)
      (Fin.castAdd 6 g)=
      -(∫t in (0:ℝ)..T,laplaceWeight lambda t*
        (dressedQuantumReader event transfer (originalNullColumn 0 (Fin.castAdd 6 g)) p v t+
          ∑a : Fin 12,∑mu : Fin 4,(p mu*(gaugeColorRaw g a:ℂ))*
            dressedQuantumReader event transfer (fun row=>(gaugeField mu a row:ℂ)) p v t)) :=by
  rw [source_constraint_native_nonlinear event transfer p lambda T future v inside]
  simp_rw [native_color_constraint_current event transfer p g v]

end LowEnergy.GaussComposite.ActualDressedNativeQuantumWard
