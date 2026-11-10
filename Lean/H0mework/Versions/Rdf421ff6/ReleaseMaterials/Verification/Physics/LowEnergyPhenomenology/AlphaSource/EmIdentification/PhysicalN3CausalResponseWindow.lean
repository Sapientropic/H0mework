import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3JointResponseTime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3CausalWindow
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumNoetherChart PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldPerturbation.Blocks PreparationVacuumFullPoleContinuation
open ActualEMJointCurrentMomentum ActualElectronPhysicalJointInverse ActualElectronWholeChargeSoft
open ActualElectronWholeNoetherObserver ActualDressedFullCoulomb ActualDressedNoether
open ActualElectronFullNoetherMixedSoft
open PreparationVacuumSourcePreparedResponse GaussComposite.SourceGraph
open SourcePropagationCommonMomentum SourcePropagationTimeDependentFeedback
open SourceFamilyHilbert SourceFamilyOperator Filter
open scoped Topology InnerProductSpace
open intervalIntegral MeasureTheory
local instance windowRationalOperators : NormedAlgebra ℚ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℚ ℂ _
local instance windowRealOperators : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance windowOperatorNorm : NormedAddCommGroup (H→L[ℂ]H):=ContinuousLinearMap.toNormedAddCommGroup
local instance windowOperatorRealSpace : NormedSpace ℝ (H→L[ℂ]H):=windowRealOperators.toNormedSpace
attribute [local irreducible] actualFullNoetherVariation jointResolvent jointCurrent jointGenerator jointHessian
  physicalTime noetherReader noetherReaderContact rawReaderContact timeSlope mixedVertex
  actualPhysicalEulerObserver actualElectronPhysicalState actualNoetherBackground

/-- The finite causal window is the original source Laplace weight times the complete five-term
Noether variation over the finite age interval `0..T`; the kernel still uses `-age`, so the
negative-time leg inside each factor is not discarded. -/
def physicalN3ResponseWindowOperator (event : DressedEvent) (k : PhysicalMomentum) (lambda : ℂ)
    (T : ℝ) (reader force : Field289) : H→L[ℂ]H:=
  ∫ age in (0:ℝ)..T,(laplaceWeight lambda age)•actualFullNoetherVariation event (-k) reader force age

/-- The actual N3 Euler observer reads the same window operator on its physical state and on the
unchanged original sourceProfile background. -/
def physicalN3ResponseWindow (event : DressedEvent) (leg : CompositeLeg) (k : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (reader force : Field289) : ℂ:=
  actualPhysicalEulerObserver event leg (physicalN3ResponseWindowOperator event k lambda T reader force)

/-- At every physical preparation frame the window read uses the source-generated actual N3 unit
`u_F` and the original normalized background `b`; the event frame is never identified with `F`. -/
def physicalN3FrameRead (event : DressedEvent) (leg : CompositeLeg) (k : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (reader force : Field289) (F : GaussUnitaryHistory.Index) : ℂ:=
  let psi:=actualElectronPhysicalUnit event.momentum F event.energy leg
  let A:=physicalN3ResponseWindowOperator event k lambda T reader force
  let b:=prepared (sourceProfile event.epsilon event.precision);
  -inner ℂ psi (A psi)+inner ℂ b (A b)

/-- The complete physical observation keeps all `289*289` reader/force slots. -/
def physicalN3ResponseWindowMatrix (event : DressedEvent) (leg : CompositeLeg) (k : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ:=
  fun i j=>physicalN3ResponseWindow event leg k lambda T (fieldUnit i) (fieldUnit j)

private theorem n3_family_observer_return {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) (U b : Family E u) (A : Operator I E) :
    Tendsto (fun F=>-inner ℂ (value U F) (A.component F (value U F))+
      inner ℂ (value b F) (A.component F (value b F))) u
      (𝓝 (-inner ℂ (U : Hilbert E u) (lift u A (U : Hilbert E u))+
        inner ℂ (b : Hilbert E u) (lift u A (b : Hilbert E u)))) := by
  rw [lift_coe,lift_coe,inner_coe,inner_coe]
  exact (pair_tendsto u U (act u A U)).neg.add (pair_tendsto u b (act u A b))

private theorem n3_embed_constant {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) (x : E) :
    SourceFamilyHilbert.embed u x=
      (SourceFamilyHilbert.constant u x : SourceFamilyHilbert.Hilbert E u):=rfl

private theorem n3_pairing_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : ℝ) (f : ℝ→(E→L[ℂ]E)) (hf : IntervalIntegrable f volume 0 T) (x b : E) :
    -inner ℂ x ((∫ age in (0:ℝ)..T,f age) x)+inner ℂ b ((∫ age in (0:ℝ)..T,f age) b)=
      ∫ age in (0:ℝ)..T,(-inner ℂ x (f age x)+inner ℂ b (f age b)):=by
  have leval : ∀A : E→L[ℂ]E,
      (-((innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ E x)))+
        ((innerSL ℂ b).comp ((ContinuousLinearMap.apply ℂ E b)))) A=
        -inner ℂ x (A x)+inner ℂ b (A b):=fun A=>by
        simp only [neg_apply,add_apply,ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.apply_apply,innerSL_apply_apply]
  have comm :=(-((innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ E x)))+
    ((innerSL ℂ b).comp ((ContinuousLinearMap.apply ℂ E b))):
      (E→L[ℂ]E)→L[ℂ]ℂ).intervalIntegral_comp_comm hf
  rw [←leval (∫ age in (0:ℝ)..T,f age),←comm]
  apply intervalIntegral.integral_congr
  intro age _
  exact leval (f age)

private theorem n3_weighted_linear_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (L : E→L[ℂ]ℂ) (T : ℝ)
    (weight : ℝ→ℂ) (f : ℝ→E)
    (hf : IntervalIntegrable (fun t=>weight t • f t) volume 0 T) :
    L (∫t in (0:ℝ)..T,weight t • f t)=∫t in (0:ℝ)..T,weight t * L (f t) := by
  rw [←L.intervalIntegral_comp_comm hf]
  apply intervalIntegral.integral_congr
  intro t _
  exact L.map_smul (weight t) (f t)

private theorem n3_weighted_pairing_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T : ℝ) (weight : ℝ→ℂ)
    (f : ℝ→(E→L[ℂ]E))
    (hf : IntervalIntegrable (fun t=>weight t • f t) volume 0 T) (x b : E) :
    -inner ℂ x ((∫t in (0:ℝ)..T,weight t • f t) x)+
      inner ℂ b ((∫t in (0:ℝ)..T,weight t • f t) b)=
      ∫t in (0:ℝ)..T,weight t * (-inner ℂ x (f t x)+inner ℂ b (f t b)) := by
  rw [n3_pairing_integral T (fun t=>weight t • f t) hf x b]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [smul_apply,inner_smul_right]
  ring

private theorem n3_weighted_operator_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T : ℝ) (weight : ℝ→ℂ)
    (f : ℝ→(E→L[ℂ]E)) (hw : Continuous weight) (hf : Continuous f) :
    IntervalIntegrable (fun t=>weight t • f t) volume 0 T:=
  (hw.smul hf).intervalIntegrable (μ:=volume) 0 T

theorem physical_n3_window_operator_integrable (event : DressedEvent) (k : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    IntervalIntegrable
      (fun age : ℝ=>(laplaceWeight lambda age)•actualFullNoetherVariation event (-k) reader force age)
      volume 0 T := by
  have weight : Continuous (fun t : ℝ=>laplaceWeight lambda t):=by unfold laplaceWeight;fun_prop
  have field : Continuous (fun age : ℝ=>
      actualFullNoetherVariation event (-k) reader force age):=by
    simpa only [Function.comp_def,id_eq] using
      (physical_n3_variation_joint event reader force).comp
        ((continuous_const (y:=k)).prodMk continuous_id)
  exact n3_weighted_operator_integrable T (laplaceWeight lambda)
    (fun age=>actualFullNoetherVariation event (-k) reader force age) weight field

/-- The observer commutes with the source Bochner integral exactly on the full response. -/
theorem physical_n3_window_observer_integral (event : DressedEvent) (leg : CompositeLeg)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    physicalN3ResponseWindow event leg k lambda T reader force=
      ∫ age in (0:ℝ)..T,(laplaceWeight lambda age)•
        actualPhysicalFullResponse event leg reader force age k := by
  unfold physicalN3ResponseWindow physicalN3ResponseWindowOperator
  exact n3_weighted_linear_integral (actualPhysicalEulerObserver event leg) T
    (laplaceWeight lambda) (fun age=>actualFullNoetherVariation event (-k) reader force age)
    (physical_n3_window_operator_integrable event k lambda T reader force)

/-- The finite-frame read is the same age integral of the source scalar response. -/
theorem physical_n3_frame_read_integral (event : DressedEvent) (leg : CompositeLeg)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289)
    (F : GaussUnitaryHistory.Index) :
    physicalN3FrameRead event leg k lambda T reader force F=
      ∫ age in (0:ℝ)..T,(laplaceWeight lambda age)*
        (-inner ℂ (actualElectronPhysicalUnit event.momentum F event.energy leg)
          (actualFullNoetherVariation event (-k) reader force age
            (actualElectronPhysicalUnit event.momentum F event.energy leg))+
        inner ℂ (prepared (sourceProfile event.epsilon event.precision))
          (actualFullNoetherVariation event (-k) reader force age
            (prepared (sourceProfile event.epsilon event.precision)))) := by
  unfold physicalN3FrameRead physicalN3ResponseWindowOperator
  exact n3_weighted_pairing_integral T (laplaceWeight lambda)
    (fun age=>actualFullNoetherVariation event (-k) reader force age)
    (physical_n3_window_operator_integrable event k lambda T reader force)
    (actualElectronPhysicalUnit event.momentum F event.energy leg)
    (prepared (sourceProfile event.epsilon event.precision))

/-- The physical preparation returns the same window on the original sourceFilter. -/
theorem physical_n3_window_source_return (event : DressedEvent) (leg : CompositeLeg)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    Tendsto (physicalN3FrameRead event leg k lambda T reader force) GaussUnitaryHistory.sourceFilter
      (𝓝 (physicalN3ResponseWindow event leg k lambda T reader force)) := by
  unfold physicalN3ResponseWindow physicalN3FrameRead
  rw [actual_physical_euler_observer_value]
  simp only [actualElectronPhysicalState,actualNoetherBackground,
    GaussUnitaryHistory.inclusion,GaussUnitaryHistory.reader,n3_embed_constant]
  exact n3_family_observer_return GaussUnitaryHistory.sourceFilter
    (actualElectronPhysicalStateFamily event.momentum event.energy event.nonreal leg)
    (SourceFamilyHilbert.constant GaussUnitaryHistory.sourceFilter
      (prepared (sourceProfile event.epsilon event.precision)))
    (SourceFamilyOperator.constant
      (physicalN3ResponseWindowOperator event k lambda T reader force))

end LowEnergy.GaussComposite.PhysicalN3CausalWindow
