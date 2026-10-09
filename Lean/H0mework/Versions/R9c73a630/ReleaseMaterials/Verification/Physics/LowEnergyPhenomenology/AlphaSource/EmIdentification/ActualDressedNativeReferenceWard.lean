import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMSourceLockedResponse
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationPreparedNativeCarrier
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFixedMomentumHamiltonian

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedLockedWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussNativeMatter FullQuantum.StateGreen SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussHistoryHilbert GaussCoreHilbert
open GaussQuantumMultiplier CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve PreparationVacuumGaugeSourceInjection
open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumNoetherChart
open PreparationVacuumActualFieldQuantization PreparationVacuumFixedMomentumActionReturn
open scoped Matrix BigOperators Topology

/-- The actual configuration deviation is acted on by the original native contact map. -/
def nativeReferenceDeviation (n : Fin 9) (theta : ℝ) (s : ActionState) : ActionState :=
  stateContact n theta (s-sourceState sourcePoint.val)

theorem native_reference_state (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) (s : ActionState) :
    stateVariation n theta gradient s=
      fieldDirection (nativeSourceColumn n theta gradient)+nativeReferenceDeviation n theta s := by
  rw [nativeSourceColumn_state]
  have paid:=stateVariation_affine n theta gradient (sourceState sourcePoint.val)
    (s-sourceState sourcePoint.val) 1
  have same : sourceState sourcePoint.val+(1:ℝ) • (s-sourceState sourcePoint.val)=s := by module
  rw [same,one_smul] at paid
  exact paid

/-- This is the original fixed-momentum action on a generated configuration deviation, not a difference of readers. -/
def nativeDeviationNoether (n : Fin 9) (theta : ℝ) (p : PhysicalMomentum)
    (base candidate : ActionState) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight base*symbolFirst p candidate (nativeReferenceDeviation n theta candidate))

/-- Its mixed response keeps the actual variation of the symmetry direction itself. -/
def nativeDeviationMixed (n : Fin 9) (theta : ℝ) (force : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight base*
    (symbolSecond p candidate (nativeReferenceDeviation n theta candidate) (fieldDirection force)+
      symbolFirst p candidate (stateContact n theta (fieldDirection force))))

private theorem weighted_split (D : ActionState→L[ℝ]FullMatrix) (W : FullMatrix)
    (v a b : ActionState) (same : v=a+b) :
    -(4:ℂ) • (W*D a)= -(4:ℂ) • (W*D v)-(-(4:ℂ) • (W*D b)) := by
  rw [same,map_add,mul_add,smul_add,add_sub_cancel_right]

private theorem weighted_contact_split (D : ActionState→L[ℝ]FullMatrix) (W q : FullMatrix)
    (v a b : ActionState) (same : v=a+b) :
    -(4:ℂ) • (W*D a)= -(4:ℂ) • (W*(D v+q))-(-(4:ℂ) • (W*(D b+q))) := by
  rw [same,map_add]
  simp only [mul_add,smul_add]
  abel

/-- Every fixed reference native direction returns through the full configuration-dependent Noether action plus its source-owned deviation. -/
theorem native_reference_gradient (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : PhysicalMomentum) (base candidate : ActionState) :
    sourceFixedMomentumGradient (nativeSourceColumn n theta gradient) p base candidate=
      nativeNoether n theta gradient p base candidate-nativeDeviationNoether n theta p base candidate := by
  exact weighted_split (fderiv ℝ (sourceSymbol p) candidate) (sourceActionWeight base)
    (stateVariation n theta gradient candidate) (fieldDirection (nativeSourceColumn n theta gradient))
    (nativeReferenceDeviation n theta candidate) (native_reference_state n theta gradient candidate)

/-- The contact of the moving native transformation appears on both true source branches and cancels only in this exact fixed-reference return. -/
theorem native_reference_contact (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (base candidate : ActionState) :
    sourceFixedMomentumContact (nativeSourceColumn n theta gradient) force p base candidate=
      nativeNoetherMixed n theta gradient force p base candidate-nativeDeviationMixed n theta force p base candidate := by
  exact weighted_contact_split (fderiv ℝ (fderiv ℝ (sourceSymbol p)) candidate (fieldDirection force))
    (sourceActionWeight base) (symbolFirst p candidate (stateContact n theta (fieldDirection force)))
    (stateVariation n theta gradient candidate) (fieldDirection (nativeSourceColumn n theta gradient))
    (nativeReferenceDeviation n theta candidate) (native_reference_state n theta gradient candidate)

/-- The actual fixed-pi Noether reader, not the raw-action contact, consumes the original reference-direction decomposition. -/
theorem native_reference_transport (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : PhysicalMomentum) (base candidate : ActionState) (valid : candidate∈validStates) :
    transportedRawSymbol (nativeSourceColumn n theta gradient) base candidate p=
      nativeNoether n theta gradient p base candidate-nativeDeviationNoether n theta p base candidate := by
  rw [←sourceFixedMomentumGradient_raw _ p base candidate valid]
  exact native_reference_gradient n theta gradient p base candidate

theorem native_reference_noether_contact (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    noetherContactSymbol (nativeSourceColumn n theta gradient) force (sourceState z.val) p=
      nativeNoetherMixed n theta gradient force p (sourceState z.val) (sourceState z.val)-
        nativeDeviationMixed n theta force p (sourceState z.val) (sourceState z.val) := by
  rw [←sourceFixedMomentumContact_noether _ force p z]
  exact native_reference_contact n theta gradient force p (sourceState z.val) (sourceState z.val)

/-- Both independent full504 branches and all occupations retain the same decomposition. -/
theorem native_reference_quantized (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : PhysicalMomentum) (base candidate : ActionState) (valid : candidate∈validStates) :
    quantizer (transportedRawSymbol (nativeSourceColumn n theta gradient) base candidate p)=
      quantizer (nativeNoether n theta gradient p base candidate)-quantizer (nativeDeviationNoether n theta p base candidate) := by
  rw [native_reference_transport n theta gradient p base candidate valid,map_sub]

end LowEnergy.GaussComposite.ActualDressedLockedWard
