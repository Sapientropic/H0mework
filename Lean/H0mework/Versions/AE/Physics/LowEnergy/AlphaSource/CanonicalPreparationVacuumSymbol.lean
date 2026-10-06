import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationVacuumHamiltonian
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationBorelPrincipal

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFactor
open SaturationMonoid.PhysicsCore StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussLiveMomentum GaussDensityCore GaussHistoryHilbert
open GaussQuantumMultiplier GaussNativeEnergy GaussNativePotential GaussNativeForm
open CanonicalPreparationCreation CanonicalPreparationCore PreparationActualFactor
open scoped BigOperators ContDiff Matrix Topology
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

def zeroShiftTime (n : ℝ) : Fin 4 → ℝ := ![n,0,0,0]

theorem original_zeroShift_BF_mixed (n : ℝ) (q : Coframe) (i j : Fin 3) :
    sourceBFKernel (zeroShiftTime n) q (Fin.castAdd 3 i) (Fin.natAdd 3 j)=0 := by
  rw [sourceBFKernel_wedge]
  fin_cases i <;> fin_cases j <;>
    simp [ProofFreeRicherAnholonomicSource.coframeWedge,
      ProofFreeRicherAnholonomicSource.pairFirst,ProofFreeRicherAnholonomicSource.pairSecond,
      lorentzianTwoFormSign,coframe,zeroShiftTime,Fin.sum_univ_six]

def scalarConnectionSymbol (z : SourceCoordinateSlice) (p : Cotangent) :
    FockFiber →L[ℂ] FockFiber :=
  (-Complex.I) • ∑ a : ScalarIndex,
    ((scalarWeight z*scalarMomentum z p a : ℝ) : ℂ) • connection (scalarDirection a) z

def gaugeConnectionSymbol (z : SourceCoordinateSlice) (p : Cotangent) :
    FockFiber →L[ℂ] FockFiber :=
  (-Complex.I/2) • ∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
    (gaugeWeight z i j : ℂ) •
      ((electricMomentum z p i a : ℂ) • connection (gaugeDirection j a) z+
        (electricMomentum z p j a : ℂ) • connection (gaugeDirection i a) z)

def coframeConnectionSymbol (z : SourceCoordinateSlice) (p : Cotangent) :
    FockFiber →L[ℂ] FockFiber :=
  (GaussCoframeForm.currentCoefficient 0 z*coframeMomentum p 1 : ℂ) • quantized (GaussCoframeSpin.full 5)+
  (GaussCoframeForm.currentCoefficient 1 z*coframeMomentum p 3 : ℂ) • quantized (GaussCoframeSpin.full 3)-
  (GaussCoframeForm.currentCoefficient 0 z*coframeMomentum p 3 : ℂ) • quantized (GaussCoframeSpin.full 4)+
  (GaussCoframeForm.currentCoefficient 2 z*coframeMomentum p 4 : ℂ) • quantized (GaussCoframeSpin.full 3)

def zeroShiftCurrentSymbol (n : ℝ) (z : SourceCoordinateSlice) (p : Cotangent) :
    FockFiber →L[ℂ] FockFiber :=
  ((n/sourceTime 0 : ℝ) : ℂ) • (scalarConnectionSymbol z p+coframeConnectionSymbol z p)+
    ((sourceTime 0/n : ℝ) : ℂ) • gaugeConnectionSymbol z p

theorem connection_fiber_vacuum (v : Ambient) (z : SourceCoordinateSlice) :
    connection v z vacuumFiber=0 := nativeFock_vacuum _

theorem scalarConnectionSymbol_vacuum (z : SourceCoordinateSlice) (p : Cotangent) :
    scalarConnectionSymbol z p vacuumFiber=0 := by
  simp only [scalarConnectionSymbol,smul_apply,sum_apply,connection_fiber_vacuum,
    smul_zero,Finset.sum_const_zero]

theorem gaugeConnectionSymbol_vacuum (z : SourceCoordinateSlice) (p : Cotangent) :
    gaugeConnectionSymbol z p vacuumFiber=0 := by
  simp only [gaugeConnectionSymbol,smul_apply,sum_apply,add_apply,connection_fiber_vacuum,
    smul_zero,add_zero,Finset.sum_const_zero]

theorem coframeConnectionSymbol_vacuum (z : SourceCoordinateSlice) (p : Cotangent) :
    coframeConnectionSymbol z p vacuumFiber=0 := by
  simp only [coframeConnectionSymbol,add_apply,sub_apply,smul_apply,quantized_vacuum,
    smul_zero,add_zero,sub_zero]

theorem zeroShiftCurrentSymbol_vacuum (n : ℝ) (z : SourceCoordinateSlice) (p : Cotangent) :
    zeroShiftCurrentSymbol n z p vacuumFiber=0 := by
  simp only [zeroShiftCurrentSymbol,add_apply,smul_apply,scalarConnectionSymbol_vacuum,
    coframeConnectionSymbol_vacuum,gaugeConnectionSymbol_vacuum,add_zero,smul_zero]

def nativePrincipalCurrent (zp : CanonicalPreparationCutoff.FlatConfiguration ×
    CanonicalPreparationSquareCutoff.PhysicalMomentum) : FockFiber →L[ℂ] FockFiber :=
  zeroShiftCurrentSymbol (C (nativePhase zp).1 (nativePhase zp).2)
    (nativePhase zp).1 (nativePhase zp).2

theorem nativePrincipalCurrent_vacuum (zp : CanonicalPreparationCutoff.FlatConfiguration ×
    CanonicalPreparationSquareCutoff.PhysicalMomentum) : nativePrincipalCurrent zp vacuumFiber=0 :=
  zeroShiftCurrentSymbol_vacuum _ _ _

-- This algebraic consumer applies to the original radius weight after its
-- source fold. It supplies no radius, prepared vector or normalization datum.
theorem factor_current_vacuum (zp : CanonicalPreparationCutoff.FlatConfiguration ×
    CanonicalPreparationSquareCutoff.PhysicalMomentum) (weight : ℂ) :
    ((b1 zp : ℂ) • ContinuousLinearMap.id ℂ FockFiber+
      weight • nativePrincipalCurrent zp) vacuumFiber=(b1 zp : ℂ) • vacuumFiber := by
  simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,
    nativePrincipalCurrent_vacuum,smul_zero,add_zero]

theorem coreHalfDensity_square (z : physicalChart) :
    coreHalfDensity 0 z.val*coreHalfDensity 0 z.val=complexDensity 0 z.val := by
  change (Real.sqrt (density 0 z.val) : ℂ)*(Real.sqrt (density 0 z.val) : ℂ)=(density 0 z.val : ℂ)
  have square : Real.sqrt (density 0 z.val)*Real.sqrt (density 0 z.val)=density 0 z.val := by
    simpa only [pow_two] using Real.sq_sqrt (density_pos 0 z).le
  exact_mod_cast square

theorem original_density_derivative (D : SourceCoordinateSlice) (z : physicalChart) :
    fderiv ℝ (complexDensity 0) z.val D=
      2*coreHalfDensity 0 z.val*fderiv ℝ (coreHalfDensity 0) z.val D := by
  have half := ((coreHalfDensity_smooth 0 z).differentiableAt (by simp)).hasFDerivAt
  have same : (fun w => coreHalfDensity 0 w*coreHalfDensity 0 w) =ᶠ[𝓝 z.val] complexDensity 0 := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact coreHalfDensity_square ⟨w,hw⟩
  have equality := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L D) same.fderiv_eq
  have product : fderiv ℝ (fun w => coreHalfDensity 0 w*coreHalfDensity 0 w) z.val=
      coreHalfDensity 0 z.val • fderiv ℝ (coreHalfDensity 0) z.val+
      coreHalfDensity 0 z.val • fderiv ℝ (coreHalfDensity 0) z.val := by
    simpa using! (half.mul half).fderiv
  rw [product] at equality
  simp only [add_apply,smul_apply,smul_eq_mul] at equality
  linear_combination -equality

theorem original_halfDensity_drift_cancel (D : SourceCoordinateSlice) (z : physicalChart) :
    (complexDensity 0 z.val)⁻¹*fderiv ℝ (complexDensity 0) z.val D-
      2*(coreHalfDensity 0 z.val)⁻¹*fderiv ℝ (coreHalfDensity 0) z.val D=0 := by
  rw [original_density_derivative,←coreHalfDensity_square z]
  have nonzero := coreHalfDensity_ne_zero 0 z
  field_simp
  ring

end LowEnergy.PreparationVacuumFactor
