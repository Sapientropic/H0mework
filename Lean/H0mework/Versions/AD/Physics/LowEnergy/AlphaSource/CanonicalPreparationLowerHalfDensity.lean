import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerNativeDifferential

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerLeaves
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussDensityCore GaussScalarTransport GaussCoreDifferential
open PreparationVacuumFactor CanonicalPreparationCore
open scoped ContDiff Topology

def sourceHalf (z : SourceCoordinateSlice) : ℂ := coreHalfDensity 0 z

def sourceHalfLog (D z : SourceCoordinateSlice) : ℂ :=
  (sourceHalf z)⁻¹*fderiv ℝ sourceHalf z D

def halfCore : ScalarTest →ₗ[ℂ] ScalarTest :=
  multiply sourceHalf (coreHalfDensity_smooth 0)

def inverseHalfCore : ScalarTest →ₗ[ℂ] ScalarTest :=
  multiply (fun z => (sourceHalf z)⁻¹)
    (fun z => (coreHalfDensity_smooth 0 z).inv (coreHalfDensity_ne_zero 0 z))

theorem inverseHalfCore_apply (f : ScalarTest) (z : SourceCoordinateSlice) :
    inverseHalfCore f z=(sourceHalf z)⁻¹*f z := rfl

theorem sourceHalf_inverseCore (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*inverseHalfCore f z.val=f z.val := by
  rw [inverseHalfCore_apply]
  have nz:=coreHalfDensity_ne_zero 0 z
  change coreHalfDensity 0 z.val*((coreHalfDensity 0 z.val)⁻¹*f z.val)=f z.val
  rw [←mul_assoc,mul_inv_cancel₀ nz,one_mul]

theorem densityDrift_halfLog (D : SourceCoordinateSlice) (z : physicalChart) :
    densityDrift D z.val=2*sourceHalfLog D z.val := by
  have original:=original_halfDensity_drift_cancel D z
  unfold densityDrift sourceHalfLog sourceHalf
  linear_combination original

theorem sourceHalf_derivative_readback (D : SourceCoordinateSlice) (f : ScalarTest)
    (z : physicalChart) :
    sourceHalf z.val*fderiv ℝ (inverseHalfCore f) z.val D=
      fderiv ℝ f z.val D-sourceHalfLog D z.val*f z.val := by
  have hu:=((coreHalfDensity_smooth 0 z).differentiableAt (by simp)).hasFDerivAt
  have hg:=((inverseHalfCore f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z.val)
  have equal : (fun w => sourceHalf w*inverseHalfCore f w)=ᶠ[𝓝 z.val] f := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact sourceHalf_inverseCore f ⟨w,hw⟩
  have derived:=congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L D) equal.fderiv_eq
  have product : fderiv ℝ (fun w => sourceHalf w*inverseHalfCore f w) z.val=
      sourceHalf z.val • fderiv ℝ (inverseHalfCore f) z.val+
        inverseHalfCore f z.val • fderiv ℝ sourceHalf z.val := by
    simpa only [sourceHalf] using! (hu.mul hg).fderiv
  rw [product] at derived
  simp only [add_apply,smul_apply,smul_eq_mul,inverseHalfCore_apply] at derived
  unfold sourceHalfLog
  linear_combination derived

theorem sourceHalf_fieldDerivative (v : GaussLiveMomentum.Ambient) (f : ScalarTest)
    (z : physicalChart) :
    sourceHalf z.val*fieldDerivative v (inverseHalfCore f) z.val=
      fieldD v f z.val-sourceHalfLog (direction v z.val) z.val*f z.val := by
  rw [fieldDerivative_apply]
  exact sourceHalf_derivative_readback _ f z

theorem sourceHalf_fieldTranspose (v : GaussLiveMomentum.Ambient) (f : ScalarTest)
    (z : physicalChart) :
    sourceHalf z.val*fieldTranspose 0 v (inverseHalfCore f) z.val=
      -fieldD v f z.val-(divergence v z.val+sourceHalfLog (direction v z.val) z.val)*f z.val := by
  rw [original_fieldTranspose_readback]
  unfold fieldT
  rw [densityDrift_halfLog,inverseHalfCore_apply]
  have derivative:=sourceHalf_derivative_readback (direction v z.val) f z
  change sourceHalf z.val*(-fderiv ℝ (inverseHalfCore f) z.val (direction v z.val)-
      (divergence v z.val+2*sourceHalfLog (direction v z.val) z.val)*
        ((sourceHalf z.val)⁻¹*f z.val))=_
  change sourceHalf z.val*fderiv ℝ (inverseHalfCore f) z.val (direction v z.val)=
    fieldD v f z.val-sourceHalfLog (direction v z.val) z.val*f z.val at derivative
  have cancel : sourceHalf z.val*((sourceHalf z.val)⁻¹*f z.val)=f z.val :=
    sourceHalf_inverseCore f z
  calc
    _=-(sourceHalf z.val*fderiv ℝ (inverseHalfCore f) z.val (direction v z.val))-
      (divergence v z.val+2*sourceHalfLog (direction v z.val) z.val)*
        (sourceHalf z.val*((sourceHalf z.val)⁻¹*f z.val)) := by ring
    _=_ := by rw [derivative,cancel]; ring

theorem sourceHalf_constantTranspose (D : SourceCoordinateSlice) (f : ScalarTest)
    (z : physicalChart) :
    sourceHalf z.val*weightedTranspose 0 D (inverseHalfCore f) z.val=
      -constantD D f z.val-sourceHalfLog D z.val*f z.val := by
  rw [original_constantTranspose_readback]
  unfold constantT
  rw [densityDrift_halfLog,inverseHalfCore_apply]
  have derivative:=sourceHalf_derivative_readback D f z
  have cancel : sourceHalf z.val*((sourceHalf z.val)⁻¹*f z.val)=f z.val :=
    sourceHalf_inverseCore f z
  unfold constantD
  calc
    _=-(sourceHalf z.val*fderiv ℝ (inverseHalfCore f) z.val D)-
      (2*sourceHalfLog D z.val)*(sourceHalf z.val*((sourceHalf z.val)⁻¹*f z.val)) := by ring
    _=_ := by rw [derivative,cancel]; ring

def originalHalfDensityLocalAction (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  sourceHalf z*originalLocalVacuumAction (fun w => (sourceHalf w)⁻¹*f w) z

def originalHalfDensityPotential (z : SourceCoordinateSlice) : ℂ :=
  originalHalfDensityLocalAction (fun _ => 1) z

theorem originalHalfDensityLocalAction_readback (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*scalarVacuumAction (inverseHalfCore f) z.val=
      originalHalfDensityLocalAction f z.val := by
  rw [originalLocalVacuumAction_readback]
  rfl

end LowEnergy.PreparationVacuumLowerLeaves
