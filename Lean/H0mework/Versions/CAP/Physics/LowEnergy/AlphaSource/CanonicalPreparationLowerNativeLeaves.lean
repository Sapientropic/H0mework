import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerHalfDensity
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationEnergyPrincipalLeaves

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerLeaves
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussNativeForm GaussLiveMomentum
open PreparationActualFactor PreparationVacuumFactor PreparationScalarCoordinates
open PreparationVacuumEnergyTail CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open CanonicalPreparationCore
open SaturationMonoid.PhysicsCore
open scoped BigOperators ContDiff RealInnerProductSpace Matrix

-- These are the actual raw100 coordinate directions and conjugate covectors.
def rawDirection (i : Fin 100) : SourceCoordinateSlice := fullCoordinates.symm (Pi.single i 1)
def rawCovector (i : Fin 100) : Cotangent :=
  nativeCovector (WithLp.toLp 2 (Pi.single i 1))

theorem original_raw_duality (i j : Fin 100) :
    rawCovector i (rawDirection j)=if i=j then 1 else 0 := by
  simp [rawCovector,rawDirection,nativeCovector_apply,Pi.single_apply,eq_comm]

def rawPrincipalCoefficient (j : Fin 13) (i k : Fin 100)
    (z : SourceCoordinateSlice) : ℝ :=
  (originalPrincipalLeaves z (rawCovector i+rawCovector k) j-
    originalPrincipalLeaves z (rawCovector i) j-
    originalPrincipalLeaves z (rawCovector k) j)/2

theorem rawPrincipalCoefficient_symmetric (j : Fin 13) (i k : Fin 100)
    (z : SourceCoordinateSlice) : rawPrincipalCoefficient j i k z=
      rawPrincipalCoefficient j k i z := by
  unfold rawPrincipalCoefficient
  rw [add_comm (rawCovector i)]
  ring

def realSourceHalf (z : SourceCoordinateSlice) : ℝ := Real.sqrt (GaussDensityCore.density 0 z)
def rawHalfLog (i : Fin 100) (z : SourceCoordinateSlice) : ℝ :=
  (realSourceHalf z)⁻¹*fderiv ℝ realSourceHalf z (rawDirection i)

theorem realSourceHalf_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ realSourceHalf z.val :=
  (GaussDensityCore.density_smooth 0 z).sqrt (GaussDensityCore.density_pos 0 z).ne'

theorem sourceHalf_rawLog (i : Fin 100) (z : physicalChart) :
    sourceHalfLog (rawDirection i) z.val=(rawHalfLog i z.val : ℂ) := by
  have derivative:=Complex.ofRealCLM.hasFDerivAt.comp z.val
    ((realSourceHalf_smooth z).differentiableAt (by simp)).hasFDerivAt
  have read : fderiv ℝ sourceHalf z.val=
      Complex.ofRealCLM.comp (fderiv ℝ realSourceHalf z.val) := by
    simpa only [sourceHalf,coreHalfDensity,realSourceHalf] using! derivative.fderiv
  unfold sourceHalfLog rawHalfLog
  rw [read]
  simp only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,
    Complex.ofReal_mul,Complex.ofReal_inv]
  rfl

-- The original density and original principal tensor generate the correction;
-- no lower symbol table or numerical coefficient is supplied.
def nativeHalfCorrection (j : Fin 13) (z : SourceCoordinateSlice) : ℝ :=
  ∑ i : Fin 100, ∑ k : Fin 100,
    (rawPrincipalCoefficient j i k z*
      (rawHalfLog i z*rawHalfLog k z+
        fderiv ℝ (rawHalfLog k) z (rawDirection i))+
      fderiv ℝ (rawPrincipalCoefficient j i k) z (rawDirection i)*rawHalfLog k z)

def nativeWeylCorrection (j : Fin 13) (z : SourceCoordinateSlice) : ℝ :=
  (1/4 : ℝ)*∑ i : Fin 100, ∑ k : Fin 100,
    fderiv ℝ (fun w => fderiv ℝ (rawPrincipalCoefficient j i k) w (rawDirection k))
      z (rawDirection i)

def nativeScalarClassical (z : SourceCoordinateSlice) : ℝ :=
  scalarPotential z/sourceTime 0+3*volume z

def nativeMagneticGram (z : SourceCoordinateSlice) (i j : Fin 3) : ℝ :=
  ⟪magneticField z i,magneticField z j⟫

def nativeMagneticTensor (z : SourceCoordinateSlice) (k l : Fin 3) : ℝ :=
  volume z/sourceSigma*∑ i : Fin 3,∑ j : Fin 3,
    triadInverse z.1 i k*nativeMagneticGram z i j*triadInverse z.1 j l

theorem nativeMagneticTensor_symmetric (z : SourceCoordinateSlice) (k l : Fin 3) :
    nativeMagneticTensor z k l=nativeMagneticTensor z l k := by
  unfold nativeMagneticTensor
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have inner : nativeMagneticGram z j i=nativeMagneticGram z i j := real_inner_comm _ _
  rw [inner]
  ring

def originalClassicalLeaves (z : SourceCoordinateSlice) : Fin 13 → ℝ :=
  ![nativeScalarClassical z,0,0,0,
    nativeMagneticTensor z 0 0,nativeMagneticTensor z 1 1,nativeMagneticTensor z 2 2,
    nativeMagneticTensor z 0 1,nativeMagneticTensor z 0 2,nativeMagneticTensor z 1 2,0,0,0]

def originalZeroLeaves (z : SourceCoordinateSlice) : Fin 14 → ℝ :=
  Fin.snoc (fun j : Fin 13 => originalClassicalLeaves z j+
    nativeHalfCorrection j z+nativeWeylCorrection j z) 0

def scalarContraction (z : SourceCoordinateSlice) (p : Cotangent) (i : Fin 3) : ℝ :=
  ∑ a : ScalarIndex,scalarMomentum z p a*⟪scalarBasis a,scalarGradient z i⟫

def gaugeContraction (z : SourceCoordinateSlice) (p : Cotangent) (i j : Fin 3) : ℝ :=
  ∑ a : LieIndex,electricMomentum z p i a*⟪lieBasis a,magneticField z j⟫

def sourceCross (b : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0,-b 2,b 1;b 2,0,-b 0;-b 1,b 0,0]

def scalarShiftLeaf (z : SourceCoordinateSlice) (p : Cotangent) (r : Fin 3) : ℝ :=
  ∑ i : Fin 3,triadInverse z.1 i r*scalarContraction z p i

def gaugeShiftLeaf (z : SourceCoordinateSlice) (p : Cotangent) (r : Fin 3) : ℝ :=
  volume z*∑ i : Fin 3,∑ j : Fin 3,
    (triadInverse z.1*sourceCross (Pi.single r 1)*(triadInverse z.1).transpose) i j*
      gaugeContraction z p i j

def originalFirstLeaves (z : SourceCoordinateSlice) (p : Cotangent) : Fin 14 → ℝ :=
  ![0,scalarShiftLeaf z p 0,scalarShiftLeaf z p 1,scalarShiftLeaf z p 2,
    0,0,0,0,0,0,gaugeShiftLeaf z p 0,gaugeShiftLeaf z p 1,gaugeShiftLeaf z p 2,0]

def nativeFirstTime (n : ℝ) (b : Fin 3 → ℝ) (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  (∑ r : Fin 3,b r*scalarShiftLeaf z p r)-
    volume z/(n^2-∑ r : Fin 3,b r^2)*∑ i : Fin 3,∑ j : Fin 3,
      (triadInverse z.1*sourceCross b*(triadInverse z.1).transpose) i j*gaugeContraction z p i j

def originalTimeColumn (n : ℝ) (b : Fin 3 → ℝ) : Fin 4 → ℝ := ![n,b 0,b 1,b 2]
def originalElectricBlock (n : ℝ) (b : Fin 3 → ℝ) (z : SourceCoordinateSlice) :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  sourceBFKernel (originalTimeColumn n b) z.1 (Fin.castAdd 3 i) (Fin.castAdd 3 j)
def originalMixedBlock (n : ℝ) (b : Fin 3 → ℝ) (z : SourceCoordinateSlice) :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  sourceBFKernel (originalTimeColumn n b) z.1 (Fin.castAdd 3 i) (Fin.natAdd 3 j)
def actualGaugeFirstTime (n : ℝ) (b : Fin 3 → ℝ)
    (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  -∑ i : Fin 3,∑ j : Fin 3,
    ((originalElectricBlock n b z)⁻¹*originalMixedBlock n b z) i j*gaugeContraction z p i j

def generatedElectricInverse (n : ℝ) (b : Fin 3 → ℝ) (z : SourceCoordinateSlice) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (sourceSigma*volume z/(n*(n^2-∑ r : Fin 3,b r^2))) •
    (triadInverse z.1*(n^2 • (1 : Matrix (Fin 3) (Fin 3) ℝ)-Matrix.vecMulVec b b)*
      (triadInverse z.1).transpose)

theorem originalMixedBlock_generated (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart) :
    originalMixedBlock n b z.val=
      (1/(sourceSigma*n)) • ((triad z.val.1).transpose*sourceCross b*(triadInverse z.val.1).transpose) := by
  have h0:=(ne_of_gt z.property.1)
  have h2:=(ne_of_gt z.property.2.1)
  have h5:=(ne_of_gt z.property.2.2.1)
  ext i j
  unfold originalMixedBlock
  rw [sourceBFKernel_wedge,coframe_determinant]
  fin_cases i <;> fin_cases j <;>
    simp [SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.coframeWedge,
      SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.pairFirst,
      SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.pairSecond,
      SaturationMonoid.PhysicsCore.StageNineGlobalIntegratedAction.lorentzianTwoFormSign,coframe,originalTimeColumn,
      sourceCross,triad,triadInverse,Matrix.mul_apply,Fin.sum_univ_six,Fin.sum_univ_three] <;>
    field_simp <;> ring

theorem originalElectricInverse_generated (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart)
    (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    (originalElectricBlock n b z.val)⁻¹=generatedElectricInverse n b z.val := by
  apply Matrix.inv_eq_right_inv
  have hs:=source_sigma_nonzero
  have h0:=(ne_of_gt z.property.1)
  have h2:=(ne_of_gt z.property.2.1)
  have h5:=(ne_of_gt z.property.2.2.1)
  have hd : n^2-(b 0^2+b 1^2+b 2^2)≠0 := by simpa only [Fin.sum_univ_three] using timelike
  ext i j
  simp only [Matrix.mul_apply,originalElectricBlock,sourceBFKernel_wedge,coframe_determinant,
    generatedElectricInverse,Matrix.smul_apply,Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.coframeWedge,
      SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.pairFirst,
      SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.pairSecond,
      SaturationMonoid.PhysicsCore.StageNineGlobalIntegratedAction.lorentzianTwoFormSign,coframe,originalTimeColumn,
      triadInverse,Matrix.vecMulVec,
      Fin.sum_univ_six,Fin.sum_univ_three,volume] <;>
    field_simp <;> ring

theorem originalGaugeMix_generated (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart)
    (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    (originalElectricBlock n b z.val)⁻¹*originalMixedBlock n b z.val=
      (volume z.val/(n^2-∑ r : Fin 3,b r^2)) •
        (triadInverse z.val.1*sourceCross b*(triadInverse z.val.1).transpose) := by
  rw [originalElectricInverse_generated n b z timeNonzero timelike,
    originalMixedBlock_generated]
  have hs:=source_sigma_nonzero
  have h0:=(ne_of_gt z.property.1)
  have h2:=(ne_of_gt z.property.2.1)
  have h5:=(ne_of_gt z.property.2.2.1)
  have hd : n^2-(b 0^2+b 1^2+b 2^2)≠0 := by simpa only [Fin.sum_univ_three] using timelike
  ext i j
  simp only [generatedElectricInverse,Matrix.smul_apply,Matrix.mul_apply,Matrix.sub_apply,
    Matrix.transpose_apply,Matrix.vecMulVec_apply,Matrix.one_apply,smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp [sourceCross,triad,triadInverse,Fin.sum_univ_three,volume] <;> field_simp <;> ring

theorem actualGaugeFirstTime_readback (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart)
    (p : Cotangent) (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    actualGaugeFirstTime n b z.val p=
      -volume z.val/(n^2-∑ r : Fin 3,b r^2)*∑ i : Fin 3,∑ j : Fin 3,
        (triadInverse z.val.1*sourceCross b*(triadInverse z.val.1).transpose) i j*
          gaugeContraction z.val p i j := by
  rw [actualGaugeFirstTime,originalGaugeMix_generated n b z timeNonzero timelike]
  simp only [Matrix.smul_apply,smul_eq_mul,mul_assoc,←Finset.mul_sum]
  ring

def generatedCoframeInverse (n : ℝ) (b : Fin 3 → ℝ) (q : Coframe) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![n⁻¹,0,0,0;
    -(∑ r : Fin 3,triadInverse q 0 r*b r)/n,triadInverse q 0 0,triadInverse q 0 1,triadInverse q 0 2;
    -(∑ r : Fin 3,triadInverse q 1 r*b r)/n,triadInverse q 1 0,triadInverse q 1 1,triadInverse q 1 2;
    -(∑ r : Fin 3,triadInverse q 2 r*b r)/n,triadInverse q 2 0,triadInverse q 2 1,triadInverse q 2 2]

theorem originalCoframeInverse_generated (n : ℝ) (b : Fin 3 → ℝ)
    (z : physicalChart) (timeNonzero : n≠0) :
    (coframe (originalTimeColumn n b) z.val.1)⁻¹=generatedCoframeInverse n b z.val.1 := by
  apply Matrix.inv_eq_right_inv
  have h0:=(ne_of_gt z.property.1)
  have h2:=(ne_of_gt z.property.2.1)
  have h5:=(ne_of_gt z.property.2.2.1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coframe,originalTimeColumn,generatedCoframeInverse,triadInverse,
      Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_three] <;> field_simp <;> ring

def originalScalarMetric (n : ℝ) (b : Fin 3 → ℝ) (z : SourceCoordinateSlice) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  (coframe (originalTimeColumn n b) z.1).det •
    (lorentzianMetricOfCoframe (coframe (originalTimeColumn n b) z.1))⁻¹

def actualScalarFirstTime (n : ℝ) (b : Fin 3 → ℝ)
    (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  -∑ i : Fin 3, originalScalarMetric n b z 0 (Fin.succ i)/originalScalarMetric n b z 0 0*
    scalarContraction z p i

private theorem originalMinkowskiInverse : minkowskiInternalMetric⁻¹=minkowskiInternalMetric := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowskiInternalMetric,Matrix.mul_apply,Fin.sum_univ_four]

theorem originalScalarMixed_generated (n : ℝ) (b : Fin 3 → ℝ)
    (z : physicalChart) (timeNonzero : n≠0) (i : Fin 3) :
    originalScalarMetric n b z.val 0 (Fin.succ i)/originalScalarMetric n b z.val 0 0=
      -(∑ r : Fin 3,triadInverse z.val.1 i r*b r) := by
  have formula : originalScalarMetric n b z.val=
      (n*volume z.val) • (generatedCoframeInverse n b z.val.1*minkowskiInternalMetric*
        (generatedCoframeInverse n b z.val.1).transpose) := by
    unfold originalScalarMetric lorentzianMetricOfCoframe
    rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv,
      originalMinkowskiInverse,originalCoframeInverse_generated n b z timeNonzero,
      coframe_determinant]
    simp only [originalTimeColumn,Matrix.mul_assoc,volume]
    rfl
  rw [formula]
  have h0:=(ne_of_gt z.property.1)
  have h2:=(ne_of_gt z.property.2.1)
  have h5:=(ne_of_gt z.property.2.2.1)
  simp only [Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,smul_eq_mul]
  fin_cases i <;>
    simp [generatedCoframeInverse,triadInverse,minkowskiInternalMetric,
      Fin.sum_univ_four,Fin.sum_univ_three,volume] <;> field_simp

theorem actualScalarFirstTime_readback (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart)
    (p : Cotangent) (timeNonzero : n≠0) :
    actualScalarFirstTime n b z.val p=∑ r : Fin 3,b r*scalarShiftLeaf z.val p r := by
  simp only [actualScalarFirstTime,originalScalarMixed_generated n b z timeNonzero,
    neg_mul,Finset.sum_neg_distrib,neg_neg,Finset.sum_mul,scalarShiftLeaf,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem originalMixedHamiltonian_readback (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart)
    (p : Cotangent) (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    actualScalarFirstTime n b z.val p+actualGaugeFirstTime n b z.val p=
      nativeFirstTime n b z.val p := by
  rw [actualScalarFirstTime_readback n b z p timeNonzero,
    actualGaugeFirstTime_readback n b z p timeNonzero timelike]
  unfold nativeFirstTime
  ring

theorem scalarShiftLeaf_add (z : SourceCoordinateSlice) (p q : Cotangent) (r : Fin 3) :
    scalarShiftLeaf z (p+q) r=scalarShiftLeaf z p r+scalarShiftLeaf z q r := by
  simp only [scalarShiftLeaf,scalarContraction,scalarMomentum,add_apply,add_mul,
    Finset.sum_add_distrib,mul_add]

theorem gaugeShiftLeaf_add (z : SourceCoordinateSlice) (p q : Cotangent) (r : Fin 3) :
    gaugeShiftLeaf z (p+q) r=gaugeShiftLeaf z p r+gaugeShiftLeaf z q r := by
  simp only [gaugeShiftLeaf,gaugeContraction,electricMomentum,add_apply,add_mul,
    Finset.sum_add_distrib,mul_add]

theorem scalarShiftLeaf_smul (z : SourceCoordinateSlice) (p : Cotangent) (s : ℝ) (r : Fin 3) :
    scalarShiftLeaf z (s • p) r=s*scalarShiftLeaf z p r := by
  simp only [scalarShiftLeaf,scalarContraction,scalarMomentum,smul_apply,smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem gaugeShiftLeaf_smul (z : SourceCoordinateSlice) (p : Cotangent) (s : ℝ) (r : Fin 3) :
    gaugeShiftLeaf z (s • p) r=s*gaugeShiftLeaf z p r := by
  simp only [gaugeShiftLeaf,gaugeContraction,electricMomentum,smul_apply,smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

def originalFirstLinear (z : SourceCoordinateSlice) : Cotangent →ₗ[ℝ] (Fin 14 → ℝ) where
  toFun := originalFirstLeaves z
  map_add' p q := by
    ext j
    fin_cases j <;> simp [originalFirstLeaves,scalarShiftLeaf_add,gaugeShiftLeaf_add]
  map_smul' s p := by
    ext j
    fin_cases j <;> simp [originalFirstLeaves,scalarShiftLeaf_smul,gaugeShiftLeaf_smul]

def rawFirstDerivative (z : SourceCoordinateSlice) : PhysicalMomentum →L[ℝ] (Fin 14 → ℝ) :=
  originalFirstLinear z |>.toContinuousLinearMap |>.comp nativeCovectorMap

theorem originalFirstLeaves_canonical_derivative (z : SourceCoordinateSlice) (p : PhysicalMomentum) :
    HasFDerivAt (fun v => originalFirstLeaves z (nativeCovector v)) (rawFirstDerivative z) p :=
  (rawFirstDerivative z).hasFDerivAt

theorem originalFirstLeaves_canonical_second (z : SourceCoordinateSlice) (p : PhysicalMomentum) :
    fderiv ℝ (fun v => fderiv ℝ (fun w => originalFirstLeaves z (nativeCovector w)) v) p=0 := by
  simp only [(originalFirstLeaves_canonical_derivative z _).fderiv]
  simp

theorem sourceCross_generated (b : Fin 3 → ℝ) :
    sourceCross b=∑ r : Fin 3,b r • sourceCross (Pi.single r 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceCross,Fin.sum_univ_three,Pi.single_apply]

theorem originalFirstTemporalReplay (n : ℝ) (b : Fin 3 → ℝ)
    (z : SourceCoordinateSlice) (p : Cotangent) :
    (∑ j : Fin 13,originalTemporalWeights n b j*originalFirstLeaves z p (Fin.castSucc j))=
      nativeFirstTime n b z p := by
  have linear : (∑ r : Fin 3,b r*gaugeShiftLeaf z p r)=
      volume z*∑ i : Fin 3,∑ j : Fin 3,
      (triadInverse z.1*sourceCross b*(triadInverse z.1).transpose) i j*gaugeContraction z p i j := by
    rw [sourceCross_generated]
    simp only [gaugeShiftLeaf,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,
      Matrix.smul_mul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro r _
    ring
  unfold nativeFirstTime
  have product : volume z/(n^2-∑ r : Fin 3,b r^2)*
      (∑ i : Fin 3,∑ j : Fin 3,
      (triadInverse z.1*sourceCross b*(triadInverse z.1).transpose) i j*gaugeContraction z p i j)=
      (∑ r : Fin 3,b r*gaugeShiftLeaf z p r)/(n^2-∑ r : Fin 3,b r^2) := by
    rw [linear]
    ring
  rw [product]
  simp only [Fin.sum_univ_three]
  unfold originalTemporalWeights originalFirstLeaves
  norm_num [Fin.sum_univ_succ]
  ring

theorem originalFirstLeaves_zeroShift (n : ℝ) (z : SourceCoordinateSlice) (p : Cotangent) :
    (∑ j : Fin 13,originalTemporalWeights n 0 j*originalFirstLeaves z p (Fin.castSucc j))=0 := by
  rw [originalFirstTemporalReplay]
  have zero : sourceCross (0 : Fin 3 → ℝ)=0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [sourceCross]
  simp [nativeFirstTime,zero]

theorem original_zeroShiftClassical (z : physicalChart) :
    (∑ j : Fin 13,originalTemporalWeights (sourceTime 0) 0 j*originalClassicalLeaves z.val j)=
      originalScalarPotential z.val+originalMagneticPotential z.val+
        GaussCoframeForm.volumePotential z.val := by
  have trace : (∑ k : Fin 3,nativeMagneticTensor z.val k k)=
      volume z.val/sourceSigma*∑ i : Fin 3,∑ j : Fin 3,
        inverseSpatial z.val i j*nativeMagneticGram z.val i j := by
    simp only [nativeMagneticTensor,inverseSpatial,Matrix.mul_apply,Matrix.transpose_apply,
      Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [scalar_potential_source z,magnetic_potential_source z]
  unfold originalTemporalWeights originalClassicalLeaves
  norm_num [Fin.sum_univ_succ]
  have nonzero:=source_time_nonzero
  have zeroTrace : ((sourceTime 0)^2/(2*sourceTime 0*((sourceTime 0)^2)))*
      (nativeMagneticTensor z.val 0 0+nativeMagneticTensor z.val 1 1+nativeMagneticTensor z.val 2 2)=
      magneticPotential z.val := by
    have read : nativeMagneticTensor z.val 0 0+nativeMagneticTensor z.val 1 1+
        nativeMagneticTensor z.val 2 2=
      volume z.val/sourceSigma*∑ i : Fin 3,∑ j : Fin 3,
        inverseSpatial z.val i j*nativeMagneticGram z.val i j := by
      simpa only [Fin.sum_univ_three] using trace
    rw [read]
    unfold magneticPotential nativeMagneticGram
    field_simp
  unfold nativeScalarClassical
  have scalarRead : sourceTime 0*(scalarPotential z.val/sourceTime 0+3*volume z.val)=
      scalarPotential z.val+3*sourceTime 0*volume z.val := by field_simp
  rw [scalarRead]
  unfold GaussCoframeForm.volumePotential
  linear_combination zeroTrace

end LowEnergy.PreparationVacuumLowerLeaves
