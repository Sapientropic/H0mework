import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalTimePairTensor

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTemporalOrdering
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussNativeForm GaussDensityCore
open GaussLiveMomentum GaussCoreDifferential GaussScalarTransport
open PreparationScalarCoordinates CanonicalPreparationCore PreparationActualFactor
open PreparationVacuumLowerLeaves PreparationVacuumLowerTensor PreparationVacuumDensityTrace
open PreparationVacuumEnergyTail PreparationVacuumFactor PreparationVacuumWeylOrdering
open SaturationMonoid.PhysicsCore
open scoped BigOperators ContDiff Topology Matrix RealInnerProductSpace

theorem actualElectricInverse_smooth (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (i j : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => (originalElectricBlock n b w)⁻¹ i j) z.val := by
  have smooth : ContDiffAt ℝ ∞ (fun w => generatedElectricInverse n b w i j) z.val := by
    unfold generatedElectricInverse
    simp only [Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,smul_eq_mul]
    apply (contDiffAt_const.mul volume_smooth.contDiffAt |>.div_const _).mul
    apply ContDiffAt.sum
    intro a _
    apply (ContDiffAt.sum (fun k _ => (triadInverse_smooth i k z).mul contDiffAt_const)).mul
      (triadInverse_smooth j a z)
  apply smooth.congr_of_eventuallyEq
  filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j)
    (originalElectricInverse_generated n b ⟨w,hw⟩ hn hd)

theorem actualTimePairCoefficient_smooth (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (a : SourcePair) (z : physicalChart) :
    ContDiffAt ℝ ∞ (actualTimePairCoefficient n b a) z.val := by
  rcases a with i|⟨a,i,j⟩|⟨i,j⟩
  · exact (contDiffAt_const.mul (scalarWeight_smooth z)).div_const 2
  · exact (actualElectricInverse_smooth n b hn hd i j z).div_const 2
  · exact contDiffAt_const.mul (GaussCoframeKinetic.coefficient_smooth i j z)

def actualTimePairAction (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (a : SourcePair) : ScalarTest →ₗ[ℂ] ScalarTest :=
  match a with
  | Sum.inl i => scalarSandwich (scalarDirection i) (scalarDirection i)
      (actualTimePairCoefficient n b a) (actualTimePairCoefficient_smooth n b hn hd a)
  | Sum.inr (Sum.inl (v,i,j)) => scalarSandwich (gaugeDirection i v) (gaugeDirection j v)
      (actualTimePairCoefficient n b a) (actualTimePairCoefficient_smooth n b hn hd a)
  | Sum.inr (Sum.inr (i,j)) => (weightedTranspose 0 (GaussCoframeCore.coframeDirection i)).comp
      ((realCoefficient (actualTimePairCoefficient n b a)
        (actualTimePairCoefficient_smooth n b hn hd a)).comp
          (GaussDensityCore.derivative (GaussCoframeCore.coframeDirection j)))

def actualPairFlux (n : ℝ) (b : Fin 3 → ℝ) (a : SourcePair) (f : Profile)
    (z : SourceCoordinateSlice) (i : Fin 100) : ℂ :=
  (actualTimePairCoefficient n b a z : ℂ)*(rawCovector i (sourceLeft a z) : ℂ)*
    fderiv ℝ f z (sourceRight a z)

theorem actualPairFlux_smooth (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (a : SourcePair) (f : ScalarTest)
    (i : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => actualPairFlux n b a f w i) z.val := by
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
    (actualTimePairCoefficient_smooth n b hn hd a z)
  have hl := Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
    ((rawCovector i).contDiff.contDiffAt.comp z.val (sourceLeft_smooth a z))
  have df : ContDiff ℝ ∞ (fderiv ℝ f) := f.contDiff.fderiv_right (by simp)
  exact (hc.mul hl).mul (df.contDiffAt.clm_apply (sourceRight_smooth a z))

theorem actualPairAction_raw (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (a : SourcePair) (f : ScalarTest) (z : physicalChart) :
    actualTimePairAction n b hn hd a f z.val=rawWeightedDivergence (actualPairFlux n b a f) z.val := by
  rcases a with i|⟨v,i,j⟩|⟨i,j⟩
  · let g := realCoefficient (actualTimePairCoefficient n b (Sum.inl i))
      (actualTimePairCoefficient_smooth n b hn hd (Sum.inl i)) (fieldDerivative (scalarDirection i) f)
    have equal : actualPairFlux n b (Sum.inl i) f=rawFieldFlux (scalarDirection i) g := by
      funext w k
      change (actualTimePairCoefficient n b (Sum.inl i) w : ℂ)*
        (rawCovector k (direction (scalarDirection i) w) : ℂ)*
          fderiv ℝ f w (direction (scalarDirection i) w)=
        (rawCovector k (direction (scalarDirection i) w) : ℂ)*
          ((actualTimePairCoefficient n b (Sum.inl i) w : ℂ)*fieldDerivative (scalarDirection i) f w)
      rw [fieldDerivative_apply]
      ring
    rw [equal]
    exact original_fieldTranspose_rawFlux _ g z
  · let g := realCoefficient (actualTimePairCoefficient n b (Sum.inr (Sum.inl (v,i,j))))
      (actualTimePairCoefficient_smooth n b hn hd (Sum.inr (Sum.inl (v,i,j))))
        (fieldDerivative (gaugeDirection j v) f)
    have equal : actualPairFlux n b (Sum.inr (Sum.inl (v,i,j))) f=rawFieldFlux (gaugeDirection i v) g := by
      funext w k
      change (actualTimePairCoefficient n b (Sum.inr (Sum.inl (v,i,j))) w : ℂ)*
        (rawCovector k (direction (gaugeDirection i v) w) : ℂ)*
          fderiv ℝ f w (direction (gaugeDirection j v) w)=
        (rawCovector k (direction (gaugeDirection i v) w) : ℂ)*
          ((actualTimePairCoefficient n b (Sum.inr (Sum.inl (v,i,j))) w : ℂ)*fieldDerivative (gaugeDirection j v) f w)
      rw [fieldDerivative_apply]
      ring
    rw [equal]
    exact original_fieldTranspose_rawFlux _ g z
  · let g := realCoefficient (actualTimePairCoefficient n b (Sum.inr (Sum.inr (i,j))))
      (actualTimePairCoefficient_smooth n b hn hd (Sum.inr (Sum.inr (i,j))))
        (GaussDensityCore.derivative (GaussCoframeCore.coframeDirection j) f)
    have equal : actualPairFlux n b (Sum.inr (Sum.inr (i,j))) f=
        constantFlux (GaussCoframeCore.coframeDirection i) g := by
      funext w k
      change (actualTimePairCoefficient n b (Sum.inr (Sum.inr (i,j))) w : ℂ)*
        (rawCovector k (GaussCoframeCore.coframeDirection i) : ℂ)*
          fderiv ℝ f w (GaussCoframeCore.coframeDirection j)=
        (rawCovector k (GaussCoframeCore.coframeDirection i) : ℂ)*
          ((actualTimePairCoefficient n b (Sum.inr (Sum.inr (i,j))) w : ℂ)*
            GaussDensityCore.derivative (GaussCoframeCore.coframeDirection j) f w)
      rw [GaussDensityCore.derivative_apply]
      ring
    rw [equal]
    exact original_constantTranspose_rawFlux _ g z

def actualTimeFlux (n : ℝ) (b : Fin 3 → ℝ) (f : Profile)
    (z : SourceCoordinateSlice) (i : Fin 100) : ℂ := ∑ a : SourcePair,actualPairFlux n b a f z i

theorem actualTimeFlux_tensor (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (f : Profile) (z : physicalChart) (i : Fin 100) :
    actualTimeFlux n b f z.val i=∑ k : Fin 100,timeTensor n b i k z.val*D k f z.val := by
  have raw : actualTimeFlux n b f z.val i=
      ∑ k : Fin 100,(actualTimePairTensor n b i k z.val : ℂ)*D k f z.val := by
    unfold actualTimeFlux actualPairFlux actualTimePairTensor
    simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    have read := original_raw_read (sourceRight a z.val) (fderiv ℝ f z.val)
    rw [show (∑ k : Fin 100,(actualTimePairCoefficient n b a z.val : ℂ)*
        (rawCovector i (sourceLeft a z.val) : ℂ)*(rawCovector k (sourceRight a z.val) : ℂ)*D k f z.val)=
      (actualTimePairCoefficient n b a z.val : ℂ)*(rawCovector i (sourceLeft a z.val) : ℂ)*
        (∑ k : Fin 100,(rawCovector k (sourceRight a z.val) : ℂ)*D k f z.val) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring]
    change _=(actualTimePairCoefficient n b a z.val : ℂ)*
      (rawCovector i (sourceLeft a z.val) : ℂ)*
        (∑ k : Fin 100,(rawCovector k (sourceRight a z.val) : ℂ)*fderiv ℝ f z.val (rawDirection k))
    rw [read]
  rw [raw]
  simp only [actualTimePairTensor_extraction n b _ _ z hn hd]

theorem actualTimeKinetic_raw (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (f : ScalarTest) (z : physicalChart) :
    (∑ a : SourcePair,actualTimePairAction n b hn hd a f z.val)=
      rawWeightedDivergence (actualTimeFlux n b f) z.val := by
  simp only [actualPairAction_raw]
  symm
  unfold rawWeightedDivergence actualTimeFlux
  have derivative (i : Fin 100) :
      fderiv ℝ (fun w => ∑ a : SourcePair,actualPairFlux n b a f w i) z.val=
        ∑ a : SourcePair,fderiv ℝ (fun w => actualPairFlux n b a f w i) z.val :=
    fderiv_fun_sum (fun a _ => (actualPairFlux_smooth n b hn hd a f i z).differentiableAt (by simp))
  simp only [derivative,sum_apply,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  congr 1
  exact Finset.sum_comm

def actualScalarSchur (n : ℝ) (b : Fin 3 → ℝ) (z : SourceCoordinateSlice) (i j : Fin 3) : ℝ :=
  originalScalarMetric n b z (Fin.succ i) (Fin.succ j)-
    originalScalarMetric n b z (Fin.succ i) 0*originalScalarMetric n b z 0 (Fin.succ j)/
      originalScalarMetric n b z 0 0

def originalMagneticBlock (n : ℝ) (b : Fin 3 → ℝ) (z : SourceCoordinateSlice) :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  sourceBFKernel (originalTimeColumn n b) z.1 (Fin.natAdd 3 i) (Fin.natAdd 3 j)

def actualMagneticSchur (n : ℝ) (b : Fin 3 → ℝ) (z : SourceCoordinateSlice) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (originalMixedBlock n b z).transpose*(originalElectricBlock n b z)⁻¹*originalMixedBlock n b z-
    originalMagneticBlock n b z

private theorem minkowskiInverse : minkowskiInternalMetric⁻¹=minkowskiInternalMetric := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowskiInternalMetric,Matrix.mul_apply,Fin.sum_univ_four]

theorem actualScalarSchur_generated (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (z : physicalChart) (i j : Fin 3) :
    actualScalarSchur n b z.val i j=n*volume z.val*inverseSpatial z.val i j := by
  have formula : originalScalarMetric n b z.val=
      (n*volume z.val) • (generatedCoframeInverse n b z.val.1*minkowskiInternalMetric*
        (generatedCoframeInverse n b z.val.1).transpose) := by
    unfold originalScalarMetric lorentzianMetricOfCoframe
    rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv,minkowskiInverse,
      originalCoframeInverse_generated n b z hn,coframe_determinant]
    simp only [originalTimeColumn,Matrix.mul_assoc,volume]
    rfl
  unfold actualScalarSchur
  rw [formula]
  have h0 := (ne_of_gt z.property.1)
  have h2 := (ne_of_gt z.property.2.1)
  have h5 := (ne_of_gt z.property.2.2.1)
  simp only [Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp [generatedCoframeInverse,minkowskiInternalMetric,
      inverseSpatial,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_four,Fin.sum_univ_three,
      triadInverse,volume] <;> field_simp <;> ring

theorem actualMagneticSchur_generated (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (z : physicalChart) :
    actualMagneticSchur n b z.val=
      (sourceSigma^2)⁻¹ • generatedElectricInverse n b z.val := by
  have hs := source_sigma_nonzero
  have h0 := (ne_of_gt z.property.1)
  have h2 := (ne_of_gt z.property.2.1)
  have h5 := (ne_of_gt z.property.2.2.1)
  have delta : n^2-(b 0^2+b 1^2+b 2^2)≠0 := by simpa only [Fin.sum_univ_three] using hd
  apply Matrix.ext
  intro i j
  simp only [actualMagneticSchur,Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply]
  simp only [originalElectricInverse_generated n b z hn hd,originalMixedBlock_generated n b z,
    originalMagneticBlock,sourceBFKernel_wedge,coframe_determinant]
  simp only [generatedElectricInverse,Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,
    Matrix.sub_apply,Matrix.vecMulVec_apply,Matrix.one_apply,smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp [coframe,originalTimeColumn,
      SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.coframeWedge,
      SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.pairFirst,
      SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.pairSecond,
      SaturationMonoid.PhysicsCore.StageNineGlobalIntegratedAction.lorentzianTwoFormSign,
      triad,triadInverse,sourceCross,volume,Fin.sum_univ_six,Fin.sum_univ_three] <;>
    field_simp <;> ring

def actualTimeClassical (n : ℝ) (b : Fin 3 → ℝ) (z : SourceCoordinateSlice) : ℝ :=
  (coframe (originalTimeColumn n b) z.1).det*⟪scalarField z-vacuum,scalarField z-vacuum⟫-
    (1/2 : ℝ)*∑ i : Fin 3,∑ j : Fin 3,actualScalarSchur n b z i j*
      ⟪scalarGradient z i,scalarGradient z j⟫+
    (1/2 : ℝ)*∑ i : Fin 3,∑ j : Fin 3,actualMagneticSchur n b z i j*
      ⟪magneticField z i,magneticField z j⟫+
    (n/sourceTime 0)*GaussCoframeForm.volumePotential z

theorem actualTimeClassical_extraction (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (z : physicalChart) :
    actualTimeClassical n b z.val=
      ∑ j : Fin 13,originalTemporalWeights n b j*originalClassicalLeaves z.val j := by
  have magnetic : (1/2 : ℝ)*∑ i : Fin 3,∑ j : Fin 3,actualMagneticSchur n b z.val i j*
      ⟪magneticField z.val i,magneticField z.val j⟫=
      ∑ j : Fin 13,originalTemporalWeights n b j*
        (![0,0,0,0,nativeMagneticTensor z.val 0 0,nativeMagneticTensor z.val 1 1,
          nativeMagneticTensor z.val 2 2,nativeMagneticTensor z.val 0 1,
          nativeMagneticTensor z.val 0 2,nativeMagneticTensor z.val 1 2,0,0,0] : Fin 13 → ℝ) j := by
    rw [actualMagneticSchur_generated n b hn hd z]
    simp only [Matrix.smul_apply,smul_eq_mul]
    have symmetric (i j : Fin 3) : ⟪magneticField z.val j,magneticField z.val i⟫=
        ⟪magneticField z.val i,magneticField z.val j⟫ := real_inner_comm _ _
    unfold originalTemporalWeights nativeMagneticTensor nativeMagneticGram generatedElectricInverse
    simp [Fin.sum_univ_succ,Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.sub_apply,Matrix.vecMulVec_apply,Matrix.one_apply]
    rw [symmetric 0 1,symmetric 0 2,symmetric 1 2]
    have delta : n^2-(b 0^2+b 1^2+b 2^2)≠0 := by simpa only [Fin.sum_univ_three] using hd
    have hs := source_sigma_nonzero
    field_simp
    ring
  unfold actualTimeClassical
  rw [magnetic,show (coframe (originalTimeColumn n b) z.val.1).det=n*volume z.val by
    rw [coframe_determinant]; rfl]
  simp only [actualScalarSchur_generated n b hn z]
  have scalar : n*volume z.val*⟪scalarField z.val-vacuum,scalarField z.val-vacuum⟫-
      (1/2 : ℝ)*∑ i : Fin 3,∑ j : Fin 3,n*volume z.val*inverseSpatial z.val i j*
        ⟪scalarGradient z.val i,scalarGradient z.val j⟫+
      (n/sourceTime 0)*GaussCoframeForm.volumePotential z.val=n*nativeScalarClassical z.val := by
    simp only [scalarField,add_sub_cancel_left,nativeScalarClassical,scalarPotential,
      GaussCoframeForm.volumePotential,←Finset.mul_sum,mul_assoc]
    have nn := source_time_nonzero
    field_simp
  have reorder : n*volume z.val*⟪scalarField z.val-vacuum,scalarField z.val-vacuum⟫-
      (1/2 : ℝ)*∑ i : Fin 3,∑ j : Fin 3,n*volume z.val*inverseSpatial z.val i j*
        ⟪scalarGradient z.val i,scalarGradient z.val j⟫+
      (∑ j : Fin 13,originalTemporalWeights n b j*
        (![0,0,0,0,nativeMagneticTensor z.val 0 0,nativeMagneticTensor z.val 1 1,
          nativeMagneticTensor z.val 2 2,nativeMagneticTensor z.val 0 1,
          nativeMagneticTensor z.val 0 2,nativeMagneticTensor z.val 1 2,0,0,0] : Fin 13 → ℝ) j)+
      (n/sourceTime 0)*GaussCoframeForm.volumePotential z.val=
    (n*volume z.val*⟪scalarField z.val-vacuum,scalarField z.val-vacuum⟫-
      (1/2 : ℝ)*∑ i : Fin 3,∑ j : Fin 3,n*volume z.val*inverseSpatial z.val i j*
        ⟪scalarGradient z.val i,scalarGradient z.val j⟫+
      (n/sourceTime 0)*GaussCoframeForm.volumePotential z.val)+
      (∑ j : Fin 13,originalTemporalWeights n b j*
        (![0,0,0,0,nativeMagneticTensor z.val 0 0,nativeMagneticTensor z.val 1 1,
          nativeMagneticTensor z.val 2 2,nativeMagneticTensor z.val 0 1,
          nativeMagneticTensor z.val 0 2,nativeMagneticTensor z.val 1 2,0,0,0] : Fin 13 → ℝ) j) := by ring
  rw [reorder,scalar]
  unfold originalClassicalLeaves originalTemporalWeights
  norm_num [Fin.sum_univ_succ]

theorem scalarShiftLeaf_smooth (p : Cotangent) (r : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => scalarShiftLeaf w p r) z.val := by
  unfold scalarShiftLeaf scalarContraction
  apply ContDiffAt.sum
  intro i _
  apply (triadInverse_smooth i r z).mul
  apply ContDiffAt.sum
  intro a _
  have momentum : ContDiffAt ℝ ∞ (fun w => scalarMomentum w p a) z.val :=
    p.contDiff.contDiffAt.comp z.val (direction_smooth (scalarDirection a) z)
  exact momentum.mul (contDiffAt_const.inner ℝ (scalarGradient_smooth i).contDiffAt)

theorem gaugeShiftLeaf_smooth (p : Cotangent) (r : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => gaugeShiftLeaf w p r) z.val := by
  unfold gaugeShiftLeaf gaugeContraction
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  apply volume_smooth.contDiffAt.mul
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  apply (ContDiffAt.sum (fun l _ =>
    (ContDiffAt.sum (fun k _ => (triadInverse_smooth i k z).mul contDiffAt_const)).mul
      (triadInverse_smooth j l z))).mul
  apply ContDiffAt.sum
  intro a _
  have momentum : ContDiffAt ℝ ∞ (fun w => electricMomentum w p i a) z.val :=
    p.contDiff.contDiffAt.comp z.val (direction_smooth (gaugeDirection i a) z)
  exact momentum.mul (contDiffAt_const.inner ℝ (magneticField_smooth j).contDiffAt)

theorem originalFirstLeaf_smooth (j : Fin 13) (p : Cotangent) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => originalFirstLeaves w p (Fin.castSucc j)) z.val := by
  fin_cases j <;> first | exact scalarShiftLeaf_smooth p _ z | exact gaugeShiftLeaf_smooth p _ z | exact contDiffAt_const

def actualShiftCoefficient (n : ℝ) (b : Fin 3 → ℝ) (i : Fin 100) (z : SourceCoordinateSlice) : ℝ :=
  actualScalarFirstTime n b z (rawCovector i)+actualGaugeFirstTime n b z (rawCovector i)

theorem actualShiftCoefficient_extraction (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (i : Fin 100) (z : physicalChart) :
    actualShiftCoefficient n b i z.val=
      ∑ j : Fin 13,originalTemporalWeights n b j*originalFirstLeaves z.val (rawCovector i) (Fin.castSucc j) := by
  rw [actualShiftCoefficient,originalMixedHamiltonian_readback n b z (rawCovector i) hn hd,
    originalFirstTemporalReplay]

theorem actualShiftCoefficient_smooth (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (i : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (actualShiftCoefficient n b i) z.val := by
  have smooth : ContDiffAt ℝ ∞ (fun w => ∑ j : Fin 13,originalTemporalWeights n b j*
      originalFirstLeaves w (rawCovector i) (Fin.castSucc j)) z.val :=
    ContDiffAt.sum (fun j _ => contDiffAt_const.mul (originalFirstLeaf_smooth j (rawCovector i) z))
  apply smooth.congr_of_eventuallyEq
  filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
  exact actualShiftCoefficient_extraction n b hn hd i ⟨w,hw⟩

def actualShiftAction (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) : ScalarTest →ₗ[ℂ] ScalarTest :=
  (-Complex.I/2 : ℂ) • ∑ i : Fin 100,
    ((realCoefficient (actualShiftCoefficient n b i) (actualShiftCoefficient_smooth n b hn hd i)).comp
      (GaussDensityCore.derivative (rawDirection i))-
    (weightedTranspose 0 (rawDirection i)).comp
      (realCoefficient (actualShiftCoefficient n b i) (actualShiftCoefficient_smooth n b hn hd i)))

def leafFirstWeyl (j : Fin 13) (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  (-Complex.I/2 : ℂ)*∑ i : Fin 100,
    ((originalFirstLeaves z (rawCovector i) (Fin.castSucc j) : ℂ)*D i f z+
      D i (fun w => (originalFirstLeaves w (rawCovector i) (Fin.castSucc j) : ℂ)*f w) z)

def actualTimeN0Action (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (f : ScalarTest) (z : SourceCoordinateSlice) : ℂ :=
  (∑ a : SourcePair,actualTimePairAction n b hn hd a f z)+actualShiftAction n b hn hd f z+
    (actualTimeClassical n b z : ℂ)*f z

section TimeDifferential
variable (n : ℝ) (b : Fin 3 → ℝ)

theorem timeTensor_symm (i k : Fin 100) (z : SourceCoordinateSlice) :
    timeTensor n b i k z=timeTensor n b k i z := by
  unfold timeTensor leafP
  apply Finset.sum_congr rfl
  intro j _
  rw [rawPrincipalCoefficient_symmetric j i k]

def timePrincipalAction (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  -∑ i : Fin 100,∑ k : Fin 100,
    (timeTensor n b i k z*fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z (rawDirection i)+
      fderiv ℝ (timeTensor n b i k) z (rawDirection i)*fderiv ℝ f z (rawDirection k))

def timeHalfPotential (z : SourceCoordinateSlice) : ℂ :=
  ∑ i : Fin 100,∑ k : Fin 100,
    (fderiv ℝ (timeTensor n b i k) z (rawDirection i)*ell k z+
      timeTensor n b i k z*(fderiv ℝ (ell k) z (rawDirection i)+ell i z*ell k z))

def timeQuarter (z : SourceCoordinateSlice) : ℂ :=
  (1/4 : ℂ)*∑ i : Fin 100,∑ k : Fin 100,D i (D k (timeTensor n b i k)) z

def timeWeylPrincipalAction (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  timePrincipalAction n b f z-timeQuarter n b z*f z

private theorem timeSecondProduct (i k : Fin 100) (f : ScalarTest) (z : physicalChart) :
    D i (D k (fun w => timeTensor n b i k w*f w)) z.val=
      timeTensor n b i k z.val*D i (D k f) z.val+D i (timeTensor n b i k) z.val*D k f z.val+
      D k (timeTensor n b i k) z.val*D i f z.val+D i (D k (timeTensor n b i k)) z.val*f z.val := by
  have localProduct : D k (fun w => timeTensor n b i k w*f w)=ᶠ[𝓝 z.val]
      (fun w => timeTensor n b i k w*D k f w+D k (timeTensor n b i k) w*f w) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact D_product k ((timeTensor_smooth n b i k ⟨w,hw⟩).differentiableAt (by simp))
      ((f.contDiff.differentiable (by simp)).differentiableAt)
  have hp := (timeTensor_smooth n b i k z).differentiableAt (by simp)
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt (x:=z.val)
  have hdp := (D_smooth k (timeTensor_smooth n b i k z)).differentiableAt (by simp)
  have hdf := (D_smooth k (f.contDiff.contDiffAt (x:=z.val))).differentiableAt (by simp)
  have equality := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L (rawDirection i))
    localProduct.fderiv_eq
  change D i (D k (fun w => timeTensor n b i k w*f w)) z.val=
    D i (fun w => timeTensor n b i k w*D k f w+D k (timeTensor n b i k) w*f w) z.val at equality
  rw [equality,D_add i (a:=fun w => timeTensor n b i k w*D k f w)
    (b:=fun w => D k (timeTensor n b i k) w*f w) (hp.mul hdf) (hdp.mul hf),
    D_product i hp hdf,D_product i hdp hf]
  ring

theorem timeFourTermWeyl_normalForm (f : ScalarTest) (z : physicalChart) :
    timeFourTermWeyl n b f z.val=timeWeylPrincipalAction n b f z.val := by
  have crossSecond : (∑ i : Fin 100,∑ k : Fin 100,timeTensor n b i k z.val*D k (D i f) z.val)=
      ∑ i : Fin 100,∑ k : Fin 100,timeTensor n b i k z.val*D i (D k f) z.val := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [timeTensor_symm n b k i]
  have crossFirst : (∑ i : Fin 100,∑ k : Fin 100,D k (timeTensor n b i k) z.val*D i f z.val)=
      ∑ i : Fin 100,∑ k : Fin 100,D i (timeTensor n b i k) z.val*D k f z.val := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    have symmetry : timeTensor n b k i=timeTensor n b i k := by
      funext w
      exact timeTensor_symm n b k i w
    rw [symmetry]
  have term (i k : Fin 100) :
      timeTensor n b i k z.val*D i (D k f) z.val+D i (fun w => timeTensor n b i k w*D k f w) z.val+
        D k (fun w => timeTensor n b i k w*D i f w) z.val+D i (D k (fun w => timeTensor n b i k w*f w)) z.val=
      3*(timeTensor n b i k z.val*D i (D k f) z.val)+timeTensor n b i k z.val*D k (D i f) z.val+
        2*(D i (timeTensor n b i k) z.val*D k f z.val)+2*(D k (timeTensor n b i k) z.val*D i f z.val)+
        D i (D k (timeTensor n b i k)) z.val*f z.val := by
    rw [D_product i ((timeTensor_smooth n b i k z).differentiableAt (by simp))
      ((D_smooth k f.contDiff.contDiffAt).differentiableAt (by simp)),
      D_product k ((timeTensor_smooth n b i k z).differentiableAt (by simp))
      ((D_smooth i f.contDiff.contDiffAt).differentiableAt (by simp)),timeSecondProduct]
    ring
  unfold timeFourTermWeyl
  simp only [term,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  have crossFactored : (∑ i : Fin 100,(∑ k : Fin 100,D k (timeTensor n b i k) z.val)*D i f z.val)=
      ∑ i : Fin 100,∑ k : Fin 100,D i (timeTensor n b i k) z.val*D k f z.val := by
    simpa only [Finset.sum_mul] using crossFirst
  rw [crossSecond,crossFactored]
  have principal : timePrincipalAction n b f z.val=
      -∑ i : Fin 100,∑ k : Fin 100,(timeTensor n b i k z.val*D i (D k f) z.val+
        D i (timeTensor n b i k) z.val*D k f z.val) := rfl
  have correction : timeQuarter n b z.val=
      (1/4 : ℂ)*∑ i : Fin 100,∑ k : Fin 100,D i (D k (timeTensor n b i k)) z.val := rfl
  rw [timeWeylPrincipalAction,principal,correction]
  simp only [Finset.sum_add_distrib]
  ring

def timeFlux (f : Profile) (z : SourceCoordinateSlice) (i : Fin 100) : ℂ :=
  ∑ k : Fin 100,timeTensor n b i k z*fderiv ℝ f z (rawDirection k)

theorem timeFlux_smooth (f : ScalarTest) (i : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => timeFlux n b f w i) z.val := by
  unfold timeFlux
  apply ContDiffAt.sum
  intro k _
  have derivative : ContDiff ℝ ∞ (fderiv ℝ f) := f.contDiff.fderiv_right (by simp)
  exact (timeTensor_smooth n b i k z).mul (derivative.contDiffAt.clm_apply contDiffAt_const)

def timeHalfFlux (f : Profile) (z : SourceCoordinateSlice) (i : Fin 100) : ℂ :=
  ∑ k : Fin 100,timeTensor n b i k z*(fderiv ℝ f z (rawDirection k)-ell k z*f z)

theorem timeHalfFlux_readback (f : ScalarTest) (z : physicalChart) (i : Fin 100) :
    sourceHalf z.val*timeFlux n b (inverseHalfCore f) z.val i=timeHalfFlux n b f z.val i := by
  unfold timeFlux timeHalfFlux
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have derivative:=sourceHalf_derivative_readback (rawDirection k) f z
  change sourceHalf z.val*(timeTensor n b i k z.val*fderiv ℝ (inverseHalfCore f) z.val (rawDirection k))=
    timeTensor n b i k z.val*(fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val)
  rw [mul_left_comm,derivative]
  rfl

theorem timeHalfFlux_smooth (f : ScalarTest) (i : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => timeHalfFlux n b f w i) z.val := by
  unfold timeHalfFlux
  apply ContDiffAt.sum
  intro k _
  have derivative : ContDiff ℝ ∞ (fderiv ℝ f) := f.contDiff.fderiv_right (by simp)
  exact (timeTensor_smooth n b i k z).mul ((derivative.contDiffAt.clm_apply contDiffAt_const).sub
    ((ell_smooth k z).mul f.contDiff.contDiffAt))

private theorem timeHalfFlux_derivative (f : ScalarTest) (i : Fin 100) (z : physicalChart) :
    fderiv ℝ (fun w => timeHalfFlux n b f w i) z.val (rawDirection i)=
      sourceHalf z.val*fderiv ℝ (fun w => timeFlux n b (inverseHalfCore f) w i) z.val (rawDirection i)+
      timeFlux n b (inverseHalfCore f) z.val i*fderiv ℝ sourceHalf z.val (rawDirection i) := by
  have equal : (fun w => sourceHalf w*timeFlux n b (inverseHalfCore f) w i)=ᶠ[𝓝 z.val]
      (fun w => timeHalfFlux n b f w i) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact timeHalfFlux_readback n b f ⟨w,hw⟩ i
  have hu:=((coreHalfDensity_smooth 0 z).differentiableAt (by simp)).hasFDerivAt
  have hg:=((timeFlux_smooth n b (inverseHalfCore f) i z).differentiableAt (by simp)).hasFDerivAt
  have product : fderiv ℝ (fun w => sourceHalf w*timeFlux n b (inverseHalfCore f) w i) z.val=
      sourceHalf z.val • fderiv ℝ (fun w => timeFlux n b (inverseHalfCore f) w i) z.val+
      timeFlux n b (inverseHalfCore f) z.val i • fderiv ℝ sourceHalf z.val := by
    simpa only [sourceHalf] using! (hu.mul hg).fderiv
  rw [←equal.fderiv_eq,product]
  rfl

theorem timeHalfDivergence (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*rawWeightedDivergence (timeFlux n b (inverseHalfCore f)) z.val=
      -∑ i : Fin 100,(fderiv ℝ (fun w => timeHalfFlux n b f w i) z.val (rawDirection i)+ell i z.val*timeHalfFlux n b f z.val i) := by
  unfold rawWeightedDivergence
  rw [mul_neg,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [densityDrift_halfLog,timeHalfFlux_derivative n b,←timeHalfFlux_readback n b f z i]
  have nonzero:=coreHalfDensity_ne_zero 0 z
  change sourceHalf z.val*(fderiv ℝ (fun w => timeFlux n b (inverseHalfCore f) w i) z.val (rawDirection i)+
      2*((sourceHalf z.val)⁻¹*fderiv ℝ sourceHalf z.val (rawDirection i))*timeFlux n b (inverseHalfCore f) z.val i)=
    sourceHalf z.val*fderiv ℝ (fun w => timeFlux n b (inverseHalfCore f) w i) z.val (rawDirection i)+
      timeFlux n b (inverseHalfCore f) z.val i*fderiv ℝ sourceHalf z.val (rawDirection i)+
      ((sourceHalf z.val)⁻¹*fderiv ℝ sourceHalf z.val (rawDirection i))*
        (sourceHalf z.val*timeFlux n b (inverseHalfCore f) z.val i)
  change sourceHalf z.val≠0 at nonzero
  field_simp
  ring

private theorem timeHalfFlux_expand (f : ScalarTest) (i : Fin 100) (z : physicalChart) :
    fderiv ℝ (fun w => timeHalfFlux n b f w i) z.val (rawDirection i)=
      ∑ k : Fin 100,
        (fderiv ℝ (timeTensor n b i k) z.val (rawDirection i)*
          (fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val)+
        timeTensor n b i k z.val*(fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z.val (rawDirection i)-
          fderiv ℝ (ell k) z.val (rawDirection i)*f z.val-ell k z.val*fderiv ℝ f z.val (rawDirection i))) := by
  have derivative : ContDiff ℝ ∞ (fderiv ℝ f) := f.contDiff.fderiv_right (by simp)
  have terms (k : Fin 100) : DifferentiableAt ℝ
      (fun w => timeTensor n b i k w*(fderiv ℝ f w (rawDirection k)-ell k w*f w)) z.val :=
    ((timeTensor_smooth n b i k z).mul ((derivative.contDiffAt.clm_apply contDiffAt_const).sub
      ((ell_smooth k z).mul f.contDiff.contDiffAt))).differentiableAt (by simp)
  unfold timeHalfFlux
  rw [fderiv_fun_sum (fun k _ => terms k)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hp:=((timeTensor_smooth n b i k z).differentiableAt (by simp)).hasFDerivAt
  have hd:=((derivative.contDiffAt (x:=z.val) |>.clm_apply (contDiffAt_const (c:=rawDirection k))).differentiableAt
    (by simp)).hasFDerivAt
  have he:=((ell_smooth k z).differentiableAt (by simp)).hasFDerivAt
  have hf:=(f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z.val)
  have product : fderiv ℝ (fun w => timeTensor n b i k w*(fderiv ℝ f w (rawDirection k)-ell k w*f w)) z.val=
      timeTensor n b i k z.val • (fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z.val-
        (ell k z.val • fderiv ℝ f z.val+f z.val • fderiv ℝ (ell k) z.val))+
      (fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val) • fderiv ℝ (timeTensor n b i k) z.val := by
    simpa only using! (hp.mul (hd.sub (he.mul hf))).fderiv
  rw [product]
  simp only [add_apply,sub_apply,smul_apply,smul_eq_mul]
  ring

theorem timeHalfNormal (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*rawWeightedDivergence (timeFlux n b (inverseHalfCore f)) z.val=
      timePrincipalAction n b f z.val+timeHalfPotential n b z.val*f z.val := by
  have cross : (∑ i : Fin 100,∑ k : Fin 100,timeTensor n b i k z.val*ell k z.val*fderiv ℝ f z.val (rawDirection i))=
      ∑ i : Fin 100,∑ k : Fin 100,timeTensor n b i k z.val*ell i z.val*fderiv ℝ f z.val (rawDirection k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [timeTensor_symm n b k i]
  have term (i k : Fin 100) :
      -(fderiv ℝ (timeTensor n b i k) z.val (rawDirection i)*
          (fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val)+
        timeTensor n b i k z.val*(fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z.val (rawDirection i)-
          fderiv ℝ (ell k) z.val (rawDirection i)*f z.val-ell k z.val*fderiv ℝ f z.val (rawDirection i))+
        ell i z.val*(timeTensor n b i k z.val*(fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val)))=
      -(timeTensor n b i k z.val*fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z.val (rawDirection i)+
        fderiv ℝ (timeTensor n b i k) z.val (rawDirection i)*fderiv ℝ f z.val (rawDirection k))+
      (fderiv ℝ (timeTensor n b i k) z.val (rawDirection i)*ell k z.val+
        timeTensor n b i k z.val*(fderiv ℝ (ell k) z.val (rawDirection i)+ell i z.val*ell k z.val))*f z.val+
      timeTensor n b i k z.val*ell k z.val*fderiv ℝ f z.val (rawDirection i)-
        timeTensor n b i k z.val*ell i z.val*fderiv ℝ f z.val (rawDirection k) := by ring
  have fluxterm (i : Fin 100) :
      fderiv ℝ (fun w => timeHalfFlux n b f w i) z.val (rawDirection i)+ell i z.val*timeHalfFlux n b f z.val i=
      ∑ k : Fin 100,(fderiv ℝ (timeTensor n b i k) z.val (rawDirection i)*
          (fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val)+
        timeTensor n b i k z.val*(fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z.val (rawDirection i)-
          fderiv ℝ (ell k) z.val (rawDirection i)*f z.val-ell k z.val*fderiv ℝ f z.val (rawDirection i))+
        ell i z.val*(timeTensor n b i k z.val*(fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val))) := by
    rw [timeHalfFlux_expand n b]
    simp only [timeHalfFlux,Finset.mul_sum,←Finset.sum_add_distrib]
  rw [timeHalfDivergence n b]
  simp only [fluxterm]
  rw [←Finset.sum_neg_distrib]
  simp only [←Finset.sum_neg_distrib]
  simp only [term]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_neg_distrib,←Finset.sum_mul]
  have crossFactored : (∑ i : Fin 100,(∑ k : Fin 100,timeTensor n b i k z.val*ell k z.val)*
      fderiv ℝ f z.val (rawDirection i))=
      ∑ i : Fin 100,∑ k : Fin 100,timeTensor n b i k z.val*ell i z.val*fderiv ℝ f z.val (rawDirection k) := by
    simpa only [Finset.sum_mul] using cross
  rw [crossFactored]
  unfold timePrincipalAction timeHalfPotential
  simp only [Finset.sum_add_distrib]
  ring

end TimeDifferential

theorem actualTimeKinetic_tensor (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (f : ScalarTest) (z : physicalChart) :
    (∑ a : SourcePair,actualTimePairAction n b hn hd a f z.val)=
      rawWeightedDivergence (timeFlux n b f) z.val := by
  rw [actualTimeKinetic_raw]
  unfold rawWeightedDivergence
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have equal : (fun w => actualTimeFlux n b f w i)=ᶠ[𝓝 z.val] (fun w => timeFlux n b f w i) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact actualTimeFlux_tensor n b hn hd f ⟨w,hw⟩ i
  rw [equal.fderiv_eq,actualTimeFlux_tensor n b hn hd f z i]
  rfl

theorem timeHalfPotential_extraction (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart) :
    timeHalfPotential n b z.val=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*(nativeHalfCorrection j z.val : ℂ) := by
  have term (i k : Fin 100) : D i (timeTensor n b i k) z.val*ell k z.val+
      timeTensor n b i k z.val*(D i (ell k) z.val+ell i z.val*ell k z.val)=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*
        (D i (leafP j i k) z.val*ell k z.val+
          leafP j i k z.val*(D i (ell k) z.val+ell i z.val*ell k z.val)) := by
    rw [D_timeTensor]
    simp only [timeTensor,Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (∑ i : Fin 100,∑ k : Fin 100,(D i (timeTensor n b i k) z.val*ell k z.val+
    timeTensor n b i k z.val*(D i (ell k) z.val+ell i z.val*ell k z.val)))=_
  simp only [term]
  have reorder (a : Fin 100 → Fin 100 → Fin 13 → ℂ) :
      (∑ i : Fin 100,∑ k : Fin 100,∑ j : Fin 13,a i k j)=
        ∑ j : Fin 13,∑ i : Fin 100,∑ k : Fin 100,a i k j := by
    calc
      _=∑ i : Fin 100,∑ j : Fin 13,∑ k : Fin 100,a i k j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _=_ := by rw [Finset.sum_comm]
  rw [reorder]
  simp only [←leafHalf_original _ z,leafHalf,Finset.mul_sum]

theorem timeQuarter_extraction (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart) :
    timeQuarter n b z.val=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*(nativeWeylCorrection j z.val : ℂ) := by
  unfold timeQuarter
  simp only [DD_timeTensor]
  have reorder (a : Fin 100 → Fin 100 → Fin 13 → ℂ) :
      (∑ i : Fin 100,∑ k : Fin 100,∑ j : Fin 13,a i k j)=
        ∑ j : Fin 13,∑ i : Fin 100,∑ k : Fin 100,a i k j := by
    calc
      _=∑ i : Fin 100,∑ j : Fin 13,∑ k : Fin 100,a i k j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _=_ := by rw [Finset.sum_comm]
  rw [reorder]
  simp only [←leafQuarter_original _ z,leafQuarter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem actualTimeKinetic_halfOrdering (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*(∑ a : SourcePair,actualTimePairAction n b hn hd a (inverseHalfCore f) z.val)=
      timeFourTermWeyl n b f z.val+(timeHalfPotential n b z.val+timeQuarter n b z.val)*f z.val := by
  rw [actualTimeKinetic_tensor,timeHalfNormal,timeFourTermWeyl_normalForm]
  unfold timeWeylPrincipalAction
  ring

private def evaluation (z : SourceCoordinateSlice) : ScalarTest →ₗ[ℂ] ℂ where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem actualShiftAction_half (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*actualShiftAction n b hn hd (inverseHalfCore f) z.val=
      (-Complex.I/2 : ℂ)*∑ i : Fin 100,
        ((actualShiftCoefficient n b i z.val : ℂ)*D i f z.val+
          D i (fun w => (actualShiftCoefficient n b i w : ℂ)*f w) z.val) := by
  have term (i : Fin 100) :
      sourceHalf z.val*((actualShiftCoefficient n b i z.val : ℂ)*D i (inverseHalfCore f) z.val-
        weightedTranspose 0 (rawDirection i)
          (realCoefficient (actualShiftCoefficient n b i) (actualShiftCoefficient_smooth n b hn hd i)
            (inverseHalfCore f)) z.val)=
      (actualShiftCoefficient n b i z.val : ℂ)*D i f z.val+
        D i (fun w => (actualShiftCoefficient n b i w : ℂ)*f w) z.val := by
    have hc : DifferentiableAt ℝ (fun w => (actualShiftCoefficient n b i w : ℂ)) z.val := by
      simpa only [Function.comp_apply,Complex.ofRealCLM_apply] using!
        (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
          (actualShiftCoefficient_smooth n b hn hd i z)).differentiableAt (by simp)
    rw [original_constantTranspose_readback]
    change sourceHalf z.val*((actualShiftCoefficient n b i z.val : ℂ)*D i (inverseHalfCore f) z.val-
      (-D i (fun w => (actualShiftCoefficient n b i w : ℂ)*inverseHalfCore f w) z.val-
        densityDrift (rawDirection i) z.val*((actualShiftCoefficient n b i z.val : ℂ)*inverseHalfCore f z.val)))=_
    rw [D_product i (a:=fun w => (actualShiftCoefficient n b i w : ℂ)) hc
      ((inverseHalfCore f).contDiff.differentiable (by simp)).differentiableAt,
      D_product i (a:=fun w => (actualShiftCoefficient n b i w : ℂ)) hc
        (f.contDiff.differentiable (by simp)).differentiableAt,densityDrift_halfLog]
    have derivative := sourceHalf_derivative_readback (rawDirection i) f z
    have cancel := sourceHalf_inverseCore f z
    change sourceHalf z.val*D i (inverseHalfCore f) z.val=D i f z.val-ell i z.val*f z.val at derivative
    change sourceHalf z.val*((actualShiftCoefficient n b i z.val : ℂ)*D i (inverseHalfCore f) z.val-
      (-((actualShiftCoefficient n b i z.val : ℂ)*D i (inverseHalfCore f) z.val+
        D i (fun w => (actualShiftCoefficient n b i w : ℂ)) z.val*inverseHalfCore f z.val)-
        2*ell i z.val*((actualShiftCoefficient n b i z.val : ℂ)*inverseHalfCore f z.val)))=
      (actualShiftCoefficient n b i z.val : ℂ)*D i f z.val+
        ((actualShiftCoefficient n b i z.val : ℂ)*D i f z.val+
          D i (fun w => (actualShiftCoefficient n b i w : ℂ)) z.val*f z.val)
    linear_combination 2*(actualShiftCoefficient n b i z.val : ℂ)*derivative+
      (D i (fun w => (actualShiftCoefficient n b i w : ℂ)) z.val+
        2*ell i z.val*(actualShiftCoefficient n b i z.val : ℂ))*cancel
  change sourceHalf z.val*evaluation z.val (actualShiftAction n b hn hd (inverseHalfCore f))=_
  rw [actualShiftAction,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum]
  change sourceHalf z.val*((-Complex.I/2 : ℂ)*∑ i : Fin 100,
    ((actualShiftCoefficient n b i z.val : ℂ)*D i (inverseHalfCore f) z.val-
      weightedTranspose 0 (rawDirection i)
        (realCoefficient (actualShiftCoefficient n b i) (actualShiftCoefficient_smooth n b hn hd i)
          (inverseHalfCore f)) z.val))=_
  rw [mul_left_comm,Finset.mul_sum]
  simp only [term]

theorem actualShiftAction_leafExtraction (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*actualShiftAction n b hn hd (inverseHalfCore f) z.val=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*leafFirstWeyl j f z.val := by
  rw [actualShiftAction_half]
  have product (i : Fin 100) :
      D i (fun w => (actualShiftCoefficient n b i w : ℂ)*f w) z.val=
        ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*
          D i (fun w => (originalFirstLeaves w (rawCovector i) (Fin.castSucc j) : ℂ)*f w) z.val := by
    have equal : (fun w => (actualShiftCoefficient n b i w : ℂ)*f w)=ᶠ[𝓝 z.val]
        (fun w => ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*
          ((originalFirstLeaves w (rawCovector i) (Fin.castSucc j) : ℂ)*f w)) := by
      filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
      rw [actualShiftCoefficient_extraction n b hn hd i ⟨w,hw⟩]
      simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul,mul_assoc]
    change fderiv ℝ (fun w => (actualShiftCoefficient n b i w : ℂ)*f w) z.val (rawDirection i)=_
    have each (j : Fin 13) : DifferentiableAt ℝ
        (fun w => (originalFirstLeaves w (rawCovector i) (Fin.castSucc j) : ℂ)*f w) z.val := by
      simpa only [Function.comp_apply,Complex.ofRealCLM_apply] using!
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
          (originalFirstLeaf_smooth j (rawCovector i) z)).mul f.contDiff.contDiffAt).differentiableAt (by simp)
    rw [equal.fderiv_eq,fderiv_fun_sum (fun j _ => (each j).const_mul (originalTemporalWeights n b j : ℂ))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_const_mul (each j)]
    rfl
  simp only [product,actualShiftCoefficient_extraction n b hn hd _ z,Complex.ofReal_sum,
    Complex.ofReal_mul,Finset.sum_mul,←Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [leafFirstWeyl,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem actualTimeN0_halfExtraction (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0)
    (hd : n^2-∑ r : Fin 3,b r^2≠0) (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*actualTimeN0Action n b hn hd (inverseHalfCore f) z.val=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*
        (leafFourTermWeyl j f z.val+leafFirstWeyl j f z.val+
          (originalZeroLeaves z.val (Fin.castSucc j) : ℂ)*f z.val) := by
  unfold actualTimeN0Action
  rw [mul_add,mul_add,actualTimeKinetic_halfOrdering,actualShiftAction_leafExtraction,
    timeFourTermWeyl_extraction,timeHalfPotential_extraction,timeQuarter_extraction]
  have potential : sourceHalf z.val*((actualTimeClassical n b z.val : ℂ)*inverseHalfCore f z.val)=
      (∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*(originalClassicalLeaves z.val j : ℂ))*f z.val := by
    rw [show sourceHalf z.val*((actualTimeClassical n b z.val : ℂ)*inverseHalfCore f z.val)=
      (actualTimeClassical n b z.val : ℂ)*(sourceHalf z.val*inverseHalfCore f z.val) by ring,
      sourceHalf_inverseCore,actualTimeClassical_extraction n b hn hd z]
    simp only [Complex.ofReal_sum,Complex.ofReal_mul]
  rw [potential]
  have factor (v : Fin 13 → ℂ) :
      (∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*(v j*f z.val))=
        (∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*v j)*f z.val := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [originalZeroLeaves,Fin.snoc_castSucc,Complex.ofReal_add,mul_add,add_mul,
    Finset.sum_add_distrib,factor]
  ring

end LowEnergy.PreparationVacuumTemporalOrdering
