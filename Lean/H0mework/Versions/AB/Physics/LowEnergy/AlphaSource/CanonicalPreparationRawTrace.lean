import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationDensityLog
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDensityTrace
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussNativeForm GaussLiveMomentum GaussCoreDifferential
open GaussScalarTransport GaussDensityCore PreparationScalarCoordinates
open PreparationVacuumLowerLeaves PreparationActualFactor PreparationVacuumEnergyTail
open scoped BigOperators ContDiff Topology

def actualRawBasis : Module.Basis (Fin 100) ℝ SourceCoordinateSlice :=
  (Pi.basisFun ℝ (Fin 100)).map fullCoordinates.symm.toLinearEquiv

theorem actualRawBasis_vector (i : Fin 100) : actualRawBasis i=rawDirection i := by
  rw [actualRawBasis,Module.Basis.map_apply,Pi.basisFun_apply]
  rfl

theorem actualRawBasis_read (x : SourceCoordinateSlice) (i : Fin 100) :
    actualRawBasis.repr x i=rawCovector i x := by
  change (Pi.basisFun ℝ (Fin 100)).repr (fullCoordinates x) i=_
  rw [Pi.basisFun_repr]
  simp [rawCovector,nativeCovector_apply]

def rawDivergence (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  ∑ i : Fin 100, rawCovector i (fderiv ℝ (direction v) z (rawDirection i))

theorem originalCoefficient_derivative (v : Ambient) (i : FrameIndex)
    (z : physicalChart) (D : SourceCoordinateSlice) :
    fderiv ℝ (fun w => (coefficient v i w : ℂ)) z.val D=
      (frame.coord i (fderiv ℝ (direction v) z.val D) : ℂ) := by
  let read : SourceCoordinateSlice →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (frame.coord i).toContinuousLinearMap
  have derivative:=read.hasFDerivAt.comp z.val
    ((direction_smooth v z).differentiableAt (by simp)).hasFDerivAt
  change fderiv ℝ (read ∘ direction v) z.val D=_
  rw [derivative.fderiv]
  rfl

theorem rawDivergence_trace (v : Ambient) (z : SourceCoordinateSlice) :
    rawDivergence v z=LinearMap.trace ℝ SourceCoordinateSlice
      (fderiv ℝ (direction v) z).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ actualRawBasis]
  simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply,actualRawBasis_read,actualRawBasis_vector]
  rfl

theorem originalDivergence_raw (v : Ambient) (z : physicalChart) :
    divergence v z.val=(rawDivergence v z.val : ℂ) := by
  have original : (∑ i : FrameIndex,frame.coord i (fderiv ℝ (direction v) z.val (frame i)))=
      LinearMap.trace ℝ SourceCoordinateSlice (fderiv ℝ (direction v) z.val).toLinearMap := by
    rw [LinearMap.trace_eq_matrix_trace ℝ frame]
    simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply]
    rfl
  rw [divergence]
  simp only [originalCoefficient_derivative,←Complex.ofReal_sum]
  rw [original,rawDivergence_trace]

theorem originalHalfTranspose_raw (v : Ambient) (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*fieldTranspose 0 v (inverseHalfCore f) z.val=
      -fieldD v f z.val-
        ((rawDivergence v z.val : ℂ)+
          ((literalHalf z.val)⁻¹*fderiv ℝ literalHalf z.val (direction v z.val) : ℝ))*f z.val := by
  rw [sourceHalf_fieldTranspose,originalDivergence_raw,original_complexHalfLog_feed]

theorem original_raw_read (x : SourceCoordinateSlice) (L : SourceCoordinateSlice →L[ℝ] ℂ) :
    (∑ i : Fin 100,(rawCovector i x : ℂ)*L (rawDirection i))=L x := by
  have generated : (∑ i : Fin 100,rawCovector i x • rawDirection i)=x := by
    simpa only [actualRawBasis_read,actualRawBasis_vector] using actualRawBasis.sum_repr x
  calc
    _=∑ i : Fin 100,L (rawCovector i x • rawDirection i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul,RCLike.real_smul_eq_coe_mul]
      rfl
    _=L (∑ i : Fin 100,rawCovector i x • rawDirection i) := (map_sum L _ _).symm
    _=L x := congrArg L generated

def rawFieldFlux (v : Ambient) (f : Profile) (z : SourceCoordinateSlice) (i : Fin 100) : ℂ :=
  (rawCovector i (direction v z) : ℂ)*f z

def rawWeightedDivergence (G : SourceCoordinateSlice → Fin 100 → ℂ)
    (z : SourceCoordinateSlice) : ℂ :=
  -∑ i : Fin 100,(fderiv ℝ (fun w => G w i) z (rawDirection i)+densityDrift (rawDirection i) z*G z i)

private theorem rawFieldFlux_derivative (v : Ambient) (f : ScalarTest) (i : Fin 100)
    (z : physicalChart) :
    fderiv ℝ (fun w => rawFieldFlux v f w i) z.val (rawDirection i)=
      (rawCovector i (direction v z.val) : ℂ)*fderiv ℝ f z.val (rawDirection i)+
        (rawCovector i (fderiv ℝ (direction v) z.val (rawDirection i)) : ℂ)*f z.val := by
  let read : SourceCoordinateSlice →L[ℝ] ℂ := Complex.ofRealCLM.comp (rawCovector i)
  have hv:=read.hasFDerivAt.comp z.val
    ((direction_smooth v z).differentiableAt (by simp)).hasFDerivAt
  have hf:=(f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z.val)
  have product := (hv.mul hf).fderiv
  change fderiv ℝ ((read ∘ direction v)*(f : Profile)) z.val (rawDirection i)=_
  rw [product]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply]
  change (rawCovector i (direction v z.val) : ℂ)*fderiv ℝ f z.val (rawDirection i)+
    f z.val*(rawCovector i (fderiv ℝ (direction v) z.val (rawDirection i)) : ℂ)=_
  ring

theorem original_fieldTranspose_rawFlux (v : Ambient) (f : ScalarTest) (z : physicalChart) :
    fieldTranspose 0 v f z.val=rawWeightedDivergence (rawFieldFlux v f) z.val := by
  have derivative : (∑ i : Fin 100,fderiv ℝ (fun w => rawFieldFlux v f w i) z.val (rawDirection i))=
      fieldD v f z.val+(rawDivergence v z.val : ℂ)*f z.val := by
    simp only [rawFieldFlux_derivative,Finset.sum_add_distrib,←Finset.sum_mul,←Complex.ofReal_sum]
    rw [original_raw_read]
    rfl
  have weighted : (∑ i : Fin 100,densityDrift (rawDirection i) z.val*rawFieldFlux v f z.val i)=
      densityDrift (direction v z.val) z.val*f z.val := by
    unfold densityDrift rawFieldFlux
    have group : (∑ i : Fin 100,(complexDensity 0 z.val)⁻¹*
        fderiv ℝ (complexDensity 0) z.val (rawDirection i)*
          ((rawCovector i (direction v z.val) : ℂ)*f z.val))=
      (complexDensity 0 z.val)⁻¹*(∑ i : Fin 100,(rawCovector i (direction v z.val) : ℂ)*
        fderiv ℝ (complexDensity 0) z.val (rawDirection i))*f z.val := by
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [group,original_raw_read]
  rw [original_fieldTranspose_readback]
  unfold fieldT rawWeightedDivergence
  rw [Finset.sum_add_distrib,derivative,weighted,originalDivergence_raw]
  ring

def originalActionRawCoefficient (i k : Fin 100) (z : SourceCoordinateSlice) : ℝ :=
  (nativePrincipal z (rawCovector i+rawCovector k)-nativePrincipal z (rawCovector i)-
    nativePrincipal z (rawCovector k))/2

def originalTemporalRawCoefficient (i k : Fin 100) (z : SourceCoordinateSlice) : ℝ :=
  ∑ j : Fin 13,originalTemporalWeights (sourceTime 0) 0 j*rawPrincipalCoefficient j i k z

theorem originalActionRawCoefficient_readback (i k : Fin 100) (z : physicalChart) :
    originalActionRawCoefficient i k z.val=originalTemporalRawCoefficient i k z.val := by
  have replay (p : Cotangent) :
      (∑ j : Fin 13,originalTemporalWeights (sourceTime 0) 0 j*originalPrincipalLeaves z.val p j)=
        nativePrincipal z.val p := by
    change originalPrincipalTemporalReplay (sourceTime 0) 0 z.val p=_
    have timelike : (sourceTime 0)^2-∑ i : Fin 3,(0 : Fin 3 → ℝ) i^2≠0 := by
      simpa using pow_ne_zero 2 source_time_nonzero
    rw [originalPrincipalTemporalReplay_native _ _ _ _ source_time_nonzero timelike,
      zero_shift_principal _ _ _ source_time_nonzero]
    exact (nativePrincipal_original_coefficients z p).symm
  unfold originalActionRawCoefficient originalTemporalRawCoefficient
  rw [←replay (rawCovector i+rawCovector k),←replay (rawCovector i),←replay (rawCovector k)]
  unfold rawPrincipalCoefficient
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem originalActionRawCoefficient_derivative (i k : Fin 100) (D : SourceCoordinateSlice)
    (z : physicalChart) :
    fderiv ℝ (originalActionRawCoefficient i k) z.val D=
      fderiv ℝ (originalTemporalRawCoefficient i k) z.val D := by
  have equal : originalActionRawCoefficient i k=ᶠ[𝓝 z.val] originalTemporalRawCoefficient i k := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact originalActionRawCoefficient_readback i k ⟨w,hw⟩
  exact congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℝ => L D) equal.fderiv_eq

theorem originalActionRawCoefficient_second (i k : Fin 100) (D E : SourceCoordinateSlice)
    (z : physicalChart) :
    fderiv ℝ (fun w => fderiv ℝ (originalActionRawCoefficient i k) w E) z.val D=
      fderiv ℝ (fun w => fderiv ℝ (originalTemporalRawCoefficient i k) w E) z.val D := by
  have equal : (fun w => fderiv ℝ (originalActionRawCoefficient i k) w E)=ᶠ[𝓝 z.val]
      (fun w => fderiv ℝ (originalTemporalRawCoefficient i k) w E) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact originalActionRawCoefficient_derivative i k E ⟨w,hw⟩
  exact congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℝ => L D) equal.fderiv_eq

end LowEnergy.PreparationVacuumDensityTrace
