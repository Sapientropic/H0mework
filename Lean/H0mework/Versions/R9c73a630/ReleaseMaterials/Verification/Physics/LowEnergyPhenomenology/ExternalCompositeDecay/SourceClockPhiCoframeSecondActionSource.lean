import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiUDPhysicalNoetherWork
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCoframeCovariantSquare
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentPayerNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare
open SourceClockPhiCoframeForwardCore SourceClockPhiForwardNativeReturn SourceClockPhiCombinedScalePressure
open SourceClockPhiCorrectedWeightTransport SourceClockPhiHeatLocalNativeGaussian
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource PositiveClockGenerator
open SourceClockPhiMatchedDiffusionSource SourceClockPhiNormalizedScalarBudget FinitePhysicalSource
open SourceCoframeVolume SourceCoframeCovariantAction GaussCoframeCore MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction embed

private theorem transpose_component (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : physicalChart) :
    GaussCoframeCore.transpose v f z.val word =
      GaussDensityCore.weightedTranspose word.card v (component word f) z.val := by
  let h := GaussDensityCore.weightedTranspose word.card v (component word f)
  have row : embed (GaussCoframeCore.transpose v f) word = scalarLp word.card h := by
    rw [GaussCoframeCore.transpose_embed]
    rfl
  have ae : (fun w : physicalChart => GaussCoframeCore.transpose v f w.val word) =ᵐ[
      GaussHistoryHilbert.numberMeasure word.card] (fun w : physicalChart => h w.val) :=
    (embed_ae (GaussCoframeCore.transpose v f) word).symm.trans (row ▸ scalarLp_ae word.card h)
  have he := MeasureTheory.Measure.eq_of_ae_eq ae
    ((component word (GaussCoframeCore.transpose v f)).continuous.comp continuous_subtype_val)
    (h.continuous.comp continuous_subtype_val)
  exact congrFun he z
private theorem transpose_formula (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : physicalChart) :
    GaussCoframeCore.transpose v f z.val word = -fderiv ℝ (component word f) z.val v -
      (GaussDensityCore.complexDensity word.card z.val)⁻¹ *
        fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val v * f z.val word := by
  rw [transpose_component,GaussDensityCore.weightedTranspose_apply,
    fderiv_fun_mul ((GaussDensityCore.complexDensity_smooth word.card z).differentiableAt (by simp))
      ((component word f).contDiff.differentiable (by simp)).differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul]
  have hn : GaussDensityCore.complexDensity word.card z.val ≠ 0 := by
    change (GaussDensityCore.density word.card z.val:ℂ) ≠ 0
    exact_mod_cast (GaussDensityCore.density_pos word.card z).ne'
  change -(GaussDensityCore.complexDensity word.card z.val)⁻¹ *
    (GaussDensityCore.complexDensity word.card z.val * fderiv ℝ (component word f) z.val v +
      f z.val word * fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val v) = _
  field_simp [hn]
  ring

private theorem density_coframe_derivative (N : ℕ) (i : Fin 6) (z : physicalChart) :
    fderiv ℝ (GaussDensityCore.density N) z.val (coframeDirection i) =
      GaussHistoryHilbert.jacobian z.val.2.2 * (N+2:ℝ) * (volume z.val)^(N+1) * volumeGradient z.val i := by
  have hl : HasDerivAt (fun t : ℝ => z.val+t • coframeDirection i) (coframeDirection i) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (coframeDirection i)).const_add z.val
  have hv := volume_smooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt (x:=z.val)
  have hv' := hv.comp_hasDerivAt_of_eq 0 hl (by simp)
  rw [volume_coordinate_derivative] at hv'
  have hd := (hv'.pow (N+2)).const_mul (GaussHistoryHilbert.jacobian z.val.2.2)
  have hreal := ((GaussDensityCore.density_smooth N z).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  have he : (fun t : ℝ => GaussDensityCore.density N (z.val+t • coframeDirection i)) =
      fun t : ℝ => GaussHistoryHilbert.jacobian z.val.2.2 * (volume (z.val+t • coframeDirection i))^(N+2) := by
    funext t
    simp only [GaussDensityCore.density,coframeDirection,Prod.snd_add,Prod.smul_snd,smul_zero,add_zero]
    rfl
  dsimp only [Function.comp_def] at hreal hd
  rw [he] at hreal
  have heq := hreal.unique hd
  simpa only [zero_smul,add_zero,show N+2-1=N+1 by omega,Nat.cast_add,Nat.cast_ofNat,mul_assoc] using heq
private theorem complex_density_log (N : ℕ) (i : Fin 6) (z : physicalChart) :
    (GaussDensityCore.complexDensity N z.val)⁻¹ *
      fderiv ℝ (GaussDensityCore.complexDensity N) z.val (coframeDirection i) =
      (N+2:ℂ)*(reciprocalVolume z.val:ℂ)*(volumeGradient z.val i:ℂ) := by
  have hd := (Complex.ofRealCLM.hasFDerivAt (x:=GaussDensityCore.density N z.val)).comp z.val
    ((GaussDensityCore.density_smooth N z).differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt (GaussDensityCore.complexDensity N) _ z.val at hd
  rw [hd.fderiv]
  change (GaussDensityCore.density N z.val:ℂ)⁻¹ *
    (fderiv ℝ (GaussDensityCore.density N) z.val (coframeDirection i):ℂ) = _
  rw [density_coframe_derivative]
  have hV : volume z.val ≠ 0 := (volume_pos z).ne'
  have hJ : GaussHistoryHilbert.jacobian z.val.2.2 ≠ 0 := by
    have hp := GaussDensityCore.density_pos N z
    change 0 < GaussHistoryHilbert.jacobian z.val.2.2*(volume z.val)^(N+2) at hp
    exact (ne_of_gt (pos_of_mul_pos_left hp (pow_nonneg (volume_pos z).le _)))
  unfold GaussDensityCore.density reciprocalVolume
  change ((GaussHistoryHilbert.jacobian z.val.2.2 * (volume z.val)^(N+2):ℝ):ℂ)⁻¹ * _ = _
  push_cast
  rw [show N+2=(N+1)+1 by omega,pow_succ]
  field_simp [Complex.ofReal_ne_zero.mpr hV,Complex.ofReal_ne_zero.mpr hJ]

private def currentColumn (i : Fin 6) : End :=
  inverseVolumeAction * gradientAction i
private def numberPlusTwo : End := GaussCoframeForm.number+(2:ℂ) • (1:End)
private theorem coframe_adjoint_current (i : Fin 6) :
    GaussCoframeCore.adjoint i = GaussCoframeCore.momentum i -
      Complex.I • (currentColumn i*numberPlusTwo) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · apply PiLp.ext
    intro word
    have ht := transpose_formula (coframeDirection i) f word ⟨z,hz⟩
    rw [complex_density_log] at ht
    have hd := congrArg (fun q : GaussDensityCore.ScalarTest => q z)
      (GaussCoframeCore.component_derivative (coframeDirection i) f word)
    rw [GaussDensityCore.derivative_apply] at hd
    change GaussCoframeCore.derivative (coframeDirection i) f z word = _ at hd
    change Complex.I * (GaussCoframeCore.transpose (coframeDirection i) f z word) =
      -Complex.I * (GaussCoframeCore.derivative (coframeDirection i) f z word) -
      Complex.I * ((reciprocalVolume z:ℂ) * ((volumeGradient z i:ℂ) *
        (GaussCoframeForm.number f z word + 2*f z word)))
    rw [ht,hd,GaussCoframeForm.number_apply]
    push_cast
    ring
  · have hzero (q : QuantumTest) : q z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm

/-- The original Number density supplies the complete coframe adjoint correction. -/
theorem actual_covariant_adjoint_current (i : Fin 6) :
    covariantAdjoint i = SourceCoframeCovariantAction.covariantMomentum i - Complex.I • (currentColumn i*numberPlusTwo) := by
  unfold covariantAdjoint SourceCoframeCovariantAction.covariantMomentum
  rw [coframe_adjoint_current]
  module
private theorem forward_number (t : ℝ) (ht : 0 ≤ t) :
    Commute (sourceForwardCore t ht) GaussCoframeForm.number := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change forwardValue t (GaussCoframeForm.number f) z =
    GaussQuantumMultiplier.quantized (Matrix.diagonal (fun _ : Mode => (1:ℂ))) (forwardValue t f z)
  by_cases hz : 18*t < volume z
  · simp only [forwardValue,if_pos hz]
    let c : ℕ → ℂ := fun N => (Real.rpow (backwardRatio t z) ((N+3:ℝ)/2):ℂ)
    change GaussFockWeights.weight c (GaussQuantumMultiplier.quantized _ (f (backwardPoint t z))) =
      GaussQuantumMultiplier.quantized _ (GaussFockWeights.weight c (f (backwardPoint t z)))
    exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f (backwardPoint t z)))
      (GaussQuantumMultiplier.weight_commute c (Matrix.diagonal (fun _ : Mode => (1:ℂ)))).eq
  · simp only [forwardValue,if_neg hz,map_zero]
private theorem profile_number (t : ℝ) (ht : 0 < t) (ξ η : ℝ) :
    Commute (correctedProfileCore t ht ξ η) GaussCoframeForm.number := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η z)):ℂ) •
      GaussQuantumMultiplier.quantized (Matrix.diagonal (fun _ : Mode => (1:ℂ)))
        (f (ClockPhiMatchedNoiseCore.combinedMap (1*correctedCoefficient t ξ η z) z)) =
    GaussQuantumMultiplier.quantized (Matrix.diagonal (fun _ : Mode => (1:ℂ)))
      ((Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η z)):ℂ) •
        f (ClockPhiMatchedNoiseCore.combinedMap (1*correctedCoefficient t ξ η z) z))
  exact (map_smul _ _ _).symm
private theorem gain_number (t : ℝ) :
    Commute (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)) GaussCoframeForm.number := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ) •
      GaussQuantumMultiplier.quantized (Matrix.diagonal (fun _ : Mode => (1:ℂ))) (f z) =
    GaussQuantumMultiplier.quantized (Matrix.diagonal (fun _ : Mode => (1:ℂ)))
      ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ) • f z)
  exact (map_smul _ _ _).symm
private theorem complete_number (t : ℝ) (ht : 0 < t) (ξ η : ℝ) :
    Commute (correctedCompleteCore t ht ξ η) GaussCoframeForm.number := by
  have hJ := (forward_number t ht.le).eq
  have hP := (profile_number t ht ξ η).eq
  have hG := (gain_number t).eq
  change (sourceForwardCore t ht.le*correctedProfileCore t ht ξ η*
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t))*GaussCoframeForm.number =
    GaussCoframeForm.number*(sourceForwardCore t ht.le*correctedProfileCore t ht ξ η*
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t))
  calc
    _ = sourceForwardCore t ht.le*correctedProfileCore t ht ξ η*
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)*GaussCoframeForm.number) := by noncomm_ring
    _ = sourceForwardCore t ht.le*(correctedProfileCore t ht ξ η*GaussCoframeForm.number)*
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) := by rw [hG];noncomm_ring
    _ = (sourceForwardCore t ht.le*GaussCoframeForm.number)*correctedProfileCore t ht ξ η*
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) := by rw [hP];noncomm_ring
    _ = _ := by rw [hJ];noncomm_ring
private theorem current_smooth (i : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x => reciprocalVolume x*volumeGradient x i) z.val := by
  have hg : ContDiff ℝ ∞ (fun x : SourceCoordinateSlice => volumeGradient x i) := by
    fin_cases i <;> dsimp [volumeGradient] <;> fun_prop
  exact (reciprocal_volume_smooth z).mul hg.contDiffAt
private theorem current_return (t : ℝ) (ht : 0 < t) (ξ η : ℝ) (i : Fin 6) :
    currentColumn i*correctedCompleteCore t ht ξ η =
      correctedCompleteCore t ht ξ η*returnedCurrentColumn t ht i := by
  have hc : currentColumn i = multiply (fun z => reciprocalVolume z*volumeGradient z i) (current_smooth i) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change (reciprocalVolume z:ℂ) • ((volumeGradient z i:ℂ) • f z) =
      ((reciprocalVolume z*volumeGradient z i:ℝ):ℂ) • f z
    rw [Complex.ofReal_mul,mul_smul]
  rw [hc]
  exact actual_corrected_complete_coframe_multiplier t ht ξ η _ _ (by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    cases h
    rfl)

def returnedAdjointRow (t : ℝ) (ht : 0 < t) (ξ η : ℝ) (i : Fin 6) : End :=
  ClockPhiHeatCorrectedCoframeWork.correctedCovariantRow t ht ξ η i -
    Complex.I • (returnedCurrentColumn t ht i*numberPlusTwo)

theorem actual_corrected_covariant_adjoint_return (t : ℝ) (ht : 0 < t) (ξ η : ℝ) (i : Fin 6) :
    covariantAdjoint i*correctedCompleteCore t ht ξ η =
      correctedCompleteCore t ht ξ η*returnedAdjointRow t ht ξ η i := by
  have hN := (complete_number t ht ξ η).eq
  have hN2 : numberPlusTwo*correctedCompleteCore t ht ξ η = correctedCompleteCore t ht ξ η*numberPlusTwo := by
    unfold numberPlusTwo
    rw [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,hN]
  apply LinearMap.ext
  intro f
  have hp := LinearMap.congr_fun (corrected_covariant_return t ht ξ η i) f
  have hn := LinearMap.congr_fun hN2 f
  have hc := LinearMap.congr_fun (current_return t ht ξ η i) (numberPlusTwo f)
  simp only [Module.End.mul_apply] at hp hn hc
  rw [actual_covariant_adjoint_current]
  change SourceCoframeCovariantAction.covariantMomentum i (correctedCompleteCore t ht ξ η f) -
    Complex.I • currentColumn i (numberPlusTwo (correctedCompleteCore t ht ξ η f)) = _
  rw [hp,hn,hc]
  simp only [returnedAdjointRow,Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul]

private theorem metric_forward_smooth (t : ℝ) (ht : 0 < t) (i j : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x => GaussCoframeKinetic.coefficient i j (forwardPoint t x)) z.val :=
  ContDiffAt.comp (f:=forwardPoint t) z.val
    (GaussCoframeKinetic.coefficient_smooth i j ⟨_,forward_chart t ht.le z⟩) (forward_smooth t ht.le z)
def returnedMetric (t : ℝ) (ht : 0 < t) (i j : Fin 6) : End :=
  multiply (fun x => GaussCoframeKinetic.coefficient i j (forwardPoint t x)) (metric_forward_smooth t ht i j)
private theorem metric_return (t : ℝ) (ht : 0 < t) (ξ η : ℝ) (i j : Fin 6) :
    metricAction i j*correctedCompleteCore t ht ξ η =
      correctedCompleteCore t ht ξ η*returnedMetric t ht i j := by
  exact actual_corrected_complete_coframe_multiplier t ht ξ η _ _ (by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    cases h
    rfl)

def returnedCoframeKinetic (t : ℝ) (ht : 0 < t) (ξ η : ℝ) : End :=
  ∑ i : Fin 6,∑ j : Fin 6,returnedAdjointRow t ht ξ η i*returnedMetric t ht i j*
    ClockPhiHeatCorrectedCoframeWork.correctedCovariantRow t ht ξ η j

/-- Every original ordered row is returned as an actual second-order action; coefficients remain inside both derivatives. -/
theorem actual_corrected_coframe_second_order (t : ℝ) (ht : 0 < t) (ξ η : ℝ) :
    covariantKinetic*correctedCompleteCore t ht ξ η =
      correctedCompleteCore t ht ξ η*returnedCoframeKinetic t ht ξ η := by
  unfold covariantKinetic returnedCoframeKinetic
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = covariantAdjoint i*metricAction i j*(SourceCoframeCovariantAction.covariantMomentum j*correctedCompleteCore t ht ξ η) := by noncomm_ring
    _ = covariantAdjoint i*(metricAction i j*correctedCompleteCore t ht ξ η)*
      ClockPhiHeatCorrectedCoframeWork.correctedCovariantRow t ht ξ η j := by rw [corrected_covariant_return];noncomm_ring
    _ = (covariantAdjoint i*correctedCompleteCore t ht ξ η)*returnedMetric t ht i j*
      ClockPhiHeatCorrectedCoframeWork.correctedCovariantRow t ht ξ η j := by rw [metric_return];noncomm_ring
    _ = _ := by rw [actual_corrected_covariant_adjoint_return];noncomm_ring
end LowEnergy.FirstCurrentPayerNext
