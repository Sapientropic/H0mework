import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPositiveTimeWorkGenerator
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointElectricSource
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare
open SourceClockPhiCoframeForwardCore SourceClockPhiForwardNativeReturn SourceClockPhiCombinedScalePressure
open SourceClockPhiCorrectedWeightTransport SourceClockPhiHeatLocalNativeGaussian
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource PositiveClockGenerator
open SourceClockPhiMatchedDiffusionSource SourceClockPhiHeatNativeClosedGraph SourceScalarDoubleCurrent
open SourceClockPhiNativeMatchedSource SourceClockPhiNormalizedScalarBudget SourceClockPhiWholeSignedWorkIntegrable
open FinitePhysicalSource MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev A : End := combinedConjugate
private abbrev U : End := inverseVolumeAction
private abbrev D : End := combinedGenerator
private abbrev H0 : End := diagonalAction
private abbrev Q := completeCurrent
private abbrev C : End := bracket H0 A
attribute [local irreducible] diagonalAction embed

private theorem A_pair (f g : QuantumTest) : sourcePair f (A g) = -sourcePair (A f) g := by
  have h := actual_A_formal_pair (coreEquiv f) (coreEquiv g)
  change inner ℂ (embed (A (coreEquiv.symm (coreEquiv f)))) (embed g) =
    inner ℂ (embed f) (embed ((-A) (coreEquiv.symm (coreEquiv g)))) at h
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply] at h
  have h' : sourcePair (A f) g = -sourcePair f (A g) := by
    simpa only [sourcePair, LinearMap.neg_apply, map_neg, inner_neg_right] using h
  simpa only [neg_neg] using (congrArg Neg.neg h').symm
private theorem C_pair (f g : QuantumTest) : sourcePair f (C g) = sourcePair (C f) g := by
  change sourcePair f (H0 (A g) - A (H0 g)) = sourcePair (H0 (A f) - A (H0 f)) g
  have h1 : sourcePair f (H0 (A g)) = -sourcePair (A (H0 f)) g := by
    rw [diagonalAction_pair f (A g), A_pair (H0 f) g]
  have h2 : sourcePair f (A (H0 g)) = -sourcePair (H0 (A f)) g := by
    rw [A_pair f (H0 g), diagonalAction_pair (A f) g]
  simp only [sourcePair, map_sub, inner_sub_left, inner_sub_right] at h1 h2 ⊢
  linear_combination h1 - h2

def conditionalHamiltonianSquare : End :=
  Q (H0*H0) - Q H0*H0 - H0*Q H0 + H0*Q (1:End)*H0

/-- The complete gain retains H Q(1) H in its original order and cancels internally. -/
theorem actual_full_conditional_carre (f : QuantumTest) :
    (sourcePair f (conditionalHamiltonianSquare f)).re = 2 * ‖embed (C f)‖^2 := by
  have he : conditionalHamiltonianSquare = (2:ℂ) • (C*C) := by
    unfold conditionalHamiltonianSquare Q completeCurrent diffusionCurrent diffusionDrift
      diffusionDriftTranspose C bracket
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      mul_smul_comm, smul_mul_assoc, smul_add, smul_sub]
    noncomm_ring
  rw [he]
  change (sourcePair f ((2:ℂ) • C (C f))).re = _
  have hp : sourcePair f (C (C f)) = sourcePair (C f) (C f) := C_pair f (C f)
  simp only [sourcePair, map_smul, inner_smul_right] at hp ⊢
  rw [hp]
  have hs : (inner ℂ (embed (C f)) (embed (C f))).re = ‖embed (C f)‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) (embed (C f))).symm
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, hs]

private theorem complete_pair (s : ℝ) (hs : 0 < s) (ξ η : ℝ) (f g : QuantumTest) :
    sourcePair (correctedCompleteCore s hs ξ η f) (correctedCompleteCore s hs ξ η g) =
      sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) f)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) g) := by
  change sourcePair
    (sourceForwardCore s hs.le (correctedProfileCore s hs ξ η (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) f)))
    (sourceForwardCore s hs.le (correctedProfileCore s hs ξ η (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) g))) = _
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _
private theorem UD_return (s : ℝ) (hs : 0 < s) (ξ η : ℝ) (f : QuantumTest) :
    U (D (correctedCompleteCore s hs ξ η f)) =
      correctedCompleteCore s hs ξ η (forwardUAction s hs.le (D f)) := by
  have hD := LinearMap.congr_fun (actual_corrected_complete_generator_commute s hs ξ η).eq f
  have hU := LinearMap.congr_fun (actual_corrected_complete_inverse_volume s hs ξ η) (D f)
  change D (correctedCompleteCore s hs ξ η f) = correctedCompleteCore s hs ξ η (D f) at hD
  change U (correctedCompleteCore s hs ξ η (D f)) = _ at hU
  rw [hD, hU]
  rfl

private theorem gain_square_inverse_power(t:ℝ)(ht:0<t)(f:QuantumTest):
    SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
        (forwardUAction t ht.le (forwardUAction t ht.le f)))=
      inverseVolumeAction (forwardUAction t ht.le (gaussianProfileWeight t ht (-2/3) f)):=by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hg:SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z^2=(forwardRatio t z)^(1/3:ℝ):=by
      unfold SourceClockPhiActualCovarianceStep.gainProfile
      rw [Real.sq_sqrt ht.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
      norm_num
    have hp:(forwardRatio t z)^(1/3:ℝ)=(forwardRatio t z)^(-2/3:ℝ)*forwardRatio t z:=by
      calc
        _=(forwardRatio t z)^((-2/3:ℝ)+1):=by norm_num
        _=(forwardRatio t z)^(-2/3:ℝ)*(forwardRatio t z)^(1:ℝ):=Real.rpow_add hr _ _
        _=_:=by rw [Real.rpow_one]
    have hu:forwardU t z*forwardRatio t z=reciprocalVolume z:=by
      unfold forwardU forwardRatio reciprocalVolume
      have hV:(volume z)≠0:=(volume_pos ⟨z,hz⟩).ne'
      have hW:(volume z+18*t)≠0:=by linarith [volume_pos ⟨z,hz⟩]
      field_simp [hV,hW]
    have he:SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z*
        (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z*(forwardU t z*forwardU t z))=
        reciprocalVolume z*(forwardU t z*(forwardRatio t z)^(-2/3:ℝ)):=by
      calc _=SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z^2*(forwardU t z)^2:=by ring
           _=_:=by rw [hg,hp];linear_combination (norm:=ring) (forwardU t z)*(forwardRatio t z)^(-2/3:ℝ)*hu
    change (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ) •
      ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ) • ((forwardU t z:ℂ) • ((forwardU t z:ℂ) • f z)))=
      (reciprocalVolume z:ℂ) • ((forwardU t z:ℂ) • ((((forwardRatio t z)^(-2/3:ℝ):ℝ):ℂ) • f z))
    simpa only [Complex.ofReal_mul,mul_smul] using congrArg (fun r:ℝ=>(r:ℂ) • f z) he
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem multiplier_pair (b : SourceCoordinateSlice → ℝ)
    (hb : ∀ z : physicalChart, ContDiffAt ℝ ∞ b z.val) (f g : QuantumTest) :
    sourcePair (multiply b hb f) g = sourcePair f (multiply b hb g) := (multiply_pair _ _ f g).symm
private theorem multiplier_commute (b c : SourceCoordinateSlice → ℝ)
    (hb : ∀ z : physicalChart, ContDiffAt ℝ ∞ b z.val)
    (hc : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (multiply b hb) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (b z : ℂ) (c z : ℂ) (f z)

def clockPotential (s : ℝ) (hs : 0 < s) (f : QuantumTest) : ℂ :=
  sourcePair (A f) (gaussianProfileWeight s hs (-2/3) (A f))

def clockUDDensity (s : ℝ) (hs : 0 < s) (f : QuantumTest) : ℂ :=
  sourcePair (forwardUAction s hs.le (A f)) (gaussianProfileWeight s hs (-2/3) (A f))

/-- Both actual noise coordinates have one identical full UD square on the pulled-back source. -/
theorem actual_corrected_UD_clock_density (s : ℝ) (hs : 0 < s) (ξ η : ℝ) (f : QuantumTest) :
    clockUDDensity s hs f = (‖embed (U (D (correctedCompleteCore s hs ξ η f)))‖^2 : ℂ) := by
  have hu : sourcePair (U (D (correctedCompleteCore s hs ξ η f)))
      (U (D (correctedCompleteCore s hs ξ η f))) =
      sourcePair (D f) (U (forwardUAction s hs.le (gaussianProfileWeight s hs (-2/3) (D f)))) := by
    rw [UD_return, complete_pair]
    have hg (p q : QuantumTest) :
        sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) p) q =
          sourcePair p (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) q) := by
      exact (multiply_pair _ _ p q).symm
    have hsU (p q : QuantumTest) : sourcePair (forwardUAction s hs.le p) q =
        sourcePair p (forwardUAction s hs.le q) := by exact (multiply_pair _ _ p q).symm
    rw [hg, hsU]
    rw [show ∀ q : QuantumTest,
      forwardUAction s hs.le (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) q)) =
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) (forwardUAction s hs.le q)) from
      fun q => by
        apply DFunLike.ext
        intro z
        change (forwardU s z : ℂ) • ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) z : ℂ) •
          ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) z : ℂ) • q z)) =
          (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) z : ℂ) •
          ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) z : ℂ) • ((forwardU s z : ℂ) • q z))
        simp only [smul_smul]
        congr 1
        ring]
    rw [gain_square_inverse_power]
  have hroot (q : QuantumTest) : A q = inverseRootAction (D q) := rfl
  have ha : clockUDDensity s hs f =
      sourcePair (D f) (U (forwardUAction s hs.le (gaussianProfileWeight s hs (-2/3) (D f)))) := by
    unfold clockUDDensity
    rw [hroot]
    have hr := multiplier_commute (forwardU s) inverseRootVolume (forwardU_smooth s hs.le) inverse_root_volume_smooth
    have hw := multiplier_commute (fun z => (forwardRatio s z)^(-2/3:ℝ)) inverseRootVolume
      (fun z => by
        have hp : ContDiffAt ℝ ∞ (forwardRatio s) z.val :=
          (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
        exact hp.rpow_const_of_ne (forward_ratio_pos s hs.le z).ne') inverse_root_volume_smooth
    have hR := LinearMap.congr_fun hr.eq (D f)
    have hW := LinearMap.congr_fun hw.eq (D f)
    change forwardUAction s hs.le (inverseRootAction (D f)) = inverseRootAction (forwardUAction s hs.le (D f)) at hR
    change gaussianProfileWeight s hs (-2/3) (inverseRootAction (D f)) =
      inverseRootAction (gaussianProfileWeight s hs (-2/3) (D f)) at hW
    have hp (p q : QuantumTest) : sourcePair (inverseRootAction p) q =
        sourcePair p (inverseRootAction q) := by exact (multiply_pair _ _ p q).symm
    have hsU (p q : QuantumTest) : sourcePair (forwardUAction s hs.le p) q =
        sourcePair p (forwardUAction s hs.le q) := by exact (multiply_pair _ _ p q).symm
    rw [hR, hW, hp, inverse_root_square, hsU]
    congr 1
    apply DFunLike.ext
    intro z
    change (forwardU s z : ℂ) • ((reciprocalVolume z : ℂ) •
        ((((forwardRatio s z)^(-2/3:ℝ) : ℝ) : ℂ) • D f z)) =
      (reciprocalVolume z : ℂ) • ((forwardU s z : ℂ) •
        ((((forwardRatio s z)^(-2/3:ℝ) : ℝ) : ℂ) • D f z))
    simp only [smul_smul]
    congr 1
    ring
  rw [ha, ←hu]
  simpa only [sourcePair, Complex.ofReal_pow] using!
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed (U (D (correctedCompleteCore s hs ξ η f))))

/-- The source positive-clock jet differentiates the exact UD payment primitive. -/
theorem actual_UD_clock_primitive_slope (s : ℝ) (hs : 0 < s) (ξ η : ℝ) (f : QuantumTest) :
    Tendsto (fun h : ℝ => if hh : 0 < h then (h:ℂ)⁻¹ *
      (clockPotential (s+h) (add_pos hs hh) f - clockPotential s hs f) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 ((-12:ℂ) * (‖embed (U (D (correctedCompleteCore s hs ξ η f)))‖^2 : ℂ))) := by
  have h := actual_gaussian_weighted_positive_time_jet s hs (-2/3) (A f) (A f)
  have hc : (18:ℂ)*(((-2/3:ℝ):ℂ)) = -12 := by norm_num
  change Tendsto _ _ (𝓝 ((18*((-2/3:ℝ):ℂ)) * clockUDDensity s hs f)) at h
  rw [hc, actual_corrected_UD_clock_density s hs ξ η f] at h
  exact h
end LowEnergy.FirstCurrentPayer
