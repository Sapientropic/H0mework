import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SteinEnergy

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.SteinRaw

open Complex Filter MeasureTheory Set Classical
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalPaPhysicalGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier

local instance : CompleteSpace M := IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- The half-window rank-one contact of the original smooth return. -/
def halfMean (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  (4 : ℂ) * ∫ x : ℝ in symmetricInterval (q / 2), burnolRieszReturnRaw coordinate x

private def backward (coordinate : BurnolCompletedMellinCoordinate) : Hq :=
  burnolQuarterRestriction (burnolMultiplicativeDilation (-Real.log 2)
    (burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq)))

private theorem seed_read : (ConstantDual.seed : ℝ → ℂ) =ᵐ[volume]
    (symmetricInterval q).indicator (fun _ => (1 : ℂ)) := by
  have constant := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (intervalConstant_coeFn q)
  filter_upwards [burnolQuarterZeroExtension_coe (intervalConstant q), constant] with x read value
  change burnolQuarterZeroExtension (intervalConstant q) x = _
  rw [read]
  by_cases inside : x ∈ symmetricInterval q
  · simp only [indicator_of_mem inside, value inside]
  · simp only [indicator_of_notMem inside]

private theorem forward_constant_read :
    (burnolMultiplicativeDilation (Real.log 2) ConstantDual.seed : ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval (q / 2)).indicator (fun _ => (Real.sqrt 2 : ℂ)) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => (2 : ℝ) * x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) (r := (2 : ℝ)) (by norm_num))
  filter_upwards [burnolMultiplicativeDilation_coeFn (Real.log 2) ConstantDual.seed,
    qmp.ae seed_read] with x read seed
  have membership : 2 * x ∈ symmetricInterval q ↔ x ∈ symmetricInterval (q / 2) := by
    simp only [symmetricInterval, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [read]
  change (Real.exp (Real.log 2 / 2) : ℂ) * ConstantDual.seed (Real.exp (Real.log 2) * x) = _
  have amplitude : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2), amplitude, seed]
  by_cases inside : x ∈ symmetricInterval (q / 2)
  · rw [indicator_of_mem inside, indicator_of_mem (membership.mpr inside), mul_one]
  · rw [indicator_of_notMem inside, indicator_of_notMem (fun h => inside (membership.mp h)), mul_zero]

private theorem return_extension_read (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq) : ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval q).indicator (burnolRieszReturnRaw coordinate) := by
  have actual := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (Constructor.returnState_read coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe (Constructor.returnState coordinate : Hq), actual] with x ext read
  rw [ext]
  by_cases inside : x ∈ symmetricInterval q
  · simp only [indicator_of_mem inside, read inside]
  · simp only [indicator_of_notMem inside]

private theorem backward_mean (coordinate : BurnolCompletedMellinCoordinate) :
    (Real.sqrt 2 : ℂ) * burnolQuarterMeanCoefficient (backward coordinate) = halfMean coordinate := by
  have paired : inner ℂ (intervalConstant q) (backward coordinate) =
      inner ℂ (burnolMultiplicativeDilation (Real.log 2) ConstantDual.seed)
        (burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq)) := by
    have first : inner ℂ (intervalConstant q) (backward coordinate) =
      inner ℂ ConstantDual.seed (burnolMultiplicativeDilation (-Real.log 2)
        (burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq))) :=
      (ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _).symm
    rw [first]
    have second := (burnolMultiplicativeDilation (Real.log 2)).inner_map_eq_flip ConstantDual.seed
      (burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq))
    rw [← burnolMultiplicativeDilation_neg_eq_symm] at second
    exact second.symm
  have rawPair : inner ℂ (burnolMultiplicativeDilation (Real.log 2) ConstantDual.seed)
      (burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq)) =
      (Real.sqrt 2 : ℂ) * ∫ x : ℝ in symmetricInterval (q / 2), burnolRieszReturnRaw coordinate x := by
    rw [L2.inner_def, ← integral_const_mul, ← integral_indicator (measurableSet_symmetricInterval (q / 2))]
    apply integral_congr_ae
    filter_upwards [forward_constant_read, return_extension_read coordinate] with x first second
    rw [first, second]
    by_cases inside : x ∈ symmetricInterval (q / 2)
    · have large : x ∈ symmetricInterval q := ⟨by linarith [inside.1], by linarith [inside.2]⟩
      simp only [indicator_of_mem inside, indicator_of_mem large, RCLike.inner_apply, starRingEnd_apply]
      rw [show star (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) from Complex.conj_ofReal _]
      ring
    · simp only [indicator_of_notMem inside, inner_zero_left]
  have mean : burnolQuarterMeanCoefficient (backward coordinate) =
      (2 : ℂ) * inner ℂ (intervalConstant q) (backward coordinate) := by
    unfold burnolQuarterMeanCoefficient
    rw [Complex.ofReal_pow, burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)]
    norm_num
    ring
  rw [mean, paired, rawPair, halfMean]
  have square : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ = 2 * (Real.sqrt 2 : ℂ) ^ 2 * (∫ x : ℝ in symmetricInterval (q / 2), burnolRieszReturnRaw coordinate x) := by ring
    _ = _ := by rw [square]; ring

private theorem projected_extension (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterZeroExtension (ShiftPair.forward (ShiftPair.reverse (Constructor.returnState coordinate)) : Hq) =
      originalPhysicalCutoff (q / 2) (burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq)) -
        burnolQuarterMeanCoefficient (backward coordinate) • burnolMultiplicativeDilation (Real.log 2) ConstantDual.seed := by
  rw [ShiftPair.forward_extension]
  have centered : (ShiftPair.reverse (Constructor.returnState coordinate) : Hq) = backward coordinate -
      burnolQuarterMeanCoefficient (backward coordinate) • intervalConstant q := Constructor.zeroMean_read _
  rw [centered, map_sub, map_smul, map_sub, map_smul]
  congr 1
  change burnolMultiplicativeDilation (Real.log 2) (originalPhysicalCutoff q
    (burnolMultiplicativeDilation (-Real.log 2) (burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq)))) = _
  rw [originalPhysicalCutoff_dilation, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have radius : (2 : ℝ)⁻¹ * q = q / 2 := by norm_num
  rw [radius, burnolMultiplicativeDilation_add, add_neg_cancel, burnolMultiplicativeDilation_zero]

private theorem half_subset : symmetricInterval (q / 2) ⊆ symmetricInterval q := by
  intro x inside
  exact ⟨by linarith [inside.1], by linarith [inside.2]⟩

private theorem defect_extension (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterZeroExtension (SteinEnergy.defect coordinate : Hq) =
      burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq) -
        originalPhysicalCutoff (q / 2) (burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq)) +
        burnolQuarterMeanCoefficient (backward coordinate) • burnolMultiplicativeDilation (Real.log 2) ConstantDual.seed := by
  change burnolQuarterZeroExtension ((Constructor.returnState coordinate : Hq) -
    (ShiftPair.forward (ShiftPair.reverse (Constructor.returnState coordinate)) : Hq)) = _
  rw [map_sub, projected_extension]
  abel

/-- The same generated defect is constant on the half window and the original return on its exterior. -/
theorem defect_coeFn (coordinate : BurnolCompletedMellinCoordinate) :
    ((SteinEnergy.defect coordinate : Hq) : ℝ → ℂ) =ᵐ[μq]
      fun x => if x ∈ symmetricInterval (q / 2) then halfMean coordinate else burnolRieszReturnRaw coordinate x := by
  let returned := burnolQuarterZeroExtension (Constructor.returnState coordinate : Hq)
  let sliced := originalPhysicalCutoff (q / 2) returned
  let constant := burnolMultiplicativeDilation (Real.log 2) ConstantDual.seed
  let mean := burnolQuarterMeanCoefficient (backward coordinate)
  have ambientRead : (burnolQuarterZeroExtension (SteinEnergy.defect coordinate : Hq) : ℝ → ℂ) =ᵐ[volume]
      fun x => if x ∈ symmetricInterval (q / 2) then halfMean coordinate else
        (symmetricInterval q).indicator (burnolRieszReturnRaw coordinate) x := by
    rw [defect_extension]
    filter_upwards [Lp.coeFn_add (returned - sliced) (mean • constant), Lp.coeFn_sub returned sliced,
      Lp.coeFn_smul mean constant, return_extension_read coordinate,
      originalPhysicalCutoff_coeFn (q / 2) returned, forward_constant_read] with x addAt subAt scaledAt returnAt sliceAt constantAt
    change (returned - sliced + mean • constant) x = _
    rw [addAt]
    change (returned - sliced) x + (mean • constant) x = _
    rw [subAt, scaledAt]
    change returned x - sliced x + mean * constant x = _
    change returned x = _ at returnAt
    change sliced x = _ at sliceAt
    change constant x = _ at constantAt
    rw [sliceAt, constantAt]
    by_cases inside : x ∈ symmetricInterval (q / 2)
    · rw [if_pos inside, indicator_of_mem inside, indicator_of_mem inside]
      have paid : mean * (Real.sqrt 2 : ℂ) = halfMean coordinate := by
        rw [mul_comm]
        exact backward_mean coordinate
      rw [sub_self, zero_add, paid]
    · rw [if_neg inside, indicator_of_notMem inside, indicator_of_notMem inside, mul_zero,
        sub_zero, add_zero, returnAt]
  have restriction := LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
    (burnolQuarterZeroExtension (SteinEnergy.defect coordinate : Hq))
  change (burnolQuarterRestriction (burnolQuarterZeroExtension (SteinEnergy.defect coordinate : Hq)) : ℝ → ℂ) =ᵐ[μq] _ at restriction
  rw [burnolQuarterRestriction_zeroExtension] at restriction
  filter_upwards [restriction, ae_restrict_of_ae ambientRead,
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x localAt ambientAt inside
  rw [localAt, ambientAt, indicator_of_mem inside]

/-- The full half-window mass is retained as a positive rank-one contact. -/
theorem defect_norm (coordinate : BurnolCompletedMellinCoordinate) :
    ‖SteinEnergy.defect coordinate‖ ^ 2 =
      (∫ x : ℝ in (symmetricInterval q) \ (symmetricInterval (q / 2)), ‖burnolRieszReturnRaw coordinate x‖ ^ 2) +
        4 * ‖∫ x : ℝ in symmetricInterval (q / 2), burnolRieszReturnRaw coordinate x‖ ^ 2 := by
  classical
  let half := symmetricInterval (q / 2)
  let outer := (symmetricInterval q) \ half
  let raw := fun x => if x ∈ half then halfMean coordinate else burnolRieszReturnRaw coordinate x
  have hhalf : MeasurableSet half := measurableSet_symmetricInterval _
  have houter : MeasurableSet outer := (measurableSet_symmetricInterval q).diff hhalf
  have squareIntegrable : IntegrableOn (fun x : ℝ => ‖burnolRieszReturnRaw coordinate x‖ ^ 2) outer :=
    ((burnolRieszReturnRaw_continuous coordinate).norm.pow 2).integrableOn_Icc.mono_set sdiff_subset
  have constantIntegrable : IntegrableOn (fun _ : ℝ => ‖halfMean coordinate‖ ^ 2) half := continuous_const.integrableOn_Icc
  have split : (symmetricInterval q).indicator (fun x => ‖raw x‖ ^ 2) =
      half.indicator (fun _ => ‖halfMean coordinate‖ ^ 2) +
        outer.indicator (fun x => ‖burnolRieszReturnRaw coordinate x‖ ^ 2) := by
    funext x
    by_cases small : x ∈ half
    · have large := half_subset small
      have outside : x ∉ outer := fun h => h.2 small
      simp only [raw, if_pos small, indicator_of_mem small, indicator_of_mem large, Pi.add_apply,
        indicator_of_notMem outside, add_zero]
    · by_cases large : x ∈ symmetricInterval q
      · have outside : x ∈ outer := ⟨large, small⟩
        simp only [raw, if_neg small, indicator_of_notMem small, indicator_of_mem large, Pi.add_apply,
          indicator_of_mem outside, zero_add]
      · have outside : x ∉ outer := fun h => large h.1
        simp only [indicator_of_notMem small, indicator_of_notMem large, Pi.add_apply,
          indicator_of_notMem outside, add_zero]
  have sourceNorm : ‖SteinEnergy.defect coordinate‖ ^ 2 = ∫ x : ℝ in symmetricInterval q, ‖raw x‖ ^ 2 := by
    change ‖(SteinEnergy.defect coordinate : Hq)‖ ^ 2 = _
    rw [← burnolQuarterInterval_integral_norm_sq (SteinEnergy.defect coordinate : Hq)]
    exact integral_congr_ae ((defect_coeFn coordinate).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  rw [sourceNorm, ← integral_indicator (measurableSet_symmetricInterval q), split]
  simp only [Pi.add_apply]
  rw [integral_add ((integrable_indicator_iff hhalf).mpr constantIntegrable) ((integrable_indicator_iff houter).mpr squareIntegrable),
    integral_indicator hhalf, integral_indicator houter, setIntegral_const]
  have volumeHalf : volume.real half = q := by
    change volume.real (Icc (-(q / 2)) (q / 2)) = q
    rw [Real.volume_real_Icc]
    norm_num
  rw [volumeHalf]
  change q * ‖halfMean coordinate‖ ^ 2 + _ = _
  rw [halfMean, norm_mul]
  dsimp only [outer, half]
  norm_num
  ring

/-- Original inverse energy, exterior return energy and the actual half-window mean in one source identity. -/
theorem original_energy (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ (ShiftPair.forward (burnolRieszSingleFourierSource coordinate))
      (burnolMeanZeroOneMinusSquare (ShiftPair.forward (burnolRieszSingleFourierSource coordinate))) -
      inner ℂ (burnolRieszSingleFourierSource coordinate)
        (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate)) =
      ((∫ x : ℝ in (symmetricInterval q) \ (symmetricInterval (q / 2)), ‖burnolRieszReturnRaw coordinate x‖ ^ 2) +
        4 * ‖∫ x : ℝ in symmetricInterval (q / 2), burnolRieszReturnRaw coordinate x‖ ^ 2 : ℝ) := by
  rw [SteinEnergy.original_energy, ← Complex.ofReal_pow, defect_norm]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.SteinRaw
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
