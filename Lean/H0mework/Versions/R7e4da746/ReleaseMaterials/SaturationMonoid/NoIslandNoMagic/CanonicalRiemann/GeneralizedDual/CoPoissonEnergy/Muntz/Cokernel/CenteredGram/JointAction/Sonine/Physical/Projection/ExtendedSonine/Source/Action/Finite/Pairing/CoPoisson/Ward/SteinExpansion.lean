import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SteinRaw
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SteinPaRead
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCountingGram

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.SteinExpansion

open Complex Filter MeasureTheory Set Classical
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "K" => burnolCompletedMellinRieszVector

/-- The reverse unitary dilation acts on the same original inverse defect. -/
def expanded (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolMultiplicativeDilation (-Real.log 2)
    (burnolQuarterZeroExtension (SteinEnergy.defect coordinate : Hq))

private theorem membership (x radius : ℝ) : x ∈ symmetricInterval radius ↔ |x| ≤ radius := abs_le.symm

private theorem defect_extension_read (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolQuarterZeroExtension (SteinEnergy.defect coordinate : Hq) : ℝ → ℂ) =ᵐ[volume]
      fun x => if |x| ≤ q then
        (if |x| ≤ q / 2 then SteinRaw.halfMean coordinate else burnolRieszReturnRaw coordinate x) else 0 := by
  have actual := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (SteinRaw.defect_coeFn coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe (SteinEnergy.defect coordinate : Hq), actual] with x ext read
  rw [ext]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, read inside, if_pos ((membership _ _).mp inside)]
    simp only [membership]
  · rw [indicator_of_notMem inside, if_neg (fun h => inside ((membership _ _).mpr h))]

private theorem return_abs (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszReturnRaw coordinate (|x| / 2) = burnolRieszReturnRaw coordinate (x / 2) := by
  rcases le_or_gt 0 x with positive | negative
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg negative, neg_div, return_raw_even]

/-- Full source equality, including the inner constant and both shell boundaries. -/
theorem original_source (coordinate : BurnolCompletedMellinCoordinate) :
    expanded coordinate = (Real.sqrt 2 : ℂ)⁻¹ •
      (SteinRaw.halfMean coordinate • ConstantDual.seed + SteinPaRead.source coordinate) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (-Real.log 2) * x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := Real.exp (-Real.log 2)) (Real.exp_ne_zero _))
  have amplitude : Real.exp (-Real.log 2 / 2) = (Real.sqrt 2)⁻¹ := by
    have root : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [show -Real.log 2 / 2 = -(Real.log 2 / 2) by ring, Real.exp_neg, root]
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn (-Real.log 2)
      (burnolQuarterZeroExtension (SteinEnergy.defect coordinate : Hq)),
    qmp.ae (defect_extension_read coordinate),
    Lp.coeFn_smul (Real.sqrt 2 : ℂ)⁻¹ (SteinRaw.halfMean coordinate • ConstantDual.seed + SteinPaRead.source coordinate),
    Lp.coeFn_add (SteinRaw.halfMean coordinate • ConstantDual.seed) (SteinPaRead.source coordinate),
    Lp.coeFn_smul (SteinRaw.halfMean coordinate) ConstantDual.seed,
    ConstantDual.seed_coeFn, SteinPaRead.source_read coordinate] with x dilation source scaled addAt head seed shell
  change burnolMultiplicativeDilation (-Real.log 2)
    (burnolQuarterZeroExtension (SteinEnergy.defect coordinate : Hq)) x = _
  rw [dilation, scaled]
  change (Real.exp (-Real.log 2 / 2) : ℂ) *
      burnolQuarterZeroExtension (SteinEnergy.defect coordinate : Hq) (Real.exp (-Real.log 2) * x) =
    (Real.sqrt 2 : ℂ)⁻¹ * (SteinRaw.halfMean coordinate • ConstantDual.seed + SteinPaRead.source coordinate) x
  rw [source, amplitude, Complex.ofReal_inv, addAt]
  change (Real.sqrt 2 : ℂ)⁻¹ * _ = (Real.sqrt 2 : ℂ)⁻¹ *
    ((SteinRaw.halfMean coordinate • ConstantDual.seed) x + SteinPaRead.source coordinate x)
  rw [head]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [seed, shell]
  simp only [ConstantDual.seedRaw, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have argument : (2 : ℝ)⁻¹ * x = x / 2 := by ring
  rw [argument, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), return_abs coordinate]
  by_cases inner : |x| ≤ q
  · have outer : |x| / 2 ≤ q := by linarith [abs_nonneg x]
    have half : |x| / 2 ≤ q / 2 := by linarith
    rw [if_pos outer, if_pos half, if_pos inner, if_neg (fun h => (not_lt_of_ge inner) h.1), mul_one, add_zero]
  · have ninner : q < |x| := lt_of_not_ge inner
    have nhalf : ¬|x| / 2 ≤ q / 2 := by linarith
    rw [if_neg inner, mul_zero, zero_add]
    by_cases outer : |x| ≤ 2 * q
    · rw [if_pos (by linarith : |x| / 2 ≤ q), if_neg nhalf, if_pos ⟨ninner, outer⟩]
    · rw [if_neg (by linarith : ¬|x| / 2 ≤ q), if_neg (fun h => outer h.2)]

/-- The original forward counting limit reads both the actual constant and its outer shell. -/
theorem original_pair (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    inner ℂ (KCountingGram.value coordinate) (expanded coordinate) =
      (SteinRaw.halfMean coordinate / (Real.sqrt 2 : ℂ)) *
        (-(q : ℂ) ^ (1 - coordinate.value) / coordinate.value +
          (1 / 2 : ℂ) * star (positionMean coordinate) * (Real.eulerMascheroniConstant - 1) -
          inner ℂ (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : Hq))
            (fourierL2 ReturnConstantTail.outside)) +
        (Real.sqrt 2 : ℂ)⁻¹ * inner ℂ (KCountingGram.value coordinate) (SteinPaRead.source coordinate) := by
  rw [original_source, inner_smul_right, inner_add_right, inner_smul_right,
    KCountingGram.constant_pairing coordinate zero, HKernelRead.original_pair coordinate zero]
  ring

/-- Same finite N and complete head/body survive the limit; no reverse Pa reading is set to zero. -/
theorem original_tendsto (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => inner ℂ (FiniteForcing.source N (K coordinate : BurnolL2)) (expanded coordinate)) atTop
      (𝓝 ((SteinRaw.halfMean coordinate / (Real.sqrt 2 : ℂ)) *
        (-(q : ℂ) ^ (1 - coordinate.value) / coordinate.value +
          (1 / 2 : ℂ) * star (positionMean coordinate) * (Real.eulerMascheroniConstant - 1) -
          inner ℂ (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : Hq))
            (fourierL2 ReturnConstantTail.outside)) +
        (Real.sqrt 2 : ℂ)⁻¹ * inner ℂ (KCountingGram.value coordinate) (SteinPaRead.source coordinate))) := by
  simpa only [original_pair coordinate zero] using
    (KCountingGram.forward_tendsto coordinate zero).inner (𝕜 := ℂ)
      (tendsto_const_nhds (x := expanded coordinate))

end
end OriginalRieszFinitePairing.CoPoisson.Ward.SteinExpansion
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
