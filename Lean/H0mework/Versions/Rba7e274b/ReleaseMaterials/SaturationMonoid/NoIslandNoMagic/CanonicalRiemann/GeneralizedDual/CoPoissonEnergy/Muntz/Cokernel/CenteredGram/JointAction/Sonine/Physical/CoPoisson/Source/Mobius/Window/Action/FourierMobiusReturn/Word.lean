import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators
open OriginalRieszSource
namespace Paid
export FiniteMobiusResolventFlux (coefficient actualMean lower_window_read M lowerWindow)
end Paid

def sourceH (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n*fullFourierSource coordinate (x/(n:ℕ))
def sourceHprime (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n*((n:ℕ):ℂ)⁻¹*burnolRieszReturnRawDerivative coordinate (x/(n:ℕ))
def sourceEdge (x : ℝ) : ℂ :=
  ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n*Edge.raw (1/4:ℝ) (x/(n:ℕ))
def sourceGamma (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  Paid.actualMean (fourierL2 (C.wholeContactResponse coordinate))
def sourceSigma : ℂ := ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n

def generatedFourierMobiusRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (symmetricInterval 4).indicator
    (fun y=>Kernel.beta coordinate*sourceEdge y-(y:ℂ)*sourceHprime coordinate y-
      star coordinate.value*sourceH coordinate y-sourceSigma*sourceGamma coordinate) x

theorem original_finite_word_ward (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    (∑ n ∈ burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n*(fullFourierResponse coordinate (x/(n:ℕ))-sourceGamma coordinate))=
      Kernel.beta coordinate*sourceEdge x-(x:ℂ)*sourceHprime coordinate x-
        star coordinate.value*sourceH coordinate x-sourceSigma*sourceGamma coordinate := by
  unfold sourceEdge sourceH sourceHprime sourceSigma
  simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [original_full_response_ward]
  have castDivision : ((x/(n:ℕ)):ℝ)=((n:ℕ):ℝ)⁻¹*x := by ring
  rw [castDivision]
  push_cast
  ring

-- The same lower CLM supplies all sixteen-cutoff columns and its actual quarter mean.
theorem actual_fourier_mobius_source (coordinate : BurnolCompletedMellinCoordinate) :
    (Paid.M (fourierL2 (C.wholeContactResponse coordinate)):ℝ→ℂ)=ᵐ[volume] generatedFourierMobiusRaw coordinate := by
  have read := (ae_restrict_iff' (measurableSet_symmetricInterval 4)).mp
    (Paid.lower_window_read (fourierL2 (C.wholeContactResponse coordinate)))
  have pulled : ∀ᵐ x : ℝ ∂volume,∀ n : ℕ+,
      (fourierL2 (C.wholeContactResponse coordinate)) (x/(n:ℕ))=fullFourierResponse coordinate (x/(n:ℕ)) := by
    apply ae_all_iff.mpr
    intro n
    have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ=>x/(n:ℕ)) volume volume := by
      simpa only [div_eq_mul_inv,mul_comm,smul_eq_mul] using
        Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=((n:ℕ):ℝ)⁻¹)
          (inv_ne_zero (by exact_mod_cast n.ne_zero))
    exact qmp.ae_eq (actual_fourier_response_read coordinate)
  filter_upwards [read,pulled,burnolRadiusZeroExtension_coe
      (Paid.lowerWindow (fourierL2 (C.wholeContactResponse coordinate)))] with x window source extended
  unfold Paid.M
  rw [ContinuousLinearMap.comp_apply,extended]
  unfold generatedFourierMobiusRaw
  by_cases inside : x∈symmetricInterval 4
  · simp only [indicator_of_mem inside]
    rw [window inside]
    have replaced : (∑ n ∈ burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n*((fourierL2 (C.wholeContactResponse coordinate)) (x/(n:ℕ))-Paid.actualMean (fourierL2 (C.wholeContactResponse coordinate))))=
        ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n*(fullFourierResponse coordinate (x/(n:ℕ))-sourceGamma coordinate) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [source n]
      rfl
    rw [replaced,original_finite_word_ward]
  · simp only [indicator_of_notMem inside]

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
