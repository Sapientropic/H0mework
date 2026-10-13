import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ContactFeedback.Group
import H0mework.Versions.V2.Arithmetic.RieszGreen.GapGram
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalContactFeedbackSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators
open OriginalRieszSource

def primitiveScale (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  (-star coordinate.value*GapEuler.gapMean (1/4:ℝ) coordinate)⁻¹

def primitiveMean (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  primitiveScale coordinate*GapEuler.gapMean (1/4:ℝ) coordinate

def primitiveRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  primitiveScale coordinate*burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) x

theorem original_primitive_gap_source (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalRieszFiniteSource.edgePrimitive coordinate=primitiveScale coordinate • OriginalRieszSourceGreen.gapState coordinate := by
  unfold OriginalRieszFiniteSource.edgePrimitive primitiveScale OriginalRieszSourceGreen.gapState
  rw [burnolAmbientCompletedMellinKernelFormula_eq_radiusSpecialization]
  rfl

 theorem original_primitive_position_gap (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalRieszFiniteSource.edgePrimitive coordinate∈locallyConstantFace (1/4:ℝ) := by
  apply mem_locallyConstantFace_iff_exists.mpr
  refine ⟨primitiveMean coordinate,?_⟩
  rw [original_primitive_gap_source,map_smul]
  change primitiveMean coordinate • intervalConstant (1/4:ℝ)=primitiveScale coordinate • burnolQuarterRestriction (OriginalRieszSourceGreen.gapState coordinate)
  rw [OriginalRieszSourceGreen.gapState_restriction,smul_smul]
  rfl

 theorem original_primitive_mean (coordinate : BurnolCompletedMellinCoordinate) :
    FiniteMobiusResolventFlux.actualMean (OriginalRieszFiniteSource.edgePrimitive coordinate)=primitiveMean coordinate := by
  rw [original_primitive_gap_source,map_smul,FiniteMobiusResolventFlux.actual_mean_eq_ambient,
    OriginalRieszSourceGreen.gapState_gapCoefficient]
  rfl

 theorem original_primitive_read (coordinate : BurnolCompletedMellinCoordinate) :
    (OriginalRieszFiniteSource.edgePrimitive coordinate:ℝ→ℂ)=ᵐ[volume] primitiveRaw coordinate := by
  rw [original_primitive_gap_source]
  filter_upwards [Lp.coeFn_smul (primitiveScale coordinate) (OriginalRieszSourceGreen.gapState coordinate),
    OriginalRieszSourceGreen.gapState_read coordinate] with x scalar read
  rw [scalar]
  change primitiveScale coordinate*OriginalRieszSourceGreen.gapState coordinate x=_
  rw [read]
  rfl

 theorem primitive_inner_raw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (inside : x∈symmetricInterval (1/4:ℝ)) : primitiveRaw coordinate x=primitiveMean coordinate := by
  unfold primitiveRaw primitiveMean
  rw [OriginalRieszSourceGreen.gapState_raw_gap coordinate inside]

 theorem primitive_positive_tail (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (outside : (1/4:ℝ)<x) :
    primitiveRaw coordinate x=primitiveScale coordinate*(1/2:ℂ)*(x:ℂ)^(-star coordinate.value) := by
  unfold primitiveRaw
  rw [OriginalRieszSourceGreen.gapState_raw_tail coordinate outside]
  ring

-- Every remaining primitive column reads its exact gap/tail source and its own actual mean.
theorem primitive_lower_word (coordinate : BurnolCompletedMellinCoordinate) :
    (FiniteMobiusResolventFlux.M (OriginalRieszFiniteSource.edgePrimitive coordinate):ℝ→ℂ)=ᵐ[volume]
      (symmetricInterval 4).indicator (fun x=>∑ n∈burnolCenteredMobiusCutoffFinset 4,
        FiniteMobiusResolventFlux.coefficient n*(primitiveRaw coordinate (x/(n:ℕ))-primitiveMean coordinate)) := by
  have read := (ae_restrict_iff' (measurableSet_symmetricInterval 4)).mp
    (FiniteMobiusResolventFlux.lower_window_read (OriginalRieszFiniteSource.edgePrimitive coordinate))
  have pulled : ∀ᵐ x : ℝ ∂volume,∀ n : ℕ+,
      OriginalRieszFiniteSource.edgePrimitive coordinate (x/(n:ℕ))=primitiveRaw coordinate (x/(n:ℕ)) := by
    apply ae_all_iff.mpr
    intro n
    have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ=>x/(n:ℕ)) volume volume := by
      simpa only [div_eq_mul_inv,mul_comm,smul_eq_mul] using
        Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=((n:ℕ):ℝ)⁻¹)
          (inv_ne_zero (by exact_mod_cast n.ne_zero))
    exact qmp.ae_eq (original_primitive_read coordinate)
  filter_upwards [read,pulled,burnolRadiusZeroExtension_coe
    (FiniteMobiusResolventFlux.lowerWindow (OriginalRieszFiniteSource.edgePrimitive coordinate))] with x window source extended
  unfold FiniteMobiusResolventFlux.M
  rw [ContinuousLinearMap.comp_apply,extended]
  by_cases inside : x∈symmetricInterval 4
  · simp only [indicator_of_mem inside]
    rw [window inside,original_primitive_mean]
    apply Finset.sum_congr rfl
    intro n _
    rw [source n]
  · simp only [indicator_of_notMem inside]

end OriginalContactFeedbackSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
