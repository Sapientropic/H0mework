import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResolventReconstruction.Action
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DilationWard
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceGramAction
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalKSourceResolventReconstruction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace FourierTransform
noncomputable section

def jumpColumns : Fin 2 → BurnolL2 :=
  ![ConstantDual.seed, -fourierL2 ConstantDual.seed]

/-- Both original constant contacts remain in the L² forcing. -/
def regularForcing (coordinate : BurnolCompletedMellinCoordinate) : Fin 2 → BurnolL2 :=
  ![fourierL2 Response.wholeU - Response.wholeV +
      (1/2 - sourceRate coordinate) • ConstantDual.seed,
    Response.wholeU - fourierL2 Response.wholeV +
      (sourceRate coordinate + 1/2) • fourierL2 ConstantDual.seed]

/-- This constructor receives only the original source forcing, not Y or K. -/
def regularColumns (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) : BurnolL2 :=
  -(1/2 : ℂ) • sourceResolvent coordinate (regularForcing coordinate i)

private theorem constant_euler :
    GapEuler.euler (ConstantDual.seed : TemperedDistribution ℝ ℂ) =
      -GapEuler.edge (1/4) - (1/2 : ℂ) • (ConstantDual.seed : TemperedDistribution ℝ ℂ) := by
  ext test
  have source := ConstantDual.seed_edge test
  rw [ConstantDual.edgeRead_apply] at source
  simp only [sub_apply, neg_apply, smul_apply, smul_eq_mul]
  linear_combination -source

private theorem fourier_constant_euler :
    GapEuler.euler (fourierL2 ConstantDual.seed : TemperedDistribution ℝ ℂ) =
      FourierTransform.fourier (GapEuler.edge (1/4)) +
        (1/2 : ℂ) • (fourierL2 ConstantDual.seed : TemperedDistribution ℝ ℂ) := by
  have native : FourierTransform.fourier (ConstantDual.seed : TemperedDistribution ℝ ℂ) =
      (fourierL2 ConstantDual.seed : TemperedDistribution ℝ ℂ) := Lp.fourier_toTemperedDistribution_eq _
  rw [← native, GapEuler.euler_fourier, constant_euler]
  change -(fourierCLM ℂ (TemperedDistribution ℝ ℂ))
    (-GapEuler.edge (1/4) - (1/2 : ℂ) • (ConstantDual.seed : TemperedDistribution ℝ ℂ)) = _
  rw [map_sub, map_neg, map_smul]
  change -(-FourierTransform.fourier (GapEuler.edge (1/4)) -
      (1/2 : ℂ) • FourierTransform.fourier (ConstantDual.seed : TemperedDistribution ℝ ℂ)) =
    FourierTransform.fourier (GapEuler.edge (1/4)) +
      (1/2 : ℂ) • FourierTransform.fourier (ConstantDual.seed : TemperedDistribution ℝ ℂ)
  module

theorem regularColumns_euler (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    GapEuler.euler (regularColumns coordinate i : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • (regularColumns coordinate i : TemperedDistribution ℝ ℂ) =
        (regularForcing coordinate i : TemperedDistribution ℝ ℂ) := by
  have inverse := sourceResolvent_euler coordinate (regularForcing coordinate i)
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (regularColumns coordinate i)) +
    sourceRate coordinate • Lp.toTemperedDistributionCLM ℂ volume 2 (regularColumns coordinate i) = _
  simp only [regularColumns, map_smul, Lp.toTemperedDistributionCLM_apply]
  linear_combination (norm := module) -(1/2 : ℂ) • inverse

private theorem corrected_source_euler (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    GapEuler.euler ((sourceColumns coordinate i - jumpColumns i : BurnolL2) : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • ((sourceColumns coordinate i - jumpColumns i : BurnolL2) : TemperedDistribution ℝ ℂ) =
        (regularForcing coordinate i : TemperedDistribution ℝ ℂ) := by
  fin_cases i
  · have source := sourceY0_euler coordinate
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
      (sourceY0 coordinate - ConstantDual.seed)) +
      sourceRate coordinate • Lp.toTemperedDistributionCLM ℂ volume 2
        (sourceY0 coordinate - ConstantDual.seed) =
      Lp.toTemperedDistributionCLM ℂ volume 2 (regularForcing coordinate 0)
    simp only [regularForcing, Matrix.cons_val_zero, map_add, map_sub, map_smul,
      Lp.toTemperedDistributionCLM_apply]
    rw [Response.Psi, Lp.fourier_toTemperedDistribution_eq] at source
    change GapEuler.euler (sourceY0 coordinate : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • (sourceY0 coordinate : TemperedDistribution ℝ ℂ) =
      (fourierL2 Response.wholeU : TemperedDistribution ℝ ℂ) -
        (Response.wholeV : TemperedDistribution ℝ ℂ) - GapEuler.edge (1/4) at source
    rw [constant_euler]
    linear_combination (norm := module) source
  · have source := sourceY1_euler coordinate
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
      (sourceY1 coordinate - -fourierL2 ConstantDual.seed)) +
      sourceRate coordinate • Lp.toTemperedDistributionCLM ℂ volume 2
        (sourceY1 coordinate - -fourierL2 ConstantDual.seed) =
      Lp.toTemperedDistributionCLM ℂ volume 2 (regularForcing coordinate 1)
    simp only [regularForcing, Matrix.cons_val_one, Matrix.cons_val_zero, map_add, map_sub,
      map_neg, map_smul, Lp.toTemperedDistributionCLM_apply]
    rw [Response.Psi_fourier, Lp.fourier_toTemperedDistribution_eq] at source
    change GapEuler.euler (sourceY1 coordinate : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • (sourceY1 coordinate : TemperedDistribution ℝ ℂ) =
      (Response.wholeU : TemperedDistribution ℝ ℂ) -
        (fourierL2 Response.wholeV : TemperedDistribution ℝ ℂ) -
          FourierTransform.fourier (GapEuler.edge (1/4)) at source
    rw [fourier_constant_euler]
    linear_combination (norm := module) source

/-- Actual R inverse and Euler uniqueness identify both source columns, including their jumps. -/
theorem sourceColumns_from_regular_resolvent (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    sourceColumns coordinate i = regularColumns coordinate i + jumpColumns i := by
  have original := corrected_source_euler coordinate i
  have split : ((sourceColumns coordinate i - jumpColumns i : BurnolL2) : TemperedDistribution ℝ ℂ) =
      (sourceColumns coordinate i : TemperedDistribution ℝ ℂ) -
        (jumpColumns i : TemperedDistribution ℝ ℂ) :=
    (Lp.toTemperedDistributionCLM ℂ volume 2).map_sub _ _
  rw [split, map_sub] at original
  have generated := regularColumns_euler coordinate i
  have homogeneous : GapEuler.euler
      ((sourceColumns coordinate i - jumpColumns i - regularColumns coordinate i : BurnolL2) : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate •
        ((sourceColumns coordinate i - jumpColumns i - regularColumns coordinate i : BurnolL2) : TemperedDistribution ℝ ℂ) = 0 := by
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
      (sourceColumns coordinate i - jumpColumns i - regularColumns coordinate i)) +
      sourceRate coordinate • Lp.toTemperedDistributionCLM ℂ volume 2
        (sourceColumns coordinate i - jumpColumns i - regularColumns coordinate i) = 0
    simp only [map_sub, Lp.toTemperedDistributionCLM_apply]
    linear_combination (norm := module) original - generated
  have positive : 0 < (sourceRate coordinate).re := by
    simp only [sourceRate, Complex.sub_re, Complex.star_def, Complex.conj_re]
    norm_num
    linarith [coordinate.rightHalf]
  have same := sub_eq_zero.mp (homogeneous_L2_unique (sourceRate coordinate) positive _ homogeneous)
  exact (sub_eq_iff_eq_add).mp same

/-- The unchanged original paired character defines the full ambient bilinear defect. -/
def finitePair (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (left right : BurnolL2) : ℂ :=
  (1/2 : ℂ) * inner ℂ left
    (burnolMultiplicativeDilation h right + burnolMultiplicativeDilation (-h) right) -
  pairedMellinTranslationCharacter coordinate.value h * inner ℂ left right

private theorem finitePair_add_left (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (left right test : BurnolL2) :
    finitePair coordinate h (left + right) test = finitePair coordinate h left test + finitePair coordinate h right test := by
  simp only [finitePair, inner_add_left]
  ring

private theorem finitePair_add_right (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (test left right : BurnolL2) :
    finitePair coordinate h test (left + right) = finitePair coordinate h test left + finitePair coordinate h test right := by
  simp only [finitePair, map_add, inner_add_right]
  ring

private theorem euler_dilation (value rhs : BurnolL2)
    (equation : GapEuler.euler (value : TemperedDistribution ℝ ℂ) = (rhs : TemperedDistribution ℝ ℂ))
    (h : ℝ) :
    GapEuler.euler (burnolMultiplicativeDilation h value : TemperedDistribution ℝ ℂ) =
      (burnolMultiplicativeDilation h rhs : TemperedDistribution ℝ ℂ) := by
  ext test
  rw [OriginalRieszFiniteResponse.original_euler_action, equation,
    OriginalRieszFiniteResponse.original_read]

private theorem euler_source_shift_balance (coordinate : BurnolCompletedMellinCoordinate)
    (left leftForcing right rightForcing : BurnolL2)
    (leftEquation : GapEuler.euler (left : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • (left : TemperedDistribution ℝ ℂ) = (leftForcing : TemperedDistribution ℝ ℂ))
    (rightEquation : GapEuler.euler (right : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • (right : TemperedDistribution ℝ ℂ) = (rightForcing : TemperedDistribution ℝ ℂ))
    (h : ℝ) :
    (star (sourceRate coordinate) + sourceRate coordinate) * inner ℂ left (burnolMultiplicativeDilation h right) =
      inner ℂ leftForcing (burnolMultiplicativeDilation h right) +
        inner ℂ left (burnolMultiplicativeDilation h rightForcing) := by
  have leftActual : GapEuler.euler (left : TemperedDistribution ℝ ℂ) =
      ((leftForcing - sourceRate coordinate • left : BurnolL2) : TemperedDistribution ℝ ℂ) := by
    change _ = Lp.toTemperedDistributionCLM ℂ volume 2 (leftForcing - sourceRate coordinate • left)
    simp only [map_sub, map_smul, Lp.toTemperedDistributionCLM_apply]
    exact eq_sub_of_add_eq leftEquation
  have rightActual : GapEuler.euler (right : TemperedDistribution ℝ ℂ) =
      ((rightForcing - sourceRate coordinate • right : BurnolL2) : TemperedDistribution ℝ ℂ) := by
    change _ = Lp.toTemperedDistributionCLM ℂ volume 2 (rightForcing - sourceRate coordinate • right)
    simp only [map_sub, map_smul, Lp.toTemperedDistributionCLM_apply]
    exact eq_sub_of_add_eq rightEquation
  have skew := DilationWard.cross_balance left (leftForcing - sourceRate coordinate • left)
    (burnolMultiplicativeDilation h right)
    (burnolMultiplicativeDilation h (rightForcing - sourceRate coordinate • right))
    leftActual (euler_dilation right _ rightActual h)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply] at skew
  linear_combination -skew

theorem regular_source_Gram_Sylvester (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (i j : Fin 2) :
    (star (sourceRate coordinate) + sourceRate coordinate) *
      finitePair coordinate h (regularColumns coordinate i) (regularColumns coordinate j) =
      finitePair coordinate h (regularForcing coordinate i) (regularColumns coordinate j) +
        finitePair coordinate h (regularColumns coordinate i) (regularForcing coordinate j) := by
  have positiveShift := euler_source_shift_balance coordinate _ _ _ _
    (regularColumns_euler coordinate i) (regularColumns_euler coordinate j) h
  have negativeShift := euler_source_shift_balance coordinate _ _ _ _
    (regularColumns_euler coordinate i) (regularColumns_euler coordinate j) (-h)
  have stationary := euler_source_shift_balance coordinate _ _ _ _
    (regularColumns_euler coordinate i) (regularColumns_euler coordinate j) 0
  rw [burnolMultiplicativeDilation_zero, burnolMultiplicativeDilation_zero] at stationary
  simp only [finitePair, inner_add_right]
  linear_combination (1/2 : ℂ)*positiveShift + (1/2 : ℂ)*negativeShift -
    pairedMellinTranslationCharacter coordinate.value h * stationary

/-- Source forcing and all three jump/contact pieces generate the original Gram equation. -/
def sourceGramForcing (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (i j : Fin 2) : ℂ :=
  finitePair coordinate h (regularForcing coordinate i) (regularColumns coordinate j) +
  finitePair coordinate h (regularColumns coordinate i) (regularForcing coordinate j) +
  (star (sourceRate coordinate) + sourceRate coordinate) *
    (finitePair coordinate h (regularColumns coordinate i) (jumpColumns j) +
     finitePair coordinate h (jumpColumns i) (regularColumns coordinate j) +
     finitePair coordinate h (jumpColumns i) (jumpColumns j))

theorem sourceFiniteGram_source_action (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (i j : Fin 2) :
    (star (sourceRate coordinate) + sourceRate coordinate) * sourceFiniteGram coordinate h i j =
      sourceGramForcing coordinate h i j := by
  change (star (sourceRate coordinate) + sourceRate coordinate) *
    finitePair coordinate h (sourceColumns coordinate i) (sourceColumns coordinate j) = _
  rw [sourceColumns_from_regular_resolvent coordinate i,
    sourceColumns_from_regular_resolvent coordinate j,
    finitePair_add_left, finitePair_add_right, finitePair_add_right]
  have generated := regular_source_Gram_Sylvester coordinate h i j
  unfold sourceGramForcing
  linear_combination generated

theorem sourceRate_sum_ne_zero (coordinate : BurnolCompletedMellinCoordinate) :
    star (sourceRate coordinate) + sourceRate coordinate ≠ 0 := by
  intro zero
  have re := congrArg Complex.re zero
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re,
    sourceRate, Complex.sub_re, Complex.zero_re] at re
  norm_num at re
  linarith [coordinate.rightHalf]

/-- The original diagonal residual is governed by the full source action and every contact cross. -/
theorem original_fixedResidual_source_action (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    (star (sourceRate coordinate) + sourceRate coordinate) * burnolPaFixedShiftResidual coordinate zero =
      ∑ i : Fin 2, ∑ j : Fin 2,
        star (sourceCoefficients coordinate i) * sourceCoefficients coordinate j *
          sourceGramForcing coordinate (Real.log (Real.sqrt 3)) i j := by
  rw [original_fixedResidual_source_Gram]
  simp only [stageZeroSonineQ, Fin.sum_univ_two]
  have g00 := sourceFiniteGram_source_action coordinate (Real.log (Real.sqrt 3)) 0 0
  have g01 := sourceFiniteGram_source_action coordinate (Real.log (Real.sqrt 3)) 0 1
  have g10 := sourceFiniteGram_source_action coordinate (Real.log (Real.sqrt 3)) 1 0
  have g11 := sourceFiniteGram_source_action coordinate (Real.log (Real.sqrt 3)) 1 1
  linear_combination
    (star (sourceCoefficients coordinate 0) * sourceCoefficients coordinate 0) * g00 +
    (star (sourceCoefficients coordinate 0) * sourceCoefficients coordinate 1) * g01 +
    (star (sourceCoefficients coordinate 1) * sourceCoefficients coordinate 0) * g10 +
    (star (sourceCoefficients coordinate 1) * sourceCoefficients coordinate 1) * g11

theorem original_fixedResidual_from_source_forcing (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    burnolPaFixedShiftResidual coordinate zero =
      (star (sourceRate coordinate) + sourceRate coordinate)⁻¹ *
        ∑ i : Fin 2, ∑ j : Fin 2,
          star (sourceCoefficients coordinate i) * sourceCoefficients coordinate j *
            sourceGramForcing coordinate (Real.log (Real.sqrt 3)) i j := by
  apply mul_left_cancel₀ (sourceRate_sum_ne_zero coordinate)
  rw [← mul_assoc, mul_inv_cancel₀ (sourceRate_sum_ne_zero coordinate), one_mul]
  exact original_fixedResidual_source_action coordinate zero

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceGramAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
