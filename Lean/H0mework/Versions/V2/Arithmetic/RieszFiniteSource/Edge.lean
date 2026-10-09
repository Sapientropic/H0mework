import H0mework.Versions.V2.Arithmetic.RieszResponse.ResponseRead
import H0mework.Arithmetic.RieszResponse.Integration
import H0mework.Versions.V2.Arithmetic.RieszEuler.Even
import H0mework.Versions.V2.Arithmetic.MellinProjection.GapTailDilation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSource

open Complex MeasureTheory
open scoped Topology
open OriginalRieszSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)

private def coefficient (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  -star coordinate.value * GapEuler.gapMean q coordinate

private theorem coefficient_nonzero (coordinate : BurnolCompletedMellinCoordinate) :
    coefficient coordinate ≠ 0 := by
  have value : coordinate.value ≠ 0 := by
    intro zero
    have right := coordinate.rightHalf
    rw [zero] at right
    norm_num at right
  have mean : GapEuler.gapMean q coordinate ≠ 0 := by
    intro zero
    have primitive := GapEuler.gapMean_primitive q (by norm_num) coordinate
    rw [zero, mul_zero] at primitive
    have power : (q : ℂ) ^ (-star coordinate.value) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
    exact (mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) power) primitive.symm
  exact mul_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr value)) mean

/-- The explicit original gap/tail source generates an L² primitive of the full delta edge. -/
def edgePrimitive (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (coefficient coordinate)⁻¹ • burnolAmbientEvenPart
    (burnolRadiusAmbientCompletedMellinKernelFormula q (by norm_num) coordinate)

theorem edgePrimitive_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (edgePrimitive coordinate : TemperedDistribution ℝ ℂ) +
      (star coordinate.value - 1 / 2) •
        (edgePrimitive coordinate : TemperedDistribution ℝ ℂ) = GapEuler.edge q := by
  have primitive := GapEuler.even_gapTail_euler q (by norm_num) coordinate
  dsimp only at primitive
  have normalized := congrArg (fun value : TemperedDistribution ℝ ℂ =>
    (coefficient coordinate)⁻¹ • value) primitive
  change (coefficient coordinate)⁻¹ •
      (GapEuler.euler _ + (star coordinate.value - 1 / 2) • _) =
    (coefficient coordinate)⁻¹ • (coefficient coordinate • GapEuler.edge q) at normalized
  rw [smul_smul, inv_mul_cancel₀ (coefficient_nonzero coordinate), one_smul] at normalized
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (edgePrimitive coordinate)) +
    (star coordinate.value - 1 / 2) •
      (Lp.toTemperedDistributionCLM ℂ volume 2 (edgePrimitive coordinate)) = _
  simp only [edgePrimitive, map_smul, Lp.toTemperedDistributionCLM_apply]
  rw [← normalized]
  module

/-- Both operands come from the explicit gap/tail primitive and its original dilation action. -/
def edgeIntegral (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation endpoint (edgePrimitive coordinate) -
    fullMellinTranslationCharacter (star coordinate.value) endpoint • edgePrimitive coordinate

private theorem edge_action (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (shift : ℝ) :
    GapEuler.euler
        (burnolMultiplicativeDilation shift (edgePrimitive coordinate) : TemperedDistribution ℝ ℂ) test +
      (star coordinate.value - 1 / 2) *
        (burnolMultiplicativeDilation shift (edgePrimitive coordinate) : TemperedDistribution ℝ ℂ) test =
      GapEuler.edge q (coPoissonSchwartzEnergyTranslation (-shift) test) := by
  have source := congrArg (fun value : TemperedDistribution ℝ ℂ =>
    value (coPoissonSchwartzEnergyTranslation (-shift) test)) (edgePrimitive_euler coordinate)
  simp only [add_apply, smul_apply, smul_eq_mul] at source
  rw [OriginalRieszFiniteResponse.original_euler_action, OriginalRieszFiniteResponse.original_read]
  exact source

theorem edge_read_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    Continuous (fun shift : ℝ => GapEuler.edge q
      (coPoissonSchwartzEnergyTranslation (-shift) test)) := by
  let eval : TemperedDistribution ℝ ℂ →L[ℂ] ℂ :=
    PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test
  let valueRead : BurnolL2 →L[ℂ] ℂ := eval.comp (Lp.toTemperedDistributionCLM ℂ volume 2)
  let eulerRead : BurnolL2 →L[ℂ] ℂ :=
    (eval.comp GapEuler.euler).comp (Lp.toTemperedDistributionCLM ℂ volume 2)
  have orbit := burnolMultiplicativeDilation_stronglyContinuous (edgePrimitive coordinate)
  have generated : Continuous (fun shift : ℝ =>
      eulerRead (burnolMultiplicativeDilation shift (edgePrimitive coordinate)) +
        (star coordinate.value - 1 / 2) *
          valueRead (burnolMultiplicativeDilation shift (edgePrimitive coordinate))) :=
    (eulerRead.continuous.comp orbit).add (continuous_const.mul (valueRead.continuous.comp orbit))
  exact generated.congr (edge_action coordinate test)

theorem edgeIntegral_read (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    (edgeIntegral coordinate endpoint : TemperedDistribution ℝ ℂ) test =
      ∫ time : ℝ in (0 : ℝ)..endpoint,
        Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
          GapEuler.edge q (coPoissonSchwartzEnergyTranslation (-time) test) := by
  have derivative (shift : ℝ) : HasDerivAt
      (fun time : ℝ =>
        (burnolMultiplicativeDilation time (edgePrimitive coordinate) : TemperedDistribution ℝ ℂ) test)
      (GapEuler.edge q (coPoissonSchwartzEnergyTranslation (-shift) test) -
        (star coordinate.value - 1 / 2) *
          (burnolMultiplicativeDilation shift (edgePrimitive coordinate) : TemperedDistribution ℝ ℂ) test)
      shift := by
    rw [← edge_action, add_sub_cancel_right]
    exact Dilation.original_weak_derivative (edgePrimitive coordinate) test shift
  have generated := _root_.OriginalRieszFiniteResponse.Integration.finite_response
    (fun time : ℝ =>
      (burnolMultiplicativeDilation time (edgePrimitive coordinate) : TemperedDistribution ℝ ℂ) test)
    (fun time : ℝ => GapEuler.edge q (coPoissonSchwartzEnergyTranslation (-time) test))
    (star coordinate.value - 1 / 2) derivative (edge_read_continuous coordinate test) endpoint
  have base : (burnolMultiplicativeDilation 0 (edgePrimitive coordinate) :
      TemperedDistribution ℝ ℂ) test = (edgePrimitive coordinate : TemperedDistribution ℝ ℂ) test := by
    rw [OriginalRieszFiniteResponse.original_read, neg_zero, coPoissonSchwartzEnergyTranslation_zero]
  rw [base] at generated
  have character : fullMellinTranslationCharacter (star coordinate.value) endpoint =
      Complex.exp (-(star coordinate.value - 1 / 2) * (endpoint : ℂ)) := by
    unfold fullMellinTranslationCharacter
    congr 1
    ring
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (edgeIntegral coordinate endpoint)) test = _
  rw [edgeIntegral, map_sub, map_smul]
  simp only [sub_apply, smul_apply, smul_eq_mul, Lp.toTemperedDistributionCLM_apply]
  rw [character, generated, add_sub_cancel_left]

end
end OriginalRieszFiniteSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
