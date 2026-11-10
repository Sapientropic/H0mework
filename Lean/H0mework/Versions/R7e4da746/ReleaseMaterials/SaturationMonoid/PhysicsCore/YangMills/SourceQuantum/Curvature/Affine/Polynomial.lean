import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.Curvature.Affine.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff
noncomputable section
namespace SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Affine
open Variation Flat.Quantum FullPairing StageNineP286GaugeConnectionVariation
open StageNineP286GaugeAuxiliaryVariation StageNineHolonomicField Stage9C.Material.SpinPair
open SU7MotherLieAlgebra ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite P286CoordinateIndex
variable {n : ℕ} (η : Fin n → Variation.Input)

theorem linear_combine (q : Fin n → ℝ) (x : BasePoint) (r : Fin 6) :
    p286GaugeConnectionLinearCurvatureVariation actual (combine η q) x r =
      ∑ i, q i • p286GaugeConnectionLinearCurvatureVariation actual (η i) x r := by
  unfold p286GaugeConnectionLinearCurvatureVariation
  rw [combine_derivative, combine_derivative]
  simp only [combine, Finset.sum_apply, Pi.smul_apply, ← p286CoordinateLieBracketBilinear_apply,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, smul_add, smul_sub]

theorem quadratic_combine (q : Fin n → ℝ) (x : BasePoint) (r : Fin 6) :
    p286GaugeConnectionQuadraticCurvatureVariation (combine η q) x r =
      ∑ i, ∑ j, (q i*q j) • p286CoordinateLieBracket
        (η i x (pairFirst r)) (η j x (pairSecond r)) := by
  simp only [p286GaugeConnectionQuadraticCurvatureVariation, combine,
    Finset.sum_apply, Pi.smul_apply, ← p286CoordinateLieBracketBilinear_apply,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

def coordinateOperator : P286CoordinateCarrier →ₗ[ℝ] Variation.Operator where
  toFun z := operator (dualAction (History.coordinateAction z))
  map_add' a b := by
    ext v
    simp [History.coordinateAction_add, operator, dualAction, map_add]
  map_smul' t a := by
    apply ContinuousLinearMap.ext
    intro v
    change naturalCoordinates (flipMatter
      ((History.coordinateAction (t • a)) (naturalCoordinates.symm v))) =
      t • naturalCoordinates (flipMatter
        ((History.coordinateAction a) (naturalCoordinates.symm v)))
    rw [History.coordinateAction_smul, LinearMap.smul_apply, map_smul, map_smul]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) t _).symm

def mixed (i j : Fin n) (l : History.Label) : Variation.Operator :=
  coordinateOperator (p286CoordinateLieBracket
    (η i l.1 (pairFirst l.2)) (η j l.1 (pairSecond l.2)))

def value (q : Fin n → ℝ) : History.Polynomial →ₐ[ℂ] Variation.Operator :=
  Variation.representation.comp (quantumEvaluate (configuration η q))

theorem value_variation (q : Fin n → ℝ) (P : History.Polynomial) :
    value η q P = Variation.value (combine η q) 1 P := by
  simp only [value, configuration, Stage10.Runtime.configuration_eq]
  rfl

theorem generator (q : Fin n → ℝ) (l : History.Label) :
    value η q (FreeAlgebra.ι ℂ l) = NativeSource.GaugeWords.seed (FreeAlgebra.ι ℂ l) +
      (∑ i, q i • Variation.first (η i) l) +
        ∑ i, ∑ j, (q i*q j) • mixed η i j l := by
  rw [value_variation, Variation.generator_expansion]
  simp only [one_smul, one_pow]
  change _ + coordinateOperator
    (p286GaugeConnectionLinearCurvatureVariation actual (combine η q) l.1 l.2) +
      coordinateOperator (p286GaugeConnectionQuadraticCurvatureVariation (combine η q) l.1 l.2) = _
  rw [linear_combine, quadratic_combine]
  simp only [map_sum, map_smul]
  rfl

theorem value_smooth (P : History.Polynomial) : ContDiff ℝ ∞ (fun q => value η q P) := by
  induction P using FreeAlgebra.induction with
  | grade0 c => simpa only [AlgHom.commutes] using (contDiff_const (c := algebraMap ℂ Variation.Operator c))
  | grade1 l =>
    have linear : ContDiff ℝ ∞ (fun q : Fin n → ℝ => ∑ i, q i • Variation.first (η i) l) :=
      ContDiff.sum (fun i _ => (contDiff_apply ℝ ℝ i).smul contDiff_const)
    have quadratic : ContDiff ℝ ∞ (fun q : Fin n → ℝ => ∑ i, ∑ j, (q i*q j) • mixed η i j l) :=
      ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
        ((contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ j)).smul contDiff_const))
    simpa only [generator] using (contDiff_const.add linear).add quadratic
  | mul P Q hP hQ => simpa only [map_mul] using hP.mul hQ
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
end SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Affine
