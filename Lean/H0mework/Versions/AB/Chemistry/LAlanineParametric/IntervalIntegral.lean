import H0mework.Versions.AB.Chemistry.LAlanineParametric.IntervalLinear
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.IntervalParameterMap

open SourceGaussianModel SourceSignedEvaluator Set MeasureTheory
open scoped BigOperators

def determinantPair (a : MatrixPair) : Pair :=
  add (sub (mul (a 0 0) (sub (mul (a 1 1) (a 2 2)) (mul (a 1 2) (a 2 1))))
    (mul (a 0 1) (sub (mul (a 1 0) (a 2 2)) (mul (a 1 2) (a 2 0)))))
      (mul (a 0 2) (sub (mul (a 1 0) (a 2 1)) (mul (a 1 1) (a 2 0))))

theorem determinantPair_contains (a : MatrixPair) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (ha : ∀ i j, Holds (a i j) (A i j)) : Holds (determinantPair a) A.det := by
  have first := mul_holds _ _ _ _ (ha 0 0)
    (sub_holds _ _ _ _ (mul_holds _ _ _ _ (ha 1 1) (ha 2 2)) (mul_holds _ _ _ _ (ha 1 2) (ha 2 1)))
  have second := mul_holds _ _ _ _ (ha 0 1)
    (sub_holds _ _ _ _ (mul_holds _ _ _ _ (ha 1 0) (ha 2 2)) (mul_holds _ _ _ _ (ha 1 2) (ha 2 0)))
  have third := mul_holds _ _ _ _ (ha 0 2)
    (sub_holds _ _ _ _ (mul_holds _ _ _ _ (ha 1 0) (ha 2 1)) (mul_holds _ _ _ _ (ha 1 1) (ha 2 0)))
  convert add_holds _ _ _ _ (sub_holds _ _ _ _ first second) third using 1
  · rfl
  · rw [Matrix.det_fin_three]
    ring

def rationalBoxVolume (lower upper : Fin 3 → ℚ) : ℚ := ∏ axis : Fin 3, (upper axis - lower axis)

def integralPair (range : Pair) (lower upper : Fin 3 → ℚ) : Pair :=
  (range.1 * rationalBoxVolume lower upper, range.2 * rationalBoxVolume lower upper)

theorem integralPair_contains (range : Pair) (lower upper : Fin 3 → ℚ) (ordered : ∀ i, lower i ≤ upper i)
    (f : Point → ℝ) (continuous : Continuous f)
    (insideRange : ∀ x ∈ Icc (fun i => (lower i : ℝ)) (fun i => (upper i : ℝ)), Holds range (f x)) :
    Holds (integralPair range lower upper)
      (∫ x in Icc (fun i => (lower i : ℝ)) (fun i => (upper i : ℝ)), f x) := by
  let domain : Set Point := Icc (fun i => (lower i : ℝ)) (fun i => (upper i : ℝ))
  have horder : (fun i => (lower i : ℝ)) ≤ (fun i => (upper i : ℝ)) := fun i => Rat.cast_le.mpr (ordered i)
  have volumeEq : volume.real domain = (rationalBoxVolume lower upper : ℝ) := by
    change (volume (Icc _ _)).toReal = _
    rw [Real.volume_Icc_pi_toReal horder]
    simp only [rationalBoxVolume, Rat.cast_prod, Rat.cast_sub]
  have integrable : IntegrableOn f domain := continuous.continuousOn.integrableOn_compact isCompact_Icc
  have lowInt : IntegrableOn (fun _ : Point => (range.1 : ℝ)) domain :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have highInt : IntegrableOn (fun _ : Point => (range.2 : ℝ)) domain :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have low := setIntegral_mono_on lowInt integrable measurableSet_Icc (fun x hx => (insideRange x hx).1)
  have high := setIntegral_mono_on integrable highInt measurableSet_Icc (fun x hx => (insideRange x hx).2)
  simp only [setIntegral_const, smul_eq_mul, volumeEq] at low high
  simpa only [Holds, integralPair, Rat.cast_mul, mul_comm] using And.intro low high

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.IntervalParameterMap
