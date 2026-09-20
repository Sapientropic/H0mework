import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Energy-side incidence boundary for the quarter carrier

This file records the exact typed boundary between the source-owned quarter
`L²` carrier and a Mellin eigenfunctional.  The carrier has genuine
measure-preserving translation/reflection maps.  A Mellin functional at an
arbitrary zero is only defined on its Mellin-convergent domain; extending it
to the `L²` carrier is therefore an explicit source obligation, never a
caller-supplied field.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Filter
open scoped ENNReal

noncomputable section

abbrev PositiveMellinQuarterEnergy :=
  Lp ℂ (2 : ℝ≥0∞) (volume : Measure ℝ)

def positiveMellinQuarterEnergyTranslation
    (h : ℝ) : PositiveMellinQuarterEnergy →ₗ[ℂ]
      PositiveMellinQuarterEnergy where
  toFun := fun f => DomAddAct.mk h +ᵥ f
  map_add' f g := by
    exact DomAddAct.vadd_Lp_add (DomAddAct.mk h) f g
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • f)
        (measurePreserving_add_left (volume : Measure ℝ) h),
      Lp.coeFn_compMeasurePreserving f
        (measurePreserving_add_left (volume : Measure ℝ) h),
      (measurePreserving_add_left (volume : Measure ℝ) h).quasiMeasurePreserving.ae
        (Lp.coeFn_smul c f),
      Lp.coeFn_smul c
        (Lp.compMeasurePreserving (fun x : ℝ => h + x)
          (measurePreserving_add_left (volume : Measure ℝ) h) f)] with x hx hy hcf hcomp
    calc
      ((Lp.compMeasurePreserving (fun x : ℝ => h + x)
          (measurePreserving_add_left (volume : Measure ℝ) h)) (c • f) :
          Lp ℂ (2 : ℝ≥0∞) volume) x =
          ((c • f : Lp ℂ (2 : ℝ≥0∞) volume) ∘ fun x : ℝ => h + x) x := hx
      _ = c * (f ∘ fun x : ℝ => h + x) x := by
        simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hcf
      _ = c * ((Lp.compMeasurePreserving (fun x : ℝ => h + x)
          (measurePreserving_add_left (volume : Measure ℝ) h) f) x) := by
        rw [hy]
      _ = ((RingHom.id ℂ) c •
          (Lp.compMeasurePreserving (fun x : ℝ => h + x)
            (measurePreserving_add_left (volume : Measure ℝ) h) f)) x := by
        simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using hcomp.symm

def positiveMellinQuarterEnergyReflection :
    PositiveMellinQuarterEnergy →ₗ[ℂ] PositiveMellinQuarterEnergy where
  toFun := Lp.compMeasurePreserving (fun x : ℝ => -x)
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  map_add' f g := by
    exact (Lp.compMeasurePreserving
      (fun x : ℝ => -x)
      (Measure.measurePreserving_neg (volume : Measure ℝ))).map_add f g
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • f)
        (Measure.measurePreserving_neg (volume : Measure ℝ)),
      Lp.coeFn_compMeasurePreserving f
        (Measure.measurePreserving_neg (volume : Measure ℝ)),
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
        (Lp.coeFn_smul c f),
      Lp.coeFn_smul c
        (Lp.compMeasurePreserving (fun x : ℝ => -x)
          (Measure.measurePreserving_neg (volume : Measure ℝ)) f)] with x hx hy hcf hcomp
    calc
      ((Lp.compMeasurePreserving (fun x : ℝ => -x)
          (Measure.measurePreserving_neg (volume : Measure ℝ))) (c • f) :
          Lp ℂ (2 : ℝ≥0∞) volume) x =
          ((c • f : Lp ℂ (2 : ℝ≥0∞) volume) ∘ fun x : ℝ => -x) x := hx
      _ = c * (f ∘ fun x : ℝ => -x) x := by
        simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hcf
      _ = c * ((Lp.compMeasurePreserving (fun x : ℝ => -x)
          (Measure.measurePreserving_neg (volume : Measure ℝ)) f) x) := by
        rw [hy]
      _ = ((RingHom.id ℂ) c •
          (Lp.compMeasurePreserving (fun x : ℝ => -x)
            (Measure.measurePreserving_neg (volume : Measure ℝ)) f)) x := by
        simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using hcomp.symm

theorem positiveMellinQuarterEnergyTranslation_norm
    (h : ℝ) (f : PositiveMellinQuarterEnergy) :
    ‖positiveMellinQuarterEnergyTranslation h f‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving f
    (measurePreserving_add_left (volume : Measure ℝ) h)

theorem positiveMellinQuarterEnergyReflection_norm
    (f : PositiveMellinQuarterEnergy) :
    ‖positiveMellinQuarterEnergyReflection f‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving f
    (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem positiveMellinQuarterEnergyTranslation_zero
    (f : PositiveMellinQuarterEnergy) :
    positiveMellinQuarterEnergyTranslation 0 f = f := by
  change Lp.compMeasurePreserving (fun x : ℝ => 0 + x)
      (measurePreserving_add_left (volume : Measure ℝ) 0) f = f
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
      (measurePreserving_add_left (volume : Measure ℝ) 0)] with x hx
  rw [hx]
  simp

theorem positiveMellinQuarterEnergyTranslation_comp
    (h k : ℝ) :
  (positiveMellinQuarterEnergyTranslation h).comp
        (positiveMellinQuarterEnergyTranslation k) =
      positiveMellinQuarterEnergyTranslation (k + h) := by
  apply LinearMap.ext
  intro f
  change Lp.compMeasurePreserving (fun x : ℝ => h + x)
      (measurePreserving_add_left (volume : Measure ℝ) h)
      (Lp.compMeasurePreserving (fun x : ℝ => k + x)
        (measurePreserving_add_left (volume : Measure ℝ) k) f) =
    Lp.compMeasurePreserving (fun x : ℝ => k + h + x)
      (measurePreserving_add_left (volume : Measure ℝ) (k + h)) f
  rw [← Lp.compMeasurePreserving_comp_apply f
    (measurePreserving_add_left (volume : Measure ℝ) k)
    (measurePreserving_add_left (volume : Measure ℝ) h)]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
      (measurePreserving_add_left (volume : Measure ℝ) (k + h)),
    Lp.coeFn_compMeasurePreserving f
      ((measurePreserving_add_left (volume : Measure ℝ) k).comp
        (measurePreserving_add_left (volume : Measure ℝ) h))] with x hx hy
  rw [hx, hy]
  simp only [Function.comp_apply]
  congr 1
  ring

theorem positiveMellinQuarterEnergyReflection_involutive
    (f : PositiveMellinQuarterEnergy) :
    positiveMellinQuarterEnergyReflection
        (positiveMellinQuarterEnergyReflection f) = f := by
  change Lp.compMeasurePreserving (fun x : ℝ => -x)
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (Lp.compMeasurePreserving (fun x : ℝ => -x)
        (Measure.measurePreserving_neg (volume : Measure ℝ)) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f
    (Measure.measurePreserving_neg (volume : Measure ℝ))
    (Measure.measurePreserving_neg (volume : Measure ℝ))]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ)))] with x hx
  rw [hx]
  simp only [Function.comp_apply]
  simp

/-- The actual translation action is an isometric equivalence, with inverse
given by the opposite logarithmic shift. -/
def positiveMellinQuarterEnergyTranslationEquiv (h : ℝ) :
    PositiveMellinQuarterEnergy ≃ₗ[ℂ] PositiveMellinQuarterEnergy :=
  { positiveMellinQuarterEnergyTranslation h with
    invFun := positiveMellinQuarterEnergyTranslation (-h)
    left_inv := by
      intro f
      have comp := congrArg
        (fun F : PositiveMellinQuarterEnergy →ₗ[ℂ]
          PositiveMellinQuarterEnergy => F f)
        (positiveMellinQuarterEnergyTranslation_comp (-h) h)
      calc
        positiveMellinQuarterEnergyTranslation (-h)
            (positiveMellinQuarterEnergyTranslation h f) =
          ((positiveMellinQuarterEnergyTranslation (-h)).comp
            (positiveMellinQuarterEnergyTranslation h)) f := rfl
        _ = positiveMellinQuarterEnergyTranslation (h + -h) f := comp
        _ = f := by simpa using positiveMellinQuarterEnergyTranslation_zero f
    right_inv := by
      intro f
      have comp := congrArg
        (fun F : PositiveMellinQuarterEnergy →ₗ[ℂ]
          PositiveMellinQuarterEnergy => F f)
        (positiveMellinQuarterEnergyTranslation_comp h (-h))
      calc
        positiveMellinQuarterEnergyTranslation h
            (positiveMellinQuarterEnergyTranslation (-h) f) =
          ((positiveMellinQuarterEnergyTranslation h).comp
            (positiveMellinQuarterEnergyTranslation (-h))) f := rfl
        _ = positiveMellinQuarterEnergyTranslation (-h + h) f := comp
        _ = f := by simpa using positiveMellinQuarterEnergyTranslation_zero f }

/-- Norm preservation upgrades the translation equivalence to the genuine
isometric equivalence used by the energy boundary. -/
def positiveMellinQuarterEnergyTranslationIsometry (h : ℝ) :
    PositiveMellinQuarterEnergy ≃ₗᵢ[ℂ] PositiveMellinQuarterEnergy :=
  ⟨positiveMellinQuarterEnergyTranslationEquiv h,
    positiveMellinQuarterEnergyTranslation_norm h⟩

def positiveMellinQuarterEnergyReflectionEquiv :
    PositiveMellinQuarterEnergy ≃ₗ[ℂ] PositiveMellinQuarterEnergy :=
  { positiveMellinQuarterEnergyReflection with
    invFun := positiveMellinQuarterEnergyReflection
    left_inv := positiveMellinQuarterEnergyReflection_involutive
    right_inv := positiveMellinQuarterEnergyReflection_involutive }

def positiveMellinQuarterEnergyReflectionIsometry :
    PositiveMellinQuarterEnergy ≃ₗᵢ[ℂ] PositiveMellinQuarterEnergy :=
  ⟨positiveMellinQuarterEnergyReflectionEquiv,
    positiveMellinQuarterEnergyReflection_norm⟩

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
