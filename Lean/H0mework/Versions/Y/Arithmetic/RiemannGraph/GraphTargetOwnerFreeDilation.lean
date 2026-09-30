import H0mework.Versions.Y.Arithmetic.MuntzAction.CoPoissonMuntzGraphCokernelDilationNaturality

/-!
# Owner-free dilation on the common quarter-Mellin graph target

The graph target carries the actual half-density translation on its energy
coordinate and the identity on its measurement coordinate.  This action is
defined before any zero, Mellin character, or separator is supplied.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram

open SourceGeneratedFunctionalGraphPerfectification

noncomputable section

universe h

variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Product action `U × id` on the common Hilbert graph target. -/
def graphTargetProductIsometry
    (energyAction : H ≃ₗᵢ[ℂ] H) :
    GraphTarget H ≃ₗᵢ[ℂ] GraphTarget H :=
  LinearIsometryEquiv.withLpProdCongr (p := 2) energyAction
    (LinearIsometryEquiv.refl ℂ ℂ)

@[simp] theorem graphTargetProductIsometry_fst
    (energyAction : H ≃ₗᵢ[ℂ] H) (value : GraphTarget H) :
    (graphTargetProductIsometry energyAction value).fst =
      energyAction value.fst :=
  rfl

@[simp] theorem graphTargetProductIsometry_snd
    (energyAction : H ≃ₗᵢ[ℂ] H) (value : GraphTarget H) :
    (graphTargetProductIsometry energyAction value).snd = value.snd :=
  rfl

@[simp] theorem graphTargetProductIsometry_one :
    graphTargetProductIsometry
        (LinearIsometryEquiv.refl ℂ H) = 1 := by
  apply LinearIsometryEquiv.ext
  intro value
  rfl

@[simp] theorem graphTargetProductIsometry_mul
    (first second : H ≃ₗᵢ[ℂ] H) :
    graphTargetProductIsometry (first * second) =
      graphTargetProductIsometry first * graphTargetProductIsometry second := by
  apply LinearIsometryEquiv.ext
  intro value
  rfl

/-- Actual owner-free half-density translation on the graph target. -/
def positiveMellinQuarterGraphTargetIsometry (shift : ℝ) :
    GraphTarget PositiveMellinQuarterEnergy ≃ₗᵢ[ℂ]
      GraphTarget PositiveMellinQuarterEnergy :=
  graphTargetProductIsometry
    (positiveMellinQuarterEnergyTranslationIsometry shift)

@[simp] theorem positiveMellinQuarterGraphTargetIsometry_fst
    (shift : ℝ) (value : GraphTarget PositiveMellinQuarterEnergy) :
    (positiveMellinQuarterGraphTargetIsometry shift value).fst =
      positiveMellinQuarterEnergyTranslationIsometry shift value.fst :=
  rfl

@[simp] theorem positiveMellinQuarterGraphTargetIsometry_snd
    (shift : ℝ) (value : GraphTarget PositiveMellinQuarterEnergy) :
    (positiveMellinQuarterGraphTargetIsometry shift value).snd = value.snd :=
  rfl

/-- Genuine positive-scale group action with no zero-dependent field. -/
def positiveMellinQuarterGraphTargetPositiveDilationAction :
    Units NNReal →*
      (GraphTarget PositiveMellinQuarterEnergy ≃ₗᵢ[ℂ]
        GraphTarget PositiveMellinQuarterEnergy) where
  toFun scale := positiveMellinQuarterGraphTargetIsometry
    (Real.log (positiveUnitValue scale))
  map_one' := by
    have energyIdentity :
        positiveMellinQuarterEnergyTranslationIsometry 0 =
          LinearIsometryEquiv.refl ℂ PositiveMellinQuarterEnergy := by
      apply LinearIsometryEquiv.ext
      intro value
      exact positiveMellinQuarterEnergyTranslation_zero value
    rw [positiveUnitValue_one, Real.log_one]
    change graphTargetProductIsometry
        (positiveMellinQuarterEnergyTranslationIsometry 0) = 1
    rw [energyIdentity, graphTargetProductIsometry_one]
  map_mul' first second := by
    have energyComposition :
        positiveMellinQuarterEnergyTranslationIsometry
            (Real.log (positiveUnitValue (first * second))) =
          positiveMellinQuarterEnergyTranslationIsometry
              (Real.log (positiveUnitValue first)) *
            positiveMellinQuarterEnergyTranslationIsometry
              (Real.log (positiveUnitValue second)) := by
      apply LinearIsometryEquiv.ext
      intro value
      change positiveMellinQuarterEnergyTranslation
          (Real.log (positiveUnitValue (first * second))) value =
        positiveMellinQuarterEnergyTranslation
          (Real.log (positiveUnitValue first))
          (positiveMellinQuarterEnergyTranslation
            (Real.log (positiveUnitValue second)) value)
      rw [positiveUnitValue_mul,
        Real.log_mul (positiveUnitValue_pos first).ne'
          (positiveUnitValue_pos second).ne']
      have composition := LinearMap.congr_fun
        (positiveMellinQuarterEnergyTranslation_comp
          (Real.log (positiveUnitValue first))
          (Real.log (positiveUnitValue second))) value
      simpa [add_comm] using composition.symm
    change graphTargetProductIsometry
        (positiveMellinQuarterEnergyTranslationIsometry
          (Real.log (positiveUnitValue (first * second)))) =
      graphTargetProductIsometry
          (positiveMellinQuarterEnergyTranslationIsometry
            (Real.log (positiveUnitValue first))) *
        graphTargetProductIsometry
          (positiveMellinQuarterEnergyTranslationIsometry
            (Real.log (positiveUnitValue second)))
    rw [energyComposition, graphTargetProductIsometry_mul]

@[simp] theorem positiveMellinQuarterGraphTargetPositiveDilationAction_fst
    (scale : Units NNReal)
    (value : GraphTarget PositiveMellinQuarterEnergy) :
    (positiveMellinQuarterGraphTargetPositiveDilationAction scale value).fst =
      positiveMellinQuarterEnergyTranslationIsometry
        (Real.log (positiveUnitValue scale)) value.fst :=
  rfl

@[simp] theorem positiveMellinQuarterGraphTargetPositiveDilationAction_snd
    (scale : Units NNReal)
    (value : GraphTarget PositiveMellinQuarterEnergy) :
    (positiveMellinQuarterGraphTargetPositiveDilationAction scale value).snd =
      value.snd :=
  rfl

end


end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
