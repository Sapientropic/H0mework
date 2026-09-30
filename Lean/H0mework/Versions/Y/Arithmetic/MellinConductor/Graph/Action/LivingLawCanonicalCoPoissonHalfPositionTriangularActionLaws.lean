import H0mework.Versions.Y.Arithmetic.MellinConductor.Graph.Action.LivingLawCanonicalCoPoissonHalfPositionTriangularAction

/-!
# Action laws for the half-position graph translation

The triangular graph maps form the actual additive translation action.  The
laws are proved from the underlying energy translations and their forced
commutator correction; no domain-specific eigenvalue or stationarity premise
is accepted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace MuntzConductor
namespace HalfPositionSource
namespace GraphAction

noncomputable section

theorem halfPositionRawTriangularAction_zero :
    halfPositionRawTriangularAction 0 =
      ContinuousLinearMap.id ℂ
        (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) := by
  apply ContinuousLinearMap.ext
  intro value
  rw [halfPositionRawTriangularAction_apply]
  simp only [zero_div, Complex.ofReal_zero, zero_smul, sub_zero,
    ContinuousLinearMap.id_apply]
  rw [positiveMellinQuarterEnergyTranslation_zero,
    positiveMellinQuarterEnergyTranslation_zero]

theorem halfPositionRawTriangularAction_comp
    (first second : ℝ) :
    (halfPositionRawTriangularAction first).comp
        (halfPositionRawTriangularAction second) =
      halfPositionRawTriangularAction (second + first) := by
  apply ContinuousLinearMap.ext
  intro value
  simp only [ContinuousLinearMap.comp_apply,
    halfPositionRawTriangularAction_apply]
  apply Prod.ext
  · exact LinearMap.congr_fun
      (positiveMellinQuarterEnergyTranslation_comp first second) value.1
  · have firstComp := LinearMap.congr_fun
      (positiveMellinQuarterEnergyTranslation_comp first second) value.1
    have secondComp := LinearMap.congr_fun
      (positiveMellinQuarterEnergyTranslation_comp first second) value.2
    have firstComp' :
        positiveMellinQuarterEnergyTranslation first
            (positiveMellinQuarterEnergyTranslation second value.1) =
          positiveMellinQuarterEnergyTranslation (second + first) value.1 := by
      simpa only [LinearMap.comp_apply] using firstComp
    have secondComp' :
        positiveMellinQuarterEnergyTranslation first
            (positiveMellinQuarterEnergyTranslation second value.2) =
          positiveMellinQuarterEnergyTranslation (second + first) value.2 := by
      simpa only [LinearMap.comp_apply] using secondComp
    simp only [map_sub, map_smul]
    rw [firstComp', secondComp']
    push_cast
    module

theorem halfPositionGraphTriangularAction_zero :
    halfPositionGraphTriangularAction 0 =
      ContinuousLinearMap.id ℂ HalfPositionGraphCarrier := by
  apply ContinuousLinearMap.ext
  intro value
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ
    PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy).injective
  change halfPositionGraphToProduct
      (halfPositionGraphTriangularAction 0 value) =
    halfPositionGraphToProduct value
  rw [halfPositionGraphToProduct_triangularAction,
    halfPositionRawTriangularAction_zero,
    ContinuousLinearMap.id_apply]

theorem halfPositionGraphTriangularAction_comp
    (first second : ℝ) :
    (halfPositionGraphTriangularAction first).comp
        (halfPositionGraphTriangularAction second) =
      halfPositionGraphTriangularAction (second + first) := by
  apply ContinuousLinearMap.ext
  intro value
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ
    PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy).injective
  change halfPositionGraphToProduct
      (halfPositionGraphTriangularAction first
        (halfPositionGraphTriangularAction second value)) =
    halfPositionGraphToProduct
      (halfPositionGraphTriangularAction (second + first) value)
  rw [halfPositionGraphToProduct_triangularAction,
    halfPositionGraphToProduct_triangularAction,
    halfPositionGraphToProduct_triangularAction]
  exact congrArg
    (fun action :
      (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) →L[ℂ]
        (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) =>
      action (halfPositionGraphToProduct value))
    (halfPositionRawTriangularAction_comp first second)

/-- Every graph action has the opposite-shift bounded inverse. -/
def halfPositionGraphTriangularEquiv (shift : ℝ) :
    HalfPositionGraphCarrier ≃L[ℂ] HalfPositionGraphCarrier :=
  ContinuousLinearEquiv.mk
    { toLinearMap := (halfPositionGraphTriangularAction shift).toLinearMap
      invFun := halfPositionGraphTriangularAction (-shift)
      left_inv := by
        intro value
        change halfPositionGraphTriangularAction (-shift)
            (halfPositionGraphTriangularAction shift value) = value
        have composition := congrArg
          (fun action : HalfPositionGraphCarrier →L[ℂ]
              HalfPositionGraphCarrier => action value)
          (halfPositionGraphTriangularAction_comp (-shift) shift)
        simpa only [add_neg_cancel, halfPositionGraphTriangularAction_zero,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
          using composition
      right_inv := by
        intro value
        change halfPositionGraphTriangularAction shift
            (halfPositionGraphTriangularAction (-shift) value) = value
        have composition := congrArg
          (fun action : HalfPositionGraphCarrier →L[ℂ]
              HalfPositionGraphCarrier => action value)
          (halfPositionGraphTriangularAction_comp shift (-shift))
        simpa only [neg_add_cancel, halfPositionGraphTriangularAction_zero,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
          using composition }
    (halfPositionGraphTriangularAction shift).continuous
    (halfPositionGraphTriangularAction (-shift)).continuous

@[simp] theorem halfPositionGraphTriangularEquiv_apply
    (shift : ℝ) (value : HalfPositionGraphCarrier) :
    halfPositionGraphTriangularEquiv shift value =
      halfPositionGraphTriangularAction shift value :=
  rfl

end
end GraphAction
end HalfPositionSource
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
