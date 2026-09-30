import H0mework.Versions.Y.Arithmetic.MellinConductor.Prefix.Source.LivingLawCanonicalCoPoissonHalfPositionConductorPrefix

/-!
# Closed-graph half-position triangular action

The actual energy translation lifts to the closed half-position graph by the
triangular law

`(u, Xu) ↦ (T_h u, T_h Xu - (h / 2) T_h u)`.

The correction is forced by the already generated half-position commutator.
Consequently the maximal graph is stable without assuming a second position
moment, and every source dilation factors through this same bounded graph
action.
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

open HalfPositionDomain
open SourcePrefix

noncomputable section

def halfPositionEnergyTranslationCLM (shift : ℝ) :
    PositiveMellinQuarterEnergy →L[ℂ] PositiveMellinQuarterEnergy :=
  (positiveMellinQuarterEnergyTranslationIsometry shift
    ).toLinearIsometry.toContinuousLinearMap

/-- The canonical triangular correction whose shear is dictated by the
half-position translation commutator. -/
def halfPositionRawTriangularAction (shift : ℝ) :
    (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) →L[ℂ]
      (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) :=
  ((halfPositionEnergyTranslationCLM shift).comp
      (ContinuousLinearMap.fst ℂ PositiveMellinQuarterEnergy
        PositiveMellinQuarterEnergy)).prod
    (((halfPositionEnergyTranslationCLM shift).comp
        (ContinuousLinearMap.snd ℂ PositiveMellinQuarterEnergy
          PositiveMellinQuarterEnergy)) -
      (((shift / 2 : ℝ) : ℂ) •
        ((halfPositionEnergyTranslationCLM shift).comp
          (ContinuousLinearMap.fst ℂ PositiveMellinQuarterEnergy
            PositiveMellinQuarterEnergy))))

/-- The bounded triangular action transported to the actual `WithLp` graph
carrier. -/
def halfPositionGraphTriangularAction (shift : ℝ) :
    HalfPositionGraphCarrier →L[ℂ] HalfPositionGraphCarrier :=
  halfPositionProductHilbertEquiv.toContinuousLinearMap.comp
    ((halfPositionRawTriangularAction shift).comp halfPositionGraphToProduct)

def halfPositionGraphSnd :
    HalfPositionGraphCarrier →L[ℂ] PositiveMellinQuarterEnergy :=
  (ContinuousLinearMap.snd ℂ
      PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy).comp
    halfPositionGraphToProduct

def halfPositionGraphForcedTrace (shift : ℝ) :
    HalfPositionGraphCarrier →L[ℂ] PositiveMellinQuarterEnergy :=
  ((shift / 2 : ℝ) : ℂ) •
    ((halfPositionEnergyTranslationCLM shift).comp halfPositionGraphFst)

@[simp] theorem halfPositionGraphForcedTrace_apply
    (shift : ℝ) (value : HalfPositionGraphCarrier) :
    halfPositionGraphForcedTrace shift value =
      ((shift / 2 : ℝ) : ℂ) •
        positiveMellinQuarterEnergyTranslation shift
          (halfPositionGraphFst value) :=
  rfl

@[simp] theorem halfPositionRawTriangularAction_apply
    (shift : ℝ)
    (value : PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) :
    halfPositionRawTriangularAction shift value =
      (positiveMellinQuarterEnergyTranslation shift value.1,
        positiveMellinQuarterEnergyTranslation shift value.2 -
          ((shift / 2 : ℝ) : ℂ) •
            positiveMellinQuarterEnergyTranslation shift value.1) := by
  rfl

/-- The triangular action preserves the full closed graph, not only the
finite source image. -/
theorem halfPositionRawTriangularAction_preserves_operatorGraph
    (shift : ℝ)
    (value : PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy)
    (membership : value ∈ HalfPositionOperator.graph) :
    halfPositionRawTriangularAction shift value ∈
      HalfPositionOperator.graph := by
  rw [LinearPMap.mem_graph_iff] at membership ⊢
  rcases membership with ⟨domainValue, inputEq, outputEq⟩
  refine ⟨halfPositionDomainTranslation shift domainValue, ?_, ?_⟩
  · change positiveMellinQuarterEnergyTranslation shift domainValue.1 =
      positiveMellinQuarterEnergyTranslation shift value.1
    rw [inputEq]
  · rw [halfPositionRawTriangularAction_apply]
    change HalfPositionOperator
        (halfPositionDomainTranslation shift domainValue) =
      positiveMellinQuarterEnergyTranslation shift value.2 -
        ((shift / 2 : ℝ) : ℂ) •
          positiveMellinQuarterEnergyTranslation shift value.1
    rw [halfPositionOperator_translation_eq]
    unfold translatedHalfPositionOutput
    rw [outputEq, inputEq]

theorem halfPositionGraphToProduct_triangularAction
    (shift : ℝ) (value : HalfPositionGraphCarrier) :
    halfPositionGraphToProduct
        (halfPositionGraphTriangularAction shift value) =
      halfPositionRawTriangularAction shift
        (halfPositionGraphToProduct value) := by
  change (WithLp.prodContinuousLinearEquiv 2 ℂ
      PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy)
      ((WithLp.prodContinuousLinearEquiv 2 ℂ
        PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy).symm
        (halfPositionRawTriangularAction shift
          (halfPositionGraphToProduct value))) = _
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ
    PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy
    ).apply_symm_apply _

@[simp] theorem halfPositionGraphFst_triangularAction
    (shift : ℝ) (value : HalfPositionGraphCarrier) :
    halfPositionGraphFst (halfPositionGraphTriangularAction shift value) =
      positiveMellinQuarterEnergyTranslation shift
        (halfPositionGraphFst value) := by
  change (halfPositionGraphToProduct
      (halfPositionGraphTriangularAction shift value)).1 = _
  rw [halfPositionGraphToProduct_triangularAction,
    halfPositionRawTriangularAction_apply]
  rfl

@[simp] theorem halfPositionGraphSnd_triangularAction
    (shift : ℝ) (value : HalfPositionGraphCarrier) :
    halfPositionGraphSnd (halfPositionGraphTriangularAction shift value) =
      positiveMellinQuarterEnergyTranslation shift
          (halfPositionGraphSnd value) -
        ((shift / 2 : ℝ) : ℂ) •
          positiveMellinQuarterEnergyTranslation shift
            (halfPositionGraphFst value) := by
  change (halfPositionGraphToProduct
      (halfPositionGraphTriangularAction shift value)).2 = _
  rw [halfPositionGraphToProduct_triangularAction,
    halfPositionRawTriangularAction_apply]
  rfl

/-- The graph incidence is not an arbitrary residual: the existing action
forces it to be exactly the half-position trace of the same translated
state. -/
theorem halfPositionGraphTriangularAction_forcedTrace
    (shift : ℝ) (value : HalfPositionGraphCarrier) :
    positiveMellinQuarterEnergyTranslation shift
          (halfPositionGraphSnd value) -
        halfPositionGraphSnd
          (halfPositionGraphTriangularAction shift value) =
      ((shift / 2 : ℝ) : ℂ) •
        positiveMellinQuarterEnergyTranslation shift
          (halfPositionGraphFst value) := by
  rw [halfPositionGraphSnd_triangularAction]
  abel

theorem halfPositionGraphDiagonalSnd_decomposition
    (shift : ℝ) (value : HalfPositionGraphCarrier) :
    positiveMellinQuarterEnergyTranslation shift
        (halfPositionGraphSnd value) =
      halfPositionGraphSnd
          (halfPositionGraphTriangularAction shift value) +
        halfPositionGraphForcedTrace shift value := by
  rw [halfPositionGraphSnd_triangularAction,
    halfPositionGraphForcedTrace_apply]
  abel

theorem halfPositionDomainFeature_sourceDilation
    (z : ℂ) (scale : ℝ) (positive : 0 < scale)
    (value : quarterMellinHalfPositionSourceDomain z) :
    halfPositionDomainFeature z
        (halfPositionSourceDilation z scale positive value) =
      halfPositionDomainTranslation (Real.log scale)
        (halfPositionDomainFeature z value) := by
  apply Subtype.ext
  have covariance := LinearMap.congr_fun
    (quarterDilationFeature_covariance z scale positive) value.1
  exact covariance.symm

/-- Source dilation and the bounded closed-graph action are two dependent
faces of the same generated operation. -/
theorem halfPositionGraphTriangularAction_sourceDilation
    (z : ℂ) (scale : ℝ) (positive : 0 < scale)
    (value : quarterMellinHalfPositionSourceDomain z) :
    halfPositionGraphTriangularAction (Real.log scale)
        (halfPositionGraphFeature z value) =
      halfPositionGraphFeature z
        (halfPositionSourceDilation z scale positive value) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ
    PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy).injective
  change halfPositionGraphToProduct
      (halfPositionGraphTriangularAction (Real.log scale)
        (halfPositionGraphFeature z value)) =
    halfPositionGraphToProduct
      (halfPositionGraphFeature z
        (halfPositionSourceDilation z scale positive value))
  rw [halfPositionGraphToProduct_triangularAction,
    halfPositionGraphToProduct_feature,
    halfPositionGraphToProduct_feature,
    halfPositionRawTriangularAction_apply]
  apply Prod.ext
  · exact (LinearMap.congr_fun
      (quarterDilationFeature_covariance z scale positive) value.1)
  · change
      positiveMellinQuarterEnergyTranslation (Real.log scale)
          (HalfPositionOperator (halfPositionDomainFeature z value)) -
        (((Real.log scale / 2 : ℝ) : ℂ)) •
          positiveMellinQuarterEnergyTranslation (Real.log scale)
            (quarterMellinL2Feature z value.1) =
      HalfPositionOperator
        (halfPositionDomainFeature z
          (halfPositionSourceDilation z scale positive value))
    rw [halfPositionDomainFeature_sourceDilation]
    exact halfPositionOperator_translation_eq
      (Real.log scale) (halfPositionDomainFeature z value) |>.symm

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
