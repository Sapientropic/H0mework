import H0mework.Physics.DiracEvolution.SafeSpatialL2TestCarrier
import H0mework.Physics.Cauchy.CanonicalCauchyCoordinateProjection
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Countable dense Cauchy-safe matter tests

Every fixed spatial box has a source-owned countable family of smooth compact
matter tests whose algebraic span remains dense in the physical `L²` carrier.
This is the exact countable mouth consumed by the common Galerkin subsequence.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCauchySafeMatterCountableDenseTestCarrier

open Set
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false

variable (a b : DiracMatterSpatialCoordinates)

local instance two_ne_top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local instance matterCoordinateSeparableSpace :
    TopologicalSpace.SeparableSpace MatterCoordinateCarrier :=
  TopologicalSpace.SecondCountableTopology.to_separableSpace

local instance l2SecondCountableTopology :
    SecondCountableTopology (CauchySafeMatterSpatialL2 a b) :=
  MeasureTheory.Lp.SecondCountableTopology

private abbrev CauchySafeMatterSmoothCompactTestL2Range :=
  Set.range (cauchySafeMatterSmoothCompactTestToL2 a b)

/-- A countable family chosen inside the exact `L²` image of the smooth
compact test carrier. -/
def cauchySafeMatterCountableDenseTest
    (index : ℕ) : CauchySafeMatterSmoothCompactTest :=
  Classical.choose
    ((TopologicalSpace.denseSeq
      (CauchySafeMatterSmoothCompactTestL2Range a b) index).property)

theorem cauchySafeMatterCountableDenseTest_toL2
    (index : ℕ) :
    cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCountableDenseTest a b index) =
      (TopologicalSpace.denseSeq
        (CauchySafeMatterSmoothCompactTestL2Range a b) index).1 :=
  Classical.choose_spec
    ((TopologicalSpace.denseSeq
      (CauchySafeMatterSmoothCompactTestL2Range a b) index).property)

/-- The generated countable family itself is dense after `L²` embedding. -/
theorem cauchySafeMatterCountableDenseTest_denseRange :
    DenseRange (fun index =>
      cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCountableDenseTest a b index)) := by
  have rangeDense :
      Dense (CauchySafeMatterSmoothCompactTestL2Range a b) :=
    cauchySafeMatterSmoothCompactTestToL2_denseRange a b
  have denseComposition := rangeDense.denseRange_val.comp
    (TopologicalSpace.denseRange_denseSeq
      (CauchySafeMatterSmoothCompactTestL2Range a b))
    continuous_subtype_val
  have functionEq :
      (fun index => cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCountableDenseTest a b index)) =
      ((fun point : CauchySafeMatterSmoothCompactTestL2Range a b =>
          (point : CauchySafeMatterSpatialL2 a b)) ∘
        TopologicalSpace.denseSeq
          (CauchySafeMatterSmoothCompactTestL2Range a b)) := by
    funext index
    exact cauchySafeMatterCountableDenseTest_toL2 a b index
  rw [functionEq]
  exact denseComposition

abbrev CauchySafeMatterCountableTestSpan :=
  Submodule.span ℝ (Set.range (cauchySafeMatterCountableDenseTest a b))

/-- The algebraic span of the countable generated tests embeds linearly into
the physical spatial `L²` carrier. -/
def cauchySafeMatterCountableTestSpanToL2 :
    CauchySafeMatterCountableTestSpan a b →ₗ[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  (cauchySafeMatterSmoothCompactTestToL2 a b).comp
    (Submodule.subtype (CauchySafeMatterCountableTestSpan a b))

/-- Passing from the countable family to its algebraic span preserves the
dense `L²` range needed by canonical actualization. -/
theorem cauchySafeMatterCountableTestSpanToL2_denseRange :
    DenseRange (cauchySafeMatterCountableTestSpanToL2 a b) := by
  apply (cauchySafeMatterCountableDenseTest_denseRange a b).mono
  rintro _ ⟨index, rfl⟩
  refine ⟨⟨cauchySafeMatterCountableDenseTest a b index, ?_⟩, rfl⟩
  exact Submodule.subset_span (Set.mem_range_self index)

/-- Canonical spacetime extension of one generated spatial test.  It reads
only the fixed spatial projection and introduces no temporal test data. -/
def cauchySafeMatterCountableDenseSpacetimeTest
    (test : ℕ) : BasePoint → MatterCoordinateCarrier :=
  fun point ↦
    (cauchySafeMatterCountableDenseTest a b test).1
      ((EuclideanSpace.equiv (Fin 3) ℝ) (canonicalSpatialProjection point))

theorem cauchySafeMatterCountableDenseSpacetimeTest_contDiff_one : ∀ test,
    ContDiff ℝ 1
      (cauchySafeMatterCountableDenseSpacetimeTest a b test) := by
  intro test
  exact ((cauchySafeMatterCountableDenseTest a b test).property.2.of_le
      (by norm_num)).comp
    ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearEquiv.contDiff.comp
      canonicalSpatialProjection.contDiff)

@[simp] theorem cauchySafeMatterCountableDenseSpacetimeTest_slice
    (test : ℕ)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    cauchySafeMatterCountableDenseSpacetimeTest a b test
        (diracMatterSpacetimeCoordinatePoint time space) =
      (cauchySafeMatterCountableDenseTest a b test).1 space := by
  simp only [cauchySafeMatterCountableDenseSpacetimeTest,
    diracMatterSpacetimeCoordinatePoint, canonicalSpatialProjection_slice]
  exact congrArg
    (cauchySafeMatterCountableDenseTest a b test).1
    ((EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply space)

end

end
  SaturationMonoid.PhysicsCore.StageNineCauchySafeMatterCountableDenseTestCarrier
