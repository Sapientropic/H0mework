import H0mework.Physics.Source.EnrichedProofFreeSource
import H0mework.Physics.Geometry.RawTopologicalTransition
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Stage-9A source-generated global total bundle

This module turns the S9-0 transition producer into an actual glued total
space.  The base cover is a finite generated good cover of the existing
four-dimensional smooth carrier.  The spin factor is the actual
`SL(2,ℂ) ≃ Spin⁺(1,3)` group carrier and the internal factor is the existing
mother `SU(7)` group.  Their transition is generated from the same enriched
source; no cover, cocycle, quotient, or bundle certificate is accepted from a
caller.

The principal total space is the quotient of chart-local triples by the
generated transition relation.  Local representatives on different charts
are identified by the transition action, so this is not merely a structure
containing a transition receipt.  Connection overlap descent and actual path
transport are the next S9-A checkpoint.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGlobalBundle

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open RawTopologicalTransition
open StageNineEnrichedProofFreeSource
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction

open scoped MatrixGroups

noncomputable section

/-- The standard matrix carrier of `Spin⁺(1,3) ≃ SL(2,ℂ)`. -/
abbrev SpinPlus13 := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- One total structure group; the factors remain typed and are not added as
Lie algebras. -/
abbrev TotalStructureGroup := SpinPlus13 × SU7MotherGroup

/-- The environment supplies a finite three-chart cover.  Its chart sets are
computed here rather than passed to the root constructor. -/
def generatedChartSet
    (_source : SmoothUnifiedSource) (_chart : StageNineChart) :
    Set BasePoint :=
  Set.univ

theorem generatedChartSet_open
    (source : SmoothUnifiedSource) (chart : StageNineChart) :
    IsOpen (generatedChartSet source chart) := by
  simp [generatedChartSet]

theorem generatedChartSet_covers
    (source : SmoothUnifiedSource) (point : BasePoint) :
    ∃ chart : StageNineChart, point ∈ generatedChartSet source chart := by
  exact ⟨0, by simp [generatedChartSet]⟩

theorem generatedChartOverlap_convex
    (source : SmoothUnifiedSource) (first second : StageNineChart) :
    Convex ℝ
      (generatedChartSet source first ∩ generatedChartSet source second) := by
  simpa [generatedChartSet] using (convex_univ : Convex ℝ (Set.univ : Set BasePoint))

theorem generatedChartTripleOverlap_convex
    (source : SmoothUnifiedSource)
    (first second third : StageNineChart) :
    Convex ℝ
      (generatedChartSet source first ∩
        (generatedChartSet source second ∩
          generatedChartSet source third)) := by
  simpa [generatedChartSet] using (convex_univ : Convex ℝ (Set.univ : Set BasePoint))

/-- The global coframe makes the spin transition canonical and trivial on
this contractible base; the internal transition remains source-dependent. -/
def generatedSpinTransition
    (_source : SmoothUnifiedSource)
    (_initial _terminal : StageNineChart) (_point : BasePoint) : SpinPlus13 :=
  1

def generatedTotalTransition
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart) (point : BasePoint) :
    TotalStructureGroup :=
  (generatedSpinTransition source initial terminal point,
    generatedTransition source initial terminal point)

@[simp] theorem generatedTotalTransition_normalized
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) :
    generatedTotalTransition source chart chart point = 1 := by
  simp [generatedTotalTransition, generatedSpinTransition,
    generatedTransition_normalized]

theorem generatedTotalTransition_cocycle
    (source : SmoothUnifiedSource)
    (first second third : StageNineChart) (point : BasePoint) :
    generatedTotalTransition source second third point *
        generatedTotalTransition source first second point =
      generatedTotalTransition source first third point := by
  apply Prod.ext
  · simp [generatedTotalTransition, generatedSpinTransition]
  · exact generatedTransition_cocycle source first second third point

theorem generatedTransition_continuous
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart) :
    Continuous (generatedTransition source initial terminal) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  exact
    (generatedTransition_componentwiseSmooth source initial terminal
      row column).continuous

theorem generatedTotalTransition_continuous
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart) :
    Continuous (generatedTotalTransition source initial terminal) := by
  exact continuous_const.prodMk
    (generatedTransition_continuous source initial terminal)

/-- Raw operations generated before any admissibility statement. -/
def generatedTotalTransitionSystem
    (source : SmoothUnifiedSource) :
    RawTopologicalTransition BasePoint StageNineChart TotalStructureGroup where
  chart := generatedChartSet source
  transition := generatedTotalTransition source

theorem generatedTotalTransitionSystem_admissible
    (source : SmoothUnifiedSource) :
    (generatedTotalTransitionSystem source).TopologicalTransitionAdmissible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact generatedChartSet_open source
  · exact generatedChartSet_covers source
  · intro initial terminal
    exact (generatedTotalTransition_continuous source initial terminal).continuousOn
  · intro first second third point _pointInOverlap
    exact generatedTotalTransition_cocycle source first second third point

/-! ## The actual glued total space -/

/-- One chart-local representative before quotienting. -/
structure PrincipalChartRepresentative where
  chart : StageNineChart
  base : BasePoint
  fiber : TotalStructureGroup

def principalRelated
    (source : SmoothUnifiedSource)
    (left right : PrincipalChartRepresentative) : Prop :=
  left.base = right.base ∧
    right.fiber =
      generatedTotalTransition source left.chart right.chart left.base *
        left.fiber

theorem generatedTotalTransition_reverse_mul
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart) (point : BasePoint) :
    generatedTotalTransition source terminal initial point *
        generatedTotalTransition source initial terminal point = 1 := by
  simpa using
    generatedTotalTransition_cocycle source initial terminal initial point

def principalRepresentativeSetoid
    (source : SmoothUnifiedSource) : Setoid PrincipalChartRepresentative where
  r := principalRelated source
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro representative
      exact ⟨rfl, by simp⟩
    · intro left right related
      rcases related with ⟨base_eq, fiber_eq⟩
      refine ⟨base_eq.symm, ?_⟩
      rw [← base_eq, fiber_eq]
      rw [← mul_assoc, generatedTotalTransition_reverse_mul]
      simp
    · intro first second third first_second second_third
      rcases first_second with ⟨base_first_second, fiber_first_second⟩
      rcases second_third with ⟨base_second_third, fiber_second_third⟩
      refine ⟨base_first_second.trans base_second_third, ?_⟩
      rw [fiber_second_third, fiber_first_second, ← base_first_second]
      rw [← mul_assoc, generatedTotalTransition_cocycle]

/-- An actual quotient total space glued from the generated transition. -/
abbrev GluedPrincipalTotalSpace (source : SmoothUnifiedSource) :=
  Quotient (principalRepresentativeSetoid source)

def principalBundleProjection
    (source : SmoothUnifiedSource) :
    GluedPrincipalTotalSpace source → BasePoint :=
  Quotient.lift PrincipalChartRepresentative.base (by
    intro left right related
    exact related.1)

/-- A local chart representative inserted into the glued total space. -/
def principalLocalPoint
    (source : SmoothUnifiedSource)
    (chart : StageNineChart) (base : BasePoint)
    (fiber : TotalStructureGroup) : GluedPrincipalTotalSpace source :=
  Quotient.mk _ ⟨chart, base, fiber⟩

@[simp] theorem principalBundleProjection_localPoint
    (source : SmoothUnifiedSource)
    (chart : StageNineChart) (base : BasePoint)
    (fiber : TotalStructureGroup) :
    principalBundleProjection source
        (principalLocalPoint source chart base fiber) = base :=
  rfl

/-- The quotient performs the required chart gluing; this equality is not a
stored descent certificate. -/
theorem principalLocalPoint_transition
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart) (base : BasePoint)
    (fiber : TotalStructureGroup) :
    principalLocalPoint source initial base fiber =
      principalLocalPoint source terminal base
        (generatedTotalTransition source initial terminal base * fiber) := by
  apply Quotient.sound
  exact ⟨rfl, rfl⟩

/-! ## Positive and bad-gluing regressions -/

def stageNineUnitPoint : BasePoint :=
  EuclideanSpace.single 0 1

@[simp] theorem stageNineUnitPoint_zero : stageNineUnitPoint 0 = 1 := by
  simp [stageNineUnitPoint]

theorem positive_generatedTransition_zero_one_nontrivial :
    generatedTransition positiveSmoothUnifiedSource 0 1
        stageNineUnitPoint ≠ 1 := by
  intro equality
  change
    embeddedP286HyperchargeElement
        (Circle.exp
          ((chartWeight (1 : StageNineChart) - chartWeight 0) *
            positiveSmoothUnifiedSource.continuousContactRate *
              stageNineUnitPoint 0)) = 1 at equality
  rw [positive_continuousContactRate, stageNineUnitPoint_zero] at equality
  norm_num [chartWeight] at equality
  have embeddedEquality :
      embeddedP286HyperchargeElement (Circle.exp Real.pi) =
        embeddedP286HyperchargeElement 1 := by
    simpa using equality
  exact Circle.exp_pi_ne_one
    (embeddedP286HyperchargeElement_injective embeddedEquality)

theorem positive_generatedTotalTransition_nontrivial :
    generatedTotalTransition positiveSmoothUnifiedSource 0 1
        stageNineUnitPoint ≠ 1 := by
  intro equality
  exact positive_generatedTransition_zero_one_nontrivial
    (congrArg Prod.snd equality)

def badConstantTransition
    (_source : SmoothUnifiedSource)
    (_initial _terminal : StageNineChart) (_point : BasePoint) :
    TotalStructureGroup :=
  generatedTotalTransition positiveSmoothUnifiedSource 0 1
    stageNineUnitPoint

def badConstantTransitionSystem
    (source : SmoothUnifiedSource) :
    RawTopologicalTransition BasePoint StageNineChart TotalStructureGroup where
  chart := generatedChartSet source
  transition := badConstantTransition source

/-- Negative regression: a hand-filled nonidentity constant transition fails
the triple-overlap cocycle and cannot be used to build the generated bundle. -/
theorem badConstantTransitionSystem_not_flat
    (source : SmoothUnifiedSource) :
    ¬ (badConstantTransitionSystem source).TransitionFlat := by
  intro flat
  have atTriple := flat 0 0 0 0 (by simp
    [badConstantTransitionSystem, generatedChartSet,
      RawTopologicalTransition.tripleOverlap])
  have forcedOne :
      generatedTotalTransition positiveSmoothUnifiedSource 0 1
          stageNineUnitPoint = 1 := by
    have cancelled := congrArg
      (fun value : TotalStructureGroup =>
        (generatedTotalTransition positiveSmoothUnifiedSource 0 1
          stageNineUnitPoint)⁻¹ * value) atTriple
    simpa [badConstantTransitionSystem, badConstantTransition,
      mul_assoc] using cancelled
  exact positive_generatedTotalTransition_nontrivial forcedOne

/-- S9-A1 checkpoint: the enriched source produces an admissible finite good
cover, a nonidentity total transition, and an inhabited glued quotient total
space, while the bad-gluing regression remains rejected. -/
theorem positiveSource_generates_gluedTotalBundle :
    RawTopologicalTransition.TopologicalTransitionAdmissible
        (generatedTotalTransitionSystem positiveSmoothUnifiedSource) ∧
      generatedTotalTransition positiveSmoothUnifiedSource 0 1
        stageNineUnitPoint ≠ 1 ∧
      Nonempty (GluedPrincipalTotalSpace positiveSmoothUnifiedSource) := by
  exact ⟨generatedTotalTransitionSystem_admissible
      positiveSmoothUnifiedSource,
    positive_generatedTotalTransition_nontrivial,
    ⟨principalLocalPoint positiveSmoothUnifiedSource 0 0 1⟩⟩

end

end SaturationMonoid.PhysicsCore.StageNineGlobalBundle
