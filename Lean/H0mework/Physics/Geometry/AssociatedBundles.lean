import H0mework.Physics.Gauge.GlobalConnection
import H0mework.Physics.Matter.SU7ExteriorBreakingYukawa

/-!
# Stage-9A source-generated associated bundles

The source-generated total transition now glues the actual Stage-7 exterior
matter carrier and the actual Stage-8 `Λ⁴V` scalar carrier.  Both total-group
representations are derived by projection to the existing mother-SU(7)
representations; no local section or gluing certificate is accepted.

The construction is an actual quotient of chart-local representatives by the
generated representation action.  The `SL(2,ℂ)` factor acts trivially in this
checkpoint.  Therefore these are the internal exterior-matter and scalar
associated bundles, not yet the physical Dirac-spinor associated bundle; the
nontrivial Spin action remains an explicit S9-A boundary.
-/

namespace SaturationMonoid.PhysicsCore.StageNineAssociatedBundles

open ProofFreeRicherAnholonomicSource
open SU7ExteriorMatterRepresentation
open SU7ExteriorBreakingYukawa
open StageNineEnrichedProofFreeSource
open StageNineGlobalBundle

noncomputable section

/-- Actual Stage-7 internal matter representation of the total group. -/
def totalExteriorMatterRepresentation :
    Representation ℂ TotalStructureGroup SU7ExteriorSpinorMatterCarrier where
  toFun totalElement :=
    su7ExteriorSpinorMatterRepresentation totalElement.2
  map_one' := by
    simp
  map_mul' first second := by
    change
      su7ExteriorSpinorMatterRepresentation (first.2 * second.2) =
        su7ExteriorSpinorMatterRepresentation first.2 *
          su7ExteriorSpinorMatterRepresentation second.2
    exact map_mul su7ExteriorSpinorMatterRepresentation first.2 second.2

/-- Actual Stage-8 scalar representation of the same total group. -/
def totalExteriorBreakingScalarRepresentation :
    Representation ℂ TotalStructureGroup ExteriorBreakingScalarCarrier where
  toFun totalElement := exteriorBreakingScalarRepresentation totalElement.2
  map_one' := by
    simp
  map_mul' first second := by
    change
      exteriorBreakingScalarRepresentation (first.2 * second.2) =
        exteriorBreakingScalarRepresentation first.2 *
          exteriorBreakingScalarRepresentation second.2
    exact map_mul exteriorBreakingScalarRepresentation first.2 second.2

universe uFiber

/-- One chart-local associated-bundle representative. -/
structure AssociatedChartRepresentative (Fiber : Type uFiber) where
  chart : StageNineChart
  base : BasePoint
  fiber : Fiber

def associatedRelated
    {Fiber : Type uFiber} [AddCommMonoid Fiber] [Module ℂ Fiber]
    (representation : Representation ℂ TotalStructureGroup Fiber)
    (source : SmoothUnifiedSource)
    (left right : AssociatedChartRepresentative Fiber) : Prop :=
  left.base = right.base ∧
    right.fiber =
      representation
        (generatedTotalTransition source left.chart right.chart left.base)
        left.fiber

theorem representation_mul_apply
    {Fiber : Type uFiber} [AddCommMonoid Fiber] [Module ℂ Fiber]
    (representation : Representation ℂ TotalStructureGroup Fiber)
    (first second : TotalStructureGroup) (fiber : Fiber) :
    representation (first * second) fiber =
      representation first (representation second fiber) := by
  rw [map_mul]
  rfl

def associatedRepresentativeSetoid
    {Fiber : Type uFiber} [AddCommMonoid Fiber] [Module ℂ Fiber]
    (representation : Representation ℂ TotalStructureGroup Fiber)
    (source : SmoothUnifiedSource) :
    Setoid (AssociatedChartRepresentative Fiber) where
  r := associatedRelated representation source
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro representative
      exact ⟨rfl, by simp⟩
    · intro left right related
      rcases related with ⟨base_eq, fiber_eq⟩
      refine ⟨base_eq.symm, ?_⟩
      rw [← base_eq, fiber_eq]
      rw [← representation_mul_apply,
        generatedTotalTransition_reverse_mul]
      simp
    · intro first second third first_second second_third
      rcases first_second with ⟨base_first_second, fiber_first_second⟩
      rcases second_third with ⟨base_second_third, fiber_second_third⟩
      refine ⟨base_first_second.trans base_second_third, ?_⟩
      rw [fiber_second_third, fiber_first_second, ← base_first_second]
      rw [← representation_mul_apply,
        generatedTotalTransition_cocycle]

/-- Actual quotient associated bundle for any generated total representation. -/
abbrev GluedAssociatedBundle
    {Fiber : Type uFiber} [AddCommMonoid Fiber] [Module ℂ Fiber]
    (representation : Representation ℂ TotalStructureGroup Fiber)
    (source : SmoothUnifiedSource) :=
  Quotient (associatedRepresentativeSetoid representation source)

def associatedBundleProjection
    {Fiber : Type uFiber} [AddCommMonoid Fiber] [Module ℂ Fiber]
    (representation : Representation ℂ TotalStructureGroup Fiber)
    (source : SmoothUnifiedSource) :
    GluedAssociatedBundle representation source → BasePoint :=
  Quotient.lift (fun representative => representative.base) (by
    intro left right related
    exact related.1)

def associatedLocalPoint
    {Fiber : Type uFiber} [AddCommMonoid Fiber] [Module ℂ Fiber]
    (representation : Representation ℂ TotalStructureGroup Fiber)
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (base : BasePoint) (fiber : Fiber) :
    GluedAssociatedBundle representation source :=
  Quotient.mk _ ⟨chart, base, fiber⟩

@[simp] theorem associatedBundleProjection_localPoint
    {Fiber : Type uFiber} [AddCommMonoid Fiber] [Module ℂ Fiber]
    (representation : Representation ℂ TotalStructureGroup Fiber)
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (base : BasePoint) (fiber : Fiber) :
    associatedBundleProjection representation source
        (associatedLocalPoint representation source chart base fiber) = base :=
  rfl

/-- The quotient gluing equation for associated fibers. -/
theorem associatedLocalPoint_transition
    {Fiber : Type uFiber} [AddCommMonoid Fiber] [Module ℂ Fiber]
    (representation : Representation ℂ TotalStructureGroup Fiber)
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart) (base : BasePoint)
    (fiber : Fiber) :
    associatedLocalPoint representation source initial base fiber =
      associatedLocalPoint representation source terminal base
        (representation
          (generatedTotalTransition source initial terminal base) fiber) := by
  apply Quotient.sound
  exact ⟨rfl, rfl⟩

abbrev ExteriorMatterAssociatedBundle (source : SmoothUnifiedSource) :=
  GluedAssociatedBundle totalExteriorMatterRepresentation source

abbrev ExteriorBreakingScalarAssociatedBundle
    (source : SmoothUnifiedSource) :=
  GluedAssociatedBundle totalExteriorBreakingScalarRepresentation source

/-- S9-A3 positive checkpoint: the same source-generated transition glues both
actual exterior carriers into inhabited associated-bundle quotients. -/
theorem positiveSource_generates_matter_and_scalar_associatedBundles :
    Nonempty (ExteriorMatterAssociatedBundle positiveSmoothUnifiedSource) ∧
      Nonempty
        (ExteriorBreakingScalarAssociatedBundle positiveSmoothUnifiedSource) :=
  ⟨⟨associatedLocalPoint totalExteriorMatterRepresentation
      positiveSmoothUnifiedSource 0 0 0⟩,
    ⟨associatedLocalPoint totalExteriorBreakingScalarRepresentation
      positiveSmoothUnifiedSource 0 0 0⟩⟩

/-- The same bad hand-filled transition rejected at S9-A1 cannot be promoted
to either associated bundle, because it fails before any representation is
applied. -/
theorem badConstantTransition_rejected_before_associatedBundle
    (source : SmoothUnifiedSource) :
    ¬ (badConstantTransitionSystem source).TransitionFlat :=
  badConstantTransitionSystem_not_flat source

end

end SaturationMonoid.PhysicsCore.StageNineAssociatedBundles
