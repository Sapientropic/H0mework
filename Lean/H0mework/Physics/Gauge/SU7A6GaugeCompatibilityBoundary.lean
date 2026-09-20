import H0mework.Physics.Admission.SU7A6RootGraphStandingAdapter
import H0mework.Physics.Geometry.ConcreteOperationAdapters

/-!
# SU7/A6 root motion versus the P348 gauge-field balance

The unfiltered A6 root graph is reachable and confluent, but that does not yet
make every root move a legal standing transformation of the source-generated
P348 field.  This file gives a concrete obstruction using repository-native
readouts only.

Start from the concrete A6 endpoint-source label with endpoint codes `(2,2)`
in fiber `n = 2`.  Its raw-code color-loop field is trace exact.  Lowering by
simple root `0` is a genuine `su7A6LowerBySimpleRoot` operation, but the same
endpoint readout becomes `(0,3)`, so trace exactness fails.  Therefore the
unfiltered A6 standing graph cannot be attached wholesale to the gauge audit.
The missing branching/filter-preservation theorem must identify the legal
subgraph on which the source-generated field standing predicates are stable.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7A6GaugeCompatibilityBoundary

open StandardModelConstraint
open SU7A6RootGraphStandingAdapter

noncomputable section

def simpleRootZero : RootIndex := 0

def balancedRootLabel : SU7A6WeightLabel :=
  su7A6EndpointSourceLabel 2 2 1

def balancedPresentation : Presentation where
  rootLabel := balancedRootLabel
  moves := 0

def loweredPresentation : Presentation where
  rootLabel := balancedRootLabel
  moves := simpleRootZero ::ₘ 0

theorem rootMove_applies :
    apply simpleRootZero balancedPresentation =
      some loweredPresentation := by
  rfl

theorem currentLabel_balanced :
    balancedPresentation.currentLabel = balancedRootLabel := by
  exact generatedLabel_zero balancedRootLabel

theorem currentLabel_lowered :
    loweredPresentation.currentLabel =
      su7A6LowerBySimpleRoot simpleRootZero balancedRootLabel := by
  calc
    loweredPresentation.currentLabel =
        generatedLabel balancedRootLabel (simpleRootZero ::ₘ 0) := rfl
    _ = su7A6LowerBySimpleRoot simpleRootZero
        (generatedLabel balancedRootLabel 0) :=
      generatedLabel_cons balancedRootLabel 0 simpleRootZero
    _ = su7A6LowerBySimpleRoot simpleRootZero balancedRootLabel := by
      rw [generatedLabel_zero]

def leftCode (presentation : Presentation) : Nat :=
  su7A6EndpointSourceLeftCodeOf presentation.currentLabel

def rightCode (presentation : Presentation) : Nat :=
  su7A6EndpointSourceRightCodeOf presentation.currentLabel

theorem balanced_codes :
    leftCode balancedPresentation = 2 ∧
      rightCode balancedPresentation = 2 := by
  simp [leftCode, rightCode, currentLabel_balanced, balancedRootLabel,
    su7A6EndpointSourceLabel_leftCode,
    su7A6EndpointSourceLabel_rightCode]

theorem lowered_codes :
    leftCode loweredPresentation = 0 ∧
      rightCode loweredPresentation = 3 := by
  constructor <;>
    norm_num [leftCode, rightCode, currentLabel_lowered,
      simpleRootZero, balancedRootLabel,
      su7A6EndpointSourceLeftCodeOf,
      su7A6EndpointSourceRightCodeOf,
      su7A6LowerBySimpleRoot, su7A6CartanEntry, su7A6Adjacent,
      su7A6EndpointSourceLabel]

def field (presentation : Presentation) : ColorLoopField :=
  rawCodeColorLoopMatrix 2
    (leftCode presentation) (rightCode presentation)

def TraceExact (presentation : Presentation) : Prop :=
  ColorLoopTraceExact (field presentation)

theorem balanced_traceExact : TraceExact balancedPresentation := by
  unfold TraceExact field
  apply (rawCodeColorLoop_traceExact_iff_balance 2
    (leftCode balancedPresentation)
    (rightCode balancedPresentation)).mpr
  rw [balanced_codes.1, balanced_codes.2]

theorem lowered_not_traceExact : ¬ TraceExact loweredPresentation := by
  rw [TraceExact, field,
    rawCodeColorLoop_traceExact_iff_balance,
    lowered_codes.1, lowered_codes.2]
  norm_num

/-- Concrete failure of native-move invariance.  This is the exact reason a
filtered SU7 source graph is required before the gauge atom can join the same
standing carrier. -/
theorem traceExact_not_nativeMoveInvariant :
    ¬ NativeMoveInvariant operations.toNativeStandingOperations
        TraceExact := by
  intro hinvariant
  have hiff := hinvariant simpleRootZero
    balancedPresentation loweredPresentation rootMove_applies
  exact lowered_not_traceExact (hiff.mp balanced_traceExact)

theorem traceExact_not_standingInvariant :
    ¬ StandingInvariant
        (generatedStandingIdentity operations.toNativeStandingOperations)
        TraceExact := by
  rw [standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant]
  exact traceExact_not_nativeMoveInvariant

end
end SU7A6GaugeCompatibilityBoundary
end PhysicsCore
end SaturationMonoid
