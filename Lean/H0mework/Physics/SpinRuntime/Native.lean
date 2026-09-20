import H0mework.Physics.Revision.InquiryPrograms
import H0mework.Physics.SpinPair.Regularity

/-! The original spin-pair source law and emitted configurations, before
projection admission. History and weak observers share this one native law. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineFormNativeGaugeAuxiliaryVariation
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite

noncomputable section

def sourceVisit := materialVisit 3
def sourceEntry := materialEntry (materialCurrentSupport sourceVisit.current)
def sourceAuthority := materialAuthorityAt 3

def initialState : MaterialState where
  current := Material.SpinPair.actual
  smooth := Material.SpinPair.actual_smooth
  nondegenerate := Material.SpinPair.actual_nondegenerate
  auxiliaryEquation := fun point =>
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff _ _).1
      (Reduction.algebraicCartanReduction_p286Auxiliary_zero positiveSmoothUnifiedSource
        Material.SpinPair.seed Material.SpinPair.seed_nondegenerate point)

inductive Current
  | ingress
  | running (state : MaterialState)

def underlying : Current → MaterialCurrent
  | .ingress => sourceVisit.current
  | .running state => .running state

def support (current : Current) : MaterialSupport := materialCurrentSupport (underlying current)

def next : Current → Current
  | .ingress => .running initialState
  | .running state => .running (materialStateNext state)

def vocabulary : Vocabulary where
  Current := Current
  Anchor := MaterialN.Anchor
  Incidence := MaterialSupport
  Lineage := MaterialN.Lineage
  anchorAt := fun _ => positiveSmoothUnifiedSource
  incidenceAt := support
  lineageAt := fun _ => positiveSmoothUnifiedSource
  NativeWriteAt := fun current => MaterialActionAt (underlying current)
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary

structure EventAt (current : Current) (targetSupport : MaterialSupport) : Type where
  support_eq : targetSupport = support current

def eventAlgebra : SourceNativeEventAlgebra MaterialN V where
  EventAt := EventAt
  compile := fun {current} {_support} _ => .nativeWrite (materialActionAt (underlying current))
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current targetSupport event
    cases event.support_eq
    exact materialInventoryPresentation _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.support_eq.symm
  lineage_commutes := fun _ => rfl

def source : SourceNativeSource MaterialN V where
  initial := .ingress
  law := eventAlgebra

def emitted (current : Current) : source.toRootSource.actual.OccurrenceAt current :=
  ⟨support current, ⟨rfl⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair
