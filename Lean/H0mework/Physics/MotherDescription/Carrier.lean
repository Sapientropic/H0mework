import H0mework.Physics.RootRuntime.RecognitionWholeCarrier
import H0mework.Physics.Actual.FieldsCompactEnumeration
import H0mework.Foundation.Relations.ConsumerQuotient

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.WholeDescription

open Stage9C.Revision Stage9CU.Fields StageNineHolonomicField
open ProofFreeRicherAnholonomicSource
open NoIslandNoMagic.Consciousness.Representation

noncomputable section

abbrev Current := SpinPair.V.Current

theorem smooth (current : Current) : (Recognition.wholeField current).Smooth := by
  cases current with
  | ingress => exact (materialStateNext (materialStateNext materialInitialState)).smooth
  | running state => exact state.smooth

/-- The complete original physical-coordinate inventory, before selecting a description. -/
def consumers : IndependentConsumerSystem Current where
  Consumer := Unit ⊕ (Coordinate × BasePoint)
  Output
    | .inl _ => Bool
    | .inr _ => ℝ
  read
    | .inl _ => Recognition.isRunning
    | .inr (coordinate, point) => fun current => realCoordinate (Recognition.wholeField current) coordinate point
  positive := ⟨.inl ()⟩

theorem consumers_complete {left right : Current}
    (same : consumers.Indistinguishable left right) : left = right :=
  Recognition.reverseFaithful (same (.inl ())) (fun coordinate point => same (.inr (coordinate, point)))

def pointwise (current : Current) : Bool × (Coordinate → BasePoint → ℝ) :=
  (Recognition.isRunning current, realCoordinate (Recognition.wholeField current))

def compact (current : Current) : Bool × (ℕ → CompactL2) :=
  (Recognition.isRunning current, compactCoordinates (Recognition.wholeField current) (smooth current))

theorem pointwise_injective : Function.Injective pointwise := by
  intro left right same
  exact Recognition.reverseFaithful (congrArg Prod.fst same)
    (fun coordinate point => congrFun (congrFun (congrArg Prod.snd same) coordinate) point)

theorem compact_injective : Function.Injective compact := by
  intro left right same
  have field := configuration_eq_of_compactCoordinates_eq (smooth left) (smooth right) (congrArg Prod.snd same)
  exact Recognition.reverseFaithful (congrArg Prod.fst same)
    (fun coordinate point => congrArg (fun configuration => realCoordinate configuration coordinate point) field)

theorem pointwise_exact : FaceKernelExactAt consumers pointwise := by
  intro left right
  constructor
  · intro same
    cases pointwise_injective same
    exact consumers.indistinguishable_refl _
  · intro same
    cases consumers_complete same
    rfl

theorem compact_exact : FaceKernelExactAt consumers compact := by
  intro left right
  constructor
  · intro same
    cases compact_injective same
    exact consumers.indistinguishable_refl _
  · intro same
    cases consumers_complete same
    rfl

abbrev Pointwise := Set.range pointwise
abbrev Compact := Set.range compact

def point (current : Current) : Pointwise := ⟨pointwise current, current, rfl⟩
def weak (current : Current) : Compact := ⟨compact current, current, rfl⟩

def decodePoint : Pointwise → Current := (Equiv.ofInjective pointwise pointwise_injective).symm
def decodeWeak : Compact → Current := (Equiv.ofInjective compact compact_injective).symm

theorem decodePoint_point (current : Current) : decodePoint (point current) = current :=
  Equiv.ofInjective_symm_apply pointwise_injective current

theorem decodeWeak_weak (current : Current) : decodeWeak (weak current) = current :=
  Equiv.ofInjective_symm_apply compact_injective current

theorem point_decodePoint (description : Pointwise) : point (decodePoint description) = description :=
  (Equiv.ofInjective pointwise pointwise_injective).apply_symm_apply description

theorem weak_decodeWeak (description : Compact) : weak (decodeWeak description) = description :=
  (Equiv.ofInjective compact compact_injective).apply_symm_apply description

def equivalence : Pointwise ≃ Compact := pointwise_exact.completeCarrierEquiv compact_exact

theorem equivalence_point (current : Current) : equivalence (point current) = weak current :=
  pointwise_exact.completeCarrierEquiv_commutes compact_exact current

theorem equivalence_decodes (description : Pointwise) :
    decodeWeak (equivalence description) = decodePoint description := by
  rw [← point_decodePoint description, equivalence_point, decodeWeak_weak, decodePoint_point]

/-- Every other complete description is compared over the same physical occurrences. -/
theorem every_complete_description {Description : Type*} (describe : Current → Description)
    (complete : FaceKernelExactAt consumers describe) :
    ∃! comparison : Pointwise ≃ Set.range describe,
      ∀ current, comparison (point current) = ⟨describe current, current, rfl⟩ :=
  ⟨pointwise_exact.completeCarrierEquiv complete,
    pointwise_exact.completeCarrierEquiv_commutes complete,
    fun comparison same => pointwise_exact.completeCarrierEquiv_unique complete comparison same⟩

end
end SaturationMonoid.PhysicsCore.Stage10.WholeDescription
