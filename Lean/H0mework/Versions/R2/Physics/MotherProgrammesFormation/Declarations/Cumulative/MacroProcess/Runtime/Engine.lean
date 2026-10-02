import H0mework.Versions.R2.Foundation.Inquiry.Engine

/-! Literal process recovery transports the existing sealed engine and
activation law. No new activation or source-owned query choice is introduced. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroRuntime
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

universe u

variable {source target : SourceNativeInquiryEngineProcess.{u}} (same : source = target)

def transportEngine (engine : Engine source) : Engine target := same ▸ engine

def transportActivation {engine : Engine source}
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    Engine.SourceNativeInquiryActivationAt (transportEngine same engine) := by
  cases same
  exact activation

def transportLaw (law : Engine.SourceNativeInquiryActivationLaw source) :
    Engine.SourceNativeInquiryActivationLaw target := same ▸ law

def transportOccurrence {engine : Engine source}
    (activation : Engine.SourceNativeInquiryActivationAt engine)
    (occurrence : Engine.ExactRootInquiryOccurrenceAt engine activation.query) :
    Engine.ExactRootInquiryOccurrenceAt (transportEngine same engine)
      (transportActivation same activation).query := by
  cases same
  exact occurrence

theorem initial_commutes :
    transportEngine same (Engine.initial source) = Engine.initial target := by
  cases same
  rfl

theorem activation_query_commutes {engine : Engine source}
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    HEq (transportActivation same activation).query activation.query := by
  cases same
  rfl

/-- The complete recursive law, including every nextAt value, is retained. -/
theorem law_recovers (law : Engine.SourceNativeInquiryActivationLaw source) :
    HEq (transportLaw same law) law ∧
    HEq (transportLaw same law).initial law.initial ∧
    HEq (transportLaw same law).nextAt law.nextAt := by
  cases same
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem ask_commutes (engine : Engine source)
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    (transportEngine same engine).ask (transportActivation same activation) =
      transportOccurrence same activation (engine.ask activation) := by
  cases same
  rfl

/-- These are readouts of the whole transported occurrence, including the
exact successor engine; no resolution constructor is inspected. -/
theorem ask_readouts (engine : Engine source)
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    let actual := (transportEngine same engine).ask (transportActivation same activation)
    let original := engine.ask activation
    HEq actual original ∧
    HEq actual.resolution original.resolution ∧
    HEq actual.answer original.answer ∧
    HEq actual.receipt original.receipt ∧
    actual.next = transportEngine same original.next := by
  cases same
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl⟩

theorem nextAfter_commutes (law : Engine.SourceNativeInquiryActivationLaw source)
    {engine : Engine source} (activation : Engine.SourceNativeInquiryActivationAt engine) :
    HEq ((transportLaw same law).nextAfter (transportActivation same activation))
      (transportActivation same (law.nextAfter activation)) := by
  cases same
  rfl

end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroRuntime
