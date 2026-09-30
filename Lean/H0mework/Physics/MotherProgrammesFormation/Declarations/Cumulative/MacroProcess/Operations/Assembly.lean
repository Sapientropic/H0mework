import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Operations.Factory

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroOperations
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}} (domain : MotherArenaHigher.Material rank) (nodes : Nodes domain)

def ActiveInjective : Prop :=
  ∀ {left right : State domain} {leftState rightState : RootInquiryStatePresentation.{0}},
    nodes left = .active leftState → nodes right = .active rightState →
    leftState.erase = rightState.erase → left = right

def SuccessorCompatible (fields : Fields nodes) : Prop :=
  ∀ state query,
    (nodes (fields.next state query)).erase = MotherNativeRegistry.nextCurrent (nodes state) query ∧
    (nodes state).PreservesGeneratedLivingLawAt query (nodes (fields.next state query))

def Admissible (fields : Fields nodes) : Prop := ActiveInjective domain nodes ∧ SuccessorCompatible domain nodes fields

/-- Public registry construction pattern; the private resolution is reduced
only by the original node cases in its dependent proof obligation. -/
def assemble (fields : Fields nodes) (checked : Admissible domain nodes fields) : SourceNativeInquiryEngineProcess.{0} where
  State := State domain
  stateAt := nodes
  erase_injective := checked.1
  initial := fields.initial
  successorAt := by
    intro state query
    refine ⟨fields.next state query, ?_, (checked.2 state query).2⟩
    apply (checked.2 state query).1.trans
    generalize source_eq : nodes state = source at query ⊢
    cases source with
    | active prior => rfl
    | answered prior oldQuery => exact nomatch query

def formProcess (event : Event nodes ↪ MotherArenaHigher.Base rank) (material : MotherArenaHigher.Material rank) :
    Option SourceNativeInquiryEngineProcess.{0} :=
  (formFields domain nodes event material).bind (fun fields =>
    if checked : Admissible domain nodes fields then some (assemble domain nodes fields checked) else none)

theorem every_process_fields (event : Event nodes ↪ MotherArenaHigher.Base rank)
    (original : Fields nodes) (checked : Admissible domain nodes original) :
    ∃ material : MotherArenaHigher.Material rank,
      formProcess domain nodes event material = some (assemble domain nodes original checked) := by
  obtain ⟨material, formed⟩ := every_fields domain nodes event original
  refine ⟨material, ?_⟩
  simp only [formProcess, formed, Option.bind_some, dif_pos checked]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroOperations
