import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material.Flows
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Interpretation.Step

/-! Physical credits are partitioned at their original instruction.  The
relation family is a source-produced input to this consumer; it is never
inferred from positive credit.  Unexplained access keeps its whole amount. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material

open Program ProgrammeControl
open ProgrammeControl.Kernel.AssetAuthority

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (family : OriginalItem law current word → List Port) (group : List Party)

def ControlledAt (item : OriginalItem law current word) : Prop :=
  law.Valid item.val.before item.val.request ∧
    ∃ port ∈ law.requiredPorts item.val.before item.val.request, port ∈ family item

instance (item : OriginalItem law current word) : Decidable (ControlledAt law current word family item) := by
  unfold ControlledAt
  infer_instance

def IndependentlyAccessible (item : OriginalItem law current word) (location : Party × Good) : Prop :=
  law.Valid item.val.before item.val.request ∧
  (∀ port ∈ law.requiredPorts item.val.before item.val.request,
    port ∉ family item ∧
      Exit.Interpretation.ExplainedPort law current word group item port) ∧
  ¬ Law.SourceRelations.OpaqueAt law item ∧
  law.Valid item.val.before { item.val.request with signer := location.1, consents := [] }

instance (item : OriginalItem law current word) (location : Party × Good) :
    Decidable (IndependentlyAccessible law current word family group item location) := by
  unfold IndependentlyAccessible
  infer_instance

inductive AcquisitionClass (item : OriginalItem law current word) (location : Party × Good)
  | dependent (controlled : ControlledAt law current word family item)
  | independent (executable : IndependentlyAccessible law current word family group item location)
  | unresolved (notControlled : ¬ ControlledAt law current word family item)
      (notIndependent : ¬ IndependentlyAccessible law current word family group item location)

def classifyAcquisition (item : OriginalItem law current word) (location : Party × Good) :
    AcquisitionClass law current word family group item location :=
  if controlled : ControlledAt law current word family item then .dependent controlled
  else if executable : IndependentlyAccessible law current word family group item location then
    .independent executable
  else .unresolved controlled executable

def dependentAmount (item : OriginalItem law current word) (location : Party × Good) : ℚ :=
  match classifyAcquisition law current word family group item location with
  | .dependent _ => Decoder.acquired law item.val location.1 location.2
  | _ => 0

def independentAmount (item : OriginalItem law current word) (location : Party × Good) : ℚ :=
  match classifyAcquisition law current word family group item location with
  | .independent _ => Decoder.acquired law item.val location.1 location.2
  | _ => 0

def unresolvedAmount (item : OriginalItem law current word) (location : Party × Good) : ℚ :=
  match classifyAcquisition law current word family group item location with
  | .unresolved .. => Decoder.acquired law item.val location.1 location.2
  | _ => 0

theorem acquisition_partition (item : OriginalItem law current word) (location : Party × Good) :
    dependentAmount law current word family group item location +
      independentAmount law current word family group item location +
      unresolvedAmount law current word family group item location =
        Decoder.acquired law item.val location.1 location.2 := by
  unfold dependentAmount independentAmount unresolvedAmount
  cases classifyAcquisition law current word family group item location <;> simp

theorem acquisition_nonnegative (item : OriginalItem law current word) (location : Party × Good) :
    0 ≤ dependentAmount law current word family group item location ∧
      0 ≤ independentAmount law current word family group item location ∧
      0 ≤ unresolvedAmount law current word family group item location := by
  have positive := acquired_nonnegative law item.val location.1 location.2
  unfold dependentAmount independentAmount unresolvedAmount
  cases classifyAcquisition law current word family group item location <;> simp [positive]

theorem positive_credit_returns_actual_control (item : OriginalItem law current word)
    (location : Party × Good)
    (positive : 0 < dependentAmount law current word family group item location) :
    ∃ use : ControlUse law current word family, use.item = item := by
  unfold dependentAmount at positive
  cases classified : classifyAcquisition law current word family group item location with
  | dependent controlled =>
      obtain ⟨accepted, port, required, member⟩ := controlled
      exact ⟨⟨item, accepted, port, required, member⟩, rfl⟩
  | independent _ => simp only [classified] at positive; exact (lt_irrefl _ positive).elim
  | unresolved _ _ => simp only [classified] at positive; exact (lt_irrefl _ positive).elim

theorem positive_independent_credit_has_personal_access (item : OriginalItem law current word)
    (location : Party × Good)
    (positive : 0 < independentAmount law current word family group item location) :
    IndependentlyAccessible law current word family group item location := by
  unfold independentAmount at positive
  cases classified : classifyAcquisition law current word family group item location with
  | independent executable => exact executable
  | dependent _ => simp only [classified] at positive; exact (lt_irrefl _ positive).elim
  | unresolved _ _ => simp only [classified] at positive; exact (lt_irrefl _ positive).elim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material
