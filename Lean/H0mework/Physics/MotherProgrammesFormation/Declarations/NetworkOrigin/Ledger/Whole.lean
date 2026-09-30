import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.Rows
import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

private def wholeData (N : WorldRelationNetwork.{0}) (s t : N.Support) :
    LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩ ≃
      ((a : OpenResponsibilityAt N s) → Σ b : OpenResponsibilityAt N t, LedgerEntryEvolutionAt N a b) ×
      ((b : OpenResponsibilityAt N t) → Σ a : OpenResponsibilityAt N s, LedgerEntryEvolutionAt N a b) where
  toFun := fun whole => (whole.destination, whole.origin)
  invFun := fun whole => ⟨whole.1, whole.2⟩
  left_inv := fun whole => by cases whole; rfl
  right_inv := fun whole => by cases whole; rfl

/-- Both complete tables are transported: every old destination and every new
origin. No bijection between source and target rows is imposed. -/
def Presentation.wholeLedgerEquiv {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    (s t : N.Support) :
    LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩ ≃ LedgerWriteEvolutionAt G ⟨p.support s⟩ ⟨p.support t⟩ :=
  (wholeData N s t).trans ((Equiv.prodCongr
    (Equiv.piCongr (p.ledger s) (fun a =>
      Equiv.sigmaCongr (p.ledger t) (fun b => p.rowEquiv a b)))
    (Equiv.piCongr (p.ledger t) (fun b =>
      Equiv.sigmaCongr (p.ledger s) (fun a => p.rowEquiv a b)))).trans
        (wholeData G (p.support s) (p.support t)).symm)

def Presentation.terminalRowEquiv {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {s : N.Support} (a : OpenResponsibilityAt N s) :
    LedgerEntryTerminalAt N a ≃ LedgerEntryTerminalAt G (p.ledger s a) where
  toFun := fun row => ⟨p.dispositionAt s .supportSettlement row.receipt⟩
  invFun := fun row => ⟨(p.dispositionAt s .supportSettlement).symm row.receipt⟩
  left_inv := fun row => by cases row; simp only [Equiv.symm_apply_apply]
  right_inv := fun row => by cases row; simp only [Equiv.apply_symm_apply]

private def terminalData (N : WorldRelationNetwork.{0}) (s : N.Support) :
    LedgerTerminalEvolutionAt N ⟨s⟩ ≃
      ((a : OpenResponsibilityAt N s) → LedgerEntryTerminalAt N a) where
  toFun := fun whole => whole.discharge
  invFun := fun whole => ⟨whole⟩
  left_inv := fun whole => by cases whole; rfl
  right_inv := fun _ => rfl

def Presentation.wholeTerminalEquiv {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    (s : N.Support) :
    LedgerTerminalEvolutionAt N ⟨s⟩ ≃ LedgerTerminalEvolutionAt G ⟨p.support s⟩ :=
  (terminalData N s).trans ((Equiv.piCongr (p.ledger s) (fun a => p.terminalRowEquiv a)).trans
    (terminalData G (p.support s)).symm)

theorem Presentation.whole_destination {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {s t : N.Support} (whole : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩) (entry : OpenResponsibilityAt N s) :
    (p.wholeLedgerEquiv s t whole).destination (p.ledger s entry) =
      ⟨p.ledger t (whole.destination entry).1, p.mapRow (whole.destination entry).2⟩ := by
  change (Equiv.piCongr
    (Z := fun a : OpenResponsibilityAt G (p.support s) =>
      Σ b : OpenResponsibilityAt G (p.support t), LedgerEntryEvolutionAt G a b)
    (p.ledger s) (fun a =>
    Equiv.sigmaCongr (p.ledger t) (fun b => p.rowEquiv a b))) whole.destination (p.ledger s entry) = _
  exact Equiv.piCongr_apply_apply _ _ whole.destination entry

theorem Presentation.whole_origin {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {s t : N.Support} (whole : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩) (entry : OpenResponsibilityAt N t) :
    (p.wholeLedgerEquiv s t whole).origin (p.ledger t entry) =
      ⟨p.ledger s (whole.origin entry).1, p.mapRow (whole.origin entry).2⟩ := by
  change (Equiv.piCongr
    (Z := fun b : OpenResponsibilityAt G (p.support t) =>
      Σ a : OpenResponsibilityAt G (p.support s), LedgerEntryEvolutionAt G a b)
    (p.ledger t) (fun b =>
    Equiv.sigmaCongr (p.ledger s) (fun a => p.rowEquiv a b))) whole.origin (p.ledger t entry) = _
  exact Equiv.piCongr_apply_apply _ _ whole.origin entry

theorem Presentation.whole_discharge {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {s : N.Support} (whole : LedgerTerminalEvolutionAt N ⟨s⟩) (entry : OpenResponsibilityAt N s) :
    (p.wholeTerminalEquiv s whole).discharge (p.ledger s entry) =
      p.terminalRowEquiv entry (whole.discharge entry) := by
  change (Equiv.piCongr (p.ledger s) (fun a => p.terminalRowEquiv a)) whole.discharge (p.ledger s entry) = _
  exact Equiv.piCongr_apply_apply _ _ whole.discharge entry

theorem formed_network_consumes_original_whole_ledgers (N : WorldRelationNetwork.{0})
    (encode : Total N ↪ MotherNetworkFactory.B) :
    ∃ m : MotherNetworkFactory.M, ∃ G : WorldRelationNetwork.{0}, ∃ p : Presentation N G,
      MotherNetworkFactory.formNetwork m = some G ∧
      (∀ (s t : N.Support) (whole : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩),
        (p.wholeLedgerEquiv s t).symm (p.wholeLedgerEquiv s t whole) = whole) ∧
      (∀ (s : N.Support) (whole : LedgerTerminalEvolutionAt N ⟨s⟩),
        (p.wholeTerminalEquiv s).symm (p.wholeTerminalEquiv s whole) = whole) := by
  obtain ⟨m, G, formed, ⟨p⟩⟩ := every_jointly_embedded_network N encode
  exact ⟨m, G, p, formed, fun s t whole => (p.wholeLedgerEquiv s t).symm_apply_apply whole,
    fun s whole => (p.wholeTerminalEquiv s).symm_apply_apply whole⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
