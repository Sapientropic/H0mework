import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Core
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Consumers.StoredAccess
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global.Capital

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel
noncomputable section

abbrev body := Kernel.Consumers.StoredAccess.body
def state (clock : ℚ) (round : Nat) :=
  { Kernel.Consumers.StoredAccess.current with clock := clock,round := round }

/-- Only the actual production-site permission row changes. The original
technique, needs, stock, claims, emitted operations and payment units remain. -/
def law (ownerGranted recipientGranted : Bool) : RawLaw Bool Unit Bool Unit Unit :=
  { Kernel.Consumers.StoredAccess.law with allowed := fun _ port actor =>
      if port then true else if actor then recipientGranted else ownerGranted }

def input (ownerGranted recipientGranted : Bool) : Root.ProgrammeSource.Input Bool Unit Bool Unit Unit :=
  { law := law ownerGranted recipientGranted,initial := state 0 0,instructions := [],emission? := some (fun _ => body) }

def item (ownerGranted recipientGranted : Bool) (clock : ℚ) (round : Nat) (index : Fin 3) :=
  itemAt (law ownerGranted recipientGranted) (state clock round) body
    ⟨index.val,by simpa only [body,Kernel.Consumers.StoredAccess.body,List.length_cons,List.length_nil] using index.isLt⟩

def proposal (ownerGranted recipientGranted : Bool) (clock : ℚ) (round : Nat) :
    Proposal (law ownerGranted recipientGranted) (state clock round) body where
  access := {
    access := item ownerGranted recipientGranted clock round 0
    necessity := item ownerGranted recipientGranted clock round 2
    mode := .acquired
    accessHolder := true
    recipient := true
    port := false
    accessGood := ()
    necessityGood := ()
    delivery := [] }
  reciprocity := .returnFlow () () [⟨item ownerGranted recipientGranted clock round 1,(false,())⟩]
  disposal := {
    position := item ownerGranted recipientGranted clock round 0
    request := ⟨false,[],false,[],.use false [((),1)] .external⟩
    good := () }

theorem no_material_or_necessity_data_is_changed (ownerGranted recipientGranted : Bool) :
    (law ownerGranted recipientGranted).technique = Kernel.Consumers.StoredAccess.law.technique ∧
    (law ownerGranted recipientGranted).necessities = Kernel.Consumers.StoredAccess.law.necessities ∧
    (law ownerGranted recipientGranted).mandatoryMaintenance = Kernel.Consumers.StoredAccess.law.mandatoryMaintenance ∧
    (input ownerGranted recipientGranted).initial = state 0 0 := ⟨rfl,rfl,rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions
