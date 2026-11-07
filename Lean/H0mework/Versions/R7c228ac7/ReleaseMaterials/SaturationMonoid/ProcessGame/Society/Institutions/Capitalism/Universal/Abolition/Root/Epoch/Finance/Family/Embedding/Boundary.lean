import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Lifecycle
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Embedding.Archive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Embedding

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat) (index : Index)

local notation "OldV" => Finance.vocabulary (sources index) (depths index) (counts index)
local notation "NewV" => Family.vocabulary sources depths counts
local notation "OldProcess" => Finance.process (sources index) (depths index) (counts index)
local notation "NewProcess" => Family.process sources depths counts

def boundary {original : AdmittedObligation OldV}
    (old : Finance.Boundary (sources index) (depths index) (counts index) original) :
    Family.Boundary sources depths counts (obligation sources depths counts index original) where
  event := event sources depths counts index old.event
  lawful := old.lawful
  content_eq := congrArg (Sigma.mk index) old.content_eq
  before_eq := old.before_eq
  owns := {
    anchor_eq := by
      have same := congrArg MinimalRegistrableSourceAnchor.scope old.owns.anchor_eq
      exact congrArg (fun original : Finance.Origin (sources index) (depths index) (counts index) =>
        MinimalRegistrableSourceAnchor.canonical
          (⟨index, original⟩ : Family.Origin sources depths counts) (⟨index, original⟩ : Family.Origin sources depths counts)) same
    incidence_eq := congrArg (Sigma.mk index) old.owns.incidence_eq }
  scope_eq := congrArg (Sigma.mk index) old.scope_eq

theorem boundary_target {original : AdmittedObligation OldV}
    (old : Finance.Boundary (sources index) (depths index) (counts index) original) :
    (Family.boundaryDisposition sources depths counts (boundary sources depths counts index old)).targetSlot =
      slot sources depths counts index (Finance.boundaryDisposition (sources index) (depths index) (counts index) old).targetSlot := by
  by_cases cleared : old.event.after (sources index) (depths index) (counts index) = 0
  · have mapped : (boundary sources depths counts index old).event.after sources depths counts = 0 := cleared
    simp only [Family.boundaryDisposition, dif_pos mapped,
      Finance.boundaryDisposition, dif_pos cleared]
    rfl
  · have mapped : ¬ (boundary sources depths counts index old).event.after sources depths counts = 0 := cleared
    simp only [Family.boundaryDisposition, dif_neg mapped,
      Finance.boundaryDisposition, dif_neg cleared]
    rfl

@[simp] theorem payload_admission (claim : Finance.Claim (sources index) (depths index) (counts index)) :
    payload sources depths counts index (Finance.admission (sources index) (depths index) (counts index) claim) =
      Family.admission sources depths counts ⟨index, claim⟩ := rfl

@[simp] theorem obligation_admission (claim : Finance.Claim (sources index) (depths index) (counts index)) :
    obligation sources depths counts index (Finance.admission (sources index) (depths index) (counts index) claim).toObligation =
      (Family.admission sources depths counts ⟨index, claim⟩).toObligation := rfl

#print axioms boundary_target

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Embedding
