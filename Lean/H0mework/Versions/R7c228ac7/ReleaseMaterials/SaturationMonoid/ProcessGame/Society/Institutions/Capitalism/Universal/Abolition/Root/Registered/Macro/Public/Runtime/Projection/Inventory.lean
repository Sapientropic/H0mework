import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Living
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.Living
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Types
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Origin
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

deriving instance DecidableEq for Public.Source.Projection
deriving instance DecidableEq for Public.Accounting.Born.Source.Projection
deriving instance DecidableEq for Public.Inquiry.Projection
deriving instance DecidableEq for Abolition.Functions.Revision.Enactment.Projection

private instance : Fintype Public.Source.Projection where
  elems := {.ledger, .account, .pending, .physical, .sourceInput, .sourceExecution, .sourceResult, .interpreter}
  complete := by intro projection; cases projection <;> simp

private instance : Fintype Public.Accounting.Born.Source.Projection where
  elems := {.ledger, .account, .pending, .physical, .sourceInput, .sourceExecution, .sourceResult, .interpreter}
  complete := by intro projection; cases projection <;> simp

private instance : Fintype Public.Inquiry.Projection where
  elems := {.query, .answer, .compilation, .consumer, .snapshot, .nativeAccount, .publicLaw, .sourceReport}
  complete := by intro projection; cases projection <;> simp

private instance : Fintype Abolition.Functions.Revision.Enactment.Projection where
  elems := {.originalSnapshot, .originalRawReadout, .nativeDispositions, .currentScope}
  complete := by intro projection; cases projection <;> simp

theorem public_source_projection_card : Nat.card Public.Source.Projection = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem born_source_projection_card : Nat.card Public.Accounting.Born.Source.Projection = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem public_inquiry_projection_card : Nat.card Public.Inquiry.Projection = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem original_provenance_projection_card : Nat.card Abolition.Functions.Revision.Enactment.Projection = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime
