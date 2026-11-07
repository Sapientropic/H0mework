import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.World

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def registrationReceipt (point : Carrier root boundary) : RegistrationAt root boundary
    (root.toAuthoritativeRoot.toRoot.supportAt boundary.current,true) := by
  let attained := every_completed_budget_is_attained_in_the_original_actual_past root boundary point
  let cut := Classical.choose attained
  let rows := Classical.choose_spec attained
  let original := Classical.choose rows
  have exact := Classical.choose_spec rows
  exact .completed point cut original exact.1 exact.2

def firstReceipt (row : OpenResponsibilityAt (W root boundary)
    (root.toAuthoritativeRoot.toRoot.supportAt boundary.current,true)) :
    LedgerEntryEvolutionAt (W root boundary) row row := by
  rcases row with ⟨key,opened⟩
  cases key with
  | inl _ => exact .carried rfl (HEq.rfl)
  | inr point => exact .transferred (.inr (registrationReceipt root boundary point)) rfl rfl (Nat.le_refl _)

def firstLedger : LedgerWriteEvolutionAt (W root boundary)
    ⟨(root.toAuthoritativeRoot.toRoot.supportAt boundary.current,true)⟩
    ⟨(root.toAuthoritativeRoot.toRoot.supportAt boundary.current,true)⟩ where
  destination := fun row => ⟨row,firstReceipt root boundary row⟩
  origin := fun row => ⟨row,firstReceipt root boundary row⟩

theorem the_first_destination_retains_its_actual_original_row (row) :
    ((firstLedger root boundary).destination row).1 = row := rfl

theorem the_first_origin_retains_its_actual_original_row (row) :
    ((firstLedger root boundary).origin row).1 = row := rfl

theorem the_first_write_really_consumes_the_source_registration
    (point : Carrier root boundary) (same) :
    ((firstLedger root boundary).destination (landingRow root boundary point same)).2 =
      .transferred (.inr (registrationReceipt root boundary point)) rfl rfl (Nat.le_refl _) := rfl

theorem the_first_write_carries_every_old_actual_landing_row
    (old : OpenResponsibilityAt N (root.toAuthoritativeRoot.toRoot.supportAt boundary.current)) :
    ((firstLedger root boundary).destination (oldRow root boundary true old)).2 = .carried rfl (HEq.rfl) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
