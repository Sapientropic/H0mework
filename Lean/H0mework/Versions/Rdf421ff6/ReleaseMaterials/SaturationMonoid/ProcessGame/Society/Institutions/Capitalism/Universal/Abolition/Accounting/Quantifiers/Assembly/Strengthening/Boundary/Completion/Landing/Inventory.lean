import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Compatibility

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

abbrev OldLanding := OpenResponsibilityAt N (root.toAuthoritativeRoot.toRoot.supportAt boundary.current)
abbrev LandingEntry := OpenResponsibilityAt (W root boundary)
  (root.toAuthoritativeRoot.toRoot.supportAt boundary.current,true)

theorem no_completed_standing_is_active_at_a_finite_cut (cut : Nat) (point : Carrier root boundary) :
    IsEmpty ((W root boundary).OpenAt
      (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt cut).current,false) (.inr point)) :=
  ⟨fun impossible => nomatch impossible⟩

def presentLanding (compatible : Compatible root boundary) :
    OldLanding root boundary ⊕ Carrier root boundary → LandingEntry root boundary
  | .inl original => oldRow root boundary true original
  | .inr point => landingRow root boundary point (compatible point)

def readLanding : LandingEntry root boundary → OldLanding root boundary ⊕ Carrier root boundary
  | ⟨.inl key,opened⟩ => .inl ⟨key,opened⟩
  | ⟨.inr point,_⟩ => .inr point

def completePresentation (compatible : Compatible root boundary) :
    ConstructivePresentation (OldLanding root boundary ⊕ Carrier root boundary) (LandingEntry root boundary) where
  forward := presentLanding root boundary compatible
  backward := readLanding root boundary
  forward_backward := by
    rintro ⟨key,opened⟩
    cases key with
    | inl _ => rfl
    | inr _ => rfl
  backward_forward := by rintro (old | point) <;> rfl

theorem no_old_landing_row_is_deleted (compatible : Compatible root boundary)
    (original : OldLanding root boundary) :
    (completePresentation root boundary compatible).backward
      ((completePresentation root boundary compatible).forward (.inl original)) = .inl original := rfl

theorem every_completed_standing_is_actually_presented (compatible : Compatible root boundary)
    (point : Carrier root boundary) :
    (completePresentation root boundary compatible).backward
      ((completePresentation root boundary compatible).forward (.inr point)) = .inr point := rfl

theorem every_landing_entry_has_its_original_source (compatible : Compatible root boundary)
    (entry : LandingEntry root boundary) :
    presentLanding root boundary compatible (readLanding root boundary entry) = entry :=
  (completePresentation root boundary compatible).forward_backward entry

theorem the_two_source_channels_do_not_merge_original_standings
    (compatible : Compatible root boundary) (old : OldLanding root boundary) (point : Carrier root boundary) :
    presentLanding root boundary compatible (.inl old) ≠ presentLanding root boundary compatible (.inr point) := by
  intro merged
  have impossible := congrArg (readLanding root boundary) merged
  change (Sum.inl old : OldLanding root boundary ⊕ Carrier root boundary) = Sum.inr point at impossible
  cases impossible

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
