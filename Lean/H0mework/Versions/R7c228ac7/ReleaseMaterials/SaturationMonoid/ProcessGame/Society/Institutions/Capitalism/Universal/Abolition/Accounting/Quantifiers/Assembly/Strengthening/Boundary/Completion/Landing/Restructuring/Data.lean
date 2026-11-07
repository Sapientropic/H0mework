import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

abbrev oldLaw := root.source.base.restructuringSource.compiler.restructuringLaw
abbrev Original := (oldLaw root).vocabulary
abbrev WorldEntry := Sigma (OpenResponsibilityAt (W root boundary))

/-- The original admission remains data. World-entry identity supplies the
key even for synthetic mixed lifecycle values; no default debt is needed. -/
inductive Content : Type
  | old (entry : WorldEntry root boundary) (original : (Original root).Obligation)
  | added (entry : WorldEntry root boundary)

def entry : Content root boundary → WorldEntry root boundary
  | .old row _ => row
  | .added row => row

def originalContent : Content root boundary → Option (Original root).base.Content
  | .old _ original => some original.content
  | .added _ => none

def originalAdmission : Content root boundary → Option (Original root).Obligation
  | .old _ original => some original
  | .added _ => none

abbrev SourceEvent := (Original root).base.SourceEvent ⊕ (W root boundary).Support
abbrev Scope := (Original root).base.Scope ⊕ (W root boundary).Support
abbrev Lineage := (Original root).base.Lineage ⊕ N.Lineage

def observation : ComplementObservation.ComplementObservationCarrier where
  Carrier := (Original root).base.SourceObservation.Carrier ⊕ (N.Anchor × Bool)
  null := .inl (Original root).base.SourceObservation.null
  complement := Sum.map (Original root).base.SourceObservation.complement (fun p => (p.1,!p.2))
  complement_involutive := by
    rintro (old | ⟨anchor,bit⟩)
    · exact congrArg Sum.inl ((Original root).base.SourceObservation.complement_involutive old)
    · cases bit <;> rfl
  null_ne_complement_null := fun same =>
    (Original root).base.SourceObservation.null_ne_complement_null (Sum.inl.inj same)

def oldAnchor (anchor : MinimalRegistrableSourceAnchor (Original root).base.SourceObservation
    (Original root).base.Scope (Original root).base.Lineage) :
    MinimalRegistrableSourceAnchor (observation root) (Scope root boundary) (Lineage root) where
  identity := .inl anchor.identity
  identity_ne_complement_identity := fun same => anchor.identity_ne_complement_identity (Sum.inl.inj same)
  scope := .inl anchor.scope
  lineage := .inl anchor.lineage

def addedAnchor (support : (W root boundary).Support) :
    MinimalRegistrableSourceAnchor (observation root) (Scope root boundary) (Lineage root) where
  identity := .inr ((W root boundary).anchorAt support,false)
  identity_ne_complement_identity := fun same => Bool.noConfusion (congrArg Prod.snd (Sum.inr.inj same))
  scope := .inr support
  lineage := .inr ((W root boundary).lineageAt support)

def OldDemandAt (event : (Original root).base.SourceEvent) :=
  Sigma fun _row : WorldEntry root boundary => Sigma fun original : (Original root).Obligation =>
    Sigma fun obstruction : (Original root).base.ObstructionAt event =>
      PLift ((Original root).base.demandContent obstruction = original.content)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
