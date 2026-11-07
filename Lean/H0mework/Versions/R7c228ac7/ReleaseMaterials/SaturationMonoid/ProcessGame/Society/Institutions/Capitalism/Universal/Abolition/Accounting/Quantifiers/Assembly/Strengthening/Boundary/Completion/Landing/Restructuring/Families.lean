import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Data

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

def both2 {A B C D : Type} (left : A → C → Type) (right : B → D → Type) :
    (A ⊕ B) → (C ⊕ D) → Type
  | .inl a,.inl c => left a c
  | .inr b,.inr d => right b d
  | _,_ => PEmpty

def both3 {A B C D E F : Type} (left : A → C → E → Type) (right : B → D → F → Type) :
    (A ⊕ B) → (C ⊕ D) → (E ⊕ F) → Type
  | .inl a,.inl c,.inl e => left a c e
  | .inr b,.inr d,.inr f => right b d f
  | _,_,_ => PEmpty

def old4 {A B C D E F G H : Type} (left : A → C → E → G → Type) :
    (A ⊕ B) → (C ⊕ D) → (E ⊕ F) → (G ⊕ H) → Type
  | .inl a,.inl c,.inl e,.inl g => left a c e g
  | _,_,_,_ => PEmpty

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def contentFamily (left : (Original root).base.SourceEvent → (Original root).base.Content → Type)
    (right : (W root boundary).Support → WorldEntry root boundary → Type) :
    SourceEvent root boundary → Content root boundary → Type
  | .inl event,.old _ original => left event original.content
  | .inr support,.added row => right support row
  | _,_ => PEmpty

def contentScope (left : (Original root).base.SourceEvent → (Original root).base.Content →
    (Original root).base.Scope → Type) :
    SourceEvent root boundary → Content root boundary → Scope root boundary → Type
  | .inl event,.old _ original,.inl scope => left event original.content scope
  | _,_,_ => PEmpty

def jurisdiction : Content root boundary → Scope root boundary → Type
  | .old _ original,.inl scope => (Original root).base.DischargeJurisdiction original.content scope
  | .added row,.inr support => PLift (row.1 = support)
  | _,_ => PEmpty

def progress : SourceEvent root boundary → Content root boundary →
    ((Original root).base.Residual ⊕ PUnit) → ((Original root).base.Residual ⊕ PUnit) → Type
  | .inl event,.old _ original,.inl before,.inl after =>
      (Original root).base.ProgressAt event original.content before after
  | _,_,_,_ => PEmpty

def replacement (left : (Original root).base.SourceEvent → (Original root).base.Incidence →
    (Original root).base.Content → (Original root).base.Incidence → (Original root).base.Content →
    (Original root).base.Scope → (Original root).base.Scope → Type) :
    SourceEvent root boundary → ((Original root).base.Incidence ⊕ N.Incidence) → Content root boundary →
    ((Original root).base.Incidence ⊕ N.Incidence) → Content root boundary → Scope root boundary → Scope root boundary → Type
  | .inl event,.inl oldInc,.old _ old,.inl newInc,.old _ next,.inl oldScope,.inl newScope =>
      left event oldInc old.content newInc next.content oldScope newScope
  | _,_,_,_,_,_,_ => PEmpty

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
