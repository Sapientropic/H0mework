import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.LegacyLaw
import H0mework.Foundation.Responsibility.DebtWorldReadback

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private def sumLeft {A B C : Type} (map : ConstructiveRetract A B) : ConstructiveRetract (A ⊕ C) (B ⊕ C) where
  forward := Sum.map map.forward id
  backward := Sum.map map.backward id
  backward_forward := by intro value; cases value with
    | inl value => exact congrArg Sum.inl (map.backward_forward value)
    | inr value => rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
  (before : (Financial.process input).GeneratedState) (claim : Financial.IssuedClaim input)
  {OldBase NewBase : WorldRelationNetwork} (base : TypedSemanticWorldNetworkTranslationAt OldBase NewBase)

abbrev OldWorld := ExtendedNetwork OldBase (LegacyLaw.oldLaw input before claim)
abbrev NewWorld := ExtendedNetwork NewBase (LegacyLaw.law input depth count before claim)

def supportForward (support : (OldWorld input before claim (OldBase := OldBase)).Support) :
    (NewWorld input depth count before claim (NewBase := NewBase)).Support :=
  (base.support.forward support.1, support.2.map LegacyLaw.State.legacy)

def supportBackward (support : (NewWorld input depth count before claim (NewBase := NewBase)).Support) :
    (OldWorld input before claim (OldBase := OldBase)).Support :=
  (base.support.backward support.1, support.2.map (LegacyLaw.backward input depth count before claim))

def supportRetract : ConstructiveRetract (OldWorld input before claim (OldBase := OldBase)).Support
    (NewWorld input depth count before claim (NewBase := NewBase)).Support where
  forward := supportForward input depth count before claim base
  backward := supportBackward input depth count before claim base
  backward_forward := by
    rintro ⟨support, state⟩
    apply Prod.ext
    · exact base.support.backward_forward support
    · cases state <;> rfl

def rowForward (support : OldBase.Support) (state : Option (LegacyLaw.oldLaw input before claim).DebtState) :
    OpenResponsibilityAt (OldWorld input before claim) (support, state) →
    OpenResponsibilityAt (NewWorld input depth count before claim)
      (supportForward input depth count before claim base (support, state)) := by
  rintro ⟨responsibility, opened⟩
  cases responsibility with
  | inl original => exact oldEntry ((base.oldOpenLedger support).forward ⟨original, opened⟩)
  | inr debt =>
      cases state with
      | none => exact opened.elim
      | some state => exact ⟨.inr debt, opened⟩

def rowBackward (support : OldBase.Support) (state : Option (LegacyLaw.oldLaw input before claim).DebtState) :
    OpenResponsibilityAt (NewWorld input depth count before claim)
      (supportForward input depth count before claim base (support, state)) →
    OpenResponsibilityAt (OldWorld input before claim) (support, state) := by
  rintro ⟨responsibility, opened⟩
  cases responsibility with
  | inl original => exact oldEntry ((base.oldOpenLedger support).backward ⟨original, opened⟩)
  | inr debt =>
      cases state with
      | none => exact opened.elim
      | some state => exact ⟨.inr debt, opened⟩

theorem row_backward_forward (support : OldBase.Support)
    (state : Option (LegacyLaw.oldLaw input before claim).DebtState)
    (entry : OpenResponsibilityAt (OldWorld input before claim) (support, state)) :
    rowBackward input depth count before claim base support state
      (rowForward input depth count before claim base support state entry) = entry := by
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl original =>
      change oldEntry ((base.oldOpenLedger support).backward
        ((base.oldOpenLedger support).forward ⟨original, opened⟩)) = _
      rw [(base.oldOpenLedger support).backward_forward]
      rfl
  | inr debt => cases state with
      | none => exact opened.elim
      | some state => rfl

def rowRetract (support : (OldWorld input before claim (OldBase := OldBase)).Support) :
    ConstructiveRetract (OpenResponsibilityAt (OldWorld input before claim) support)
      (OpenResponsibilityAt (NewWorld input depth count before claim)
        (supportForward input depth count before claim base support)) :=
  ⟨rowForward input depth count before claim base support.1 support.2,
    rowBackward input depth count before claim base support.1 support.2,
    row_backward_forward input depth count before claim base support.1 support.2⟩

def translation : TypedSemanticWorldNetworkTranslationAt
    (OldWorld input before claim (OldBase := OldBase))
    (NewWorld input depth count before claim (NewBase := NewBase)) where
  support := supportRetract input depth count before claim base
  anchor := base.anchor
  incidence := base.incidence
  lineage := base.lineage
  responsibility := sumLeft base.responsibility
  claim := sumLeft base.claim
  anchor_commutes := fun support => base.anchor_commutes support.1
  incidence_commutes := fun support => base.incidence_commutes support.1
  lineage_commutes := fun support => base.lineage_commutes support.1
  oldOpenLedger := rowRetract input depth count before claim base
  oldOpenClaim_commutes := by
    rintro ⟨support, state⟩ ⟨responsibility, opened⟩
    cases responsibility with
    | inl original => exact congrArg Sum.inl (base.oldOpenClaim_commutes support ⟨original, opened⟩)
    | inr debt => cases state with
        | none => exact opened.elim
        | some state => rfl
  oldOpenProgressBudget_commutes := by
    rintro ⟨support, state⟩ ⟨responsibility, opened⟩
    cases responsibility with
    | inl original => exact base.oldOpenProgressBudget_commutes support ⟨original, opened⟩
    | inr debt => cases state with
        | none => exact opened.elim
        | some state => rfl
  oldHoldsSurvives := by
    rintro ⟨support, state⟩ semantic held
    cases semantic with
    | inl original => exact base.oldHoldsSurvives support original held
    | inr debt => cases state with
        | none => exact held.elim
        | some state => exact held
  oldDispositionSurvives := by
    rintro ⟨support, state⟩ kind receipt
    cases kind with
    | supportSettlement => exact base.oldDispositionSurvives support .supportSettlement receipt
    | transfer =>
        cases receipt with
        | inl original => exact .inl (base.oldDispositionSurvives support .transfer original)
        | inr active =>
            cases state with
            | none => exact active.elim
            | some state =>
                cases active with
                | inl step => exact .inr (.inl ⟨.legacy step.1, .legacy step.2⟩)
                | inr transport => exact .inr (.inr ⟨.legacy transport.1, .legacy transport.2⟩)
    | lawSurfaceExtension =>
        cases receipt with
        | inl original => exact .inl (base.oldDispositionSurvives support .lawSurfaceExtension original)
        | inr active =>
            cases state with
            | none => exact active.elim
            | some state => exact .inr active

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.translation
