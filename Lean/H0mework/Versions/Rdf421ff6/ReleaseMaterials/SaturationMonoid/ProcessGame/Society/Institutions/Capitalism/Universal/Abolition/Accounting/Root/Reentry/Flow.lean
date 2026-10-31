import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

private theorem cast_keys {N : WorldRelationNetwork} {first second target : CompleteLiveLedgerAt N}
    (same : first = second) (evolution : LedgerWriteEvolutionAt N first target)
    (keys : Financial.Installation.KeepsKeys evolution) :
    Financial.Installation.KeepsKeys
      (Eq.mp (congrArg (fun source => LedgerWriteEvolutionAt N source target) same) evolution) := by
  cases same
  exact keys

private theorem transport_keys {N : WorldRelationNetwork} {law : DebtActivationLaw}
    (support : N.Support) {source target : law.DebtState} (event : law.TransportAt source target) :
    Financial.Installation.KeepsKeys (transportLedgerEvolution support event) := by
  constructor <;> rintro ⟨responsibility,opened⟩ <;> cases responsibility with
  | inl old => rfl
  | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl

private def activeEntryEquiv {base : WorldRelationNetwork} {law : DebtActivationLaw}
    (support : base.Support) (source target : law.DebtState) :
    OpenResponsibilityAt (ExtendedNetwork base law) (support,some source) ≃
      OpenResponsibilityAt (ExtendedNetwork base law) (support,some target) where
  toFun := by
    rintro ⟨responsibility,opened⟩
    cases responsibility with
    | inl old => exact ⟨.inl old,opened⟩
    | inr debt => exact ⟨.inr debt,opened⟩
  invFun := by
    rintro ⟨responsibility,opened⟩
    cases responsibility with
    | inl old => exact ⟨.inl old,opened⟩
    | inr debt => exact ⟨.inr debt,opened⟩
  left_inv := by rintro ⟨responsibility,opened⟩; cases responsibility <;> rfl
  right_inv := by rintro ⟨responsibility,opened⟩; cases responsibility <;> rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Frame (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

local notation "N" => ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)

def support : Bool → (N).Support
  | false => Frame.support claim frame
  | true => ((Frame.support claim frame).1,some (Frame.updated claim frame word))

theorem sourceLedgerEq : (⟨Frame.support claim frame⟩ : CompleteLiveLedgerAt N) =
    activeLedger (Frame.support claim frame).1 (Frame.state claim frame) :=
  congrArg CompleteLiveLedgerAt.mk (Frame.support_eq claim frame)

def actualEvolution : LedgerWriteEvolutionAt N ⟨support claim frame word false⟩ ⟨support claim frame word true⟩ :=
  Eq.mp (congrArg (fun source => LedgerWriteEvolutionAt N source ⟨support claim frame word true⟩)
    (sourceLedgerEq claim frame).symm)
    (transportLedgerEvolution (Frame.support claim frame).1
      (Responsibility.Family.CarryAt.actual (Frame.state claim frame) frame.actualLaw word))

theorem actual_keeps_every_original_responsibility_key : Financial.Installation.KeepsKeys (actualEvolution claim frame word) :=
  cast_keys (sourceLedgerEq claim frame).symm _ (transport_keys _ _)

def evolution : (phase : Bool) → LedgerWriteEvolutionAt N ⟨support claim frame word phase⟩
    ⟨support claim frame word true⟩
  | false => actualEvolution claim frame word
  | true => LedgerWriteEvolutionAt.identity _

def entries : OpenResponsibilityAt N (Frame.support claim frame) ≃
    OpenResponsibilityAt N (support claim frame word true) := by
  let source : OpenResponsibilityAt N (Frame.support claim frame) ≃
      OpenResponsibilityAt N ((Frame.support claim frame).1,some (Frame.state claim frame)) :=
    Equiv.cast (congrArg (OpenResponsibilityAt N) (Frame.support_eq claim frame))
  exact source.trans (activeEntryEquiv (base := oldN) (law := Responsibility.Family.activationLaw claim) (Frame.support claim frame).1 (Frame.state claim frame) (Frame.updated claim frame word))

theorem entries_finite (phase : Bool) : Finite (OpenResponsibilityAt N (support claim frame word phase)) := by
  cases phase with
  | false => exact frame.finite
  | true =>
      exact @Finite.of_equiv (OpenResponsibilityAt N (support claim frame word true))
        (OpenResponsibilityAt N (Frame.support claim frame)) frame.finite (entries claim frame word)

def flow : Compiler.Flow N where
  Current := Bool
  initial := false
  support := support claim frame word
  next := fun _ => true
  writes := fun phase => !phase
  evolution := evolution claim frame word
  finite := entries_finite claim frame word
  injective := by
    intro phase
    cases phase with
    | false =>
      have keys := actual_keeps_every_original_responsibility_key claim frame word
      exact ⟨Financial.Installation.keys_imply_origin_injective _ keys frame.open_fibres,
        Financial.Installation.keys_imply_destination_injective _ keys frame.open_fibres⟩
    | true => exact ⟨Function.injective_id,Function.injective_id⟩
  open_fibres := frame.open_fibres

abbrev V := Compiler.V (flow claim frame word)
abbrev baseRoot := Compiler.livingRoot (flow claim frame word)

def previousInquiry : SourceNativeProjectionLaw (Compiler.ledgerSource (flow claim frame word)) where
  Projection := frame.root.toAuthoritativeRoot.source.projectionLaw.Projection
  ActiveAt := fun projection {_} _ => frame.root.toAuthoritativeRoot.source.projectionLaw.ActiveAt projection
    (frame.root.emitted frame.visit.current)
  InactiveAt := fun projection {_} _ => frame.root.toAuthoritativeRoot.source.projectionLaw.InactiveAt projection
    (frame.root.emitted frame.visit.current)
  classify := fun projection {_} _ => frame.root.toAuthoritativeRoot.source.projectionLaw.classify projection
    (frame.root.emitted frame.visit.current)
  PayloadAt := fun projection {_} _ active => frame.root.toAuthoritativeRoot.source.projectionLaw.PayloadAt projection
    (frame.root.emitted frame.visit.current) active
  project := fun projection {_} _ active => frame.root.toAuthoritativeRoot.source.projectionLaw.project projection
    (frame.root.emitted frame.visit.current) active

def root := (baseRoot claim frame word).withProjectionCoface (previousInquiry claim frame word)

def oldProjection (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    (root claim frame word).toAuthoritativeRoot.source.projectionLaw.Projection := .component projection

theorem oldProjection_injective : Function.Injective (oldProjection claim frame word) := by
  intro left right same
  injection same

theorem every_old_query_is_preserved (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((root claim frame word).toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (oldProjection claim frame word projection) ((root claim frame word).emitted false))
      (frame.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (frame.root.emitted frame.visit.current)) := by
  dsimp only [root,SourceNativeLivingRootClosure.withProjectionCoface,
    SourceNativeLivingRootClosure.toAuthoritativeRoot,SourceNativeAuthoritySource.withProjectionCoface,
    SourceNativeProjectionLaw.outcomeAt,oldProjection,previousInquiry]
  cases frame.root.source.base.projectionLaw.classify projection (frame.root.emitted frame.visit.current) <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry
