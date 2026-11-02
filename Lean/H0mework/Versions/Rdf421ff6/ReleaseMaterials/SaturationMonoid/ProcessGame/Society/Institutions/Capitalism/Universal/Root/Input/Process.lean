import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Input.Target

/-! One registry starts at the original Payment occurrence and continues on
the exact source-selected U8 target.  A programme's first body has already
executed at the macro successor, so its first registered target is visit two. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (datum : Datum Party Good Port Technology Instrument)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)

variable (choice : InputChoice (Party := Party) (Good := Good)
  (Port := Port) (Technology := Technology) (Instrument := Instrument))

theorem target_current_card (index : Nat) :
    Nat.card (branchPresentation oldVisit sourceIndex boundary choice index).V.Current = 0 := by
  cases choice with
  | none =>
      change Nat.card Nat = 0
      simp
  | some raw =>
      change Nat.card (ProgrammeSource.Current
        (Source.Program.RawCurrent Party Good Technology Instrument)) = 0
      let encode (n : Nat) : ProgrammeSource.Current
          (Source.Program.RawCurrent Party Good Technology Instrument) :=
        .running raw.val.initial (List.replicate n raw.val.initial)
      have injective : Function.Injective encode := by
        intro first second same
        have lengths := congrArg (fun current => (ProgrammeSource.pastAt current).length) same
        simpa [encode, ProgrammeSource.pastAt] using lengths
      let : Infinite (ProgrammeSource.Current
          (Source.Program.RawCurrent Party Good Technology Instrument)) :=
        Infinite.of_injective encode injective
      simp

theorem source_ne_target (index : Nat) :
    (presentation datum oldVisit sourceIndex boundary).erase ≠
      (branchPresentation oldVisit sourceIndex boundary choice index).erase := by
  intro same
  have cards := congrArg
    (fun erased : AnyAuthoritativeRootCurrent => Nat.card erased.current.V.Current) same
  change Nat.card Unit = Nat.card
    (branchPresentation oldVisit sourceIndex boundary choice index).V.Current at cards
  rw [target_current_card] at cards
  simp at cards

inductive RegistryState
  | source
  | target (index : Nat)

def registryPresentation : RegistryState → RootInquiryStatePresentation
  | .source => presentation datum oldVisit sourceIndex boundary
  | .target index => branchPresentation oldVisit sourceIndex boundary choice index

private def processFor (selected : selectedInput datum oldVisit sourceIndex boundary = choice) :
    SourceNativeInquiryEngineProcess.{0} where
  State := RegistryState
  stateAt := fun state => .active (registryPresentation datum oldVisit sourceIndex boundary choice state)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive same
    cases leftActive
    cases rightActive
    cases left with
    | source =>
        cases right with
        | source => rfl
        | target index => exact False.elim (source_ne_target datum oldVisit sourceIndex boundary choice index same)
    | target first =>
        cases right with
        | source => exact False.elim (source_ne_target datum oldVisit sourceIndex boundary choice first same.symm)
        | target second =>
            exact congrArg RegistryState.target
              (branch_erase_injective oldVisit sourceIndex boundary choice same)
  initial := .source
  successorAt := by
    intro state query
    cases state with
    | source =>
        change Query datum oldVisit sourceIndex boundary at query
        have unique := germ_unique datum _ query
        cases unique
        refine ⟨.target 2, ?_, ?_⟩
        · change (branchPresentation oldVisit sourceIndex boundary choice 2).erase =
            ⟨(producedRevision datum oldVisit sourceIndex boundary
              (germAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))
              ).generate.NewN,
              (TypedSemanticWorldNetworkU8Recovery.generatedNewTargetAnswerAndNext
                (producedRevision datum oldVisit sourceIndex boundary
                  (germAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))
                )).nextCurrent⟩
          unfold producedRevision
          rw [chosen_is_source_selected, selected]
          cases choice <;> rfl
        · change HEq (branchPresentation oldVisit sourceIndex boundary choice 2).state.base.root
            (producedRevision datum oldVisit sourceIndex boundary
              (germAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))
            ).generate.newLivingRoot
          unfold producedRevision
          rw [chosen_is_source_selected, selected]
          cases choice <;> exact HEq.rfl
    | target index =>
        refine ⟨.target (index + 1), ?_⟩
        change (RootInquiryProcessNode.active
          (branchPresentation oldVisit sourceIndex boundary choice index)).Query at query
        cases choice with
        | none =>
            change Unit at query
            cases query
            exact ((Legacy.processAt oldVisit sourceIndex (boundary + 1)).successorAt
              (.revised index) PUnit.unit).property
        | some raw =>
            change PUnit at query
            cases query
            exact ProgrammeInquiry.native_successor_valid raw.val index

def process : SourceNativeInquiryEngineProcess.{0} :=
  processFor datum oldVisit sourceIndex boundary
    (selectedInput datum oldVisit sourceIndex boundary) rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource
