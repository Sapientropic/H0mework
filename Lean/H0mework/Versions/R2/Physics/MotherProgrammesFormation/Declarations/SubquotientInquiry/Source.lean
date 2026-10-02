import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Subquotient.Formation

/-! Source-formed subquotient queries enter a coface of the original complete
physical source. The internal preparation checks descent of the entire old
query; complete old compilations remain in `oldCompiler`, outside the
low-universe projection payload. -/

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotientInquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision MotherFamilyOccurrence
open scoped Classical

noncomputable section

abbrev Base := MotherSubquotient.Base
abbrev Material := MotherSubquotient.Material

structure Input where
  material : Material
  index : Base
  typeLaw : Base
  actionLaw : Base

abbrev Query (input : Input) := MotherSubquotient.Fiber input.material input.index

def Compatible (input : Input) : Prop :=
  ∀ left right : { value : Base // MotherSubquotient.predicate input.material input.index value },
    MotherSubquotient.relation input.material input.index left.val right.val →
    MotherOriginalQueryValue.readQuery left.val = MotherOriginalQueryValue.readQuery right.val

abbrev Ready := { input : Input // Compatible input }

def prepare (input : Input) : Option Ready :=
  if compatible : Compatible input then some ⟨input, compatible⟩ else none

theorem prepare_recovers (ready : Ready) : prepare ready.val = some ready :=
  dif_pos ready.property

theorem prepare_rejects (input : Input) (incompatible : ¬ Compatible input) :
    prepare input = none := dif_neg incompatible

def decode (ready : Ready) : Query ready.val → MotherOriginalQueryValue.Query :=
  Quot.lift (fun value => MotherOriginalQueryValue.readQuery value.val) ready.property

theorem decode_rep (ready : Ready) (value : Base)
    (inside : MotherSubquotient.predicate ready.val.material ready.val.index value) :
    decode ready (Quot.mk _ ⟨value, inside⟩) = MotherOriginalQueryValue.readQuery value := rfl

theorem compatible_iff_compileDescends (input : Input) (parent : MotherVisit) :
    Compatible input ↔ MotherSubquotient.compileDescends
      input.material input.index input.typeLaw input.actionLaw parent := by
  constructor
  · intro compatible left right related
    exact congrArg (fun query => (⟨query,
      (MotherNativePhysicalQuery.nativeInquiry input.typeLaw input.actionLaw parent).compileInquiry query⟩ :
      MotherSubquotient.OriginalOutput input.typeLaw input.actionLaw parent))
      (compatible left right related)
  · intro descends left right related
    exact congrArg Sigma.fst (descends left right related)

def oldCompiler (ready : Ready) (parent : MotherVisit) (query : Query ready.val) :
    MotherSubquotient.OriginalOutput ready.val.typeLaw ready.val.actionLaw parent :=
  ⟨decode ready query,
    (MotherNativePhysicalQuery.nativeInquiry ready.val.typeLaw ready.val.actionLaw parent).compileInquiry
      (decode ready query)⟩

theorem oldCompiler_is_formed (ready : Ready) (parent : MotherVisit) :
    MotherSubquotient.compile ready.val.material ready.val.index
      ready.val.typeLaw ready.val.actionLaw parent = some (oldCompiler ready parent) := by
  have descends := (compatible_iff_compileDescends ready.val parent).mp ready.property
  unfold MotherSubquotient.compile
  rw [dif_pos descends]
  apply congrArg some
  funext query
  induction query using Quot.inductionOn with
  | h value => rfl

theorem oldCompiler_rep (ready : Ready) (parent : MotherVisit) (value : Base)
    (inside : MotherSubquotient.predicate ready.val.material ready.val.index value) :
    oldCompiler ready parent (Quot.mk _ ⟨value, inside⟩) =
      MotherOriginalQueryValue.compileRead ready.val.typeLaw ready.val.actionLaw parent value := rfl

abbrev source := MotherNativePhysicalQuery.source
abbrev Anchor := MotherNativePhysicalQuery.Anchor
abbrev Key (ready : Ready) := Anchor × Query ready.val
abbrev Answer (ready : Ready) := Query ready.val × MotherNativePhysicalQuery.Answer

def answer (ready : Ready) (query : Query ready.val) : Answer ready :=
  (query, MotherNativePhysicalQuery.answer ready.val.typeLaw ready.val.actionLaw (decode ready query))

def projectionLaw (ready : Ready) : SourceNativeProjectionLaw source where
  Projection := Key ready × Fin 3
  ActiveAt := fun projection {current} occurrence => PLift (projection.1.1 = ⟨current, occurrence⟩)
  InactiveAt := fun projection {current} occurrence => PLift (projection.1.1 ≠ ⟨current, occurrence⟩)
  classify := fun projection {current} occurrence =>
    if same : projection.1.1 = ⟨current, occurrence⟩ then .inl ⟨same⟩ else .inr ⟨same⟩
  PayloadAt := fun projection {current} occurrence _ =>
    match projection.2 with
    | 0 => Answer ready
    | 1 => SourceNativeInquiryAnswerConsumerTokenAt projection.1.2
        (ULift.up.{1, 0} occurrence) (materialEntry (SpinPair.support current)) (answer ready projection.1.2)
    | _ => SourceNativeInquiryCompilationTokenAt
        (U7 := materialU7) (calculus := materialInquiryCalculus)
        (oldTheory := TheoryState.rootSemantic MaterialN)
        (materialEntry (SpinPair.support current)) projection.1.2
        (ULift.up.{1, 0} occurrence) .answered (Answer ready)
  project := fun projection {_current} _occurrence _ => by
    rcases projection with ⟨key, tag⟩
    split
    · exact answer ready key.2
    · exact .canonical
    · exact .canonical (answer ready key.2)

def declarationSource (ready : Ready) : SourceNativeAuthoritySource MaterialN SpinPair.V :=
  (MotherNativePhysicalQuery.declarationSource ready.val.typeLaw ready.val.actionLaw).withProjectionCoface
    (projectionLaw ready)

def queryInstallation (ready : Ready) :
    SourceNativeProjectionLaw.InstallationAt (projectionLaw ready) (declarationSource ready).projectionLaw :=
  .componentCoface (MotherNativePhysicalQuery.declarationSource ready.val.typeLaw ready.val.actionLaw)
    (projectionLaw ready)

def originalQueryInstallation (ready : Ready) :
    SourceNativeProjectionLaw.InstallationAt
      (MotherNativePhysicalQuery.declarationSource ready.val.typeLaw ready.val.actionLaw).projectionLaw
      (declarationSource ready).projectionLaw :=
  .inheritedCoface (MotherNativePhysicalQuery.declarationSource ready.val.typeLaw ready.val.actionLaw)
    (projectionLaw ready)

def physicsInstallation (ready : Ready) :
    SourceNativeProjectionLaw.InstallationAt SpinPair.authoritativeRoot.source.projectionLaw
      (declarationSource ready).projectionLaw :=
  (MotherNativePhysicalQuery.physicsInstallation ready.val.typeLaw ready.val.actionLaw).trans
    (originalQueryInstallation ready)

theorem original_restructuringSource_preserved (ready : Ready) :
    (declarationSource ready).restructuringSource = SpinPair.authoritativeRoot.source.restructuringSource := rfl

theorem original_ledgerSource_preserved (ready : Ready) :
    (declarationSource ready).restructuringSource.toLedgerSource = source := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotientInquiry
