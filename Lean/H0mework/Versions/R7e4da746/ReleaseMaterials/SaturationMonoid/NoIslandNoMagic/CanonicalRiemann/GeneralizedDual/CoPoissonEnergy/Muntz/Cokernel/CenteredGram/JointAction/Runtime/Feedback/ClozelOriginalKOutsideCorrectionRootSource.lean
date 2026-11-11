import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionChildSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKOutsideCorrectionRootSource
open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
namespace A
export ActualCofinalSourceAction (wordTransport sourceWordAction packetTransport sourceBorn actual_next_packet)
end A
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (WordAt wordMapAt)
end R
namespace Born
export OriginalKBFiniteCalculation.BornInventory (Packet packetAt)
end Born
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (native packetAdmission beforeStock sourceFrame sourceBase)
end WN
namespace NW
export NativeSigma.Writeback (admissionWord)
end NW
namespace C
export OriginalKCombReceiptFeedback (Value Var receipt forcedSourceCode forcedSourceTrace)
end C
namespace FW
export OriginalKForcedInverseSourceWriteback
  (admissions oldAdmissions jointAdmissions jointWords admissions_steps admissions_words)
end FW
namespace CW
export OriginalKPaNativeCayleySourceWriteback (admissions oldAdmissions jointAdmissions source_occurrences)
end CW
namespace Action
export OriginalKPaNativeCayleyNextAction (targetSourceFace)
end Action
namespace Child
export OriginalKOutsideCorrectionChildSource (originalChild childCode original_value)
end Child
open private reindexWord languageWord stepWord from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRSourceReceiptConsumer
open private physicalValue middleIndex middle_read mapped_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextSource
local instance levelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

/-- A fixed child address in the original operation tree; no coefficient inversion is involved. -/
private def childAt {V Y : Unit → Type} [∀ t, AddCommGroup (V t)] :
    List Bool → Expr V Y () → Expr V Y ()
  | [], expression => expression
  | side :: path, .add left right => childAt path (if side then right else left)
  | _ :: path, .linear (s := ()) _ argument => childAt path argument
  | _ :: _, _ => .const 0

private theorem child_lift {V Y : Unit → Type} [∀ t, AddCommGroup (V t)]
    (path : List Bool) (expression : Expr V Y ()) :
    childAt path (liftExpr expression) = liftExpr (childAt path expression) := by
  induction path generalizing expression with
  | nil => rfl
  | cons side path previous =>
      cases expression with
      | var => rfl
      | const => rfl
      | add left right =>
          cases side <;> exact previous _
      | @linear source operation argument =>
          cases source
          exact previous _
      | bilinear => rfl

private theorem remaining_lift {V Y : Unit → Type} [∀ t, AddCommGroup (V t)]
    {sort : Unit} (expression : Expr V Y sort) : remaining (liftExpr expression) = remaining expression := by
  induction expression <;> simp_all only [liftExpr, remaining]

private def decodeFace {V Y : Unit → Type} [∀ t, AddCommGroup (V t)]
    (budget : Nat) (path : List Bool) (expression : Expr V Y ()) : V () :=
  if remaining expression = budget then (childAt path expression).eval 0 else 0

private def decodeMap {V Y : Unit → Type} [∀ t, AddCommGroup (V t)]
    (budget : Nat) (path : List Bool) : Formal ℤ V Y () →ₗ[ℤ] V () :=
  Finsupp.linearCombination ℤ (decodeFace budget path)

private theorem decodeFace_lift {V Y : Unit → Type} [∀ t, AddCommGroup (V t)]
    (budget : Nat) (path : List Bool) (expression : Expr V Y ()) :
    decodeFace budget path (liftExpr expression) = (decodeFace budget path expression, 0) := by
  simp only [decodeFace, remaining_lift]
  split_ifs with matched
  · rw [child_lift]
    change (liftExpr (childAt path expression)).eval (pairEnvironment 0 0) = _
    rw [eval_liftExpr, Expr.effect_zero]
  · rfl

private theorem decode_lift {V Y : Unit → Type} [∀ t, AddCommGroup (V t)]
    (budget : Nat) (path : List Bool) (word : Formal ℤ V Y ()) :
    decodeMap budget path (liftMap (R := ℤ) word) = (decodeMap budget path word, 0) := by
  have maps : (decodeMap (V := PairValue V) (Y := Y) budget path).comp (liftMap (R := ℤ)) =
      (decodeMap (V := V) (Y := Y) budget path).prod 0 := by
    apply Finsupp.lhom_ext
    intro expression coefficient
    simp [decodeMap, liftMap, Finsupp.lmapDomain_apply, decodeFace_lift, Prod.smul_mk]
  exact LinearMap.congr_fun maps word

private theorem decode_language {V Y Z : Unit → Type} [∀ t, AddCommGroup (V t)]
    (budget : Nat) (path : List Bool) (same : Y = Z) (word : Formal ℤ V Y ()) :
    decodeMap budget path (A.wordTransport same word) = decodeMap budget path word := by
  cases same
  rfl

variable (budget : Nat) (path : List Bool)

private theorem physical_reindex {first second : Born.Packet C.Var} (same : first = second)
    (word : R.WordAt first) :
    physicalValue second.1 (decodeMap budget path (reindexWord same word)) =
      physicalValue first.1 (decodeMap budget path word) := by
  cases same
  rfl

private theorem physical_language {Y Z : Unit → Type} (same : Y = Z)
    (packet : Born.Packet Y) (word : R.WordAt packet) :
    physicalValue (A.packetTransport same packet).1 (decodeMap budget path (languageWord same packet word)) =
      physicalValue packet.1 (decodeMap budget path word) := by
  cases same
  rfl

private theorem physical_action (packet : Born.Packet C.Var) (word : R.WordAt packet) :
    physicalValue (packet.1 + 1) (decodeMap budget path (A.sourceWordAction packet word)) =
      physicalValue packet.1 (decodeMap budget path word) := by
  change Formal ℤ (L.Value (PairValue C.Value) packet.1) C.Var () at word
  change physicalValue (packet.1 + 1)
    (decodeMap budget path (V := PairValue (L.Value (PairValue C.Value) packet.1))
      (A.wordTransport (Value := PairValue (L.Value (PairValue C.Value) packet.1))
        packet.2.2.2.down.symm
        (liftMap (R := ℤ) (Value := L.Value (PairValue C.Value) packet.1) word))) = _
  calc
    _ = physicalValue (packet.1 + 1) (decodeMap budget path (liftMap (R := ℤ) (Value := L.Value (PairValue C.Value) packet.1) word)) :=
      congrArg (physicalValue (packet.1 + 1))
        (decode_language (V := PairValue (L.Value (PairValue C.Value) packet.1)) budget path
          packet.2.2.2.down.symm
          (liftMap (R := ℤ) (Value := L.Value (PairValue C.Value) packet.1) word))
    _ = physicalValue (packet.1 + 1)
        (decodeMap budget path (V := L.Value (PairValue C.Value) packet.1) word,
          (0 : L.Value (PairValue C.Value) packet.1 ())) :=
      congrArg (physicalValue (packet.1 + 1))
        (decode_lift (V := L.Value (PairValue C.Value) packet.1) budget path word)
    _ = _ := by
      change physicalValue packet.1
        (decodeMap budget path (V := L.Value (PairValue C.Value) packet.1) word +
          (0 : L.Value (PairValue C.Value) packet.1 ())) = _
      rw [add_zero]

private theorem physical_grade_cast (old fresh : Nat) (same : fresh = old + 1)
    (word : Formal ℤ (PairValue (L.Value (PairValue C.Value) old)) C.Var ()) :
    physicalValue fresh (decodeMap budget path
      ((Eq.mp (congrArg (fun grade =>
        Formal ℤ (PairValue (L.Value (PairValue C.Value) old)) C.Var () →ₗ[ℤ]
          Formal ℤ (L.Value (PairValue C.Value) grade) C.Var ()) same.symm) LinearMap.id) word)) =
      physicalValue old ((decodeMap budget path word).1 + (decodeMap budget path word).2) := by
  cases same
  rfl

private theorem physical_admission (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
    (word : Formal ℤ (PairValue (L.Value (PairValue C.Value) packet.1)) C.Var ()) :
    physicalValue (AS.nativeAfterAdmission factory packet).1
        (decodeMap budget path (NW.admissionWord factory packet word)) =
      physicalValue packet.1 ((decodeMap budget path word).1 + (decodeMap budget path word).2) :=
  physical_grade_cast budget path packet.1 (AS.nativeAfterAdmission factory packet).1
    (AS.nativeAfterAdmission_grade factory packet) word

private theorem physical_born_language (native : NativeSigma.NativePacket)
    (word : Formal ℤ (L.Value (PairValue C.Value) native.1) C.Var ()) :
    physicalValue (AS.bornAfterNative native).1
        (decodeMap budget path (A.wordTransport (AS.bornAfterNative native).2.2.2.down.symm word)) =
      physicalValue native.1 (decodeMap budget path word) :=
  congrArg (physicalValue native.1)
    (decode_language (V := L.Value (PairValue C.Value) native.1) budget path
      (AS.bornAfterNative native).2.2.2.down.symm word)

private theorem physical_native_word (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
    (word : Formal ℤ (L.Value (PairValue C.Value) packet.1) C.Var ()) :
    physicalValue (AS.bornAfterNative (AS.nativeAfterAdmission factory packet)).1
        (decodeMap budget path (A.wordTransport
          (AS.bornAfterNative (AS.nativeAfterAdmission factory packet)).2.2.2.down.symm
          (NW.admissionWord factory packet
            (liftMap (R := ℤ) (Value := L.Value (PairValue C.Value) packet.1) word)))) =
      physicalValue packet.1 (decodeMap budget path word) := by
  refine (physical_born_language budget path (AS.nativeAfterAdmission factory packet) _).trans
    ((physical_admission budget path factory packet _).trans ?_)
  apply congrArg (physicalValue packet.1)
  exact (congrArg (fun point : PairValue (L.Value (PairValue C.Value) packet.1) () => point.1 + point.2)
    (decode_lift (V := L.Value (PairValue C.Value) packet.1) budget path word)).trans (add_zero _)



private theorem first_word_decode {V Y : Unit → Type} [∀ t, AddCommGroup (V t)]
    {environment : Env V Y} {raw last : Expr V Y ()}
    (path : List Bool) (trace : Trace environment raw last)
    (positive : 0 < (SourceOperationPaidRelations.words trace).length) :
    decodeMap (remaining raw) path
      ((SourceOperationPaidRelations.words trace).get ⟨0, positive⟩) =
      (childAt path raw).eval 0 := by
  cases trace with
  | nil => simp [SourceOperationPaidRelations.words] at positive
  | @cons raw middle last step tail =>
      have different : remaining middle ≠ remaining raw := by
        have decreases := step.remaining_eq
        omega
      simp [SourceOperationPaidRelations.words, relation, decodeMap, decodeFace, different]

private def correctionPath : List Bool :=
  [false, false, false, false, false, false, false, false, false, false,
    true, false, false, false]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "factory" => OriginalKCombFirstFullSourceDynamics.factory observation nontrivial half
local notation "packet" => Born.packetAt observation nontrivial half depth
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "raw" => C.forcedSourceCode observation nontrivial depth half
local notation "trace" => C.forcedSourceTrace observation nontrivial depth half

private theorem physical_word (budget : Nat) (path : List Bool)
    (word : Formal ℤ C.Value C.Var ()) (tick : Nat) :
    physicalValue (packet tick).1
      (decodeMap budget path (R.wordMapAt observation nontrivial half depth tick word)) =
      decodeMap budget path word := by
  induction tick with
  | zero =>
      change physicalValue 0 (decodeMap budget path (liftMap (R := ℤ) word)) = _
      exact (congrArg (physicalValue 0) (decode_lift budget path word)).trans (add_zero _)
  | succ tick previous =>
      exact (physical_reindex budget path
        (A.actual_next_packet factory (OriginalKCombFirstFullSourceDynamics.initial observation nontrivial half depth)
          (OriginalKCombFirstFullSourceDynamics.firstCfg observation nontrivial half depth) rfl tick).symm
        (stepWord observation nontrivial half (packet tick)
          (R.wordMapAt observation nontrivial half depth tick word))).trans
        ((physical_language budget path (packet tick).2.2.2.down (A.sourceBorn factory (packet tick))
          (A.sourceWordAction (packet tick) (R.wordMapAt observation nontrivial half depth tick word))).trans
          ((physical_action budget path (packet tick)
            (R.wordMapAt observation nontrivial half depth tick word)).trans previous))

attribute [local irreducible] physicalValue AS.nativeAfterAdmission

def rootAdmissions : type_of% (CW.admissions observation nontrivial half depth ordinal) :=
  (Action.targetSourceFace observation nontrivial half depth ordinal).rootRead.source.occurrences

theorem rootAdmissions_source : rootAdmissions observation nontrivial half depth ordinal =
    CW.admissions observation nontrivial half depth ordinal :=
  CW.source_occurrences observation nontrivial half depth ordinal

attribute [local irreducible] rootAdmissions

private def laterAdmissions :=
  OriginalKReturnJetStepSourceWriteback.jointAdmissions observation nontrivial half depth ordinal ++
    OriginalKPaNativePortSourceWriteback.jointAdmissions observation nontrivial half depth ordinal ++
    CW.jointAdmissions observation nontrivial half depth ordinal

private theorem rootAdmissions_ordered : rootAdmissions observation nontrivial half depth ordinal =
    FW.oldAdmissions observation nontrivial half depth ordinal ++ [] ++
      FW.jointAdmissions observation nontrivial half depth ordinal ++
        laterAdmissions observation nontrivial half depth ordinal := by
  refine (rootAdmissions_source observation nontrivial half depth ordinal).trans ?_
  simp only [CW.admissions, CW.oldAdmissions,
    OriginalKPaNativePortSourceWriteback.admissions, OriginalKPaNativePortSourceWriteback.oldAdmissions,
    OriginalKReturnJetStepSourceWriteback.admissions, OriginalKReturnJetStepSourceWriteback.oldAdmissions,
    FW.admissions, laterAdmissions, List.append_nil, List.append_assoc]

/-- Original forcing Step zero, retaining its exact admission slot through every later append. -/
def rootSlot : Fin (rootAdmissions observation nontrivial half depth ordinal).length :=
  middleIndex (rootAdmissions observation nontrivial half depth ordinal)
    (FW.oldAdmissions observation nontrivial half depth ordinal) []
    (FW.jointAdmissions observation nontrivial half depth ordinal)
    (laterAdmissions observation nontrivial half depth ordinal)
    (rootAdmissions_ordered observation nontrivial half depth ordinal)
    (FW.admissions_steps observation nontrivial half depth ordinal).2

def rootAdmission : type_of%
    ((FW.jointAdmissions observation nontrivial half depth ordinal).get
      ⟨0, (FW.admissions_steps observation nontrivial half depth ordinal).2⟩) :=
  (rootAdmissions observation nontrivial half depth ordinal).get
    (rootSlot observation nontrivial half depth ordinal)

theorem rootAdmission_source : rootAdmission observation nontrivial half depth ordinal =
    (FW.jointAdmissions observation nontrivial half depth ordinal).get
      ⟨0, (FW.admissions_steps observation nontrivial half depth ordinal).2⟩ :=
  middle_read (rootAdmissions observation nontrivial half depth ordinal)
    (FW.oldAdmissions observation nontrivial half depth ordinal) []
    (FW.jointAdmissions observation nontrivial half depth ordinal)
    (laterAdmissions observation nontrivial half depth ordinal)
    (rootAdmissions_ordered observation nontrivial half depth ordinal)
    (FW.admissions_steps observation nontrivial half depth ordinal).2

/-- The complete correction is read from this root's existing original operation word. -/
def correctionValue : BurnolL2 :=
  physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining raw) correctionPath
      (rootAdmission observation nontrivial half depth ordinal).1.word)

private theorem correction_child_syntax : childAt correctionPath raw =
    Child.childCode observation nontrivial half depth 1 := rfl

private theorem correction_child_read : (childAt correctionPath raw).eval 0 =
    (Child.originalChild observation nontrivial half depth).1 := by
  rw [correction_child_syntax]
  exact (Child.originalChild observation nontrivial half depth).2.sound

theorem correction_value_source : correctionValue observation nontrivial half depth ordinal =
    (Child.originalChild observation nontrivial half depth).1 := by
  have positive : 0 < (SourceOperationPaidRelations.words trace).length := by
    rw [SourceOperationPaidRelations.complete_steps, (trace).length_to_const]
    change 0 < _ + 1
    omega
  let index : OriginalKForcedInverseSourceOccurrences.Index observation nontrivial half depth := ⟨0, positive⟩
  let originalWord : Formal ℤ C.Value C.Var () := (SourceOperationPaidRelations.words trace).get index
  have word := (congrArg (fun admitted => admitted.1.word)
    (rootAdmission_source observation nontrivial half depth ordinal)).trans
    (mapped_read (FW.jointAdmissions observation nontrivial half depth ordinal)
      (fun admitted => admitted.1.word) (FW.jointWords observation nontrivial half depth ordinal)
      (FW.admissions_words observation nontrivial half depth ordinal)
      (FW.admissions_steps observation nontrivial half depth ordinal).2)
  refine (congrArg (fun item => physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining raw) correctionPath item)) word).trans ?_
  simp only [FW.jointWords, List.get_ofFn]
  refine (physical_native_word (remaining raw) correctionPath factory (packet (ordinal+1))
    (R.wordMapAt observation nontrivial half depth (ordinal+1) originalWord)).trans ?_
  refine (physical_word observation nontrivial half depth (remaining raw) correctionPath originalWord (ordinal+1)).trans ?_
  exact (first_word_decode correctionPath trace positive).trans
    (correction_child_read observation nontrivial half depth)

/-- The endpoint changes by the proved dependent read; the history is the original child. -/
def correctionTrace : Trace (C.receipt observation nontrivial depth half).1.environment
    (Child.childCode observation nontrivial half depth 1)
    (.const (correctionValue observation nontrivial half depth ordinal)) :=
  Eq.mp (congrArg (fun point => Trace (C.receipt observation nontrivial depth half).1.environment
    (Child.childCode observation nontrivial half depth 1) (.const point))
      (correction_value_source observation nontrivial half depth ordinal).symm)
    (Child.originalChild observation nontrivial half depth).2

theorem correctionTrace_heq : HEq (correctionTrace observation nontrivial half depth ordinal)
    (Child.originalChild observation nontrivial half depth).2 := cast_heq _ _

theorem correction_value : correctionValue observation nontrivial half depth ordinal =
    OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) :=
  (correction_value_source observation nontrivial half depth ordinal).trans
    (Child.original_value observation nontrivial half depth)

end OriginalKOutsideCorrectionRootSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKOutsideCorrectionRootSource"
