import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleySourceWriteback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word.Reentry.Splice

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativeCayleyNextSource
open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
namespace CW
export OriginalKPaNativeCayleySourceWriteback
  (generatedAction nextFace admissions oldAdmissions fieldAdmissions jointAdmissions admissions_steps
   source_occurrences actualValue actual_value_runtime fieldWords field_admissions_words)
end CW
namespace C
export OriginalKCombReceiptFeedback (Value Var receipt paNativeCayleySourceCode paNativeCayleySourceTrace)
end C
namespace Born
export OriginalKBFiniteCalculation.BornInventory (Packet packetAt)
end Born
namespace A
export ActualCofinalSourceAction (wordTransport sourceWordAction packetTransport sourceBorn actual_next_packet)
end A
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (WordAt wordMapAt)
end R
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (native packetAdmission packet_admission_word beforeStock sourceFrame sourceBase)
end WN
namespace NW
export NativeSigma.Writeback (admissionWord)
end NW
namespace PO
export OriginalKPaNativeCayleySourceOccurrences (Index actualOccurrence actual_word)
end PO
open private reindexWord languageWord stepWord from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRSourceReceiptConsumer
local instance levelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

private def terminalFace {V Y : Unit → Type} [∀ t, AddCommGroup (V t)] : Expr V Y () → V ()
  | .const point => -point
  | _ => 0

private def terminalMap {V Y : Unit → Type} [∀ t, AddCommGroup (V t)] :
    Formal ℤ V Y () →ₗ[ℤ] V () := Finsupp.linearCombination ℤ terminalFace

private theorem terminal_lift {V Y : Unit → Type} [∀ t, AddCommGroup (V t)]
    (word : Formal ℤ V Y ()) :
    terminalMap (liftMap (R := ℤ) word) = (terminalMap word, 0) := by
  have maps : (terminalMap (V := PairValue V) (Y := Y)).comp (liftMap (R := ℤ)) =
      (terminalMap (V := V) (Y := Y)).prod 0 := by
    apply Finsupp.lhom_ext
    intro expression coefficient
    cases expression <;>
      simp [terminalMap, terminalFace, liftMap, liftExpr, Finsupp.lmapDomain_apply] <;> rfl
  exact LinearMap.congr_fun maps word

private theorem terminal_language {V Y Z : Unit → Type} [∀ t, AddCommGroup (V t)]
    (same : Y = Z) (word : Formal ℤ V Y ()) :
    terminalMap (A.wordTransport same word) = terminalMap word := by
  cases same
  rfl

private def physicalValue : (grade : Nat) → L.Value (PairValue C.Value) grade () → BurnolL2
  | 0, point => point.1 + point.2
  | grade + 1, point =>
      letI : AddCommGroup (L.Value (PairValue C.Value) grade ()) := L.groups (PairValue C.Value) grade ()
      physicalValue grade
        ((show L.Value (PairValue C.Value) grade () from point.1) +
          (show L.Value (PairValue C.Value) grade () from point.2))

private theorem physical_reindex {first second : Born.Packet C.Var} (same : first = second)
    (word : R.WordAt first) :
    physicalValue second.1 (terminalMap (reindexWord same word)) =
      physicalValue first.1 (terminalMap word) := by
  cases same
  rfl

private theorem physical_language {Y Z : Unit → Type} (same : Y = Z)
    (packet : Born.Packet Y) (word : R.WordAt packet) :
    physicalValue (A.packetTransport same packet).1 (terminalMap (languageWord same packet word)) =
      physicalValue packet.1 (terminalMap word) := by
  cases same
  rfl

private theorem physical_action (packet : Born.Packet C.Var) (word : R.WordAt packet) :
    physicalValue (packet.1 + 1) (terminalMap (A.sourceWordAction packet word)) =
      physicalValue packet.1 (terminalMap word) := by
  change Formal ℤ (L.Value (PairValue C.Value) packet.1) C.Var () at word
  change physicalValue (packet.1 + 1)
    (terminalMap (V := PairValue (L.Value (PairValue C.Value) packet.1))
      (A.wordTransport (Value := PairValue (L.Value (PairValue C.Value) packet.1))
        packet.2.2.2.down.symm
        (liftMap (R := ℤ) (Value := L.Value (PairValue C.Value) packet.1) word))) = _
  calc
    _ = physicalValue (packet.1 + 1) (terminalMap (liftMap (R := ℤ) (Value := L.Value (PairValue C.Value) packet.1) word)) :=
      congrArg (physicalValue (packet.1 + 1))
        (terminal_language (V := PairValue (L.Value (PairValue C.Value) packet.1))
          packet.2.2.2.down.symm
          (liftMap (R := ℤ) (Value := L.Value (PairValue C.Value) packet.1) word))
    _ = physicalValue (packet.1 + 1)
        (terminalMap (V := L.Value (PairValue C.Value) packet.1) word,
          (0 : L.Value (PairValue C.Value) packet.1 ())) :=
      congrArg (physicalValue (packet.1 + 1))
        (terminal_lift (V := L.Value (PairValue C.Value) packet.1) word)
    _ = _ := by
      change physicalValue packet.1
        (terminalMap (V := L.Value (PairValue C.Value) packet.1) word +
          (0 : L.Value (PairValue C.Value) packet.1 ())) = _
      rw [add_zero]

private theorem physical_grade_cast (old fresh : Nat) (same : fresh = old + 1)
    (word : Formal ℤ (PairValue (L.Value (PairValue C.Value) old)) C.Var ()) :
    physicalValue fresh (terminalMap
      ((Eq.mp (congrArg (fun grade =>
        Formal ℤ (PairValue (L.Value (PairValue C.Value) old)) C.Var () →ₗ[ℤ]
          Formal ℤ (L.Value (PairValue C.Value) grade) C.Var ()) same.symm) LinearMap.id) word)) =
      physicalValue old ((terminalMap word).1 + (terminalMap word).2) := by
  cases same
  rfl

private theorem physical_admission (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
    (word : Formal ℤ (PairValue (L.Value (PairValue C.Value) packet.1)) C.Var ()) :
    physicalValue (AS.nativeAfterAdmission factory packet).1
        (terminalMap (NW.admissionWord factory packet word)) =
      physicalValue packet.1 ((terminalMap word).1 + (terminalMap word).2) :=
  physical_grade_cast packet.1 (AS.nativeAfterAdmission factory packet).1
    (AS.nativeAfterAdmission_grade factory packet) word

private theorem physical_born_language (native : NativeSigma.NativePacket)
    (word : Formal ℤ (L.Value (PairValue C.Value) native.1) C.Var ()) :
    physicalValue (AS.bornAfterNative native).1
        (terminalMap (A.wordTransport (AS.bornAfterNative native).2.2.2.down.symm word)) =
      physicalValue native.1 (terminalMap word) :=
  congrArg (physicalValue native.1)
    (terminal_language (V := L.Value (PairValue C.Value) native.1)
      (AS.bornAfterNative native).2.2.2.down.symm word)

private theorem physical_native_word (factory : NativeSigma.NativeFactory) (packet : NativeSigma.NativePacket)
    (word : Formal ℤ (L.Value (PairValue C.Value) packet.1) C.Var ()) :
    physicalValue (AS.bornAfterNative (AS.nativeAfterAdmission factory packet)).1
        (terminalMap (A.wordTransport
          (AS.bornAfterNative (AS.nativeAfterAdmission factory packet)).2.2.2.down.symm
          (NW.admissionWord factory packet
            (liftMap (R := ℤ) (Value := L.Value (PairValue C.Value) packet.1) word)))) =
      physicalValue packet.1 (terminalMap word) := by
  refine (physical_born_language (AS.nativeAfterAdmission factory packet) _).trans
    ((physical_admission factory packet _).trans ?_)
  apply congrArg (physicalValue packet.1)
  exact (congrArg (fun point : PairValue (L.Value (PairValue C.Value) packet.1) () => point.1 + point.2)
    (terminal_lift (V := L.Value (PairValue C.Value) packet.1) word)).trans (add_zero _)

private def middleIndex {α : Type} (all old left middle right : List α)
    (ordered : all = old ++ left ++ middle ++ right) (positive : 0 < middle.length) : Fin all.length :=
  ⟨old.length + left.length, by
    have lengths := congrArg List.length ordered
    simp only [List.length_append] at lengths
    omega⟩

private theorem middle_read {α : Type} (all old left middle right : List α)
    (ordered : all = old ++ left ++ middle ++ right) (positive : 0 < middle.length) :
    all.get (middleIndex all old left middle right ordered positive) = middle.get ⟨0, positive⟩ := by
  simp only [List.get_eq_getElem, middleIndex]
  simp [ordered, List.getElem_append_right]
  exact (List.getElem_append_left' positive right).symm

private theorem one_read_sum {α : Type} [AddCommMonoid α] (items : List α) (one : items.length = 1)
    (index : Fin items.length) : items.get index = items.sum := by
  cases items with
  | nil => simp at one
  | cons head tail =>
      cases tail with
      | nil => simp
      | cons second tail => simp at one

private theorem mapped_read {α β : Type} (items : List α) (f : α → β) (words : List β)
    (same : items.map f = words) (positive : 0 < items.length) :
    f (items.get ⟨0, positive⟩) = words.get ⟨0, by rw [← same, List.length_map]; exact positive⟩ := by
  subst words
  simp [List.get_eq_getElem]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "factory" => OriginalKCombFirstFullSourceDynamics.factory observation nontrivial half
local notation "packet" => Born.packetAt observation nontrivial half depth
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "trace" => C.paNativeCayleySourceTrace observation nontrivial depth half

private theorem physical_word (word : Formal ℤ C.Value C.Var ()) (tick : Nat) :
    physicalValue (packet tick).1 (terminalMap (R.wordMapAt observation nontrivial half depth tick word)) =
      terminalMap word := by
  induction tick with
  | zero =>
      change physicalValue 0 (terminalMap (liftMap (R := ℤ) word)) = _
      exact (congrArg (physicalValue 0) (terminal_lift word)).trans (add_zero _)
  | succ tick previous =>
      exact (physical_reindex
        (A.actual_next_packet factory (OriginalKCombFirstFullSourceDynamics.initial observation nontrivial half depth)
          (OriginalKCombFirstFullSourceDynamics.firstCfg observation nontrivial half depth) rfl tick).symm
        (stepWord observation nontrivial half (packet tick)
          (R.wordMapAt observation nontrivial half depth tick word))).trans
        ((physical_language (packet tick).2.2.2.down (A.sourceBorn factory (packet tick))
          (A.sourceWordAction (packet tick) (R.wordMapAt observation nontrivial half depth tick word))).trans
          ((physical_action (packet tick) (R.wordMapAt observation nontrivial half depth tick word)).trans previous))

attribute [local irreducible] physicalValue AS.nativeAfterAdmission

def nextAdmissions : type_of% (CW.admissions observation nontrivial half depth ordinal) :=
  (CW.nextFace observation nontrivial half depth ordinal).rootRead.source.occurrences

theorem nextAdmissions_source : nextAdmissions observation nontrivial half depth ordinal =
    CW.admissions observation nontrivial half depth ordinal :=
  CW.source_occurrences observation nontrivial half depth ordinal

attribute [local irreducible] nextAdmissions

private theorem nextAdmissions_ordered : nextAdmissions observation nontrivial half depth ordinal =
    CW.oldAdmissions observation nontrivial half depth ordinal ++
      CW.fieldAdmissions observation nontrivial half depth ordinal 0 ++
      CW.fieldAdmissions observation nontrivial half depth ordinal 1 ++
      CW.fieldAdmissions observation nontrivial half depth ordinal 2 := by
  rw [nextAdmissions_source]
  simp only [CW.admissions, CW.jointAdmissions, List.append_assoc]

def nextPaSlot : Fin (nextAdmissions observation nontrivial half depth ordinal).length :=
  middleIndex (nextAdmissions observation nontrivial half depth ordinal)
    (CW.oldAdmissions observation nontrivial half depth ordinal)
    (CW.fieldAdmissions observation nontrivial half depth ordinal 0)
    (CW.fieldAdmissions observation nontrivial half depth ordinal 1)
    (CW.fieldAdmissions observation nontrivial half depth ordinal 2)
    (nextAdmissions_ordered observation nontrivial half depth ordinal)
    (((CW.admissions_steps observation nontrivial half depth ordinal).1 1).2)

def nextPaAdmission : type_of%
    ((CW.fieldAdmissions observation nontrivial half depth ordinal 1).get
      ⟨0, ((CW.admissions_steps observation nontrivial half depth ordinal).1 1).2⟩) :=
  (nextAdmissions observation nontrivial half depth ordinal).get
    (nextPaSlot observation nontrivial half depth ordinal)

theorem nextPaAdmission_source : nextPaAdmission observation nontrivial half depth ordinal =
    (CW.fieldAdmissions observation nontrivial half depth ordinal 1).get
      ⟨0, ((CW.admissions_steps observation nontrivial half depth ordinal).1 1).2⟩ := by
  exact middle_read (nextAdmissions observation nontrivial half depth ordinal)
    (CW.oldAdmissions observation nontrivial half depth ordinal)
    (CW.fieldAdmissions observation nontrivial half depth ordinal 0)
    (CW.fieldAdmissions observation nontrivial half depth ordinal 1)
    (CW.fieldAdmissions observation nontrivial half depth ordinal 2)
    (nextAdmissions_ordered observation nontrivial half depth ordinal)
    (((CW.admissions_steps observation nontrivial half depth ordinal).1 1).2)

def nextPaValue : BurnolL2 :=
  physicalValue (AS.bornAfterNative native).1
    (terminalMap (nextPaAdmission observation nontrivial half depth ordinal).1.word)

theorem nextPa_value : nextPaValue observation nontrivial half depth ordinal =
    CW.actualValue observation nontrivial half depth 1 := by
  have one : (SourceOperationPaidRelations.words (trace 1)).length = 1 :=
    (SourceOperationPaidRelations.complete_steps (trace 1)).trans (trace 1).length_to_const
  let index : PO.Index observation nontrivial half depth 1 := ⟨0, by omega⟩
  let originalWord : Formal ℤ C.Value C.Var () := (SourceOperationPaidRelations.words (trace 1)).get index
  rw [nextPaValue, nextPaAdmission_source]
  rw [mapped_read (CW.fieldAdmissions observation nontrivial half depth ordinal 1)
    (fun admitted => admitted.1.word) (CW.fieldWords observation nontrivial half depth ordinal 1)
    (CW.field_admissions_words observation nontrivial half depth ordinal 1)
    (((CW.admissions_steps observation nontrivial half depth ordinal).1 1).2)]
  simp only [CW.fieldWords, List.get_ofFn, Fin.cast_mk]
  refine (physical_native_word factory (packet (ordinal+1))
    (R.wordMapAt observation nontrivial half depth (ordinal+1) originalWord)).trans ?_
  refine (physical_word observation nontrivial half depth originalWord (ordinal+1)).trans ?_
  change terminalMap ((SourceOperationPaidRelations.words (trace 1)).get index) = _
  rw [one_read_sum _ one, SourceOperationPaidRelations.paid_boundary, (trace 1).relation_boundary]
  simp [terminalMap, terminalFace, C.paNativeCayleySourceCode,
    OriginalKPaNativeCayleySourceCalculation.code, OriginalKPaNativeCayleySourceCalculation.paCode]
  change (0 : BurnolL2) + CW.actualValue observation nontrivial half depth 1 = _
  exact zero_add _

/-- This is the original paid Pa trace, with its endpoint read from the retained next source. -/
def nextPaTrace : Trace (C.receipt observation nontrivial depth half).1.environment
    (C.paNativeCayleySourceCode observation nontrivial depth half 1)
    (.const (nextPaValue observation nontrivial half depth ordinal)) :=
  Eq.mp (congrArg (fun point => Trace (C.receipt observation nontrivial depth half).1.environment
    (C.paNativeCayleySourceCode observation nontrivial depth half 1) (.const point))
      (nextPa_value observation nontrivial half depth ordinal).symm) (trace 1)

theorem nextPaTrace_heq : HEq (nextPaTrace observation nontrivial half depth ordinal) (trace 1) :=
  cast_heq _ _

theorem nextPa_zero (zero : CW.actualValue observation nontrivial half depth 1 = 0) :
    nextPaValue observation nontrivial half depth ordinal = 0 :=
  (nextPa_value observation nontrivial half depth ordinal).trans zero


end OriginalKPaNativeCayleyNextSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
