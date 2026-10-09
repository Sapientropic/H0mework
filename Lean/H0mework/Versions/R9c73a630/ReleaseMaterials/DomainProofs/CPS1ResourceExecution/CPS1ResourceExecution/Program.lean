import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ResourceExecution.Reactions
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Producer.Molecules

/-!
The original CPS1 RNA generates a typed peptide and a finite charging/elongation program.
Initiator loading and termination are explicit boundary obligations, never free reactions.
The printed protein is consumed only by an independent recognition theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1ResourceExecution.Program

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

open Lean Elab Term

def aaLabel : AA → String
  | .A => "A" | .C => "C" | .D => "D" | .E => "E" | .F => "F"
  | .G => "G" | .H => "H" | .I => "I" | .K => "K" | .L => "L"
  | .M => "M" | .N => "N" | .P => "P" | .Q => "Q" | .R => "R"
  | .S => "S" | .T => "T" | .V => "V" | .W => "W" | .Y => "Y"

def aaOfLabel? : String → Option AA
  | "A" => some .A | "C" => some .C | "D" => some .D | "E" => some .E
  | "F" => some .F | "G" => some .G | "H" => some .H | "I" => some .I
  | "K" => some .K | "L" => some .L | "M" => some .M | "N" => some .N
  | "P" => some .P | "Q" => some .Q | "R" => some .R | "S" => some .S
  | "T" => some .T | "V" => some .V | "W" => some .W | "Y" => some .Y
  | _ => none

/-- A stop must be the final translated label; it is never an amino acid. -/
def residueLabels? (labels : List String) : Option (List AA) :=
  List.rec (motive := fun _ => Option (List AA)) none
    (fun label rest decodedTail =>
      match label, rest with
      | "*", [] => some []
      | "*", _ => none
      | _, _ => do
          let aa ← aaOfLabel? label
          let tail ← decodedTail
          pure (aa :: tail)) labels

def peptideOfLabels? (labels : List String) : Option Peptide := do
  let residues ← residueLabels? labels
  match residues with
  | first :: tail => some (first,tail)
  | [] => none

/-- Decode the original chemical word before finding and translating its first coding frame. -/
def peptideFromRna? (raw : List Char) : Option Peptide := do
  let rna ← Rna.parse raw
  let coding ← Coding.coding? (Rna.template rna)
  let labels ← Coding.translate Coding.code coding
  peptideOfLabels? labels

private def aaExpr (aa : AA) : Expr :=
  mkConst (match aa with
    | .A => ``AA.A | .C => ``AA.C | .D => ``AA.D | .E => ``AA.E | .F => ``AA.F
    | .G => ``AA.G | .H => ``AA.H | .I => ``AA.I | .K => ``AA.K | .L => ``AA.L
    | .M => ``AA.M | .N => ``AA.N | .P => ``AA.P | .Q => ``AA.Q | .R => ``AA.R
    | .S => ``AA.S | .T => ``AA.T | .V => ``AA.V | .W => ``AA.W | .Y => ``AA.Y)

elab "cps1ResourcePeptide%" : term => do
  let some peptide := peptideFromRna? Source.rawMrna
    | throwError "Original CPS1 RNA did not generate a complete nonempty peptide"
  Meta.mkAppM ``Prod.mk #[aaExpr peptide.1,
    ← Meta.mkListLit (mkConst ``AA) (peptide.2.map aaExpr)]

/-- This reified object is calculated from the RNA; the generation theorem kernel-checks it. -/
def originalPeptide : Peptide := cps1ResourcePeptide%

theorem original_peptide_generated :
    peptideFromRna? Source.rawMrna = some originalPeptide := by
  decide +kernel

/-- Loading needs an external boundary action from charged initiator to loaded peptidyl state. -/
structure LoadedInitiatorBoundary where
  initiator : AA
  deriving DecidableEq, Repr

def LoadedInitiatorBoundary.required (boundary : LoadedInitiatorBoundary) : List Species :=
  [.aaTRNA boundary.initiator]

def LoadedInitiatorBoundary.loaded (boundary : LoadedInitiatorBoundary) : List Species :=
  [.peptidyl (boundary.initiator,[])]

/-- The final peptidyl state awaits a termination action; it is not a free released protein. -/
structure TerminationBoundary where
  attachedPeptide : Peptide
  deriving DecidableEq, Repr

def TerminationBoundary.required (boundary : TerminationBoundary) : List Species :=
  [.peptidyl boundary.attachedPeptide]

/-- Each residue after the initiator generates delivery, transfer and translocation. -/
def compileElongation (chain : Peptide) (tail : List AA) : List Reaction :=
  List.rec (motive := fun _ => Peptide → List Reaction) (fun _ => [])
    (fun aa _ next current =>
      .deliver current aa :: .transfer current aa ::
        .translocate (Peptide.extend current aa) :: next (Peptide.extend current aa)) tail chain

/-- Charging and the elongation core are executable blocks; the two interfaces remain boundaries. -/
structure Plan where
  peptide : Peptide
  charges : List Reaction
  loadedInitiatorBoundary : LoadedInitiatorBoundary
  elongationCore : List Reaction
  terminationBoundary : TerminationBoundary
  deriving DecidableEq, Repr

def compile (peptide : Peptide) : Plan where
  peptide := peptide
  charges := peptide.word.map Reaction.charge
  loadedInitiatorBoundary := ⟨peptide.1⟩
  elongationCore := compileElongation (peptide.1,[]) peptide.2
  terminationBoundary := ⟨peptide⟩

def planFromRna? (raw : List Char) : Option Plan :=
  (peptideFromRna? raw).map compile

def originalPlan : Plan := compile originalPeptide

/-- The premise-free mouth generates the exact reaction program from the original RNA. -/
theorem source_generated_original_plan :
    planFromRna? Source.rawMrna = some originalPlan := by
  rw [planFromRna?, original_peptide_generated]
  rfl

theorem compile_charges (peptide : Peptide) :
    (compile peptide).charges = peptide.word.map Reaction.charge := rfl

theorem compile_boundaries (peptide : Peptide) :
    (compile peptide).loadedInitiatorBoundary.required = [.aaTRNA peptide.1] ∧
    (compile peptide).loadedInitiatorBoundary.loaded = [.peptidyl (peptide.1,[])] ∧
    (compile peptide).terminationBoundary.required = [.peptidyl peptide] := ⟨rfl,rfl,rfl⟩

theorem compile_elongation_length (chain : Peptide) (tail : List AA) :
    (compileElongation chain tail).length = 3 * tail.length := by
  induction tail generalizing chain with
  | nil => rfl
  | cons aa rest inductionHypothesis =>
      change ((compileElongation (Peptide.extend chain aa) rest).length + 1 + 1 + 1) =
        3 * (rest.length + 1)
      rw [inductionHypothesis]
      omega

def deliveredCount (reactions : List Reaction) : Nat :=
  (reactions.filter (fun reaction => match reaction with | .deliver _ _ => true | _ => false)).length

def transferCount (reactions : List Reaction) : Nat :=
  (reactions.filter (fun reaction => match reaction with | .transfer _ _ => true | _ => false)).length

def translocatedCount (reactions : List Reaction) : Nat :=
  (reactions.filter (fun reaction => match reaction with | .translocate _ => true | _ => false)).length

theorem compile_elongation_counts (chain : Peptide) (tail : List AA) :
    deliveredCount (compileElongation chain tail) = tail.length ∧
    transferCount (compileElongation chain tail) = tail.length ∧
    translocatedCount (compileElongation chain tail) = tail.length := by
  induction tail generalizing chain with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons aa rest inductionHypothesis =>
      rcases inductionHypothesis (Peptide.extend chain aa) with ⟨delivery,transfer,translocation⟩
      simp only [compileElongation, deliveredCount, transferCount, translocatedCount,
        List.filter_cons, if_true, List.length_cons] at *
      exact ⟨congrArg Nat.succ delivery,congrArg Nat.succ transfer,
        congrArg Nat.succ translocation⟩

def advancePeptide (chain : Peptide) (tail : List AA) : Peptide :=
  List.rec (motive := fun _ => Peptide → Peptide) (fun current => current)
    (fun aa _ next current => next (Peptide.extend current aa)) tail chain

theorem advance_peptide_word (chain : Peptide) (tail : List AA) :
    (advancePeptide chain tail).word = chain.word ++ tail := by
  induction tail generalizing chain with
  | nil => simp only [advancePeptide, List.append_nil]
  | cons aa rest inductionHypothesis =>
      change (advancePeptide (Peptide.extend chain aa) rest).word = chain.word ++ aa :: rest
      rw [inductionHypothesis]
      simp only [Peptide.word, Peptide.extend, List.cons_append, List.append_assoc,
        List.nil_append]

theorem compile_final_attached_word (peptide : Peptide) :
    (advancePeptide (peptide.1,[]) peptide.2).word =
      (compile peptide).terminationBoundary.attachedPeptide.word := by
  rw [advance_peptide_word]
  rfl

/-- Independent printed-protein recognition consumes the generated typed peptide. -/
theorem original_printed_protein_consumed :
    originalPeptide.word.map aaLabel ++ ["*"] =
      Source.editorProtein.map String.singleton := by
  decide +kernel

theorem original_core_lengths :
    originalPeptide.word.length = 1605 ∧
    originalPlan.charges.length = 1605 ∧
    originalPeptide.2.length = 1604 ∧
    originalPlan.elongationCore.length = 4812 := by
  decide +kernel

theorem original_core_reaction_counts :
    deliveredCount originalPlan.elongationCore = 1604 ∧
    transferCount originalPlan.elongationCore = 1604 ∧
    translocatedCount originalPlan.elongationCore = 1604 := by
  decide +kernel

/-- Numeric census is an independent regression consumer, never an input to compilation. -/
theorem original_census_regression :
    ([AA.A,AA.C,AA.D,AA.E,AA.F,AA.G,AA.H,AA.I,AA.K,AA.L,
      AA.M,AA.N,AA.P,AA.Q,AA.R,AA.S,AA.T,AA.V,AA.W,AA.Y].map
        (fun aa => originalPeptide.word.count aa)) =
      [94,6,104,125,70,95,38,102,165,163,30,80,44,58,95,101,74,89,11,61] := by
  decide +kernel

/-- Explicit source override: one initiator, no elongation and both boundaries still present. -/
theorem single_residue_source_control :
    peptideFromRna? ['A','U','G','U','A','A'] = some (.M,[]) ∧
    (compile (.M,[])).charges = [.charge .M] ∧
    (compile (.M,[])).elongationCore = [] ∧
    (compile (.M,[])).loadedInitiatorBoundary.required = [.aaTRNA .M] ∧
    (compile (.M,[])).terminationBoundary.required = [.peptidyl (.M,[])] := by
  decide +kernel

theorem non_peptide_controls :
    aaOfLabel? "*" = none ∧
    peptideOfLabels? ["*"] = none ∧
    peptideOfLabels? ["M","*","A","*"] = none ∧
    peptideOfLabels? ["M"] = none ∧
    peptideFromRna? ['A','C'] = none := by
  decide +kernel

end CPS1ResourceExecution.Program
