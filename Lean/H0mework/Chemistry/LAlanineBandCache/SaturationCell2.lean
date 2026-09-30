import H0mework.Chemistry.LAlanineBandCache.SaturationSequence
import H0mework.Chemistry.LAlanineBandCache.Kernel
import H0mework.Chemistry.LAlanineBandSource.Literals

/-! The registered cell2 source boxes and Gaussian parameters generate 36 saturated groups. -/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSaturation

open SourceExponential SourceSignedEvaluator SourceGaussianModel SourceRectangle WholeBandSource
open Lean Elab Term Command

abbrev SaturatedGroup := Fin 36

/-- Original Gaussian group addresses, retained independently of their output intervals. -/
def groupAt (g : SaturatedGroup) : Group :=
  ![0, 1, 2, 3, 4, 6, 11, 12, 13, 14, 15, 17, 22, 23, 24, 25, 26, 28,
    33, 37, 41, 45, 46, 47, 56, 57, 58, 67, 71, 72, 73, 74, 75, 82, 86, 90] g

noncomputable def cell2Call (i : Fin 64) : FullBandCall := ⟨128+i.val, by omega⟩

/-- Bounds on raw source arguments and their original reduction, before any exponential output. -/
def InputBounds (box : Rectangle) (r : Group → Nat × Nat) (g : Group) : Prop :=
  let a := radialPair (groupTerm g) box
  let k := r g
  (|reducedArgument a.1 k.1| ≤ 1/2 ∧ |reducedArgument a.2 k.2| ≤ 1/2) ∧
  ((k.1 = 8 ∧ reducedArgument a.1 k.1 ≤ -7/16) ∨
    (9 ≤ k.1 ∧ reducedArgument a.1 k.1 ≤ -7/32)) ∧
  ((k.2 = 8 ∧ reducedArgument a.2 k.2 ≤ -7/16) ∨
    (9 ≤ k.2 ∧ reducedArgument a.2 k.2 ≤ -7/32))

noncomputable instance (box : Rectangle) (r : Group → Nat × Nat) (g : Group) :
    Decidable (InputBounds box r g) := by unfold InputBounds; infer_instance

/-- The original evaluator, rather than a reported result, produces the saturated interval. -/
theorem exponential_eq (box : Rectangle) (r : Group → Nat × Nat) (g : Group)
    (input : InputBounds box r g) :
    exponential (radialPair (groupTerm g) box) (r g).1 (r g).2 = (0,1/scale) := by
  exact Prod.ext (leaf_saturated input.1.1 input.2.1).1
    (leaf_saturated input.1.2 input.2.2).2

private def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command

private def fin (value size : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit size))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit size) (mkNatLit value) proof

open Lean Elab Tactic in
elab "closeSaturationRows " count:num stem:str : tactic => do
  let goals ← getGoals
  unless goals.length == count.getNat do throwError "source saturation census"
  for (goal,i) in goals.zipIdx do
    let remaining ← goal.apply
      (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple (stem.getString ++ toString i)))
    unless remaining.isEmpty do throwError "source saturation branch arguments"
  setGoals []

/-- Reify only existing box/reduction literals; every resulting inequality is kernel checked. -/
elab "checkCell2SaturationInputs" : command => do
  for i in [:64] do
    if i != 32 then
      liftTermElabM do
        WholeCellSource.declareSource (Name.mkSimple s!"rawBox{i}")
          (toExpr (← coordinateLiterals (128+i)))
        WholeCellSource.declareSource (Name.mkSimple s!"rawReductions{i}")
          (toExpr (← reductionLiterals (128+i)))
      emit s!"noncomputable def box{i} : Rectangle := fun a => integerInterval rawBox{i}[a.val]!"
      emit s!"noncomputable def reductions{i} (g : Group) : Nat × Nat := rawReductions{i}[g.val]!"
      emit s!"theorem box{i}_original : box{i} = callBox {128+i} := rfl"
      emit s!"theorem reductions{i}_original : reductions{i} = callReductions {128+i} := rfl"
      liftTermElabM do
        let root ← getCurrNamespace
        for s in [:36] do
          let group := mkApp (Lean.mkConst ``groupAt) (← fin s 36)
          let type := mkApp3 (Lean.mkConst ``InputBounds)
            (Lean.mkConst (root ++ Name.mkSimple s!"box{i}"))
            (Lean.mkConst (root ++ Name.mkSimple s!"reductions{i}")) group
          let decider ← Meta.synthInstance (mkApp (Lean.mkConst ``Decidable) type)
          let value := mkApp3 (Lean.mkConst ``of_decide_eq_true) type decider
            (← Meta.mkEqRefl (Lean.mkConst ``Bool.true))
          addDecl (.thmDecl {
            name := root ++ Name.mkSimple s!"input{i}_{s}"
            levelParams := []
            type := type
            value := value })
      emit s!"theorem input{i} (g : SaturatedGroup) : InputBounds box{i} reductions{i} (groupAt g) := by
        fin_cases g
        closeSaturationRows 36 \"input{i}_\""
      emit s!"theorem callInput{i} (g : SaturatedGroup) :
        InputBounds (callBox {128+i}) (callReductions {128+i}) (groupAt g) := by
        rw [← box{i}_original, ← reductions{i}_original]
        exact input{i} g"
    else
      emit "theorem callInput32 (g : SaturatedGroup) :
        InputBounds (callBox 160) (callReductions 160) (groupAt g) := callInput0 g"
    liftTermElabM do
      liftM (m := IO) do
        let output ← IO.getStdout
        output.putStrLn s!"cell2 source saturation: {i+1}/64 original calls"
        output.flush

checkCell2SaturationInputs

/-- All 64 original addresses retain their exact boxes and reductions. -/
theorem cell2_input_bounds (i : Fin 64) (g : SaturatedGroup) :
    InputBounds (callBox (cell2Call i)) (callReductions (cell2Call i)) (groupAt g) := by
  fin_cases i
  closeSaturationRows 64 "callInput"

/-- The 36 source groups on cell2 produce their original exponential cache entries. -/
theorem cell2_exponential_saturated (i : Fin 64) (g : SaturatedGroup) :
    exponential (radialPair (groupTerm (groupAt g)) (callBox (cell2Call i)))
      (callReductions (cell2Call i) (groupAt g)).1
      (callReductions (cell2Call i) (groupAt g)).2 = (0,1/scale) :=
  exponential_eq _ _ _ (cell2_input_bounds i g)

/-- Consume the generated exact evaluator equality in the original Gaussian inclusion theorem. -/
theorem cell2_actual_exponential (i : Fin 64) (g : SaturatedGroup) (x : Point)
    (inside : InRectangle (callBox (cell2Call i)) x) :
    Holds (0,1/scale) (Real.exp (radialArgument (groupTerm (groupAt g)) x)) := by
  rw [← cell2_exponential_saturated i g]
  exact exponential_holds _ _ _ (cell2_input_bounds i g).1.1 (cell2_input_bounds i g).1.2 _
    (radialPair_contains _ _ x inside)

end LAlanine40K2025.BasinRefinement.WholeBandSaturation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
