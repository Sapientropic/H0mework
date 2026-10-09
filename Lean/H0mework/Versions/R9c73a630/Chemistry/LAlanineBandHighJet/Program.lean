import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Grouped
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCalculation.IntegerArithmetic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open SourceRectangle SourceSignedEvaluator SourceIntegerGrid SourceRectangleChecks SourceFiniteData
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation

structure TermCode where
  weight : Interval
  group : Group
  powers : Fin 3 × Fin 3 × Fin 3
  deriving DecidableEq

def powerAt (code : TermCode) : Fin 3 → Fin 3 := ![code.powers.1,code.powers.2.1,code.powers.2.2]

def evalCode (exps : Group → Interval) (polys : Group → Fin 3 → Fin 3 → Fin 5 → Interval)
    (orders : Fin 3 → Fin 5) (code : TermCode) : Interval :=
  cachedIntegerTerm code.weight (exps code.group) (fun a => polys code.group a (powerAt code a) (orders a))

def evalProgram (codes : List TermCode) (exps : Group → Interval)
    (polys : Group → Fin 3 → Fin 3 → Fin 5 → Interval) (orders : Fin 3 → Fin 5) : Interval :=
  (codes.map (evalCode exps polys orders)).foldr addInteger (0,0)

noncomputable def sourceCode (b : Basis) (term : {t // t ∈ source_terms b}) : TermCode :=
  ⟨encode (point term.val.weight),sourceGroup b term.val term.property,
    sourcePower b term.val term.property 0,sourcePower b term.val term.property 1,sourcePower b term.val term.property 2⟩
noncomputable def sourceProgram (b : Basis) : List TermCode := (source_terms b).attach.map (sourceCode b)

 theorem sourceCode_power (b : Basis) (term : {t // t ∈ source_terms b}) (axis : Fin 3) :
    powerAt (sourceCode b term) axis = sourcePower b term.val term.property axis := by
  fin_cases axis <;> rfl

 theorem eval_sourceCode (exps : Group → Interval) (polys : Group → Fin 3 → Fin 3 → Fin 5 → Interval)
    (b : Basis) (j : JetIndex) (term : {t // t ∈ source_terms b}) :
    grid (evalCode exps polys (orderAt j) (sourceCode b term)) =
      groupTermValue (fun g => grid (exps g)) (fun g a p d => grid (polys g a p d)) b j term := by
  have weight : grid (sourceCode b term).weight = point term.val.weight := encode_rounds _ _
  unfold evalCode
  rw [grid_cachedIntegerTerm _ _ _ term.val.weight weight]
  rw [show powerAt (sourceCode b term) = sourcePower b term.val term.property from
    funext (sourceCode_power b term)]
  rfl

private theorem mapped_fold {α : Type*} (items : List α) (f : α → Interval) (g : α → Pair)
    (h : ∀ item, grid (f item) = g item) :
    grid ((items.map f).foldr addInteger (0,0)) = (items.map g).foldr add (point 0) := by
  induction items with
  | nil => exact grid_zero
  | cons item rest ih => simp only [List.map_cons,List.foldr_cons,grid_add,h,ih]

 theorem eval_sourceProgram (exps : Group → Interval) (polys : Group → Fin 3 → Fin 3 → Fin 5 → Interval)
    (b : Basis) (j : JetIndex) :
    grid (evalProgram (sourceProgram b) exps polys (orderAt j)) =
      groupOrbitalValue (fun g => grid (exps g)) (fun g a p d => grid (polys g a p d)) b j := by
  unfold evalProgram sourceProgram
  rw [List.map_map]
  exact mapped_fold (source_terms b).attach _ _ (eval_sourceCode exps polys b j)

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
