import H0mework.Chemistry.LAlanineBandCache.Kernel

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open SourceGaussianModel SourceSignedEvaluator SourceFiniteData SourceRectangle SourceRectangleChecks

 theorem original_orders : ∀ j : JetIndex, ∀ axis : Fin 3, jetMulti j axis < 5 := by decide +kernel

noncomputable section
 def orderAt (j : JetIndex) (axis : Fin 3) : Fin 5 := ⟨jetMulti j axis,original_orders j axis⟩
 def groupTermValue (exps : Group → Pair) (polys : Group → Fin 3 → Fin 3 → Fin 5 → Pair)
    (b : Basis) (j : JetIndex) (term : {t // t ∈ source_terms b}) : Pair :=
   cachedTerm term.val.weight (exps (sourceGroup b term.val term.property))
     (fun axis => polys (sourceGroup b term.val term.property) axis
       (sourcePower b term.val term.property axis) (orderAt j axis))
 def groupOrbitalValue (exps : Group → Pair) (polys : Group → Fin 3 → Fin 3 → Fin 5 → Pair)
    (b : Basis) (j : JetIndex) : Pair :=
   ((source_terms b).attach.map (groupTermValue exps polys b j)).foldr add (point 0)

 theorem group_term_commutes (box : Rectangle) (reductions : Group → Nat × Nat)
    (exps : Group → Pair) (polys : Group → Fin 3 → Fin 3 → Fin 5 → Pair)
    (expComputed : ∀ g, exps g = exponential (radialPair (groupTerm g) box) (reductions g).1 (reductions g).2)
    (polyComputed : ∀ g axis p d, polys g axis p d =
      jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) box axis))
    (b : Basis) (j : JetIndex) (term : {t // t ∈ source_terms b}) :
    groupTermValue exps polys b j term = termPair term.val (jetMulti j) box
      (WholeCellSource.sourceStepsAt reductions term.val).1 (WholeCellSource.sourceStepsAt reductions term.val).2 := by
   have components := registered_group_components b term.val term.property
   unfold groupTermValue
   apply cachedTerm_commutes
   · rw [expComputed, ← radial_same_group term.val
       (groupTerm (sourceGroup b term.val term.property)) box components.2 components.1]
     simp only [WholeCellSource.sourceStepsAt,lookupGroup_registered b term.val term.property]
   · intro axis
     rw [polyComputed]
     simp only [sourcePower,orderAt]
     rw [components.1,relative_same_group term.val
       (groupTerm (sourceGroup b term.val term.property)) box components.2 axis]

 theorem group_orbital_contains (box : Rectangle) (reductions : Group → Nat × Nat)
    (exps : Group → Pair) (polys : Group → Fin 3 → Fin 3 → Fin 5 → Pair)
    (expComputed : ∀ g, exps g = exponential (radialPair (groupTerm g) box) (reductions g).1 (reductions g).2)
    (polyComputed : ∀ g axis p d, polys g axis p d =
      jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) box axis))
    (valid : ∀ g, TermReductionValid (groupTerm g) box (reductions g).1 (reductions g).2)
    (b : Basis) (j : JetIndex) (x : Point) (inside : InRectangle box x) :
    Holds (groupOrbitalValue exps polys b j) (orbital (source_terms b) (jetMulti j) x) := by
   have assembly : groupOrbitalValue exps polys b j =
       orbitalPair (source_terms b) (jetMulti j) box (WholeCellSource.sourceStepsAt reductions) := by
     unfold groupOrbitalValue orbitalPair
     apply congrArg (fun values : List Pair => values.foldr add (point 0))
     calc
       _ = (source_terms b).attach.map (fun term => termPair term.val (jetMulti j) box
           (WholeCellSource.sourceStepsAt reductions term.val).1 (WholeCellSource.sourceStepsAt reductions term.val).2) :=
         List.map_congr_left (fun term _ => group_term_commutes box reductions exps polys expComputed polyComputed b j term)
       _ = _ := List.attach_map_val (f := fun term : Term => termPair term (jetMulti j) box
         (WholeCellSource.sourceStepsAt reductions term).1 (WholeCellSource.sourceStepsAt reductions term).2)
   rw [assembly]
   exact orbitalPair_contains (source_terms b) (jetMulti j) box (WholeCellSource.sourceStepsAt reductions)
     (fun term member => WholeCellSource.source_reduction_at box reductions valid b term member) x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
