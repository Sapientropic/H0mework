import H0mework.Chemistry.LAlanineBandHighJet.Program

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open SourceRectangle SourceSignedEvaluator SourceIntegerGrid SourceRectangleChecks SourceFiniteData SourceGaussianModel
open WholeBandCache
noncomputable section

 def prefixJet {n : Nat} (bound : n ≤ 35) (j : Fin n) : JetIndex := ⟨j.val,j.isLt.trans_le bound⟩
 def expInteger (m : Material) (g : Group) : Interval := (m.groups[g.val]!).exponential
 def polyInteger (m : Material) (g : Group) (axis power : Fin 3) (order : Fin 5) : Interval :=
   ((((m.groups[g.val]!).polynomial[axis.val]!)[power.val]!)[order.val]!)
 def polyPair (m : Material) (g : Group) (axis power : Fin 3) (order : Fin 5) : Pair :=
   grid (polyInteger m g axis power order)
 def aoInteger {n : Nat} (m : Material) (b : Basis) (j : Fin n) : Interval := (m.orbitals[b.val]!)[j.val]!

 structure GroupComputed (box : Rectangle) (r : Group → Nat × Nat) (m : Material) (g : Group) : Prop where
   relative : List.ofFn (cachedRelative m g) = List.ofFn (SourceSignedEvaluator.relative (groupTerm g) box)
   radial : cachedRadial m g = radialPair (groupTerm g) box
   exponential : grid (expInteger m g) = exponential (cachedRadial m g) (r g).1 (r g).2
   polynomial : List.ofFn (fun a => List.ofFn (fun p => List.ofFn (polyPair m g a p))) =
     List.ofFn (fun a : Fin 3 => List.ofFn (fun p : Fin 3 => List.ofFn (fun d : Fin 5 =>
       jetHorner (groupExponent g) p.val d.val (cachedRelative m g a))))
   reductions : |SourceExponential.reducedArgument (cachedRadial m g).1 (r g).1| ≤ 1/2 ∧
     |SourceExponential.reducedArgument (cachedRadial m g).2 (r g).2| ≤ 1/2

 theorem exponential_exact {box : Rectangle} {r : Group → Nat × Nat} {m : Material}
    (groups : ∀ g, GroupComputed box r m g) (g : Group) :
    grid (expInteger m g) = exponential (radialPair (groupTerm g) box) (r g).1 (r g).2 := by
   rw [(groups g).exponential,(groups g).radial]

 theorem polynomial_exact {box : Rectangle} {r : Group → Nat × Nat} {m : Material}
    (groups : ∀ g, GroupComputed box r m g) (g : Group) (axis power : Fin 3) (order : Fin 5) :
    polyPair m g axis power order = jetHorner (groupTerm g).exponent power.val order.val
      (SourceSignedEvaluator.relative (groupTerm g) box axis) := by
   have hp := congrFun (List.ofFn_injective (groups g).polynomial) axis
   have hp := congrFun (List.ofFn_injective hp) power
   have hp := congrFun (List.ofFn_injective hp) order
   have hr := congrFun (List.ofFn_injective (groups g).relative) axis
   rw [hr, ← (actual_group_terms g).2.1] at hp
   exact hp

 theorem reductions_valid {box : Rectangle} {r : Group → Nat × Nat} {m : Material}
    (groups : ∀ g, GroupComputed box r m g) (g : Group) :
    TermReductionValid (groupTerm g) box (r g).1 (r g).2 := by
   have h := (groups g).reductions
   rw [(groups g).radial] at h
   exact h

 def OrbitalComputed {n : Nat} (bound : n ≤ 35) (programs : Basis → List TermCode) (m : Material) (b : Basis) : Prop :=
   List.ofFn (aoInteger (n := n) m b) = List.ofFn (fun j : Fin n =>
     evalProgram (programs b) (expInteger m) (polyInteger m) (orderAt (prefixJet bound j)))

 theorem actual_orbital {n : Nat} (bound : n ≤ 35) (box : Rectangle) (r : Group → Nat × Nat)
    (programs : Basis → List TermCode) (sourcePrograms : ∀ b, programs b = sourceProgram b) (m : Material)
    (groups : ∀ g, GroupComputed box r m g)
    (orbitals : ∀ b, OrbitalComputed bound programs m b)
    (b : Basis) (j : Fin n) (x : Point) (inside : InRectangle box x) :
    Holds (grid (aoInteger m b j)) (orbital (source_terms b) (jetMulti (prefixJet bound j)) x) := by
   have h := congrFun (List.ofFn_injective (orbitals b)) j
   rw [h,sourcePrograms,eval_sourceProgram]
   exact group_orbital_contains box r _ _ (exponential_exact groups) (polynomial_exact groups)
     (reductions_valid groups) b (prefixJet bound j) x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
