import H0mework.Versions.AB.Chemistry.LAlanineWholeCell.SourceGrouped
import H0mework.Versions.AB.Chemistry.LAlanineContinuousGroupCache.Data

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCache

open SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData SourceRectangleChecks SourceFields

structure Material where
  groups : Array SourceGroupCache.RawCache
  orbitals : Array (Array (Int × Int))

noncomputable section

def cachedRelative (m : Material) (g : Group) (a : Fin 3) : Pair :=
  integerInterval ((m.groups[g.val]!).relative[a.val]!)
def cachedRadial (m : Material) (g : Group) : Pair := integerInterval (m.groups[g.val]!).radial
def cachedExp (m : Material) (g : Group) : Pair := integerInterval (m.groups[g.val]!).exponential
def cachedPoly (m : Material) (g : Group) (a p d : Fin 3) : Pair :=
  integerInterval ((((m.groups[g.val]!).polynomial[a.val]!)[p.val]!)[d.val]!)
def calculatedAO (m : Material) (j : LowJet) (b : Basis) : Pair :=
  integerInterval ((m.orbitals[b.val]!)[j.val]!)
def assemblyPoly (box : Rectangle) (m : Material) (g : Group) (a p : Fin 3) (d : Fin 4) : Pair :=
  if h : d.val < 3 then cachedPoly m g a p ⟨d.val,h⟩
  else jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) box a)

/-- Finite arithmetic laws, not analytic bounds or successful field conclusions. -/
structure GroupComputed (box : Rectangle) (reductions : Group → Nat × Nat) (m : Material) (g : Group) : Prop where
  relative : List.ofFn (cachedRelative m g) = List.ofFn (relative (groupTerm g) box)
  radial : cachedRadial m g = radialPair (groupTerm g) box
  exponential : cachedExp m g = exponential (cachedRadial m g) (reductions g).1 (reductions g).2
  polynomial : List.ofFn (fun a => List.ofFn (fun p => List.ofFn (cachedPoly m g a p))) =
    List.ofFn (fun a : Fin 3 => List.ofFn (fun p : Fin 3 => List.ofFn (fun d : Fin 3 =>
      jetHorner (groupExponent g) p.val d.val (cachedRelative m g a))))
  reductions : |SourceExponential.reducedArgument (cachedRadial m g).1 (reductions g).1| ≤ 1/2 ∧
    |SourceExponential.reducedArgument (cachedRadial m g).2 (reductions g).2| ≤ 1/2

theorem exp_eq_source {box : Rectangle} {r : Group → Nat × Nat} {m : Material}
    (h : ∀ g, GroupComputed box r m g) (g : Group) :
    cachedExp m g = exponential (radialPair (groupTerm g) box) (r g).1 (r g).2 := by
  rw [(h g).exponential, (h g).radial]

theorem poly_eq_source {box : Rectangle} {r : Group → Nat × Nat} {m : Material}
    (h : ∀ g, GroupComputed box r m g) (g : Group) (a p : Fin 3) (d : Fin 4) :
    assemblyPoly box m g a p d =
      jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) box a) := by
  unfold assemblyPoly
  split_ifs with hd
  · have hp := congrFun (List.ofFn_injective (h g).polynomial) a
    have hp := congrFun (List.ofFn_injective hp) p
    have hp := congrFun (List.ofFn_injective hp) (⟨d.val,hd⟩ : Fin 3)
    have hr := congrFun (List.ofFn_injective (h g).relative) a
    rw [hr, ← (actual_group_terms g).2.1] at hp
    exact hp
  · rfl

theorem group_reductions {box : Rectangle} {r : Group → Nat × Nat} {m : Material}
    (h : ∀ g, GroupComputed box r m g) (g : Group) :
    TermReductionValid (groupTerm g) box (r g).1 (r g).2 := by
  have hg := (h g).reductions
  rw [(h g).radial] at hg
  exact hg

def OrbitalComputed (box : Rectangle) (m : Material) (b : Basis) : Prop :=
  List.ofFn (fun j : LowJet => calculatedAO m j b) =
    List.ofFn (fun j : LowJet => groupCachedOrbital (cachedExp m) (assemblyPoly box m) b (fullJet j))

theorem calculatedAO_contains {box : Rectangle} {r : Group → Nat × Nat} {m : Material}
    (groups : ∀ g, GroupComputed box r m g) (orbitals : ∀ b, OrbitalComputed box m b)
    (j : LowJet) (b : Basis) (x : Point) (inside : InRectangle box x) :
    Holds (calculatedAO m j b) (orbital (source_terms b) (multiindex (fullJet j)) x) := by
  rw [congrFun (List.ofFn_injective (orbitals b)) j]
  exact WholeCellSource.source_group_orbital_contains box r (cachedExp m) (assemblyPoly box m)
    (exp_eq_source groups) (poly_eq_source groups) (group_reductions groups) b (fullJet j) x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandCache
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
