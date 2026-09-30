import H0mework.Chemistry.LAlanineBandHighJet.Scope
import H0mework.Chemistry.LAlanineBandTaylor.Jets

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceIntegerGrid ContinuousGradient
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
noncomputable section

 def wordInteger (scope : Scope) (pairs : Fin (jetCount scope) → Fin (jetCount scope) → Interval)
    (w : List (Fin 3)) (l r : MultiIndex) (bound : w.length+jetOrder l+jetOrder r ≤ degree scope) : Interval :=
   match w with
   | [] => pairs (jetFor scope l (by simpa using Nat.le_trans (Nat.le_add_right _ _) bound))
       (jetFor scope r (by simpa using Nat.le_trans (Nat.le_add_left _ _) bound))
   | a :: rest => addInteger
       (wordInteger scope pairs rest (raise l a) r (by simp only [List.length_cons,jetOrder_raise] at *; omega))
       (wordInteger scope pairs rest l (raise r a) (by simp only [List.length_cons,jetOrder_raise] at *; omega))

 theorem wordInteger_contains (scope : Scope) (pairs : Fin (jetCount scope) → Fin (jetCount scope) → Interval)
    (x : Point) (contains : ∀ j k, Holds (grid (pairs j k))
      (bilinear sourceTerms densityMatrix (jetMulti (prefixJet (count_le scope) j))
        (jetMulti (prefixJet (count_le scope) k)) x))
    (w : List (Fin 3)) (l r : MultiIndex) (bound : w.length+jetOrder l+jetOrder r ≤ degree scope) :
    Holds (grid (wordInteger scope pairs w l r bound)) (Taylor.wordJet w l r x) := by
   induction w generalizing l r with
   | nil =>
       dsimp only [wordInteger,Taylor.wordJet]
       have h := contains (jetFor scope l (by simpa using Nat.le_trans (Nat.le_add_right _ _) bound))
         (jetFor scope r (by simpa using Nat.le_trans (Nat.le_add_left _ _) bound))
       simpa only [jetFor_recovers] using h
   | cons a rest ih =>
       dsimp only [wordInteger,Taylor.wordJet]
       rw [grid_add]
       exact add_holds _ _ _ _ (ih _ _ _) (ih _ _ _)

 theorem jetWord_length (m : MultiIndex) : (Taylor.jetWord m).length = jetOrder m := by
   simp only [Taylor.jetWord,List.length_append,List.length_replicate,jetOrder]

 def densityInteger (scope : Scope) (pairs : Fin (jetCount scope) → Fin (jetCount scope) → Interval)
    (j : Fin (jetCount scope)) : Interval :=
   wordInteger scope pairs (Taylor.jetWord (jetMulti (prefixJet (count_le scope) j))) zeroJet zeroJet
     (by simpa only [jetWord_length,show jetOrder zeroJet = 0 from rfl,Nat.add_zero] using prefix_degree scope j)

 theorem densityInteger_contains (scope : Scope) (pairs : Fin (jetCount scope) → Fin (jetCount scope) → Interval)
    (x : Point) (contains : ∀ j k, Holds (grid (pairs j k))
      (bilinear sourceTerms densityMatrix (jetMulti (prefixJet (count_le scope) j))
        (jetMulti (prefixJet (count_le scope) k)) x)) (j : Fin (jetCount scope)) :
    Holds (grid (densityInteger scope pairs j)) (Taylor.sourceJet (prefixJet (count_le scope) j) x) :=
   wordInteger_contains scope pairs x contains _ _ _ _

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
