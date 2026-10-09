import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Quartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Bound

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel SourceFiniteData SourceExponential SourceCoulomb GlobalSource
open GaussianPair Laplace.Axis
open scoped BigOperators
noncomputable section

def addressMajorant (a : Nat) : ℚ :=
  pairMajorant (targetLeft a) (targetRight a)

theorem addressMajorant_nonneg (a : Nat) : 0 ≤ addressMajorant a :=
  pairMajorant_nonneg _ _

noncomputable def sourceCoefficientAbs (a : Nat) : ℚ :=
  |sourceCoefficientAt (Fin.ofNat 4851 a)|

noncomputable def reportCoefficientAbs (a : Nat) : ℚ :=
  |reportCoefficientAt (Fin.ofNat 4851 a)|

theorem sourceCoefficientAbs_nonneg (a : Nat) : 0 ≤ sourceCoefficientAbs a :=
  abs_nonneg _

theorem reportCoefficientAbs_nonneg (a : Nat) : 0 ≤ reportCoefficientAbs a :=
  abs_nonneg _

noncomputable def weightEntry (a : Nat) : ℚ × ℚ × ℚ × ℚ :=
  (addressMajorant a, addressMajorant a,
    sourceCoefficientAbs a * addressMajorant a,
    reportCoefficientAbs a * addressMajorant a)

def weightStep (acc x : ℚ × ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ × ℚ :=
  (acc.1 + x.1, max acc.2.1 x.2.1, acc.2.2.1 + x.2.2.1, acc.2.2.2 + x.2.2.2)

noncomputable def weightBlock (start len : Nat) : ℚ × ℚ × ℚ × ℚ :=
  ((List.range' start len).map weightEntry).foldl weightStep (0, 0, 0, 0)

private theorem le_foldl_max {α : Type*} [LinearOrder α] (l : List α) (init x : α)
    (h : x ≤ init ∨ x ∈ l) : x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil =>
      rcases h with hle | hmem
      · exact hle
      · exact absurd hmem List.not_mem_nil
  | cons y ys ih =>
      rw [List.foldl_cons]
      apply ih
      rcases h with hle | hmem
      · exact Or.inl (hle.trans (le_max_left _ _))
      · rcases List.mem_cons.mp hmem with hEq | hTail
        · exact Or.inl (hEq ▸ le_max_right _ _)
        · exact Or.inr hTail

private theorem foldl_max_eq_max (l : List ℚ) (init : ℚ) (hinit : 0 ≤ init)
    (hn : ∀ x ∈ l, 0 ≤ x) :
    l.foldl max init = max init (l.foldl max 0) := by
  induction l generalizing init with
  | nil =>
      simp only [List.foldl_nil]
      exact (max_eq_left hinit).symm
  | cons x xs ih =>
      have hx : 0 ≤ x := hn x List.mem_cons_self
      have hxs : ∀ y ∈ xs, 0 ≤ y :=
        fun y hy => hn y (List.mem_cons_of_mem x hy)
      simp only [List.foldl_cons]
      rw [ih (max init x) (le_trans hinit (le_max_left _ _)) hxs,
        ih (max 0 x) (le_max_left _ _) hxs, max_eq_right hx, max_assoc]

private theorem zero_le_foldl_max (l : List ℚ) (init : ℚ) (hinit : 0 ≤ init)
    (hn : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih (max init x) (le_trans hinit (le_max_left _ _))
        (fun y hy => hn y (List.mem_cons_of_mem x hy))

private theorem foldl_weightStep (l : List Nat) (init : ℚ × ℚ × ℚ × ℚ)
    (hinit : 0 ≤ init.2.1) :
    (l.map weightEntry).foldl weightStep init =
      (init.1 + (l.map fun a => (weightEntry a).1).sum,
        max init.2.1 ((l.map fun a => (weightEntry a).2.1).foldl max 0),
        init.2.2.1 + (l.map fun a => (weightEntry a).2.2.1).sum,
        init.2.2.2 + (l.map fun a => (weightEntry a).2.2.2).sum) := by
  induction l generalizing init with
  | nil =>
      obtain ⟨i1, i2, i3, i4⟩ := init
      simp only [List.map_nil, List.foldl_nil, List.sum_nil, Prod.mk.injEq]
      refine ⟨by simp, ?_, by simp, by simp⟩
      exact (max_eq_left hinit).symm
  | cons x xs ih =>
      have hpos : 0 ≤ (weightEntry x).2.1 := addressMajorant_nonneg x
      have hinit' : (0 : ℚ) ≤ (weightStep init (weightEntry x)).2.1 :=
        le_trans hinit (le_max_left _ _)
      have hxs : ∀ y ∈ xs.map (fun a => (weightEntry a).2.1), 0 ≤ y := by
        intro y hy
        rcases List.mem_map.mp hy with ⟨a, _, rfl⟩
        exact addressMajorant_nonneg a
      simp only [List.map_cons, List.foldl_cons, List.sum_cons]
      rw [ih _ hinit']
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show init.1 + (weightEntry x).1 + (xs.map fun a => (weightEntry a).1).sum =
          init.1 + ((weightEntry x).1 + (xs.map fun a => (weightEntry a).1).sum)
        ring
      · show max (max init.2.1 (weightEntry x).2.1)
            ((xs.map fun a => (weightEntry a).2.1).foldl max 0) =
          max init.2.1 (((weightEntry x).2.1 ::
            (xs.map fun a => (weightEntry a).2.1)).foldl max 0)
        rw [List.foldl_cons]
        rw [foldl_max_eq_max _ _ (le_max_left _ _) hxs,
          max_eq_right hpos, max_assoc]
      · show init.2.2.1 + (weightEntry x).2.2.1 +
            (xs.map fun a => (weightEntry a).2.2.1).sum =
          init.2.2.1 + ((weightEntry x).2.2.1 +
            (xs.map fun a => (weightEntry a).2.2.1).sum)
        ring
      · show init.2.2.2 + (weightEntry x).2.2.2 +
            (xs.map fun a => (weightEntry a).2.2.2).sum =
          init.2.2.2 + ((weightEntry x).2.2.2 +
            (xs.map fun a => (weightEntry a).2.2.2).sum)
        ring

theorem weightBlock_eq (start len : Nat) :
    weightBlock start len =
      (((List.range' start len).map fun a => (weightEntry a).1).sum,
        ((List.range' start len).map fun a => (weightEntry a).2.1).foldl max 0,
        ((List.range' start len).map fun a => (weightEntry a).2.2.1).sum,
        ((List.range' start len).map fun a => (weightEntry a).2.2.2).sum) := by
  unfold weightBlock
  rw [foldl_weightStep _ _ (le_refl (0 : ℚ))]
  simp only [Prod.mk.injEq]
  have h : (0 : ℚ) ≤ ((List.range' start len).map fun a =>
      (weightEntry a).2.1).foldl max 0 :=
    zero_le_foldl_max _ _ (le_refl 0) (fun y hy => by
      rcases List.mem_map.mp hy with ⟨a, _, rfl⟩
      exact addressMajorant_nonneg a)
  exact ⟨by simp, max_eq_right h, by simp, by simp⟩

private theorem entry_fst (a : Nat) : (weightEntry a).1 = addressMajorant a := rfl

private theorem entry_max (a : Nat) :
    (weightEntry a).2.1 = addressMajorant a := rfl

private theorem entry_source (a : Nat) :
    (weightEntry a).2.2.1 = sourceCoefficientAbs a * addressMajorant a := rfl

private theorem entry_report (a : Nat) :
    (weightEntry a).2.2.2 = reportCoefficientAbs a * addressMajorant a := rfl

theorem weightBlock_sum_eq (start len : Nat) :
    (weightBlock start len).1 =
      ((List.range' start len).map addressMajorant).sum := by
  rw [weightBlock_eq]
  show ((List.range' start len).map fun a => (weightEntry a).1).sum =
    ((List.range' start len).map addressMajorant).sum
  exact congrArg List.sum
    (List.map_congr_left (fun a _ => entry_fst a))

theorem weightBlock_max_eq (start len : Nat) :
    (weightBlock start len).2.1 =
      ((List.range' start len).map addressMajorant).foldl max 0 := by
  rw [weightBlock_eq]
  show ((List.range' start len).map fun a => (weightEntry a).2.1).foldl max 0 =
    ((List.range' start len).map addressMajorant).foldl max 0
  exact congrArg (fun l => l.foldl max 0)
    (List.map_congr_left (fun a _ => entry_max a))

theorem weightBlock_source_eq (start len : Nat) :
    (weightBlock start len).2.2.1 =
      ((List.range' start len).map fun a =>
        sourceCoefficientAbs a * addressMajorant a).sum := by
  rw [weightBlock_eq]
  show ((List.range' start len).map fun a => (weightEntry a).2.2.1).sum =
    ((List.range' start len).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum
  exact congrArg List.sum
    (List.map_congr_left (fun a _ => entry_source a))

theorem weightBlock_report_eq (start len : Nat) :
    (weightBlock start len).2.2.2 =
      ((List.range' start len).map fun a =>
        reportCoefficientAbs a * addressMajorant a).sum := by
  rw [weightBlock_eq]
  show ((List.range' start len).map fun a => (weightEntry a).2.2.2).sum =
    ((List.range' start len).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum
  exact congrArg List.sum
    (List.map_congr_left (fun a _ => entry_report a))

theorem addressMajorant_le_block_max (a start len : Nat)
    (h : a ∈ List.range' start len) :
    addressMajorant a ≤ (weightBlock start len).2.1 := by
  rw [weightBlock_max_eq]
  exact le_foldl_max _ _ _ (Or.inr (List.mem_map.mpr ⟨a, h, rfl⟩))

theorem addressMajorant_le_block_sum (a start len : Nat)
    (h : a ∈ List.range' start len) :
    addressMajorant a ≤ (weightBlock start len).1 := by
  rw [weightBlock_sum_eq]
  exact List.single_le_sum (fun x hx => by
    rcases List.mem_map.mp hx with ⟨b, _, rfl⟩
    exact addressMajorant_nonneg b) _
    (List.mem_map.mpr ⟨a, h, rfl⟩)

theorem weightBlock_report_sum_split (start n m : Nat) :
    ((List.range' start (n + m)).map fun a => (weightEntry a).2.2.2).sum =
      ((List.range' start n).map fun a => (weightEntry a).2.2.2).sum +
        ((List.range' (start + n) m).map fun a => (weightEntry a).2.2.2).sum := by
  rw [← List.range'_append]
  simp only [Nat.one_mul, List.map_append, List.sum_append]

def weightMerge (a b : ℚ × ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ × ℚ :=
  (a.1 + b.1, max a.2.1 b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

theorem weightBlock_split (start n m : Nat) :
    weightBlock start (n + m) =
      weightMerge (weightBlock start n) (weightBlock (start + n) m) := by
  rw [weightBlock_eq, weightBlock_eq, weightBlock_eq]
  unfold weightMerge
  rw [← List.range'_append]
  simp only [Nat.one_mul, List.map_append, List.sum_append, List.foldl_append]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  rw [foldl_max_eq_max _ _
    (le_foldl_max _ _ _ (Or.inl (le_refl _)))
    (fun x hx => by
      rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
      exact addressMajorant_nonneg a)]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
