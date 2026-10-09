import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Carrier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.PairFiber
variable {α κ : Type*}

abbrev Fiber (label : α → κ) (k : κ) := {i // label i=k}
abbrev Sector (label : α → κ) (a b : κ) := {p : α × α // s(label p.1,label p.2)=s(a,b)}

def embed (label : α → κ) (a b : κ) :
    (Fiber label a × Fiber label b) ⊕ (Fiber label a × Fiber label b) → Sector label a b
  | .inl (x,y) => ⟨(x.val,y.val),congrArg₂ (fun u v => s(u,v)) x.property y.property⟩
  | .inr (x,y) => ⟨(y.val,x.val),(congrArg₂ (fun u v => s(u,v)) y.property x.property).trans Sym2.eq_swap⟩

theorem injective (label : α → κ) (a b : κ) (distinct : a ≠ b) : Function.Injective (embed label a b) := by
  intro x y same
  have values := congrArg Subtype.val same
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      exact congrArg Sum.inl (Prod.ext (Subtype.ext (congrArg Prod.fst values)) (Subtype.ext (congrArg Prod.snd values)))
    | inr y =>
      exact False.elim (distinct (x.1.property.symm.trans ((congrArg label (congrArg Prod.fst values)).trans y.2.property)))
  | inr x =>
    cases y with
    | inl y =>
      exact False.elim (distinct (y.1.property.symm.trans ((congrArg label (congrArg Prod.fst values)).symm.trans x.2.property)))
    | inr y =>
      exact congrArg Sum.inr (Prod.ext (Subtype.ext (congrArg Prod.snd values)) (Subtype.ext (congrArg Prod.fst values)))

theorem surjective (label : α → κ) (a b : κ) : Function.Surjective (embed label a b) := by
  intro p
  rcases Sym2.eq_iff.mp p.property with h | h
  · exact ⟨.inl (⟨p.val.1,h.1⟩,⟨p.val.2,h.2⟩),Subtype.ext rfl⟩
  · exact ⟨.inr (⟨p.val.2,h.2⟩,⟨p.val.1,h.1⟩),Subtype.ext rfl⟩

noncomputable def offDiagonal (label : α → κ) (a b : κ) (distinct : a ≠ b) :
    (Fiber label a × Fiber label b) ⊕ (Fiber label a × Fiber label b) ≃ Sector label a b :=
  Equiv.ofBijective (embed label a b) ⟨injective label a b distinct,surjective label a b⟩

def diagonalEmbed (label : α → κ) (a : κ) (p : Fiber label a × Fiber label a) : Sector label a a :=
  ⟨(p.1.val,p.2.val),congrArg₂ (fun u v => s(u,v)) p.1.property p.2.property⟩

theorem diagonal_injective (label : α → κ) (a : κ) : Function.Injective (diagonalEmbed label a) := by
  intro x y same
  have values := congrArg Subtype.val same
  exact Prod.ext (Subtype.ext (congrArg Prod.fst values)) (Subtype.ext (congrArg Prod.snd values))

theorem diagonal_surjective (label : α → κ) (a : κ) : Function.Surjective (diagonalEmbed label a) := by
  intro p
  have both : label p.val.1=a ∧ label p.val.2=a := by
    rcases Sym2.eq_iff.mp p.property with h | h <;> exact h
  exact ⟨(⟨p.val.1,both.1⟩,⟨p.val.2,both.2⟩),Subtype.ext rfl⟩

noncomputable def diagonal (label : α → κ) (a : κ) : Fiber label a × Fiber label a ≃ Sector label a a :=
  Equiv.ofBijective (diagonalEmbed label a) ⟨diagonal_injective label a,diagonal_surjective label a⟩

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.PairFiber
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
