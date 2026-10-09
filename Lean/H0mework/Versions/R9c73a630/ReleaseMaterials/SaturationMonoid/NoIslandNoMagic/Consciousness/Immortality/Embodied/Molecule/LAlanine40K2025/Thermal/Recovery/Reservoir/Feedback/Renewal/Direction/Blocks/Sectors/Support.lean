import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Sectors.Input

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
open Propagation.Interface Load.Source
open scoped Matrix ComplexOrder
noncomputable section

def activeSector (k : Sym2 Basis) : Sym2 (Sym2 Basis) := s(k,Spectral.Current.donorOrbit)

theorem activeSector_injective : Function.Injective activeSector := by
  intro a b equal
  unfold activeSector at equal
  rcases (Sym2.mk_eq_mk_iff (p := (a,Spectral.Current.donorOrbit))
    (q := (b,Spectral.Current.donorOrbit))).mp equal with direct | swapped
  · exact congrArg Prod.fst direct
  · have left := congrArg Prod.fst swapped
    have right := congrArg Prod.snd swapped
    exact left.trans right

/-- Only source donor support is used; coherence between distinct incoming sectors remains in the state. -/
theorem input_support_left (i j : PointerIndex)
    (outside : pointerOrbit i ∉ Set.range activeSector) : inputFour i j = 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change Source.received.joint (i.1.1,i.2) (j.1.1,j.2) * Source.donor i.1.2 j.1.2 = 0
      have donorOutside : pcOrbit i.1.2 ≠ Spectral.Current.donorOrbit := by
        intro same
        apply outside
        exact ⟨pcOrbit i.1.1,by simp only [activeSector,pointerOrbit,reservoirOrbit,Sum.elim_inl,same]⟩
      rw [Spectral.Current.donor_support _ _ (Or.inl donorOutside),mul_zero]
    | inr _ => rfl
  | inr i =>
    cases j <;> rfl

theorem supported_conjugation (U : Matrix.unitaryGroup PointerIndex ℂ)
    (kept : Preserves pointerOrbit (U : PointerJoint)) (i j : PointerIndex)
    (outside : pointerOrbit i ∉ Set.range activeSector) :
    Quantum.conjugation U inputFour i j = 0 := by
  rw [Quantum.conjugation_apply,Matrix.star_eq_conjTranspose,Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_apply]
  have zero : (∑ l, (U : PointerJoint) i l * inputFour l k) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    by_cases same : pointerOrbit i = pointerOrbit l
    · rw [input_support_left l k (by simpa only [← same] using outside),mul_zero]
    · rw [kept i l same,zero_mul]
  rw [zero,zero_mul]

theorem actual_nine_support (i j : PointerIndex)
    (outside : pointerOrbit i ∉ Set.range activeSector) : Weak.origin.joint i j = 0 := by
  rw [actual_nine_from_four]
  exact supported_conjugation nineAction nine_action_preserves i j outside

theorem actual_eleven_support (i j : PointerIndex)
    (outside : pointerOrbit i ∉ Set.range activeSector) : Weak.execution.joint i j = 0 := by
  rw [actual_eleven_from_four]
  exact supported_conjugation elevenAction eleven_action_preserves i j outside

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
