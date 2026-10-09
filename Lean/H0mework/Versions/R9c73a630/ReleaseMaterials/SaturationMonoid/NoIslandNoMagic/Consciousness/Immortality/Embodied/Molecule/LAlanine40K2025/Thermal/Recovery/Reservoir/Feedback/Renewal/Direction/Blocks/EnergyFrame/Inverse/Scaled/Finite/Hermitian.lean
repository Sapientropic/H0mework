import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix
noncomputable section

theorem cast_hermitian {ι : Type*} (r i : Matrix ι ι ℚ)
    (symmetric : r.transpose=r) (skew : i.transpose= -i) : (cast r i).IsHermitian := by
  ext a b
  have hr := congrFun (congrFun symmetric a) b
  have hi := congrFun (congrFun skew a) b
  simp only [Matrix.transpose_apply,Matrix.neg_apply] at hr hi
  change star ((r b a : ℂ)+Complex.I*(i b a : ℂ))=(r a b : ℂ)+Complex.I*(i a b : ℂ)
  rw [hr,hi]
  simp only [star_add,star_mul,star_ratCast,Complex.star_def,Complex.conj_I,Rat.cast_neg,map_neg,map_ratCast]
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
