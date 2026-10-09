import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.InputSlices

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Compact
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section
variable {β γ δ : Type*} [Fintype β] [Fintype δ]

def selectedNet (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k)
    (insert : β → δ) (select : γ → β) : Matrix γ γ ℂ :=
  let p := coordinatePointer k full
  let pc := (localPC k).submatrix p p
  let nine := (nineColumns k body full insert).submatrix id select
  let eleven := (elevenColumns k body full insert).submatrix id select
  eleven.conjTranspose*pc*eleven-nine.conjTranspose*pc*nine

theorem selected_net_exact (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k)
    (insert : β → δ) (select : γ → β) :
    (channelNet k body full insert).submatrix select select=selectedNet k body full insert select := by
  unfold channelNet
  rw [Matrix.submatrix_sub]
  simp only [Pi.sub_apply]
  rw [rectangular_corner,rectangular_corner]
  rfl

def ordinaryEnergy (a b : Basis) (distinct : a ≠ b) : ℝ :=
  Collision.energy (selectedNet s(a,b) (Scaled.Order.offDiagonalPCEEquiv a b distinct) (ordinaryFullEquiv a b distinct)
    ordinaryInjection chargedInjection) (Matrix.kronecker (originalPairBlock a b) Prepared.finiteEnvironment)

def diagonalEnergy (a : Basis) (different : a ≠ 97) : ℝ :=
  Collision.energy (selectedNet s(a,a) (Scaled.Order.diagonalPCEEquiv a) (diagonalFullEquiv a different)
    diagonalInjection (fun e => (1,e))) (InputProducts.pair (a,a) (a,a) • Prepared.finiteEnvironment)

def donorEnergy : ℝ :=
  Collision.energy (selectedNet s((97 : Basis),97) (Scaled.Order.diagonalPCEEquiv 97) donorFullEquiv
    donorInjection (fun e => (1,e))) (InputProducts.pair (97,97) (97,97) • Prepared.finiteEnvironment)

theorem ordinary_energy_exact (a b : Basis) (distinct : a ≠ b) : programEnergy s(a,b)=ordinaryEnergy a b distinct := by
  rw [original_channel_energy _ _ _ _ (ordinary_donor_injection a b distinct)]
  unfold channelEnergy
  rw [body_input_ordinary,charged_environment_energy,selected_net_exact]
  rfl

theorem diagonal_energy_exact (a : Basis) (different : a ≠ 97) : programEnergy s(a,a)=diagonalEnergy a different := by
  rw [original_channel_energy _ _ _ _ (diagonal_donor_injection a different)]
  unfold channelEnergy
  rw [body_input_diagonal,diagonal_charged_energy,selected_net_exact]
  rfl

theorem donor_energy_exact : programEnergy s((97 : Basis),97)=donorEnergy := by
  rw [original_channel_energy _ _ _ _ donor_donor_injection]
  unfold channelEnergy
  rw [body_input_diagonal,diagonal_charged_energy,selected_net_exact]
  rfl

def compactEnergy (k : Sym2 Basis) : ℝ :=
  let p := Sym2.sortEquiv k
  if same : p.val.1=p.val.2 then
    if donor : p.val.1=97 then donorEnergy else diagonalEnergy p.val.1 donor
  else ordinaryEnergy p.val.1 p.val.2 same

theorem compact_energy_exact (k : Sym2 Basis) : programEnergy k=compactEnergy k := by
  let p := Sym2.sortEquiv k
  have original : s(p.val.1,p.val.2)=k := Sym2.sortEquiv.symm_apply_apply k
  change programEnergy k=(if same : p.val.1=p.val.2 then
    if donor : p.val.1=97 then donorEnergy else diagonalEnergy p.val.1 donor
    else ordinaryEnergy p.val.1 p.val.2 same)
  split_ifs with same donor
  · have source : s((97 : Basis),97)=k := by simpa only [← same,donor] using original
    rw [← source]
    exact donor_energy_exact
  · have source : s(p.val.1,p.val.1)=k := by simpa only [← same] using original
    rw [← source]
    exact diagonal_energy_exact p.val.1 donor
  · rw [← original]
    exact ordinary_energy_exact p.val.1 p.val.2 same

theorem full_compact_program_exact : InputProducts.netGain=∑ k : Sym2 Basis, compactEnergy k := by
  rw [program_energy_exact]
  exact Finset.sum_congr rfl (fun k _ => compact_energy_exact k)

theorem original_compact_program_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      ∑ k : Sym2 Basis, compactEnergy k| ≤ (109/10^7 : ℝ) := by
  rw [← full_compact_program_exact]
  exact InputProducts.original_computed_input_net_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Compact
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
