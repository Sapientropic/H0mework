import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Channels

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def ordinaryEnergy (a b : Basis) (distinct : a ≠ b) : ℝ :=
  channelEnergy s(a,b) (Scaled.Order.offDiagonalPCEEquiv a b distinct) (ordinaryFullEquiv a b distinct) ordinaryInjection

def diagonalEnergy (a : Basis) (different : a ≠ 97) : ℝ :=
  channelEnergy s(a,a) (Scaled.Order.diagonalPCEEquiv a) (diagonalFullEquiv a different) diagonalInjection

def donorEnergy : ℝ := channelEnergy s((97 : Basis),97) (Scaled.Order.diagonalPCEEquiv 97) donorFullEquiv donorInjection

theorem ordinary_energy_exact (a b : Basis) (distinct : a ≠ b) : programEnergy s(a,b)=ordinaryEnergy a b distinct :=
  original_channel_energy _ _ _ _ (ordinary_donor_injection a b distinct)

theorem diagonal_energy_exact (a : Basis) (different : a ≠ 97) : programEnergy s(a,a)=diagonalEnergy a different :=
  original_channel_energy _ _ _ _ (diagonal_donor_injection a different)

theorem donor_energy_exact : programEnergy s((97 : Basis),97)=donorEnergy :=
  original_channel_energy _ _ _ _ donor_donor_injection

def smallEnergy (k : Sym2 Basis) : ℝ :=
  let p := Sym2.sortEquiv k
  if same : p.val.1=p.val.2 then
    if donor : p.val.1=97 then donorEnergy else diagonalEnergy p.val.1 donor
  else ordinaryEnergy p.val.1 p.val.2 same

theorem small_energy_exact (k : Sym2 Basis) : programEnergy k=smallEnergy k := by
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

theorem full_small_program_exact : InputProducts.netGain=∑ k : Sym2 Basis, smallEnergy k := by
  rw [program_energy_exact]
  exact Finset.sum_congr rfl (fun k _ => small_energy_exact k)

theorem original_small_program_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      ∑ k : Sym2 Basis, smallEnergy k| ≤ (109/10^7 : ℝ) := by
  rw [← full_small_program_exact]
  exact InputProducts.original_computed_input_net_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
