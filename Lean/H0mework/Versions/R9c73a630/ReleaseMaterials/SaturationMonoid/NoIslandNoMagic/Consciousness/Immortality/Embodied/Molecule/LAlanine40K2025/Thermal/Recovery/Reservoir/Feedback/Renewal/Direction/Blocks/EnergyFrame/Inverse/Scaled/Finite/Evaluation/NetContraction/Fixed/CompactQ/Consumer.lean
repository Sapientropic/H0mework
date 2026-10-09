import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.CompactQ.Energy

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Powered.Dynamics
open scoped Matrix BigOperators
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _
def compactGainQ (k : Sym2 Basis) : ℚ :=
  let p := Sym2.sortEquiv k
  if same : p.val.1=p.val.2 then
    if donor : p.val.1=97 then donorCompactGainQ
    else diagonalCompactGainQ p.val.1 donor
  else ordinaryCompactGainQ p.val.1 p.val.2 same

theorem compact_gain_original (k : Sym2 Basis) : compactGainQ k=smallGainQ k := by
  let p := Sym2.sortEquiv k
  have original : s(p.val.1,p.val.2)=k := Sym2.sortEquiv.symm_apply_apply k
  change (if same : p.val.1=p.val.2 then
    if donor : p.val.1=97 then donorCompactGainQ
    else diagonalCompactGainQ p.val.1 donor
    else ordinaryCompactGainQ p.val.1 p.val.2 same)=smallGainQ k
  split_ifs with same donor
  · have source : s((97 : Basis),97)=k := by simpa only [← same,donor] using original
    rw [← source]
    exact donor_compact_gain_original
  · have source : s(p.val.1,p.val.1)=k := by simpa only [← same] using original
    rw [← source]
    exact diagonal_compact_gain_original p.val.1 donor
  · rw [← original]
    exact ordinary_compact_gain_original p.val.1 p.val.2 same

theorem original_net_compact_sum : Spec.netGain=∑ k : Sym2 Basis, compactGainQ k := by
  rw [net_gain_small_sum]
  simp only [compact_gain_original]

theorem original_compact_net_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-
      Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      ((∑ k : Sym2 Basis, compactGainQ k : ℚ) : ℝ)| ≤ (109/10^7 : ℝ) := by
  rw [← original_net_compact_sum]
  exact Spec.original_rational_net_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
