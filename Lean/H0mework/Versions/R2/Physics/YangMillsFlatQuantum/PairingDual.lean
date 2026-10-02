import H0mework.Versions.R2.Physics.RootRuntime.RecoveryConsumer

/-! The source's independent dual retains its original spin exchange. This
explicit source operation precedes the physical inner-product readout. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.FullPairing

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF

noncomputable section

def flipMatter : Module.End ℂ DiracExteriorMatterCarrier where
  toFun matter spin := matter (Compatibility.spinFlip spin)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flipMatter_twice (matter : DiracExteriorMatterCarrier) :
    flipMatter (flipMatter matter) = matter := by
  funext spin
  exact congrArg matter (Compatibility.spinFlip_involutive spin)

theorem flipMatter_source (matter : DiracExteriorMatterCarrier) :
    flipMatter matter = diracMatrixMatterAction
      StageNineFullDiracAdjointMaterial.diracAdjointSpinSwap matter := by
  funext spin
  fin_cases spin <;>
    simp [flipMatter, Compatibility.spinFlip, diracMatrixMatterAction,
      StageNineFullDiracAdjointMaterial.diracAdjointSpinSwap, Fin.sum_univ_four]

theorem coordinates_flip (matter : DiracExteriorMatterCarrier) (index : Source.Index) :
    Compatibility.coordinates (flipMatter matter) (Compatibility.flip index) =
      Compatibility.coordinates matter index := by
  change sourceColorDoubletDual index.2
      (matter (Compatibility.spinFlip (Compatibility.spinFlip index.1))) = _
  rw [Compatibility.spinFlip_involutive]
  rfl

theorem dual_flip (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    actual.conjugateMatter point (flipMatter matter) =
      2 * (spinScale : ℂ) *
        ∑ index : Source.Index, star (Source.vector point index) *
          Compatibility.coordinates matter index := by
  rw [Compatibility.actual_dual_evaluation]
  simp_rw [Compatibility.dualCoefficient_source_star]
  simp [Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two,
    Compatibility.flip, Compatibility.spinFlip, Compatibility.coordinates, flipMatter]
  ring

end
end SaturationMonoid.PhysicsCore.YangMills.FullPairing
