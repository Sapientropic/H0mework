import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterEpsilonQt
import H0mework.Physics.SpinPair.ColorAction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore
open NamedMatterWedgeQt LowEnergy.Electromagnetic.Identification
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open StageNineHolonomicField StageNineP286GaugeConnectionVariation
open StageNineResidualLimitScalarBalanceClosure StageNineExteriorMotherLieRepresentation
open StageNineP286GaugeConnectionVariationDensity StageNineP286LinkedActiveLieRepresentation
open GaugeProjection.ConcreteBlockDiagonal
open scoped BigOperators Matrix
local instance : LinearOrder SU7MotherIndex:=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

def colorData(A:SU3BlockLieMatrix):P286LieBlockData:=(A,0,0)
def colorMother(A:SU3BlockLieMatrix):SU7MotherLieMatrix:=p286LieBlockEmbed (colorData A)

private theorem matter_enumeration(c:Fin 3)(position:Fin 2):
    Set.powersetCard.ofFinEmbEquiv.symm (Composite.matterBasis c) position=
      if position=0 then Sum.inl c else hyperPlusIndex:=by
  let family:Fin 2→SU7MotherIndex:=fun position=>if position=0 then Sum.inl c else hyperPlusIndex
  have hm(position:Fin 2):family position∈(Composite.matterBasis c).val:=by
    change family position∈{Sum.inl c,hyperPlusIndex}
    by_cases h:position=0 <;> simp [family,h]
  have he:family=(Composite.matterBasis c).val.orderEmbOfFin (Composite.matterBasis c).property:=by
    apply Finset.orderEmbOfFin_unique _ hm
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try (norm_num at hij)
    change smBlockIndexEquivFin7 (Sum.inl c)<smBlockIndexEquivFin7 hyperPlusIndex
    fin_cases c <;> decide
  exact (congrFun he position).symm

/-- All three named colors are restrictions of the original exterior degree-two mother basis. -/
theorem actual_matter_basis_wedge(c:Fin 3):
    su7ExteriorBasis 2 (Composite.matterBasis c)=
      (exteriorPower.ιMulti ℂ 2) ![su7FundamentalBasis (Sum.inl c),su7FundamentalBasis hyperPlusIndex]:=by
  rw [←exteriorBasisInput_wedge_eq_basis_slot]
  apply congrArg (exteriorPower.ιMulti ℂ 2)
  funext i
  fin_cases i <;> simp [exteriorBasisInput,exteriorPositionEquiv,matter_enumeration]

private theorem fundamental_basis_column(M:SU7MotherLieMatrix)(j:SU7MotherIndex):
    fundamentalMotherLieAction M (su7FundamentalBasis j)=fun i=>M.val i j:=by
  funext i
  simp [fundamentalMotherLieAction,su7FundamentalBasis,Matrix.mulVecLin,Matrix.mulVec,dotProduct,Pi.single_apply]

private theorem color_fundamental(A:SU3BlockLieMatrix)(c:Fin 3):
    fundamentalMotherLieAction (colorMother A) (su7FundamentalBasis (Sum.inl c))=
      ∑r:Fin 3,A.val r c • su7FundamentalBasis (Sum.inl r):=by
  rw [fundamental_basis_column]
  funext i
  cases i with
  | inl r => simp [colorMother,colorData,p286LieBlockEmbed,rawP286LieBlock,su7FundamentalBasis,Pi.single_apply]
  | inr r => simp [colorMother,colorData,p286LieBlockEmbed,rawP286LieBlock,su7FundamentalBasis]

private theorem color_plus_zero(A:SU3BlockLieMatrix):
    fundamentalMotherLieAction (colorMother A) (su7FundamentalBasis hyperPlusIndex)=0:=by
  rw [fundamental_basis_column]
  funext i
  cases i with
  | inl r => simp [colorMother,colorData,p286LieBlockEmbed,rawP286LieBlock,weakHyperchargeLieBlock,hyperchargeLieBlock,scalarLieBlock,hyperPlusIndex]
  | inr r =>
    cases r with
    | inl w => simp [colorMother,colorData,p286LieBlockEmbed,rawP286LieBlock,weakHyperchargeLieBlock,hyperchargeLieBlock,scalarLieBlock,hyperPlusIndex]
    | inr h => cases h <;> simp [colorMother,colorData,p286LieBlockEmbed,rawP286LieBlock,weakHyperchargeLieBlock,hyperchargeLieBlock,scalarLieBlock,hyperPlusIndex]

private def wedgeWithPlus:SU7FundamentalCarrier→ₗ[ℂ](⋀[ℂ]^2 SU7FundamentalCarrier) where
  toFun v:=(exteriorPower.ιMulti ℂ 2) ![v,su7FundamentalBasis hyperPlusIndex]
  map_add' _ _:=AlternatingMap.map_vecCons_add _ _ _ _
  map_smul' _ _:=AlternatingMap.map_vecCons_smul _ _ _ _

private theorem matter_slots(A:SU3BlockLieMatrix)(c:Fin 3):
    exteriorMotherLieAction 2 (colorMother A) (su7ExteriorBasis 2 (Composite.matterBasis c))=
      (exteriorPower.ιMulti ℂ 2)
        ![fundamentalMotherLieAction (colorMother A) (su7FundamentalBasis (Sum.inl c)),su7FundamentalBasis hyperPlusIndex]+
      (exteriorPower.ιMulti ℂ 2)
        ![su7FundamentalBasis (Sum.inl c),fundamentalMotherLieAction (colorMother A) (su7FundamentalBasis hyperPlusIndex)]:=by
  rw [actual_matter_basis_wedge,exteriorMotherLieAction_eq_slotDerivedAction,
    exteriorSlotDerivedAction_apply_ιMulti,Fin.sum_univ_two]
  congr 1

/-- The whole mother exterior column returns the actual three-color action; no complement or leakage is discarded. -/
theorem actual_color_exterior_column(A:SU3BlockLieMatrix)(c:Fin 3):
    exteriorMotherLieAction 2 (colorMother A) (su7ExteriorBasis 2 (Composite.matterBasis c))=
      ∑r:Fin 3,A.val r c • su7ExteriorBasis 2 (Composite.matterBasis r):=by
  rw [matter_slots,color_plus_zero]
  have hz:(exteriorPower.ιMulti ℂ 2) ![su7FundamentalBasis (Sum.inl c),0]=0:=
    (exteriorPower.ιMulti ℂ 2).map_coord_zero (1:Fin 2) rfl
  rw [hz,add_zero,color_fundamental]
  change wedgeWithPlus (∑r:Fin 3,A.val r c • su7FundamentalBasis (Sum.inl r))=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul,actual_matter_basis_wedge]
  rfl

end LowEnergy.NamedColorQtNext
