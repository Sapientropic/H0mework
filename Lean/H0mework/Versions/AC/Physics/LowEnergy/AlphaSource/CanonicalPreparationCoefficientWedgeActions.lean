import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrimitiveAction

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCoefficientBudget
open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra StageNineHolonomicField StageNineDynamicBreakingVacuum
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorYukawaMassSpectrum
open StageNineExteriorMotherLieRepresentation
open PreparationScalarCoordinates PreparationVacuumPrimitiveMatrix
open SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal
open scoped BigOperators
local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

abbrev Occupancy := Fin 4→SU7MotherIndex

def occupiedIndex (a : Occupancy) (h : Function.Injective a) : ExteriorBasisIndex 4 :=
  ⟨Finset.image a Finset.univ,(Finset.card_image_of_injective Finset.univ h).trans (Finset.card_fin 4)⟩

def occupiedRank (a : Occupancy) (h : Function.Injective a) (i : Fin 4) : Fin 4 :=
  ((occupiedIndex a h).val.orderIsoOfFin (occupiedIndex a h).prop).toEquiv.symm
    ⟨a i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

theorem occupiedRank_injective (a : Occupancy) (h : Function.Injective a) : Function.Injective (occupiedRank a h) := by
  intro i j equal
  apply h
  have same := congrArg (fun k => (((occupiedIndex a h).val.orderIsoOfFin (occupiedIndex a h).prop).toEquiv k).val) equal
  simpa [occupiedRank] using same

def occupiedPermutation (a : Occupancy) (h : Function.Injective a) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (occupiedRank a h) ⟨occupiedRank_injective a h,
    Finite.surjective_of_injective (occupiedRank_injective a h)⟩

def wedgeInteger (a : Occupancy) (output : ExteriorBasisIndex 4) : ℤ :=
  if h : Function.Injective a then
    if occupiedIndex a h=output then ((occupiedPermutation a h).sign : ℤ) else 0
  else 0

theorem basis_wedge_exact (a : Occupancy) (h : Function.Injective a) :
    (exteriorPower.ιMulti ℂ 4) (su7FundamentalBasis ∘ a)=
      (occupiedPermutation a h).sign • su7ExteriorBasis 4 (occupiedIndex a h) := by
  rw [su7ExteriorBasis,exteriorPower.basis_apply,exteriorPower.ιMulti_family]
  rw [← AlternatingMap.map_perm]
  congr 1
  funext i
  change su7FundamentalBasis (a i)=su7FundamentalBasis
    (((occupiedIndex a h).val.orderIsoOfFin (occupiedIndex a h).prop).toEquiv
      (occupiedRank a h i)).val
  simp [occupiedRank]

/-- Exact single-occupancy readback for the actual exterior basis, including repeated slots. -/
theorem wedgeInteger_source (a : Occupancy) (output : ExteriorBasisIndex 4) :
    (su7ExteriorBasis 4).repr ((exteriorPower.ιMulti ℂ 4) (su7FundamentalBasis ∘ a)) output=
      (wedgeInteger a output : ℂ) := by
  classical
  by_cases h : Function.Injective a
  · rw [basis_wedge_exact a h]
    rcases Int.units_eq_one_or (occupiedPermutation a h).sign with hs|hs <;>
      simp [wedgeInteger,h,hs,Module.Basis.repr_self,Finsupp.single_apply,apply_ite]
  · have zero : (exteriorPower.ιMulti ℂ 4) (su7FundamentalBasis ∘ a)=0 :=
      AlternatingMap.map_eq_zero_of_not_injective _ _ (fun injective => h (Function.Injective.of_comp injective))
    simp [zero,wedgeInteger,h]

def exteriorEntry (M : Matrix SU7MotherIndex SU7MotherIndex ℂ)
    (output input : ExteriorBasisIndex 4) : ℂ :=
  ∑ s : Fin 4,∑ j : SU7MotherIndex,M j (occupancy input s)*
    (wedgeInteger (Function.update (occupancy input) s j) output : ℂ)

theorem exteriorEntry_source (M : SU7MotherLieMatrix) (output input : ExteriorBasisIndex 4) :
    (su7ExteriorBasis 4).repr (exteriorBasisLieAction 4 M input) output=
      exteriorEntry M.val output input := by
  rw [source_slot_expansion]
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    wedgeInteger_source,exteriorEntry]

theorem scalarMotherLieAction_source (M : SU7MotherLieMatrix) (v : ScalarCoordinateCarrier)
    (output : ScalarBasisIndex) :
    scalarMotherLieAction M v output=
      ∑ input : ScalarBasisIndex,exteriorEntry M.val output input*v input := by
  unfold scalarMotherLieAction
  change ((su7ExteriorBasis 4).repr (∑ input : ScalarBasisIndex,
    (su7ExteriorBasis 4).repr (scalarCoordinateEquiv.symm v) input • exteriorBasisLieAction 4 M input)) output=_
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro input hi
  change (su7ExteriorBasis 4).repr (scalarCoordinateEquiv.symm v) input*
    (su7ExteriorBasis 4).repr (exteriorBasisLieAction 4 M input) output=_
  rw [exteriorEntry_source]
  have read : (su7ExteriorBasis 4).repr (scalarCoordinateEquiv.symm v) input=v input := by
    simp [scalarCoordinateEquiv]
  rw [read,mul_comm]

end LowEnergy.PreparationVacuumCoefficientBudget
