import H0mework.Physics.Matter.SU7ExteriorYukawaMassSpectrum

/-! Exact integer coordinates of the ORIGINAL joint scalar's whole Yukawa
map, not the legacy one-channel rank theorem or the two-channel window. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.JointMass
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum
open GaugeProjection.ConcreteBlockDiagonal
noncomputable section
local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

local instance (degree : ℕ) : Fintype (ExteriorBasisIndex degree) :=
  Fintype.ofFinset (Finset.univ.powersetCard degree) (by
    intro subset
    simp [ExteriorBasisIndex, Set.powersetCard])

def wedgeCoefficient (out : ExteriorBasisIndex 6) (inp : ExteriorBasisIndex 2)
    (scalar : ExteriorBasisIndex 4) : ℤ :=
  if h : Disjoint inp.1 scalar.1 then
    if Set.powersetCard.disjUnion h = out then
      ((Set.powersetCard.permOfDisjoint h).sign : ℤ) else 0
  else 0

theorem wedgeCoefficient_actual (out : ExteriorBasisIndex 6) (inp : ExteriorBasisIndex 2)
    (scalar : ExteriorBasisIndex 4) :
    (su7ExteriorBasis 6).coord out
      (exteriorYukawaMassMap (su7ExteriorBasis 4 scalar) (su7ExteriorBasis 2 inp)) =
        (wedgeCoefficient out inp scalar : ℂ) := by
  by_cases h : Disjoint inp.1 scalar.1
  · rw [exteriorYukawaMassMap_basisPair_of_disjoint inp scalar h]
    simp [wedgeCoefficient, h, Finsupp.single_apply, Units.smul_def, eq_comm]
  · rw [exteriorYukawaMassMap_basisPair_of_not_disjoint inp scalar h]
    simp [wedgeCoefficient, h]

def coefficient (out : ExteriorBasisIndex 6) (inp : ExteriorBasisIndex 2) : ℤ :=
  ∑ o : Fin 2, ∑ i : Fin 2, wedgeCoefficient out inp (finiteGenerationScalarIndex o i)

theorem coefficient_actual (out : ExteriorBasisIndex 6) (inp : ExteriorBasisIndex 2) :
    (su7ExteriorBasis 6).coord out
      (exteriorYukawaMassMap finiteGenerationJointBreakingScalar (su7ExteriorBasis 2 inp)) =
        (coefficient out inp : ℂ) := by
  simp only [finiteGenerationJointBreakingScalar, Fin.sum_univ_two,
    exteriorYukawaMassMap_add_breaking, LinearMap.add_apply, map_add,
    finiteGenerationBreakingTensor, wedgeCoefficient_actual, coefficient, Int.cast_add]

def outputGram (left right : ExteriorBasisIndex 6) : ℤ :=
  ∑ inp : ExteriorBasisIndex 2, coefficient left inp * coefficient right inp

/-- The integer Gram formula is the exact Hermitian output Gram of the
original exterior mass map. Its numerical diagonalization is in the separate
exact-arithmetic receipt, not asserted as a kernel theorem here. -/
theorem outputGram_actual (left right : ExteriorBasisIndex 6) :
    (∑ inp : ExteriorBasisIndex 2,
      star ((su7ExteriorBasis 6).coord left
        (exteriorYukawaMassMap finiteGenerationJointBreakingScalar (su7ExteriorBasis 2 inp))) *
      ((su7ExteriorBasis 6).coord right
        (exteriorYukawaMassMap finiteGenerationJointBreakingScalar (su7ExteriorBasis 2 inp)))) =
        (outputGram left right : ℂ) := by
  simp only [coefficient_actual]
  simp [outputGram]

end
end SaturationMonoid.PhysicsCore.LowEnergy.JointMass
