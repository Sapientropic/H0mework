import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.Matter.SU7ExteriorMatterRepresentation

/-!
# Actual P286 restriction and exterior-matter branching

This module restricts the actual `Λ⁶ V ⊕ Λ² V ⊕ Λ⁴ V` SU(7) action along
P286's concrete `diag(C,W,z,z⁻¹)` monomorphism.  The U(1) characters are proved
on the exterior basis for arbitrary `z : Circle`; weight and branching
multiplicities are then counted from those same finite basis fibers.

No P458 hypercharge table, P508 canonical carrier, P523 receipt, stored
chirality Boolean, or hand-entered branching multiplicity is used.  The final
comparison with `17` is deliberately downstream of the representation result.
-/

namespace SaturationMonoid.PhysicsCore.SU7ExteriorMatterRestriction

open Matrix
open Set
open GaugeProjection
open GaugeProjection.ConcreteBlockDiagonal
open SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation
open Module

open scoped TensorProduct

noncomputable section

local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

abbrev P286ResidualGaugeGroup := StandardModelGaugeGroup

/-- Actual restriction of every exterior SU(7) action along P286's concrete
`diag(C,W,z,z⁻¹)` monomorphism. -/
def p286RestrictedExteriorRepresentation (degree : ℕ) :
    Representation ℂ P286ResidualGaugeGroup
      (⋀[ℂ]^degree SU7FundamentalCarrier) :=
  (su7ExteriorPowerRepresentation degree).comp blockDiagonalSMBlock

def p286RestrictedExteriorSpinorMatterRepresentation :
    Representation ℂ P286ResidualGaugeGroup
      SU7ExteriorSpinorMatterCarrier :=
  su7ExteriorSpinorMatterRepresentation.comp blockDiagonalSMBlock

@[simp]
theorem p286RestrictedExteriorRepresentation_apply
    (degree : ℕ) (groupElement : P286ResidualGaugeGroup) :
    p286RestrictedExteriorRepresentation degree groupElement =
      su7ExteriorPowerRepresentation degree
        (blockDiagonalSMBlock groupElement) := rfl

def quarterTurn : Circle :=
  ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

def p286HyperchargeElement (z : Circle) : StandardModelGaugeGroup :=
  (1, 1, z)

def embeddedP286HyperchargeElement (z : Circle) : SU7MotherGroup :=
  blockDiagonalSMBlock (p286HyperchargeElement z)

def hyperchargeQuarterTurn : SU7MotherGroup :=
  embeddedP286HyperchargeElement quarterTurn

def fundamentalHyperchargeWeight : SU7MotherIndex → ℤ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr _)) => -1

def fundamentalHyperchargeCharacter (z : Circle)
    (index : SU7MotherIndex) : Circle :=
  z ^ fundamentalHyperchargeWeight index

def su7FundamentalBasis :
    Basis SU7MotherIndex ℂ SU7FundamentalCarrier :=
  Pi.basisFun ℂ SU7MotherIndex

theorem p286Hypercharge_fundamental_basis
    (z : Circle) (index : SU7MotherIndex) :
    su7FundamentalRepresentation (embeddedP286HyperchargeElement z)
        (su7FundamentalBasis index) =
      (fundamentalHyperchargeCharacter z index : ℂ) •
        su7FundamentalBasis index := by
  funext row
  fin_cases index <;> fin_cases row <;>
    simp [su7FundamentalRepresentation, embeddedP286HyperchargeElement,
      p286HyperchargeElement, su7FundamentalBasis,
      fundamentalHyperchargeCharacter, fundamentalHyperchargeWeight,
      blockDiagonalSMBlock, rawBlockDiagonal, weakHyperchargeBlock,
      hyperchargePairBlock, scalarOneBlock,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]

theorem hyperchargeQuarterTurn_fundamental_basis
    (index : SU7MotherIndex) :
    su7FundamentalRepresentation hyperchargeQuarterTurn
        (su7FundamentalBasis index) =
      (fundamentalHyperchargeCharacter quarterTurn index : ℂ) •
        su7FundamentalBasis index := by
  exact p286Hypercharge_fundamental_basis quarterTurn index

abbrev ExteriorBasisIndex (degree : ℕ) :=
  Set.powersetCard SU7MotherIndex degree

def su7ExteriorBasis (degree : ℕ) :
    Basis (ExteriorBasisIndex degree) ℂ
      (⋀[ℂ]^degree SU7FundamentalCarrier) :=
  su7FundamentalBasis.exteriorPower degree

def exteriorHyperchargeWeight {degree : ℕ}
    (index : ExteriorBasisIndex degree) : ℤ :=
  ∑ i ∈ index.1, fundamentalHyperchargeWeight i

def exteriorHyperchargeCharacter (z : Circle) {degree : ℕ}
    (index : ExteriorBasisIndex degree) : Circle :=
  ∏ position : Fin degree,
    fundamentalHyperchargeCharacter z
      (Set.powersetCard.ofFinEmbEquiv.symm index position)

def exteriorPositionEquiv {degree : ℕ}
    (index : ExteriorBasisIndex degree) :
    Fin degree ≃ {basisIndex // basisIndex ∈ index.1} :=
  Equiv.ofBijective
    (fun position =>
      ⟨Set.powersetCard.ofFinEmbEquiv.symm index position,
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem index _).mp
          ⟨position, rfl⟩⟩)
    (by
      constructor
      · intro first second heq
        apply (Set.powersetCard.ofFinEmbEquiv.symm index).injective
        exact congrArg Subtype.val heq
      · rintro ⟨basisIndex, hbasisIndex⟩
        rcases
            (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
              index basisIndex).mpr hbasisIndex with
          ⟨position, hposition⟩
        exact ⟨position, Subtype.ext hposition⟩)

theorem exteriorPosition_sum_eq_subset_sum {degree : ℕ}
    (index : ExteriorBasisIndex degree) (value : SU7MotherIndex → ℤ) :
    (∑ position : Fin degree,
        value (Set.powersetCard.ofFinEmbEquiv.symm index position)) =
      ∑ basisIndex ∈ index.1, value basisIndex := by
  calc
    _ = ∑ basisIndex : {basisIndex // basisIndex ∈ index.1},
          value basisIndex :=
      (exteriorPositionEquiv index).sum_comp
        (fun basisIndex => value basisIndex)
    _ = _ := (Finset.sum_subtype index.1 (by simp) value).symm

theorem exteriorPosition_prod_eq_subset_prod {degree : ℕ}
    (index : ExteriorBasisIndex degree) (value : SU7MotherIndex → Circle) :
    (∏ position : Fin degree,
        value (Set.powersetCard.ofFinEmbEquiv.symm index position)) =
      ∏ basisIndex ∈ index.1, value basisIndex := by
  calc
    _ = ∏ basisIndex : {basisIndex // basisIndex ∈ index.1},
          value basisIndex :=
      (exteriorPositionEquiv index).prod_comp
        (fun basisIndex => value basisIndex)
    _ = _ := (Finset.prod_subtype index.1 (by simp) value).symm

theorem exteriorHyperchargeCharacter_eq_zpow
    (z : Circle) {degree : ℕ} (index : ExteriorBasisIndex degree) :
    exteriorHyperchargeCharacter z index =
      z ^ exteriorHyperchargeWeight index := by
  change
    (∏ position : Fin degree,
        z ^ fundamentalHyperchargeWeight
          (Set.powersetCard.ofFinEmbEquiv.symm index position)) =
      z ^ ∑ basisIndex ∈ index.1,
        fundamentalHyperchargeWeight basisIndex
  rw [exteriorPosition_prod_eq_subset_prod index
    (fun basisIndex => z ^ fundamentalHyperchargeWeight basisIndex)]
  induction index.1 using Finset.induction_on with
  | empty => simp
  | @insert basisIndex subset hnotmem inductionHypothesis =>
      simp only [Finset.prod_insert, hnotmem, not_false_eq_true,
        Finset.sum_insert, inductionHypothesis]
      exact (_root_.zpow_add z
        (fundamentalHyperchargeWeight basisIndex)
        (∑ basisIndex ∈ subset,
          fundamentalHyperchargeWeight basisIndex)).symm

theorem p286Hypercharge_exterior_basis
    (z : Circle) (degree : ℕ) (index : ExteriorBasisIndex degree) :
    su7ExteriorPowerRepresentation degree (embeddedP286HyperchargeElement z)
        (su7ExteriorBasis degree index) =
      (exteriorHyperchargeCharacter z index : ℂ) •
        su7ExteriorBasis degree index := by
  change
    exteriorPower.map degree
        (su7FundamentalRepresentation (embeddedP286HyperchargeElement z))
        (su7ExteriorBasis degree index) = _
  rw [su7ExteriorBasis, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family]
  change
    exteriorPower.ιMulti ℂ degree
        (fun position =>
          su7FundamentalRepresentation (embeddedP286HyperchargeElement z)
            (su7FundamentalBasis
              (Set.powersetCard.ofFinEmbEquiv.symm index position))) = _
  have hpointwise :
      (fun position =>
          su7FundamentalRepresentation (embeddedP286HyperchargeElement z)
            (su7FundamentalBasis
              (Set.powersetCard.ofFinEmbEquiv.symm index position))) =
        (fun position =>
          (fundamentalHyperchargeCharacter z
              (Set.powersetCard.ofFinEmbEquiv.symm index position) : ℂ) •
            su7FundamentalBasis
              (Set.powersetCard.ofFinEmbEquiv.symm index position)) := by
    funext position
    exact p286Hypercharge_fundamental_basis z _
  rw [hpointwise, (exteriorPower.ιMulti ℂ degree).map_smul_univ]
  change
    (∏ position : Fin degree,
        (fundamentalHyperchargeCharacter z
          (Set.powersetCard.ofFinEmbEquiv.symm index position) : ℂ)) •
        exteriorPower.ιMulti ℂ degree
          (fun position =>
            su7FundamentalBasis
              (Set.powersetCard.ofFinEmbEquiv.symm index position)) =
      ((∏ position : Fin degree,
          fundamentalHyperchargeCharacter z
            (Set.powersetCard.ofFinEmbEquiv.symm index position) : Circle) : ℂ) •
        exteriorPower.ιMulti ℂ degree
          (fun position =>
            su7FundamentalBasis
              (Set.powersetCard.ofFinEmbEquiv.symm index position))
  congr 1
  change
    (∏ position ∈ (Finset.univ : Finset (Fin degree)),
        Circle.coeHom
          (fundamentalHyperchargeCharacter z
            (Set.powersetCard.ofFinEmbEquiv.symm index position))) =
      Circle.coeHom
        (∏ position ∈ (Finset.univ : Finset (Fin degree)),
          fundamentalHyperchargeCharacter z
            (Set.powersetCard.ofFinEmbEquiv.symm index position))
  exact
    (map_prod Circle.coeHom
      (fun position : Fin degree =>
        fundamentalHyperchargeCharacter z
          (Set.powersetCard.ofFinEmbEquiv.symm index position))
      Finset.univ).symm

/-- Weight-form action theorem for the actual P286-restricted representation.
The integer weight is derived from the exterior basis subset. -/
theorem p286RestrictedHypercharge_exterior_basis_weight
    (z : Circle) (degree : ℕ) (index : ExteriorBasisIndex degree) :
    p286RestrictedExteriorRepresentation degree (p286HyperchargeElement z)
        (su7ExteriorBasis degree index) =
      ((z ^ exteriorHyperchargeWeight index : Circle) : ℂ) •
        su7ExteriorBasis degree index := by
  change
    su7ExteriorPowerRepresentation degree (embeddedP286HyperchargeElement z)
        (su7ExteriorBasis degree index) = _
  calc
    _ = (exteriorHyperchargeCharacter z index : ℂ) •
          su7ExteriorBasis degree index :=
      p286Hypercharge_exterior_basis z degree index
    _ = _ := by rw [exteriorHyperchargeCharacter_eq_zpow]

theorem hyperchargeQuarterTurn_exterior_basis
    (degree : ℕ) (index : ExteriorBasisIndex degree) :
    su7ExteriorPowerRepresentation degree hyperchargeQuarterTurn
        (su7ExteriorBasis degree index) =
      (exteriorHyperchargeCharacter quarterTurn index : ℂ) •
        su7ExteriorBasis degree index := by
  exact p286Hypercharge_exterior_basis quarterTurn degree index

def exteriorHyperchargeBasisFiber (degree : ℕ) (weight : ℤ) :
    Finset (Finset SU7MotherIndex) :=
  (Finset.univ.powersetCard degree).filter fun subset =>
    (∑ index ∈ subset, fundamentalHyperchargeWeight index) = weight

/-- Multiplicity is counted by exhaustive fibers of the same exterior basis
used by `hyperchargeQuarterTurn_exterior_basis`; it is not a stored table. -/
def exteriorHyperchargeMultiplicity (degree : ℕ) (weight : ℤ) : ℕ :=
  (exteriorHyperchargeBasisFiber degree weight).card

theorem exteriorWeightFiber_card_table :
    exteriorHyperchargeMultiplicity 6 (-1) = 1 ∧
    exteriorHyperchargeMultiplicity 6 0 = 5 ∧
    exteriorHyperchargeMultiplicity 6 1 = 1 ∧
    exteriorHyperchargeMultiplicity 2 (-1) = 5 ∧
    exteriorHyperchargeMultiplicity 2 0 = 11 ∧
    exteriorHyperchargeMultiplicity 2 1 = 5 ∧
    exteriorHyperchargeMultiplicity 4 (-1) = 10 ∧
    exteriorHyperchargeMultiplicity 4 0 = 15 ∧
    exteriorHyperchargeMultiplicity 4 1 = 10 := by
  decide

def exteriorSpinorHyperchargeMultiplicity (weight : ℤ) : ℕ :=
  ∑ degreeIndex : Fin 3,
    exteriorHyperchargeMultiplicity
      (exteriorSpinorDegree degreeIndex) weight

theorem exteriorSpinorHyperchargeMultiplicity_table :
    exteriorSpinorHyperchargeMultiplicity (-1) = 16 ∧
      exteriorSpinorHyperchargeMultiplicity 0 = 31 ∧
      exteriorSpinorHyperchargeMultiplicity 1 = 16 := by
  decide

theorem exteriorSpinorHyperchargeMultiplicity_total :
    exteriorSpinorHyperchargeMultiplicity (-1) +
        exteriorSpinorHyperchargeMultiplicity 0 +
        exteriorSpinorHyperchargeMultiplicity 1 = 63 := by
  decide

/-! ## Branching multiplicities from actual exterior-basis fibers -/

inductive ResidualColorType where
  | singlet
  | fundamental
  | antifundamental
  deriving DecidableEq, Repr, FintypeViaProxy

inductive ResidualWeakType where
  | singlet
  | doublet
  deriving DecidableEq, Repr, FintypeViaProxy

inductive ResidualHypercharge where
  | negative
  | neutral
  | positive
  deriving DecidableEq, Repr, FintypeViaProxy

namespace ResidualHypercharge

def toInt : ResidualHypercharge → ℤ
  | .negative => -1
  | .neutral => 0
  | .positive => 1

def conjugate : ResidualHypercharge → ResidualHypercharge
  | .negative => .positive
  | .neutral => .neutral
  | .positive => .negative

end ResidualHypercharge

namespace ResidualColorType

def dimension : ResidualColorType → ℕ
  | .singlet => 1
  | .fundamental => 3
  | .antifundamental => 3

def conjugate : ResidualColorType → ResidualColorType
  | .singlet => .singlet
  | .fundamental => .antifundamental
  | .antifundamental => .fundamental

end ResidualColorType

namespace ResidualWeakType

def dimension : ResidualWeakType → ℕ
  | .singlet => 1
  | .doublet => 2

end ResidualWeakType

structure ResidualExteriorIrrepLabel where
  color : ResidualColorType
  weak : ResidualWeakType
  hypercharge : ResidualHypercharge
  deriving DecidableEq, Repr, FintypeViaProxy

def ResidualExteriorIrrepLabel.componentDimension
    (label : ResidualExteriorIrrepLabel) : ℕ :=
  label.color.dimension * label.weak.dimension

def ResidualExteriorIrrepLabel.conjugate
    (label : ResidualExteriorIrrepLabel) : ResidualExteriorIrrepLabel where
  color := label.color.conjugate
  weak := label.weak
  hypercharge := label.hypercharge.conjugate

def exteriorBasisColorDegree (subset : Finset SU7MotherIndex) : ℕ :=
  (Finset.univ.filter fun colorIndex : Fin 3 =>
    (Sum.inl colorIndex : SU7MotherIndex) ∈ subset).card

def exteriorBasisWeakDegree (subset : Finset SU7MotherIndex) : ℕ :=
  (Finset.univ.filter fun weakIndex : Fin 2 =>
    (Sum.inr (Sum.inl weakIndex) : SU7MotherIndex) ∈ subset).card

def exteriorBasisColorType
    (subset : Finset SU7MotherIndex) : ResidualColorType :=
  match exteriorBasisColorDegree subset with
  | 1 => .fundamental
  | 2 => .antifundamental
  | _ => .singlet

def exteriorBasisWeakType
    (subset : Finset SU7MotherIndex) : ResidualWeakType :=
  match exteriorBasisWeakDegree subset with
  | 1 => .doublet
  | _ => .singlet

def exteriorBranchComponentFiber (degree : ℕ)
    (label : ResidualExteriorIrrepLabel) :
    Finset (Finset SU7MotherIndex) :=
  (Finset.univ.powersetCard degree).filter fun subset =>
    exteriorBasisColorType subset = label.color ∧
      exteriorBasisWeakType subset = label.weak ∧
      (∑ basisIndex ∈ subset,
        fundamentalHyperchargeWeight basisIndex) =
          label.hypercharge.toInt

def exteriorBranchComponentCount (degree : ℕ)
    (label : ResidualExteriorIrrepLabel) : ℕ :=
  (exteriorBranchComponentFiber degree label).card

def exteriorSpinorBranchComponentCount
    (label : ResidualExteriorIrrepLabel) : ℕ :=
  ∑ degreeIndex : Fin 3,
    exteriorBranchComponentCount (exteriorSpinorDegree degreeIndex) label

/-- Irrep multiplicity is the actual exterior-basis component fiber divided by
the dimension of the residual `SU(3) × SU(2)` irrep. -/
def exteriorSpinorBranchingMultiplicity
    (label : ResidualExteriorIrrepLabel) : ℕ :=
  exteriorSpinorBranchComponentCount label / label.componentDimension

theorem exteriorSpinorBranchComponentCount_factorizes :
    ∀ label : ResidualExteriorIrrepLabel,
      exteriorSpinorBranchComponentCount label =
        exteriorSpinorBranchingMultiplicity label *
          label.componentDimension := by
  decide

theorem exteriorSpinorBranchingMultiplicity_table :
    exteriorSpinorBranchingMultiplicity
        ⟨.singlet, .singlet, .negative⟩ = 2 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.singlet, .singlet, .neutral⟩ = 3 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.singlet, .singlet, .positive⟩ = 2 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.singlet, .doublet, .negative⟩ = 1 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.singlet, .doublet, .neutral⟩ = 2 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.singlet, .doublet, .positive⟩ = 1 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.fundamental, .singlet, .negative⟩ = 2 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.fundamental, .singlet, .neutral⟩ = 0 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.fundamental, .singlet, .positive⟩ = 2 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.fundamental, .doublet, .negative⟩ = 0 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.fundamental, .doublet, .neutral⟩ = 2 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.fundamental, .doublet, .positive⟩ = 0 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.antifundamental, .singlet, .negative⟩ = 0 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.antifundamental, .singlet, .neutral⟩ = 4 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.antifundamental, .singlet, .positive⟩ = 0 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.antifundamental, .doublet, .negative⟩ = 1 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.antifundamental, .doublet, .neutral⟩ = 0 ∧
    exteriorSpinorBranchingMultiplicity
        ⟨.antifundamental, .doublet, .positive⟩ = 1 := by
  decide

/-- Closed readout of the basis-fiber computation.  This table does not define
the representation multiplicity; the following theorem proves it equal to the
actual quotient of component fibers and provides a small downstream rewrite
surface. -/
def exteriorSpinorBranchingReadout :
    ResidualExteriorIrrepLabel → ℕ
  | ⟨.singlet, .singlet, .negative⟩ => 2
  | ⟨.singlet, .singlet, .neutral⟩ => 3
  | ⟨.singlet, .singlet, .positive⟩ => 2
  | ⟨.singlet, .doublet, .negative⟩ => 1
  | ⟨.singlet, .doublet, .neutral⟩ => 2
  | ⟨.singlet, .doublet, .positive⟩ => 1
  | ⟨.fundamental, .singlet, .negative⟩ => 2
  | ⟨.fundamental, .singlet, .neutral⟩ => 0
  | ⟨.fundamental, .singlet, .positive⟩ => 2
  | ⟨.fundamental, .doublet, .negative⟩ => 0
  | ⟨.fundamental, .doublet, .neutral⟩ => 2
  | ⟨.fundamental, .doublet, .positive⟩ => 0
  | ⟨.antifundamental, .singlet, .negative⟩ => 0
  | ⟨.antifundamental, .singlet, .neutral⟩ => 4
  | ⟨.antifundamental, .singlet, .positive⟩ => 0
  | ⟨.antifundamental, .doublet, .negative⟩ => 1
  | ⟨.antifundamental, .doublet, .neutral⟩ => 0
  | ⟨.antifundamental, .doublet, .positive⟩ => 1

@[simp]
theorem exteriorSpinorBranchingMultiplicity_eq_readout
    (label : ResidualExteriorIrrepLabel) :
    exteriorSpinorBranchingMultiplicity label =
      exteriorSpinorBranchingReadout label := by
  rcases label with ⟨color, weak, hypercharge⟩
  cases color <;> cases weak <;> cases hypercharge <;> decide

theorem exteriorSpinorBranching_component_total :
    (∑ label : ResidualExteriorIrrepLabel,
      exteriorSpinorBranchingMultiplicity label *
        label.componentDimension) = 63 := by
  decide

/-- The actual normalizer pairing is visible after restriction: at fixed
non-Abelian type, charge `-1` and `+1` multiplicities agree. -/
theorem exteriorSpinorBranching_charge_pair
    (color : ResidualColorType) (weak : ResidualWeakType) :
    exteriorSpinorBranchingMultiplicity ⟨color, weak, .negative⟩ =
      exteriorSpinorBranchingMultiplicity ⟨color, weak, .positive⟩ := by
  cases color <;> cases weak <;> decide

def exteriorSpinorNetChirality
    (label : ResidualExteriorIrrepLabel) : ℤ :=
  (exteriorSpinorBranchingMultiplicity label : ℤ) -
    exteriorSpinorBranchingMultiplicity label.conjugate

def exteriorSpinorChiralRemainderMultiplicity
    (label : ResidualExteriorIrrepLabel) : ℕ :=
  exteriorSpinorBranchingMultiplicity label -
    exteriorSpinorBranchingMultiplicity label.conjugate

/-- Chirality is a readout, not a premise: two `(3,1)_{-1}` multiplets remain
after cancelling conjugate residual irreps. -/
theorem exteriorSpinor_actualResidualChirality :
    exteriorSpinorNetChirality
        ⟨.fundamental, .singlet, .negative⟩ = 2 ∧
      exteriorSpinorChiralRemainderMultiplicity
        ⟨.fundamental, .singlet, .negative⟩ = 2 := by
  decide

/-- Downstream comparison only: the representation-first result has 63 actual
components, so it is not the old canonical-17 carrier. -/
theorem exteriorSpinorBranching_component_total_ne_seventeen :
    (∑ label : ResidualExteriorIrrepLabel,
      exteriorSpinorBranchingMultiplicity label *
        label.componentDimension) ≠ 17 := by
  decide

end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterRestriction
