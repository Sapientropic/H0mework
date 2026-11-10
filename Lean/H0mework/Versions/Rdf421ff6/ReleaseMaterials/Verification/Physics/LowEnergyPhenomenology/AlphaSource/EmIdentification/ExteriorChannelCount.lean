import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceFiniteYukawaPrice

set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualSourceTensorPriceEnvelopeOwn
open SaturationMonoid.PhysicsCore SU7ExteriorMatterRestriction SU7MotherLieAlgebra
open StageNineDynamicBreakingVacuum
local instance : DecidableEq SU7MotherIndex := Classical.decEq _

def originalDisjointTwo (a : ScalarBasisIndex) :=
  {two : ExteriorBasisIndex 2 // Disjoint two.val a.val}

instance (a : ScalarBasisIndex) : Fintype (originalDisjointTwo a) :=
  inferInstanceAs (Fintype {two : ExteriorBasisIndex 2 // Disjoint two.val a.val})

def originalDisjointTwoEquiv (a : ScalarBasisIndex) :
    originalDisjointTwo a ≃ ↥(a.valᶜ.powersetCard 2) where
  toFun two := ⟨two.val.val, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_compl_iff_disjoint_right.mpr two.property, two.val.property⟩⟩
  invFun two := ⟨⟨two.val, (Finset.mem_powersetCard.mp two.property).2⟩,
    Finset.subset_compl_iff_disjoint_right.mp (Finset.mem_powersetCard.mp two.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem original_disjoint_two_card (a : ScalarBasisIndex) :
    Fintype.card (originalDisjointTwo a) = 3 := by
  rw [Fintype.card_congr (originalDisjointTwoEquiv a), Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_compl]
  have ha : a.val.card = 4 := a.property
  rw [ha]
  norm_num [SU7MotherIndex, Nat.choose]

end LowEnergy.ActualSourceTensorPriceEnvelopeOwn
