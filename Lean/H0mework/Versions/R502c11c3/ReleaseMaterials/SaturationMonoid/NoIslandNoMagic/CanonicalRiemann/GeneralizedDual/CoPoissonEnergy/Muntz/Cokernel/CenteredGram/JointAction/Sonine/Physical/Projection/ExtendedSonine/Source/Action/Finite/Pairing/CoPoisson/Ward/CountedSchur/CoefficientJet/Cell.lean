import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.SourceJet

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.CoefficientJet

open Complex Finset MeasureTheory Set
open scoped BigOperators

open private scaleWeight_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.SourceJet

/-- Adjacent cutoffs use the same integer and its own continuous normalization segment at every order. -/
theorem actual_cell_jet (s : ℂ) (notOne : s ≠ 1) (j n : Nat) :
    jet j (n+1) s - jet j n s =
      (-Complex.log ((n+1 : ℕ) : ℂ))^j * ((n+1 : ℕ) : ℂ)^(-s) -
        ∫ a : ℝ in Ioc (((n+1 : ℕ) : ℝ)) (((n+1+1 : ℕ) : ℝ)), SourceJet.scaleWeight s j a := by
  let a : ℝ := (n+1 : ℕ)
  let b : ℝ := (n+1+1 : ℕ)
  let f := SourceJet.scaleWeight s j
  have lower : 1 ≤ a := by
    dsimp only [a]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have upper : a ≤ b := by
    dsimp only [a,b]
    exact_mod_cast Nat.le_succ (n+1)
  have left : IntegrableOn f (Ioc 1 a) := scaleWeight_integrable s j a
  have right : IntegrableOn f (Ioc a b) := (scaleWeight_integrable s j b).mono_set
    (Ioc_subset_Ioc lower le_rfl)
  have split := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl a))
    measurableSet_Ioc left right
  rw [Ioc_union_Ioc_eq_Ioc lower upper] at split
  change (∫ x : ℝ in Ioc 1 (((n+1+1 : ℕ) : ℝ)), SourceJet.scaleWeight s j x) =
    (∫ x : ℝ in Ioc 1 (((n+1 : ℕ) : ℝ)), SourceJet.scaleWeight s j x) +
      (∫ x : ℝ in Ioc a b, f x) at split
  rw [SourceJet.scaleIntegral_source s notOne j (n+1),
    SourceJet.scaleIntegral_source s notOne j n] at split
  rw [jet_source s notOne, jet_source s notOne, rawJet, rawJet,
    Finset.sum_Ico_succ_top (by omega : 1 ≤ n+1)]
  change _ = _ - (∫ x : ℝ in Ioc a b, f x)
  linear_combination -split

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.CoefficientJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
