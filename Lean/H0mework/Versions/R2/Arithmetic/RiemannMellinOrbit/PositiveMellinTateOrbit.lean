import H0mework.Versions.R2.Arithmetic.RiemannMellinOrbit.PositiveMellinOrbit

/-!
# Tate transport on the full positive Mellin orbit quotient

Tate inversion sends a dilation generator to the inverse-dilation generator
with the exact half-weight.  Span induction gives relation transport, and an
explicit quotient lift avoids any chosen representative.  The descended map
preserves the two Mellin quotient functionals exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex

noncomputable section

theorem positiveMellinTateMap_generator_mem_positiveDomainOrbit
    (z : ℂ)
    (source : positiveMellinConvergentSubmodule ((1 / 2 : ℂ) - z))
    (target : positiveMellinConvergentSubmodule z)
    (mapsRelation : positiveMellinTateMap z source = target)
    (a : PositiveMellinReal) :
    positiveMellinTateMap z
        (positiveMellinDilation ((1 / 2 : ℂ) - z) a.1 a.2 source) ∈
      positiveDomainMellinOrbitRelation z target := by
  have targetGenerator :
      positiveMellinDilation z a.1⁻¹ (inv_pos.mpr a.2) target ∈
        positiveDomainMellinOrbitRelation z target := by
    apply Submodule.subset_span
    exact ⟨⟨a.1⁻¹, inv_pos.mpr a.2⟩, rfl⟩
  have scaledTarget :
      (a.1 : ℂ) ^ (-(1 / 2 : ℂ)) •
          positiveMellinDilation z a.1⁻¹ (inv_pos.mpr a.2) target ∈
        positiveDomainMellinOrbitRelation z target :=
    Submodule.smul_mem _ _ targetGenerator
  have dilationEquality :
      positiveMellinDilation z a.1⁻¹ (inv_pos.mpr a.2)
          (positiveMellinTateMap z source) =
        positiveMellinDilation z a.1⁻¹ (inv_pos.mpr a.2) target :=
    congrArg
      (fun relation =>
        positiveMellinDilation z a.1⁻¹ (inv_pos.mpr a.2) relation)
      mapsRelation
  have imageEquality :
      positiveMellinTateMap z
          (positiveMellinDilation ((1 / 2 : ℂ) - z) a.1 a.2 source) =
        (a.1 : ℂ) ^ (-(1 / 2 : ℂ)) •
          positiveMellinDilation z a.1⁻¹ (inv_pos.mpr a.2) target :=
    (positiveMellinTateMap_dilation z a.1 a.2 source).trans <|
      congrArg
        (fun value => (a.1 : ℂ) ^ (-(1 / 2 : ℂ)) • value)
        dilationEquality
  exact imageEquality.symm ▸ scaledTarget

theorem positiveMellinTateMap_maps_positiveDomainOrbit
    (z : ℂ)
    (source : positiveMellinConvergentSubmodule ((1 / 2 : ℂ) - z))
    (target : positiveMellinConvergentSubmodule z)
    (mapsRelation : positiveMellinTateMap z source = target)
    (element : positiveMellinConvergentSubmodule ((1 / 2 : ℂ) - z))
    (membership :
      element ∈ positiveDomainMellinOrbitRelation
        ((1 / 2 : ℂ) - z) source) :
    positiveMellinTateMap z element ∈
      positiveDomainMellinOrbitRelation z target := by
  rw [positiveDomainMellinOrbitRelation] at membership
  refine Submodule.span_induction
    (p := fun candidate _ =>
      positiveMellinTateMap z candidate ∈
        positiveDomainMellinOrbitRelation z target)
    ?_ ?_ ?_ ?_ membership
  · intro generator generatorMem
    rcases generatorMem with ⟨a, rfl⟩
    exact positiveMellinTateMap_generator_mem_positiveDomainOrbit
      z source target mapsRelation a
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro left right _ _ leftMem rightMem
    rw [map_add]
    exact Submodule.add_mem _ leftMem rightMem
  · intro scalar candidate _ candidateMem
    rw [map_smul]
    exact Submodule.smul_mem _ scalar candidateMem

def positiveMellinTateOrbitMap
    (z : ℂ)
    (source : positiveMellinConvergentSubmodule ((1 / 2 : ℂ) - z))
    (target : positiveMellinConvergentSubmodule z)
    (mapsRelation : positiveMellinTateMap z source = target) :
    PositiveDomainMellinOrbitQuotient ((1 / 2 : ℂ) - z) source →ₗ[ℂ]
      PositiveDomainMellinOrbitQuotient z target :=
  (positiveDomainMellinOrbitRelation ((1 / 2 : ℂ) - z) source).liftQ
    ((positiveDomainMellinOrbitRelation z target).mkQ.comp
      (positiveMellinTateMap z)) <| by
      intro element membership
      rw [LinearMap.mem_ker]
      change (positiveDomainMellinOrbitRelation z target).mkQ
          (positiveMellinTateMap z element) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact positiveMellinTateMap_maps_positiveDomainOrbit
        z source target mapsRelation element membership

theorem positiveDomainFunctional_tateOrbitMap
    (z : ℂ)
    (source : positiveMellinConvergentSubmodule ((1 / 2 : ℂ) - z))
    (target : positiveMellinConvergentSubmodule z)
    (mapsRelation : positiveMellinTateMap z source = target)
    (sourceAnnihilated :
      positiveMellinFunctional ((1 / 2 : ℂ) - z) source = 0)
    (targetAnnihilated : positiveMellinFunctional z target = 0)
    (value : PositiveDomainMellinOrbitQuotient
      ((1 / 2 : ℂ) - z) source) :
    positiveDomainMellinOrbitQuotientFunctional z target
        targetAnnihilated
        (positiveMellinTateOrbitMap z source target mapsRelation value) =
      positiveDomainMellinOrbitQuotientFunctional
        ((1 / 2 : ℂ) - z) source sourceAnnihilated value := by
  refine Submodule.Quotient.induction_on
    (positiveDomainMellinOrbitRelation ((1 / 2 : ℂ) - z) source)
    value ?_
  intro representative
  change positiveMellinFunctional z
      (positiveMellinTateMap z representative) =
    positiveMellinFunctional ((1 / 2 : ℂ) - z) representative
  exact positiveMellinFunctional_tateMap z representative

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
