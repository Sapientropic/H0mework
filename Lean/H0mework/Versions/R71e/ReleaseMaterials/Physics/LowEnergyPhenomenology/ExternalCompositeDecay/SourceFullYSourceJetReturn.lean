import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYFullSourceCausalReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYBornFrequency
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicCofinalJets
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open GaussUnitaryHistory FullYDynamicSource FullYDynamicSourceRefinement
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
attribute [local irreducible] embed sourcePair GaussFullHamiltonian.fullAction GaussFullHamiltonian.sharpAction
  literalCoreResolvent literalSharpResolvent

private theorem difference_return(R S:End)(A:End)(q:QuantumTest)(z:ℂ)
    (hR:R ((A-z • (1:End)) q)=q)(hS:S ((A-z • (1:End)) q)=q):
    z • (R q-S q)=R (A q)-S (A q):=by
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,map_sub,map_smul] at hR hS
  linear_combination (norm:=module) -hR+hS

/-- A finite list of actual full-H0+Y source jets generates one cofinal event before both cutoffs and every nonreal frequency. Both independent source branches retain their literal resolvents. -/
theorem actual_cofinal_fullsource_power_return(B:Index)(q r:QuantumTest)(n:ℕ):
    ∃K₀:Index,B⊆K₀ ∧ ∀F:Index,K₀⊆F → ∀G:Index,K₀⊆G → ∀z:ℂ,∀hz:z.im≠0,
      z^n • (literalCoreResolvent F z hz q-literalCoreResolvent G z hz q)=
        literalCoreResolvent F z hz ((GaussFullHamiltonian.fullAction^n) q)-
          literalCoreResolvent G z hz ((GaussFullHamiltonian.fullAction^n) q) ∧
      z^n • (literalSharpResolvent F z hz r-literalSharpResolvent G z hz r)=
        literalSharpResolvent F z hz ((GaussFullHamiltonian.sharpAction^n) r)-
          literalSharpResolvent G z hz ((GaussFullHamiltonian.sharpAction^n) r):=by
  induction n generalizing B q r with
  | zero=>
    refine ⟨B,Finset.Subset.refl _,fun F _ G _ z hz=>?_⟩
    simp only [pow_zero,one_smul,Module.End.one_apply,and_self]
  | succ n ih=>
    obtain ⟨K₁,hB,hK₁⟩:=ih B (GaussFullHamiltonian.fullAction q) (GaussFullHamiltonian.sharpAction r)
    obtain ⟨K₂,h₁₂,hK₂⟩:=actual_full_source_forcing_return K₁ q r
    refine ⟨K₂,Finset.Subset.trans hB h₁₂,fun F hF G hG z hz=>?_⟩
    have hp:=hK₁ F (Finset.Subset.trans h₁₂ hF) G (Finset.Subset.trans h₁₂ hG) z hz
    have hFq:=hK₂ F hF z hz
    have hGq:=hK₂ G hG z hz
    have he:=difference_return (literalCoreResolvent F z hz) (literalCoreResolvent G z hz)
      GaussFullHamiltonian.fullAction q z hFq.1 hGq.1
    have hs:=difference_return (literalSharpResolvent F z hz) (literalSharpResolvent G z hz)
      GaussFullHamiltonian.sharpAction r z hFq.2 hGq.2
    constructor
    · rw [pow_succ,mul_smul,he,hp.1]
      simp only [pow_succ,Module.End.mul_apply]
    · rw [pow_succ,mul_smul,hs,hp.2]
      simp only [pow_succ,Module.End.mul_apply]

end LowEnergy.FullYDynamicCofinalJets
