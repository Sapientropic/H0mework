import H0mework.Physics.DiracEvolution.SafeCanonicalGalerkinBasis
import H0mework.Physics.DiracEvolution.GeneratedWeakLimitActualization

/-!
# Canonical dense matter Riesz actualization

This is the narrow transporter from convergence of finite linear reads on the
canonical dense matter tests to the existing dense-span Riesz actualization.
It does not generate an approximation history, a limit law, or a physical
equation.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCauchySafeMatterCanonicalDenseRieszActualization

open Filter Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField
open StageNineGeneratedWeakLimitActualization

noncomputable section

set_option autoImplicit false

/-- Generator convergence and one uniform finite-read bound produce the
canonical dense-span limit, its Riesz representative, and uniqueness. -/
theorem exists_canonicalDenseRieszSpanActualization
    (a b : DiracMatterSpatialCoordinates)
    (functional : ℕ → CauchySafeMatterSmoothCompactTest →ₗ[ℝ] ℝ)
    (subsequence : ℕ → ℕ)
    (generatorLimit : ℕ → ℝ)
    (generatorConvergence : ∀ test,
      Tendsto
        (fun sequenceIndex ↦
          functional (subsequence sequenceIndex)
            (cauchySafeMatterCanonicalInteriorDenseTest a b test))
        atTop (nhds (generatorLimit test)))
    (B : ℝ)
    (uniformBound : ∀ testCount test,
      ‖functional testCount test‖ ≤
        B * ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖) :
    ∃ limit : CauchySafeMatterCanonicalInteriorTestSpan a b → ℝ,
      ∃ convergence : ∀ test,
        Tendsto
          (fun sequenceIndex ↦
            functional (subsequence sequenceIndex) test.1)
          atTop (nhds (limit test)),
        let spanFunctional : ℕ →
            CauchySafeMatterCanonicalInteriorTestSpan a b →ₗ[ℝ] ℝ :=
          fun testCount ↦
            (functional testCount).comp
              (Submodule.subtype
                (CauchySafeMatterCanonicalInteriorTestSpan a b))
        let representative := pointwiseLimitRieszActualization
          (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b)
          spanFunctional subsequence limit convergence
        (∀ test,
          inner ℝ representative
              (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test) =
            limit test) ∧
          (∀ candidate : CauchySafeMatterSpatialL2 a b,
            (∀ test,
              inner ℝ candidate
                  (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test) =
                limit test) →
              candidate = representative) ∧
            ∀ test,
              limit ⟨cauchySafeMatterCanonicalInteriorDenseTest a b test,
                Submodule.subset_span (Set.mem_range_self test)⟩ =
                generatorLimit test := by
  exact exists_pointwiseLimitRieszActualization_of_generatorConvergence
    (cauchySafeMatterCanonicalInteriorDenseTest a b)
    (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b)
    functional subsequence generatorLimit generatorConvergence
    (cauchySafeMatterCanonicalInteriorTestSpanToL2_denseRange a b)
    B (fun testCount test ↦ uniformBound testCount test.1)

end

end SaturationMonoid.PhysicsCore.StageNineCauchySafeMatterCanonicalDenseRieszActualization
