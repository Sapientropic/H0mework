import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.ConstitutiveHardGate

/-!
# Source-generation to typed hard-gate adapter

This is the only stage-two module that sees both the upstream equality-valued
abstract packaging relation and the downstream variation/hard-gate types.
The theorem does not accept an arbitrary generation relation, expected gauge
block, GR terminal residual, or cross-compatibility predicate.

Its remaining premise is the explicit boundary of the missing producer:
every admissible source must already supply one stationary Plebanski
configuration whose bivector is the one constructed from the source tetrad.
The premise is an abstract terminal bundle, not a derivation from more
primitive source coordinates.  Other Plebanski sectors may still solve the
unconstrained equations; this adapter uses the explicit source-configuration-
domain route instead of pretending `δφ` or `Kχ` removes them.

Because that premise already supplies `q.B = B(tetradOf χ)`, this adapter
chooses `e := tetradOf χ` directly.  The `δφ=0` conjunct in `MasterOnShell` is
a stationarity/consistency check, not the producer of this tetrad.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uSource uScalar uGaugeTwoForm uTetrad uMetric uInternal
universe uConnection uBivector uMultiplier uMatter
universe uDeltaB uDeltaPhi uDeltaOmega uDeltaE
universe uActionValue

/-- A source-selected stationary family closes the stage-two typed gate.

The Hodge equality in the conclusion is definitional coherence: the generated
law's metric was already defined from the source tetrad, and the same
`hodgeOfMetric` is applied on both sides.  It is not a supplied proposition,
but it is also not a metric/Hodge producer theorem. -/
theorem sourceGeneratedConstitutiveHardGate_of_sourceConfigurationRestrictedSolutions
    {Source : Type uSource} {Scalar : Type uScalar}
    {GaugeTwoForm : Type uGaugeTwoForm} {Tetrad : Type uTetrad}
    {Metric : Type uMetric} {InternalConstitutive : Type uInternal}
    {Connection : Type uConnection} {BivectorTwoForm : Type uBivector}
    {Multiplier : Type uMultiplier} {Matter : Type uMatter}
    {ActionValue : Type uActionValue}
    {DeltaBResidual : Type uDeltaB}
    {DeltaPhiResidual : Type uDeltaPhi}
    {DeltaOmegaResidual : Type uDeltaOmega}
    {DeltaEResidual : Type uDeltaE}
    [Field Scalar] [AddCommGroup GaugeTwoForm] [Module Scalar GaugeTwoForm]
    [Nontrivial GaugeTwoForm] [Nontrivial Tetrad] [Nontrivial Metric]
    [AddCommGroup BivectorTwoForm] [Nontrivial BivectorTwoForm]
    [Zero DeltaBResidual] [Zero DeltaPhiResidual]
    [Zero DeltaOmegaResidual] [Zero DeltaEResidual]
    (G : SourceMetricConstitutiveGeometry Source Scalar Tetrad Metric
      InternalConstitutive)
    (hodgeOfMetric : Metric → GaugeTwoForm ≃ₗ[Scalar] GaugeTwoForm)
    (S : PlebanskiActionVariationSystem
      (SourceGeneratedConstitutiveLaw Scalar Metric InternalConstitutive)
      Connection BivectorTwoForm Multiplier Matter Tetrad ActionValue
      DeltaBResidual DeltaPhiResidual DeltaOmegaResidual DeltaEResidual)
    (P : PlebanskiIIPlusBranchGeometry BivectorTwoForm Tetrad)
    (hadmissible : ∃ χ : Source, G.admissible χ)
    (hvariationFaithful : SourceGeneratedVariationChannelsNontrivial G S)
    (sourceSelectedSolutions :
      ∀ (χ : Source), G.admissible χ →
        ∃ q : PlebanskiMasterConfiguration Connection BivectorTwoForm
            Multiplier Matter,
          S.residuals.MasterOnShell (G.generatedLaw χ) q ∧
            P.nondegenerate q.bivector ∧
            q.bivector =
              P.gravitationalBivector (G.tetradOf χ) ∧
            ∀ e : Tetrad,
              q.bivector = P.gravitationalBivector e →
                S.residuals.DeltaEOnShell (G.generatedLaw χ) q e) :
    SourceGeneratedUniqueSMGRConstitutiveHardGateObligation
      G hodgeOfMetric S P := by
  refine ⟨hadmissible, hvariationFaithful, ?_, ?_⟩
  · intro χ law hgenerated
    exact G.generatedBySource_unique χ law hgenerated
  · intro χ hχ
    obtain ⟨q, hmaster, hnondegenerate, hselected, hdeltaE⟩ :=
      sourceSelectedSolutions χ hχ
    have hsector : P.sector q.bivector = .gravitationalPlus := by
      rw [hselected]
      exact P.sector_gravitationalBivector_eq_gravitationalPlus
        (G.tetradOf χ)
    refine ⟨q, G.tetradOf χ, hmaster, hnondegenerate, ?_, hselected,
      hsector, hdeltaE (G.tetradOf χ) hselected, rfl, rfl⟩
    exact
      PlebanskiIIPlusSelectionEvidence.fromSourceConfigurationDomain
        hselected

end PhysicsCore
end SaturationMonoid
