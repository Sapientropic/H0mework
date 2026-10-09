import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleBalance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace LowEnergy.GeneralThreeParticleResponse
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open SourceClockYukawaCubicCurrent GaussCoreLabel NativeHistoryGrade NamedColorQtNext
open FullYDynamicSource FullYDynamicSourceRefinement FullYDynamicResponse FullYSourceResolventGraphSplice
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussYukawaOperator GaussYukawaCoefficient SourceScalarPairedTransport
open SourceResolventBandLimit
open scoped InnerProductSpace
attribute [local irreducible] embed GaussCoreLabel.project NativeHistoryGrade.projection
  literalCoreResolvent literalSharpResolvent

/-- At every finite cutoff, a vanishing actual unforced Yukawa correction
forces the bounded normalized-Y reader of the original base inverse to vanish.
The inverse here is the compressed fullY 57-word inverse, with no cofinal or
original-Hamiltonian inverse hypothesis. -/
theorem correction_zero_bounded_resolvent (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ)
    (hc : originalYCorrection F q advanced μ hμ w = 0) :
    bounded (finiteResolvent F (line (FullYPairedParseval.direction advanced * μ) w) (embed q)) = 0 := by
  let z := line (FullYPairedParseval.direction advanced * μ) w
  have hz : z.im ≠ 0 := causal_line_nonreal advanced μ w hμ
  let u := literalCoreResolvent F z hz q
  let v := resolventCore F z hz q
  have hp : project (3,0) u = v := by
    dsimp only [u,v]
    rw [actual_bottom_primal_projected_resolvent,hq]
  have hu : u = v := by
    apply embed_injective
    have he : embed u = projection (3,0) (embed u) := sub_eq_zero.mp hc
    rw [←embed_project,hp] at he
    exact he
  have hfull := LinearMap.congr_fun (literal_core_right_inverse F z hz) q
  change compressionCore F u + originalAction u - z • u = q at hfull
  rw [hu] at hfull
  have heR : embed v = finiteResolvent F z (embed q) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have heC : embed (compressionCore F v) = GaussGradedCompression.compression F (embed v) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hbase : compressionCore F v - z • v = q := by
    apply embed_injective
    rw [map_sub,map_smul,heC,heR]
    have h := congrArg (fun T : H →L[ℂ] H => T (embed q))
      (resolvent_right (GaussGradedCompression.compression F)
        (GaussGradedCompression.compression_selfAdjoint F) z hz)
    exact h
  have hY : originalAction v = 0 := by
    linear_combination (norm := module) hfull - hbase
  have ha : GaussYukawaCoefficient.action v = 0 := by
    apply DFunLike.ext
    intro x
    have hr : radiusAction (GaussYukawaCoefficient.action v) = 0 := (radius_action_return v).trans hY
    have hx := congrArg (fun f : QuantumTest => f x) hr
    change radius x • (GaussYukawaCoefficient.action v x) = 0 at hx
    exact (smul_eq_zero.mp hx).resolve_left (radius_pos x).ne'
  change bounded (finiteResolvent F z (embed q)) = 0
  rw [←heR,bounded_core,ha,map_zero]

end LowEnergy.GeneralThreeParticleResponse
