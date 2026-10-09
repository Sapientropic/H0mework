import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualSignedSectorCompression

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualSignedSector
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent FullYDynamicSource
open FullYSourceResolventGraphSplice FullYDynamicResponse
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped InnerProductSpace BigOperators
attribute [local irreducible] embed literalCoreResolvent literalSharpResolvent

private theorem compression_embed (F : Index) (q : QuantumTest) :
    embed (compressionCore F q) = GaussGradedCompression.compression F (embed q) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

theorem actual_compression_core (s : ℝ) (F : Index) : Commutes s (compressionCore (saturate s F)) := by
  intro q
  apply embed_injective
  simp only [embed_project,compression_embed]
  exact congrArg (fun A : H →L[ℂ] H => A (embed q)) (actual_graded_compression s F).eq

theorem actual_full_generator (s : ℝ) (F : Index) (sharp : Bool) :
    Commutes s (compressionCore (saturate s F) + sourceY sharp) := by
  apply commutes_add s (actual_compression_core s F)
  cases sharp
  · exact originalY s
  · exact independentSharp s

private theorem inverse_commutes (P T R : End) (h : Commute P T)
    (left : R*T=1) (right : T*R=1) : Commute P R := by
  show P*R=R*P
  calc
    _ = (R*T)*(P*R) := by rw [left,one_mul]
    _ = R*(T*P)*R := by simp only [mul_assoc]
    _ = R*(P*T)*R := by rw [←h.eq]
    _ = R*P := by simp only [mul_assoc,right,mul_one]

theorem actual_literal_primal (s : ℝ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) :
    Commutes s (literalCoreResolvent (saturate s F) z hz) := by
  have hg : Commute (project s) (compressionCore (saturate s F) + GaussYukawaOperator.originalAction) :=
    LinearMap.ext (actual_full_generator s F false)
  have ht := hg.sub_right ((Commute.one_right (project s)).smul_right z)
  have hr := inverse_commutes (project s) (literalCoreShift (saturate s F) z)
    (literalCoreResolvent (saturate s F) z hz) ht
    (literal_core_left_inverse _ _ _) (literal_core_right_inverse _ _ _)
  intro q
  exact DFunLike.congr_fun hr.eq q

theorem actual_literal_sharp (s : ℝ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) :
    Commutes s (literalSharpResolvent (saturate s F) z hz) := by
  have hg : Commute (project s) (compressionCore (saturate s F) + GaussFullHamiltonian.adjointAction) :=
    LinearMap.ext (actual_full_generator s F true)
  have ht := hg.sub_right ((Commute.one_right (project s)).smul_right z)
  have hr := inverse_commutes (project s) (literalSharpShift (saturate s F) z)
    (literalSharpResolvent (saturate s F) z hz) ht
    (literal_sharp_left_inverse _ _ _) (literal_sharp_right_inverse _ _ _)
  intro q
  exact DFunLike.congr_fun hr.eq q

theorem actual_response_sector (s : ℝ) (F : Index) (q : QuantumTest)
    (hq : project s q = q) (sharp advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    project s (literalResponse (saturate s F) sharp q advanced μ hμ w) =
      literalResponse (saturate s F) sharp q advanced μ hμ w := by
  cases sharp
  · exact (actual_literal_primal s F _ _ q).trans (congrArg _ hq)
  · exact (actual_literal_sharp s F _ _ q).trans (congrArg _ hq)

end LowEnergy.ActualSignedSector
