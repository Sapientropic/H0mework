import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.DivisorJointSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Trace
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.RawDerivative
import H0mework.Arithmetic.MellinProjection.TailKernel
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.QuadraticDivisorReadback
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.CountingQuadraticLimit OriginalGamma.Source.DivisorJoint
noncomputable section
private theorem radial_integrable (s : Set ℝ) (measurableS : MeasurableSet s)
    (positiveS : s ⊆ Ioi 0) (coefficient : ℝ → ℂ) (measurable : Measurable coefficient)
    (weighted : IntegrableOn (fun t : ℝ => Real.sqrt t * ‖coefficient t‖) s) (v : BurnolL2) :
    IntegrableOn (fun t : ℝ => coefficient t • radialOrbit t v) s := by
  have orbit : AEStronglyMeasurable (fun t : ℝ => radialOrbit t v) (volume.restrict s) :=
    ((radialOrbit_continuous v).mono positiveS).aestronglyMeasurable measurableS
  have measured := measurable.aestronglyMeasurable.smul orbit
  apply (integrable_norm_iff measured).mp
  apply (weighted.const_mul (2 * ‖v‖)).congr
  filter_upwards [ae_restrict_mem measurableS] with t inside
  change (2 * ‖v‖) * (Real.sqrt t * ‖coefficient t‖) = ‖coefficient t • radialOrbit t v‖
  rw [norm_smul, radialOrbit_norm t (positiveS inside) v]
  ring

private theorem radial_commute (L : BurnolL2 →L[ℂ] BurnolL2)
    (action : ∀ (h : ℝ) (v : BurnolL2), L (burnolMultiplicativeDilation h v) =
      burnolMultiplicativeDilation h (L v))
    (s : Set ℝ) (measurableS : MeasurableSet s) (positiveS : s ⊆ Ioi 0)
    (coefficient : ℝ → ℂ) (measurable : Measurable coefficient)
    (weighted : IntegrableOn (fun t : ℝ => Real.sqrt t * ‖coefficient t‖) s) (v : BurnolL2) :
    radialSynthesisCLM s measurableS positiveS coefficient measurable weighted (L v) =
      L (radialSynthesisCLM s measurableS positiveS coefficient measurable weighted v) := by
  simp only [radialSynthesisCLM_apply]
  rw [← L.integral_comp_comm
    (radial_integrable s measurableS positiveS coefficient measurable weighted v)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [radialOrbit, map_smul, action]

private theorem base_commute (L : BurnolL2 →L[ℂ] BurnolL2)
    (action : ∀ (h : ℝ) (v : BurnolL2), L (burnolMultiplicativeDilation h v) =
      burnolMultiplicativeDilation h (L v))
    (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    originalBaseSynthesis c (L v) = L (originalBaseSynthesis c v) := by
  simp only [originalBaseSynthesis, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_sub, map_smul]
  rw [returnSynthesis, tailSynthesis, radial_commute L action, radial_commute L action]

theorem original_base_joint (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    originalBaseSynthesis c (joint v) = joint (originalBaseSynthesis c v) :=
  base_commute joint joint_dilation c v

end
end OriginalGamma.Source.QuadraticDivisorReadback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
