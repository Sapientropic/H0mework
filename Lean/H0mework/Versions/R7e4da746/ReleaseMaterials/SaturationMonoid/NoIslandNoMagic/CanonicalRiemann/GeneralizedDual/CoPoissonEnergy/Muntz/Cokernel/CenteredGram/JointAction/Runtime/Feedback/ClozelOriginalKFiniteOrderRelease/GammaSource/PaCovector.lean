import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PaCoefficientPrice

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRSourceJointContact.PaCovector
open Complex Filter Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalGamma.Source.KGamma OriginalGamma.Source.KappaConductor
open OriginalKCrossParameterRAdjointSource
open scoped InnerProductSpace Topology
local notation "Pa" => PaNativePortSource.Pa
local notation "T" => burnolTateReciprocalL2
local notation "ν" => burnolMobiusSourceL2

/-- Every original Pa vector is read by the same source covector generated on the actual recipes. -/
theorem actual_Gamma_Pa_source_covector
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (p : ↥Pa) :
    inner ℂ (actualGammaKernel c) ((p : BurnolPaAmbientCarrier) : BurnolL2) =
      inner ℂ (sourceAnnulusCut (originalDualLogValue c)) (PaNativePortSource.sourceMap p) := by
  let left : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
    (innerSL ℂ (actualGammaKernel c)).comp
      (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL
  let right : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
    (innerSL ℂ (sourceAnnulusCut (originalDualLogValue c))).comp (burnolTateReciprocalL2.comp burnolMobiusSourceL2)
  have onRange : Set.EqOn left right (Set.range burnolCompactCoPoissonLanding) := by
    rintro _ ⟨input,rfl⟩
    induction input using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add u v hu hv => simp only [map_add,hu,hv]
    | single i z =>
      have atom : left (burnolCompactCoPoissonGenerator i) =
          right (burnolCompactCoPoissonGenerator i) := by
        change inner ℂ (actualGammaKernel c) (burnolCompactCoPoissonGenerator i : BurnolL2) =
          inner ℂ (sourceAnnulusCut (originalDualLogValue c))
            (T (ν (burnolCompactCoPoissonGenerator i)))
        rw [PaCoefficientSourceGram.sigma_generator_read]
        exact PaCoefficientPrice.actual_generator_Gamma_price c zero i
      simp only [burnolCompactCoPoissonLanding_single,map_smul,atom]
  have admitted : (p : BurnolPaAmbientCarrier) ∈
      closure (Set.range burnolCompactCoPoissonLanding) := by
    have actual : (p : BurnolPaAmbientCarrier) ∈
        (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure := p.property
    change (p : BurnolPaAmbientCarrier) ∈
      closure ((LinearMap.range burnolCompactCoPoissonLanding) : Set BurnolPaAmbientCarrier) at actual
    simpa only [LinearMap.coe_range] using actual
  exact onRange.closure left.continuous right.continuous admitted

end OriginalRSourceJointContact.PaCovector
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
