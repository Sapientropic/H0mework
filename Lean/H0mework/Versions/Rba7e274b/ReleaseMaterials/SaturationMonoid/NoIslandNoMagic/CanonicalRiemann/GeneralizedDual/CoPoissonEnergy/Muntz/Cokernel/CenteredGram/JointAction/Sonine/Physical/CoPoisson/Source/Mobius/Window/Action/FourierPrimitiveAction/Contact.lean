import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierPrimitiveAction.Window
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierPrimitiveActionSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource

def fullMobiusPrimitiveProfile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (symmetricInterval 4).indicator (fun x=>∑ n∈burnolCenteredMobiusCutoffFinset 4,
    Paid.coefficient n*(OriginalContactFeedbackSource.primitiveRaw coordinate (x/(n:ℕ))-
      OriginalContactFeedbackSource.primitiveMean coordinate)) x

theorem original_MP_profile (coordinate : BurnolCompletedMellinCoordinate) :
    (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate):ℝ→ℂ)=ᵐ[volume] fullMobiusPrimitiveProfile coordinate :=
  OriginalContactFeedbackSource.primitive_lower_word coordinate

def tateMobiusPrimitiveProfile (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  burnolTateReciprocalRaw (fullMobiusPrimitiveProfile coordinate)

theorem original_TMP_profile (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)):ℝ→ℂ)=ᵐ[volume]
      tateMobiusPrimitiveProfile coordinate := by
  have raw:=original_MP_profile coordinate
  have moved:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)))
    ((Lp.memLp (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))).ae_eq raw) raw
  exact (burnolTateReciprocalL2_coeFn _).trans moved

-- The original contact is a full actual source vector; its two Fourier and two Tate feet retain their means/cutoffs.
theorem original_contact_four_feet (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.D (FiniteMobiusResolventFlux.S.contactCorrection coordinate)=
      Kernel.A coordinate • (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)-
        burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)))-
      Kernel.beta coordinate • (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)-
        burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))) := by
  unfold FiniteMobiusResolventFlux.S.contactCorrection
  simp only [map_sub,map_smul]
  unfold Paid.D
  simp only [sub_apply,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]
  rw [OriginalContactFeedbackSource.original_fourier_primitive_return]
  rfl

 def contactDefectProfile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  Kernel.A coordinate*(fullMobiusFourierProfile coordinate x-tateMobiusPrimitiveProfile coordinate x)-
    Kernel.beta coordinate*(fullMobiusPrimitiveProfile coordinate x-tateMobiusFourierProfile coordinate x)

theorem original_contact_defect_profile (coordinate : BurnolCompletedMellinCoordinate) :
    (Paid.D (FiniteMobiusResolventFlux.S.contactCorrection coordinate):ℝ→ℂ)=ᵐ[volume]
      contactDefectProfile coordinate := by
  rw [original_contact_four_feet]
  filter_upwards [Lp.coeFn_sub
      (Kernel.A coordinate • (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)-burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))))
      (Kernel.beta coordinate • (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)-burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)))),
    Lp.coeFn_smul (Kernel.A coordinate) (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)-burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))),
    Lp.coeFn_smul (Kernel.beta coordinate) (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)-burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))),
    Lp.coeFn_sub (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)) (burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))),
    Lp.coeFn_sub (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)) (burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))),
    original_MFP_profile coordinate,original_TMP_profile coordinate,original_MP_profile coordinate,original_TMFP_profile coordinate]
    with x difference leftScalar rightScalar leftFoot rightFoot fourier tatePrimitive primitive tateFourier
  rw [difference]
  change (Kernel.A coordinate • (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)-burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))) : BurnolL2) x-
    (Kernel.beta coordinate • (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)-burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))) : BurnolL2) x=_
  rw [leftScalar,rightScalar]
  change Kernel.A coordinate*((Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)-burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))):BurnolL2) x-
    Kernel.beta coordinate*((Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)-burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))):BurnolL2) x=_
  rw [leftFoot,rightFoot]
  change Kernel.A coordinate*(Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate) x-burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)) x)-
    Kernel.beta coordinate*(Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate) x-burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)) x)=_
  rw [fourier,tatePrimitive,primitive,tateFourier]
  rfl
end OriginalFourierPrimitiveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
