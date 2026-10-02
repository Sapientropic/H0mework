import H0mework.Versions.R2.Physics.RadialDynamics.Radial

/-! The radial kinetic coefficient is read from the original mother density
after its existing, source-owned constitutive elimination. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeYangMillsReadout StageNineFormNativeMotherAction
open StageNineFormNativeGaugeAuxiliaryVariation StageNineFormNativeGaugeWedge
open StageNineTopologicalFourFormPairing StageNineP286GaugeAuxiliaryVariation
open Stage9C.Dynamics.Homogeneous Stage9C.Material.SpinPair SU7MotherLieAlgebra

noncomputable section

def radialReadout (profile : ℝ → ℝ) : StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout positiveSmoothUnifiedSource (radialWrite profile)

def radialAuxiliary (amplitude velocity : ℝ) : FormNativeP286GaugeTwoForm :=
  formNativeP286GaugeEliminatedAuxiliaryAtBoundary
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
    (homogeneousCoframe lapse) (radialCurvature amplitude velocity)

private theorem uniformBlockScale (scalar : ℝ) (form : FormNativeP286GaugeTwoForm) :
    formNativeP286BlockScale scalar scalar scalar form = scalar • form := rfl

theorem radialAuxiliary_hodge (amplitude velocity : ℝ) :
    radialAuxiliary amplitude velocity = -(sourceCoupling⁻¹ • liftGaugeTwoFormOperator
      (coframeGaugeSpacetimeHodgeLinear (homogeneousCoframe lapse)) (radialCurvature amplitude velocity)) := by
  unfold radialAuxiliary formNativeP286GaugeEliminatedAuxiliaryAtBoundary
    formNativeP286LiftedCoframeHodge
  change -formNativeP286BlockScale sourceCoupling⁻¹ sourceCoupling⁻¹ sourceCoupling⁻¹ _ = _
  rw [uniformBlockScale]

private theorem triadHodgeScale {V : Type*} [AddCommGroup V] [Module ℝ V]
    (generators : Fin 3 → V) (clock coupling amplitude velocity : ℝ) :
    -(coupling⁻¹ •
      ![clock⁻¹ • (-(amplitude^2) • generators 0), clock⁻¹ • (-(amplitude^2) • generators 1),
        clock⁻¹ • (-(amplitude^2) • generators 2), -clock • (velocity • generators 0),
        -clock • (velocity • generators 1), -clock • (velocity • generators 2)]) =
      ![(amplitude^2/(coupling*clock)) • generators 0,
        (amplitude^2/(coupling*clock)) • generators 1,
        (amplitude^2/(coupling*clock)) • generators 2,
        (clock*velocity/coupling) • generators 0,
        (clock*velocity/coupling) • generators 1,
        (clock*velocity/coupling) • generators 2] := by
  funext pair
  fin_cases pair <;> simp [smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem radialAuxiliary_eq (amplitude velocity : ℝ) :
    radialAuxiliary amplitude velocity =
      ![(amplitude^2/(sourceCoupling*lapse)) • sourceColorP286Generator 0,
        (amplitude^2/(sourceCoupling*lapse)) • sourceColorP286Generator 1,
        (amplitude^2/(sourceCoupling*lapse)) • sourceColorP286Generator 2,
        (lapse*velocity/sourceCoupling) • sourceColorP286Generator 0,
        (lapse*velocity/sourceCoupling) • sourceColorP286Generator 1,
        (lapse*velocity/sourceCoupling) • sourceColorP286Generator 2] := by
  rw [radialAuxiliary_hodge, homogeneousHodge_lift lapse (ne_of_gt lapse_pos)]
  exact triadHodgeScale sourceColorP286Generator lapse sourceCoupling amplitude velocity

theorem radialReadout_auxiliary (profile : ℝ → ℝ) (point : BasePoint) (velocity : ℝ)
    (derivative : HasDerivAt profile velocity (point 0)) :
    (radialReadout profile).gaugeAuxiliary point = radialAuxiliary (profile (point 0)) velocity := by
  unfold radialReadout
  rw [formNativeP286GaugeConstitutiveReadout_gaugeAuxiliary, radialWrite_curvature _ _ _ derivative]
  change formNativeP286GaugeEliminatedAuxiliaryAtBoundary _
    (Runtime.configuration.coframe point) _ = _
  rw [Runtime.configuration_eq, actual_coframe]
  rfl

theorem radialReadout_source : radialReadout (fun _ => gaugeScale) = Runtime.configuration := by
  unfold radialReadout
  rw [radialWrite_source]
  have auxiliary : (fun point => formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (Runtime.configuration.coframe point) (holonomicGaugeCurvature Runtime.configuration point)) =
      Runtime.configuration.gaugeAuxiliary := by
    funext point
    rw [Runtime.configuration_eq, actual_coframe, actual_gaugeCurvature, actual_gaugeAuxiliary]
    rw [show magneticCurvature gaugeScale = radialCurvature gaugeScale 0 by
      funext pair; fin_cases pair <;> simp [magneticCurvature, radialCurvature]]
    change radialAuxiliary gaugeScale 0 = electricAuxiliary lapse gaugeScale
    rw [radialAuxiliary_eq]
    simp [electricAuxiliary]
  unfold formNativeP286GaugeConstitutiveReadout
  rw [auxiliary]

def radialJet (amplitude velocity : ℝ) : StageNineContinuumPointField :=
  { toContinuumPointField Runtime.configuration 0 with
    coframe := homogeneousCoframe lapse
    gaugeCurvature := radialCurvature amplitude velocity
    gaugeAuxiliary := radialAuxiliary amplitude velocity }

def gaugeLagrangian (amplitude velocity : ℝ) : ℝ :=
  generatedFormNativeGaugeDensityAtBoundary
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) (radialJet amplitude velocity)

theorem sourceColor_pairing (first second : Fin 3) :
    formNativeP286LiePairing (sourceColorP286Generator first) (sourceColorP286Generator second) =
      if first = second then 1/2 else 0 := by
  change p286LiePairing (sourceColorP286Generator first) (sourceColorP286Generator second) = _
  rw [sourceColorP286Generator_pairing, sourceColorP286Generator_color]
  fin_cases first <;> fin_cases second <;> norm_num [sourceColorRaw]

theorem gaugeLagrangian_eq (amplitude velocity : ℝ) :
    gaugeLagrangian amplitude velocity =
      3*lapse/(4*sourceCoupling)*velocity^2 - 3/(4*sourceCoupling*lapse)*amplitude^4 := by
  unfold gaugeLagrangian
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  change formNativeP286GaugeWedgeCoefficient (radialAuxiliary amplitude velocity) _ -
    (1/2:ℝ) * formNativeP286GaugeWedgeCoefficient (radialAuxiliary amplitude velocity)
      (formNativeP286BlockwiseConstitutive (homogeneousCoframe lapse) _ _ _
        (radialAuxiliary amplitude velocity)) = _
  rw [show formNativeP286BlockwiseConstitutive (homogeneousCoframe lapse) _ _ _
    (radialAuxiliary amplitude velocity) = radialCurvature amplitude velocity from
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary_solves _ _
        (homogeneousCoframe_nondegenerate lapse lapse_pos) _]
  rw [radialAuxiliary_eq]
  simp [formNativeP286GaugeWedgeCoefficient, generatedTwoFormWedgeCoefficient,
    radialJet, radialCurvature, Fin.sum_univ_six, twoFormComplement,
    formNativeP286LiePairing_smul_left, formNativeP286LiePairing_smul_right, sourceColor_pairing]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
