import H0mework.Versions.AB.Physics.MotherSource.TemporalGauge.Source

/-! The original three coupling units generate the complete temporal gauge quadratic form. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeGaugeWedge StageNineTopologicalFourFormPairing
open StageNineFormNativeMotherAction Stage9C.Dynamics.Homogeneous
open Stage9C.Material.SpinPair EmpiricalReferenceScaleCouplingBoundary
noncomputable section

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

theorem source_couplings :
    ((sourceGeneratedUnifiedCouplings Stage10.Runtime.source).strongCouplingSquared : ℝ) = 1/2 ∧
    ((sourceGeneratedUnifiedCouplings Stage10.Runtime.source).weakCouplingSquared : ℝ) = 1/2 ∧
    ((sourceGeneratedUnifiedCouplings Stage10.Runtime.source).hyperchargeCouplingSquared : ℝ) = 1/2 := by
  rw [Stage10.Runtime.source_eq]
  change sourceCoupling = 1/2 ∧ sourceCoupling = 1/2 ∧ sourceCoupling = 1/2
  exact ⟨sourceCoupling_eq, sourceCoupling_eq, sourceCoupling_eq⟩

def field (electric magnetic : Fin 3 → P286LieBlockData) : Fin 6 → P286LieBlockData :=
  ![electric 0, electric 1, electric 2, magnetic 0, magnetic 1, magnetic 2]

/-- Positive electric norm on the complete original gauge algebra. -/
def squared (value : Fin 3 → P286LieBlockData) : ℝ :=
  ∑ axis, formNativeP286LiePairing (value axis) (value axis)

theorem auxiliary (electric magnetic : Fin 3 → P286LieBlockData) :
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings Stage10.Runtime.source) (homogeneousCoframe lapse)
      (field electric magnetic) =
    field (fun axis => -(2*lapse⁻¹) • magnetic axis) (fun axis => (2*lapse) • electric axis) := by
  unfold formNativeP286GaugeEliminatedAuxiliaryAtBoundary formNativeP286LiftedCoframeHodge
  rw [homogeneousHodge_lift lapse (ne_of_gt lapse_pos)]
  rw [source_couplings.1, source_couplings.2.1, source_couplings.2.2]
  norm_num only [inv_div, div_one]
  have uniform (s : ℝ) (form : Fin 6 → P286LieBlockData) :
      formNativeP286BlockScale s s s form = s • form := by
    funext pair
    rfl
  rw [uniform]
  funext pair
  fin_cases pair <;>
    simp [field, smul_smul, neg_smul, mul_comm]
  all_goals exact (neg_smul _ _).symm

theorem reduced_density (electric magnetic : Fin 3 → P286LieBlockData) :
    (1/2 : ℝ) * formNativeP286GaugeWedgeCoefficient
      (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Stage10.Runtime.source) (homogeneousCoframe lapse)
        (field electric magnetic)) (field electric magnetic) =
      lapse * squared electric - lapse⁻¹ * squared magnetic := by
  rw [auxiliary]
  simp [formNativeP286GaugeWedgeCoefficient, generatedTwoFormWedgeCoefficient,
    Fin.sum_univ_six, twoFormComplement, field, formNativeP286LiePairing_smul_left,
    squared, Fin.sum_univ_three]
  ring

def magnetic (axis : Fin 3) : P286LieBlockData :=
  -(gaugeScale^2) • sourceColorP286Generator axis

theorem curvature_field (potential : Potential) (point : BasePoint) :
    holonomicGaugeCurvature (primitive potential) point =
      field (electric potential point) magnetic := by
  rw [curvature]
  funext pair
  fin_cases pair <;> simp [field, electricForm, magnetic, magneticCurvature]

theorem gauge_density (potential : Potential) (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings Stage10.Runtime.source)
      (toContinuumPointField (configuration potential) point) =
      lapse * squared (electric potential point) - lapse⁻¹ * squared magnetic := by
  have nondegenerate : (primitive potential).Nondegenerate := by
    intro p
    simp only [primitive, Stage10.Runtime.configuration_eq]
    exact actual_nondegenerate p
  unfold configuration
  rw [HyperchargeResponse.constitutive_gauge_density Stage10.Runtime.source
    (primitive potential) nondegenerate point, curvature_field]
  have coframe : (primitive potential).coframe point = homogeneousCoframe lapse := by
    simp only [primitive, Stage10.Runtime.configuration_eq, actual_coframe]
  rw [coframe, reduced_density]

theorem squared_nonnegative (value : Fin 3 → P286LieBlockData) : 0 ≤ squared value :=
  Finset.sum_nonneg fun _ _ => formNativeP286LiePairing_self_nonnegative _

theorem squared_zero_iff (value : Fin 3 → P286LieBlockData) : squared value = 0 ↔ value = 0 := by
  constructor
  · intro zero
    unfold squared at zero
    funext axis
    exact (formNativeP286LiePairing_self_eq_zero_iff _).mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
        formNativeP286LiePairing_self_nonnegative (value a))).mp zero axis (Finset.mem_univ axis))
  · intro zero
    subst value
    simp [squared, formNativeP286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing]

end
end SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
