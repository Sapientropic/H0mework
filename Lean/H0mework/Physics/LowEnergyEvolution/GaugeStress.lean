import H0mework.Physics.LowEnergyEvolution.Gauge
import H0mework.Physics.Homogeneous.GaugeBalance

/-! Both electric and magnetic source auxiliaries contribute to the coframe force. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineBlockwiseConstitutive
open StageNineFormNativeMotherAction StageNineFormNativeGaugeWedge
open StageNineFormNativeGaugeAuxiliaryVariation StageNineP286GaugeAuxiliaryVariation
open StageNineTopologicalFourFormPairing StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineCartanTangentSimplicityResponse EmpiricalReferenceScaleCouplingBoundary
open SU7MotherLieAlgebra Stage9C.Dynamics.Homogeneous Stage9C.Material.SpinPair
open Stage10.GaugeSpectrum.Dynamics
open scoped Matrix.Norms.Elementwise
noncomputable section

def triadAuxiliary (electric magnetic : ℝ) : FormNativeP286GaugeTwoForm :=
  ![electric • sourceColorP286Generator 0, electric • sourceColorP286Generator 1,
    electric • sourceColorP286Generator 2, magnetic • sourceColorP286Generator 0,
    magnetic • sourceColorP286Generator 1, magnetic • sourceColorP286Generator 2]

def pairedHodgeTrace (electric magnetic : ℝ) (coframe : LorentzianCoframe) : ℝ :=
  electric^2 * (gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear coframe) 3 0 +
    gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear coframe) 4 1 +
    gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear coframe) 5 2) +
  magnetic^2 * (gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear coframe) 0 3 +
    gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear coframe) 1 4 +
    gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear coframe) 2 5) +
  electric*magnetic * ∑ i : Fin 6,
    gaugeOperatorCoefficient (coframeGaugeSpacetimeHodgeLinear coframe) i i

private theorem uniformConstitutive_eq_lift (coframe : LorentzianCoframe) (coupling : ℝ)
    (form : FormNativeP286GaugeTwoForm) :
    formNativeP286BlockwiseConstitutive coframe coupling coupling coupling form =
      liftGaugeTwoFormOperator (coupling • coframeGaugeSpacetimeHodgeLinear coframe) form := by
  funext output
  simp only [formNativeP286BlockwiseConstitutive, liftGaugeTwoFormOperator, Fin.sum_univ_six]
  rfl

theorem triadAuxiliary_quadratic (electric magnetic coupling : ℝ) (coframe : LorentzianCoframe) :
    formNativeP286GaugeWedgeCoefficient (triadAuxiliary electric magnetic)
      (formNativeP286BlockwiseConstitutive coframe coupling coupling coupling
        (triadAuxiliary electric magnetic)) = coupling/2 * pairedHodgeTrace electric magnetic coframe := by
  rw [uniformConstitutive_eq_lift]
  unfold formNativeP286GaugeWedgeCoefficient generatedTwoFormWedgeCoefficient liftGaugeTwoFormOperator
  simp [Fin.sum_univ_six, twoFormComplement, triadAuxiliary,
    formNativeP286LiePairing_add_right, formNativeP286LiePairing_smul_left,
    formNativeP286LiePairing_smul_right, sourceColor_pairing,
    gaugeOperatorCoefficient, pairedHodgeTrace]
  ring

def pairedHodgeTangent (electric magnetic : ℝ) (coframe variation : LorentzianCoframe) : ℝ :=
  electric^2 * (coframeHodgeTangent coframe variation (fun i => if i = 0 then 1 else 0) 3 +
    coframeHodgeTangent coframe variation (fun i => if i = 1 then 1 else 0) 4 +
    coframeHodgeTangent coframe variation (fun i => if i = 2 then 1 else 0) 5) +
  magnetic^2 * (coframeHodgeTangent coframe variation (fun i => if i = 3 then 1 else 0) 0 +
    coframeHodgeTangent coframe variation (fun i => if i = 4 then 1 else 0) 1 +
    coframeHodgeTangent coframe variation (fun i => if i = 5 then 1 else 0) 2) +
  electric*magnetic * ∑ i : Fin 6,
    coframeHodgeTangent coframe variation (fun j => if j = i then 1 else 0) i

theorem pairedHodgeTrace_derivative (electric magnetic : ℝ) (coframe variation : LorentzianCoframe)
    (nondegenerate : coframe.det ≠ 0) :
    HasDerivAt (fun t : ℝ => pairedHodgeTrace electric magnetic (coframe + t • variation))
      (pairedHodgeTangent electric magnetic coframe variation) 0 := by
  have entry (row col : Fin 6) := coframeHodge_line_hasDerivAt coframe variation nondegenerate
    (fun i => if i = col then 1 else 0) row
  have electricPart := (((entry 3 0).add (entry 4 1)).add (entry 5 2)).const_mul (electric^2)
  have magneticPart := (((entry 0 3).add (entry 1 4)).add (entry 2 5)).const_mul (magnetic^2)
  have crossPart := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => entry i i)).const_mul (electric*magnetic)
  exact (electricPart.add magneticPart).add crossPart

set_option maxHeartbeats 1600000 in
theorem pairedHodgeTangent_diagonal (electric magnetic n a : ℝ) (hn : n ≠ 0) (ha : a ≠ 0)
    (variation : LorentzianCoframe) :
    pairedHodgeTangent electric magnetic (diagonalCoframe n a) variation =
      electric^2 * (n/a^2*(variation 1 1+variation 2 2+variation 3 3)-3/a*variation 0 0) +
      magnetic^2 * (1/n*(variation 1 1+variation 2 2+variation 3 3)-3*a/n^2*variation 0 0) := by
  simp only [pairedHodgeTangent, coframeHodgeTangent, diagonalCoframe_inv n a hn ha]
  simp [coframeTwoFormTangent, coframeWedgeTangent, coframeTwoFormLinear,
    lorentzianCoframeHodge, coframeWedge, diagonalCoframe, pairFirst, pairSecond,
    Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_six]
  field_simp [hn, ha]
  ring

theorem Solution.gauge_frozen_density {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (candidate : LorentzianCoframe) :
    diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
      (toContinuumPointField flow.configuration point) candidate =
      formNativeP286GaugeWedgeCoefficient (flow.configuration.gaugeAuxiliary point)
        (holonomicGaugeCurvature flow.configuration point) - sourceCoupling/4 *
          pairedHodgeTrace (electricAmplitude (flow.pointState point))
            (magneticAmplitude (flow.pointState point)) candidate := by
  unfold diracDualFormNativeCoframeGaugeDensity
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  change formNativeP286GaugeWedgeCoefficient (flow.configuration.gaugeAuxiliary point)
      (holonomicGaugeCurvature flow.configuration point) - (1/2:ℝ) *
      formNativeP286GaugeWedgeCoefficient (flow.configuration.gaugeAuxiliary point)
        (formNativeP286BlockwiseConstitutive candidate sourceCoupling sourceCoupling sourceCoupling
          (flow.configuration.gaugeAuxiliary point)) = _
  have auxiliary : flow.configuration.gaugeAuxiliary point =
      triadAuxiliary (electricAmplitude (flow.pointState point)) (magneticAmplitude (flow.pointState point)) :=
    flow.gauge_auxiliary point inside
  rw [auxiliary, triadAuxiliary_quadratic]
  ring

theorem Solution.gauge_coframe {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : LorentzianCoframe) :
    diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
      (toContinuumPointField flow.configuration point) variation =
      gaugeEnergy (flow.pointState point)/(4*sourceCoupling*(clock (flow.pointState point))^2) *
        (3*flow.pointState point 0*variation 0 0 -
          clock (flow.pointState point)*(variation 1 1+variation 2 2+variation 3 3)) := by
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  have hn := ne_of_gt (clock_positive _ admissible)
  have ha := ne_of_gt admissible.1
  have derivative := diracDualFormNativeCoframeGaugeDensity_hasFDerivAt positiveSmoothUnifiedSource
    (toContinuumPointField flow.configuration point) (flow.nondegenerate_at point inside)
  change HasFDerivAt _ _ (flow.configuration.coframe point) at derivative
  have derivative' : HasFDerivAt
      (diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource (toContinuumPointField flow.configuration point))
      (diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource (toContinuumPointField flow.configuration point))
      (flow.configuration.coframe point + (0 : ℝ) • variation) := by
    simpa only [zero_smul, add_zero] using derivative
  have evaluated := derivative'.comp_hasDerivAt 0
    (coframe_line_hasDerivAt (flow.configuration.coframe point) variation)
  have computed := ((pairedHodgeTrace_derivative
    (electricAmplitude (flow.pointState point)) (magneticAmplitude (flow.pointState point))
    (flow.configuration.coframe point) variation (flow.nondegenerate_at point inside)).const_mul
      (sourceCoupling/4)).const_sub
        (formNativeP286GaugeWedgeCoefficient (flow.configuration.gaugeAuxiliary point)
          (holonomicGaugeCurvature flow.configuration point))
  have computed' : HasDerivAt
      (fun t : ℝ => diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
        (toContinuumPointField flow.configuration point) (flow.configuration.coframe point + t • variation))
      (-(sourceCoupling/4 * pairedHodgeTangent
        (electricAmplitude (flow.pointState point)) (magneticAmplitude (flow.pointState point))
        (flow.configuration.coframe point) variation)) 0 := by
    simp_rw [flow.gauge_frozen_density point inside]
    exact computed
  have observed := evaluated.unique computed'
  change diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
    (toContinuumPointField flow.configuration point) variation = _ at observed
  rw [observed, flow.coframe, pairedHodgeTangent_diagonal _ _ _ _ hn ha]
  unfold electricAmplitude magneticAmplitude gaugeEnergy
  field_simp [sourceCoupling_eq, hn, ha]
  ring

theorem Solution.gauge_coframe_coordinates {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (row col : LorentzianIndex) :
    diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
      (toContinuumPointField flow.configuration point) (Matrix.single row col 1) =
      if row = col then
        if row = 0 then 3*flow.pointState point 0*gaugeEnergy (flow.pointState point)/
          (4*sourceCoupling*(clock (flow.pointState point))^2)
        else -gaugeEnergy (flow.pointState point)/(4*sourceCoupling*clock (flow.pointState point))
      else 0 := by
  rw [flow.gauge_coframe point inside]
  have hn : clock (flow.pointState point) ≠ 0 := ne_of_gt (clock_positive _ (flow.admissible _ inside))
  fin_cases row <;> fin_cases col <;> simp
  all_goals field_simp [hn]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
