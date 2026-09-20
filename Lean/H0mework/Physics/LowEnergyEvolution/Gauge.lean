import H0mework.Physics.LowEnergyEvolution.Cartan
import H0mework.Physics.LowEnergyEvolution.Scalar
import H0mework.Physics.RadialDynamics.EulerJet

/-! Curvature and constitutive field read from the same coupled solution. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineP286GaugeConnectionVariation
open EmpiricalReferenceScaleCouplingBoundary StageNineFormNativeGaugeWedge
open StageNineBlockwiseConstitutive
open StageNineP286GaugeAuxiliaryVariation StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open Stage9C.Material.SpinPair Stage9C.Reduction SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage10.GaugeSpectrum.Dynamics
noncomputable section

private theorem curvature_congr (first second : StageNineHolonomicConfiguration)
    (same : first.gaugeConnection = second.gaugeConnection) (point : BasePoint) :
    holonomicGaugeCurvature first point = holonomicGaugeCurvature second point := by
  funext pair
  unfold holonomicGaugeCurvature p286ConnectionDerivative
  rw [same]

theorem Solution.gauge_curvature {initial : State} (flow : Solution initial) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    holonomicGaugeCurvature flow.configuration point =
      radialCurvature (flow.pointState point 2)
        (flow.pointState point 0 * flow.pointState point 3 / clock (flow.pointState point)) := by
  rw [curvature_congr flow.configuration (radialWrite (fun time => flow.curve time 2)) rfl]
  exact radialWrite_curvature _ _ _ (flow.coordinate_derivative _ inside 2)

theorem diagonalHodge (n a : ℝ) (hn : n ≠ 0) (ha : a ≠ 0) (form : GaugeTwoForm) :
    coframeGaugeSpacetimeHodgeLinear (diagonalCoframe n a) form =
      ![(a/n)*form 3, (a/n)*form 4, (a/n)*form 5,
        -(n/a)*form 0, -(n/a)*form 1, -(n/a)*form 2] := by
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [diagonalCoframe_inv n a hn ha]
  funext pair
  fin_cases pair <;>
    simp [coframeTwoFormLinear, lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
      diagonalCoframe, coframeWedge, pairFirst, pairSecond, Fin.sum_univ_six] <;>
    field_simp [hn, ha]

theorem diagonalHodge_lift {V : Type*} [AddCommGroup V] [Module ℝ V]
    (n a : ℝ) (hn : n ≠ 0) (ha : a ≠ 0) (form : Fin 6 → V) :
    liftGaugeTwoFormOperator (coframeGaugeSpacetimeHodgeLinear (diagonalCoframe n a)) form =
      ![(a/n) • form 3, (a/n) • form 4, (a/n) • form 5,
        -(n/a) • form 0, -(n/a) • form 1, -(n/a) • form 2] := by
  funext pair
  unfold liftGaugeTwoFormOperator gaugeOperatorCoefficient
  simp_rw [diagonalHodge n a hn ha]
  fin_cases pair <;> simp

def electricAmplitude (x : State) : ℝ := x 0 * (x 2)^2 / (sourceCoupling * clock x)
def magneticAmplitude (x : State) : ℝ := x 3 / sourceCoupling

def gaugeAuxiliary (x : State) : FormNativeP286GaugeTwoForm :=
  ![electricAmplitude x • sourceColorP286Generator 0,
    electricAmplitude x • sourceColorP286Generator 1,
    electricAmplitude x • sourceColorP286Generator 2,
    magneticAmplitude x • sourceColorP286Generator 0,
    magneticAmplitude x • sourceColorP286Generator 1,
    magneticAmplitude x • sourceColorP286Generator 2]

private theorem triadHodgeScale {V : Type*} [AddCommGroup V] [Module ℝ V]
    (generators : Fin 3 → V) (n a amplitude momentum coupling : ℝ)
    (hn : n ≠ 0) (ha : a ≠ 0) :
    -(coupling⁻¹ •
      ![(a/n) • (-(amplitude^2) • generators 0), (a/n) • (-(amplitude^2) • generators 1),
        (a/n) • (-(amplitude^2) • generators 2), -(n/a) • ((a*momentum/n) • generators 0),
        -(n/a) • ((a*momentum/n) • generators 1), -(n/a) • ((a*momentum/n) • generators 2)]) =
      ![(a*amplitude^2/(coupling*n)) • generators 0,
        (a*amplitude^2/(coupling*n)) • generators 1,
        (a*amplitude^2/(coupling*n)) • generators 2,
        (momentum/coupling) • generators 0,
        (momentum/coupling) • generators 1,
        (momentum/coupling) • generators 2] := by
  funext pair
  fin_cases pair <;> simp [smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  all_goals
    congr 1
    field_simp [hn, ha]

private theorem eliminatedAuxiliary_diagonal (n a amplitude momentum : ℝ)
    (hn : n ≠ 0) (ha : a ≠ 0) :
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (diagonalCoframe n a) (radialCurvature amplitude (a*momentum/n)) =
      ![(a*amplitude^2/(sourceCoupling*n)) • sourceColorP286Generator 0,
        (a*amplitude^2/(sourceCoupling*n)) • sourceColorP286Generator 1,
        (a*amplitude^2/(sourceCoupling*n)) • sourceColorP286Generator 2,
        (momentum/sourceCoupling) • sourceColorP286Generator 0,
        (momentum/sourceCoupling) • sourceColorP286Generator 1,
        (momentum/sourceCoupling) • sourceColorP286Generator 2] := by
  unfold formNativeP286GaugeEliminatedAuxiliaryAtBoundary formNativeP286LiftedCoframeHodge
  change -(sourceCoupling⁻¹ • liftGaugeTwoFormOperator
    (coframeGaugeSpacetimeHodgeLinear (diagonalCoframe n a)) _) = _
  rw [diagonalHodge_lift _ _ hn ha]
  exact triadHodgeScale sourceColorP286Generator n a amplitude momentum sourceCoupling hn ha

private theorem reductionAuxiliary_readback (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) (point : BasePoint) :
    (algebraicCartanReduction source current).gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary (sourceGeneratedUnifiedCouplings source)
        ((algebraicCartanReduction source current).coframe point)
        (holonomicGaugeCurvature (algebraicCartanReduction source current) point) := rfl

theorem Solution.gauge_auxiliary {initial : State} (flow : Solution initial) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    flow.configuration.gaugeAuxiliary point = gaugeAuxiliary (flow.pointState point) := by
  have h : Admissible (flow.pointState point) := flow.admissible _ inside
  have hn := ne_of_gt (clock_positive _ h)
  have ha := ne_of_gt h.1
  have readback := reductionAuxiliary_readback positiveSmoothUnifiedSource flow.raw point
  change flow.configuration.gaugeAuxiliary point =
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary _
      (flow.configuration.coframe point) (holonomicGaugeCurvature flow.configuration point) at readback
  rw [readback, flow.coframe, flow.gauge_curvature point inside]
  exact eliminatedAuxiliary_diagonal _ _ _ _ hn ha

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
