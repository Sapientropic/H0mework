import H0mework.Physics.SpinPair.ColorAlgebra
import H0mework.Physics.SpinPair.Regularity
import H0mework.Physics.Constitutive.P286GaugeGeometricKinematics

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineBlockwiseConstitutive
open StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineFormNativeP286GaugeConstitutiveElimination StageNineFormNativeP286GaugeYangMillsReadout
open StageNineHolonomicGaugeCurvatureTransport
open Stage9C.Reduction Stage9C.Dynamics.Homogeneous
open SU7MotherLieAlgebra SU7MotherGaugeTheory EmpiricalReferenceScaleCouplingBoundary

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def magneticCurvature (amplitude : ℝ) : Fin 6 → P286LieBlockData :=
  ![0,0,0, -(amplitude^2) • sourceColorP286Generator 0,
    -(amplitude^2) • sourceColorP286Generator 1, -(amplitude^2) • sourceColorP286Generator 2]

def electricAuxiliary (clock amplitude : ℝ) : Fin 6 → P286LieBlockData :=
  ![(amplitude^2/(sourceCoupling*clock)) • sourceColorP286Generator 0,
    (amplitude^2/(sourceCoupling*clock)) • sourceColorP286Generator 1,
    (amplitude^2/(sourceCoupling*clock)) • sourceColorP286Generator 2, 0,0,0]

theorem constantGauge_curvature
    (current : StageNineHolonomicConfiguration) (amplitude : ℝ)
    (connection : current.gaugeConnection = fun _ => gaugePotential amplitude) (point : BasePoint) :
    holonomicGaugeCurvature current point = magneticCurvature amplitude := by
  have derivative (first second : LorentzianIndex) :
      p286ConnectionDerivative current point first second = 0 := by
    unfold p286ConnectionDerivative fieldDirectionalDerivative
    rw [connection]
    rw [(hasFDerivAt_const (𝕜 := ℝ) (p286CoordinateEquiv (gaugePotential amplitude second)) point).fderiv]
    simp
  funext pair
  unfold holonomicGaugeCurvature
  simp only [derivative, sub_self, zero_add, connection]
  fin_cases pair <;>
    simp [gaugePotential, magneticCurvature, pairFirst, pairSecond,
      p286LieBracket_smul_left, p286LieBracket_smul_right,
      sourceColorP286Generator_bracket, smul_smul, pow_two]
  all_goals first
    | exact Or.inr (by simp [p286LieBracket, suLieBracket])
    | module

theorem actual_gaugeCurvature (point : BasePoint) :
    holonomicGaugeCurvature actual point = magneticCurvature gaugeScale :=
  constantGauge_curvature actual gaugeScale actual_gaugeConnection point

theorem homogeneousHodge (clock : ℝ) (nonzero : clock ≠ 0) (form : GaugeTwoForm) :
    coframeGaugeSpacetimeHodgeLinear (homogeneousCoframe clock) form =
      ![clock⁻¹*form 3, clock⁻¹*form 4, clock⁻¹*form 5,
        -clock*form 0, -clock*form 1, -clock*form 2] := by
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [homogeneousCoframe_inv clock nonzero]
  funext pair
  fin_cases pair <;>
    simp [coframeTwoFormLinear, lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
      homogeneousCoframe, coframeWedge, pairFirst, pairSecond, Fin.sum_univ_six]

theorem homogeneousHodge_lift
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (clock : ℝ) (nonzero : clock ≠ 0) (form : Fin 6 → V) :
    liftGaugeTwoFormOperator (coframeGaugeSpacetimeHodgeLinear (homogeneousCoframe clock)) form =
      ![clock⁻¹ • form 3, clock⁻¹ • form 4, clock⁻¹ • form 5,
        -clock • form 0, -clock • form 1, -clock • form 2] := by
  funext pair
  unfold liftGaugeTwoFormOperator gaugeOperatorCoefficient
  simp_rw [homogeneousHodge clock nonzero]
  fin_cases pair <;> simp

theorem actual_gaugeAuxiliary : actual.gaugeAuxiliary = fun _ => electricAuxiliary lapse gaugeScale := by
  unfold actual algebraicCartanReduction
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeAuxiliary]
  funext point
  rw [formNativeP286GaugeConstitutiveReadout_gaugeAuxiliary]
  rw [constantGauge_curvature seed gaugeScale rfl point]
  change formNativeP286GaugeEliminatedAuxiliaryAtBoundary _
    (homogeneousCoframe lapse) (magneticCurvature gaugeScale) = _
  unfold formNativeP286GaugeEliminatedAuxiliaryAtBoundary formNativeP286LiftedCoframeHodge
  rw [homogeneousHodge_lift lapse (ne_of_gt lapse_pos)]
  funext pair
  fin_cases pair <;>
    simp [formNativeP286BlockScale, magneticCurvature, electricAuxiliary,
      sourceColorP286Generator_weak_zero, sourceColorP286Generator_hypercharge_zero,
      sourceCoupling, smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  all_goals
    apply Prod.ext
    · rfl
    · apply Prod.ext <;>
        simp [sourceColorP286Generator_weak_zero, sourceColorP286Generator_hypercharge_zero]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
