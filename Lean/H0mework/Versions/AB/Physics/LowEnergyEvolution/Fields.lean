import H0mework.Versions.AB.Physics.LowEnergyEvolution.Balance
import H0mework.Versions.R2.Physics.SpinPair.Scalar

/-! The generated coupled curve writes the original primitive field carrier.
Auxiliary fields and the Cartan connection come from the original reduction. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open Stage9C.Material.SpinPair Stage9C.Reduction SU7MotherLieAlgebra SU7MotherGaugeTheory
open Response.Radial DiracExteriorMatterAction
noncomputable section

def diagonalCoframe (n a : ℝ) : LorentzianCoframe := Matrix.diagonal ![n,a,a,a]

theorem diagonalCoframe_det (n a : ℝ) : (diagonalCoframe n a).det = n*a^3 := by
  simp [diagonalCoframe, Fin.prod_univ_four]
  ring

theorem diagonalCoframe_metric_inverse (n a : ℝ) (hn : n ≠ 0) (ha : a ≠ 0) :
    (lorentzianMetricOfCoframe (diagonalCoframe n a))⁻¹ =
      Matrix.diagonal ![-(n^2)⁻¹,(a^2)⁻¹,(a^2)⁻¹,(a^2)⁻¹] := by
  apply Matrix.inv_eq_left_inv
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [diagonalCoframe, lorentzianMetricOfCoframe, minkowskiInternalMetric,
      Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp [hn, ha]

def dilution (a : ℝ) : ℝ := (a * Real.sqrt a)⁻¹

def Solution.pointState {initial : State} (flow : Solution initial) (point : BasePoint) : State :=
  flow.curve (point 0)

def Solution.raw {initial : State} (flow : Solution initial) : StageNineHolonomicConfiguration :=
  { actual with
    coframe := fun point => diagonalCoframe (clock (flow.pointState point)) (flow.pointState point 0)
    gaugeConnection := fun point => gaugePotential (flow.pointState point 2)
    scalar := fun point => direction + flow.pointState point 4 • direction
    matter := fun point =>
      let state := flow.pointState point
      spinPairMatter ((dilution (state 0) : ℂ) * Complex.exp (Complex.I * (state 6 : ℂ)))
        ((dilution (state 0) : ℂ) * Complex.exp (-Complex.I * (state 6 : ℂ)))
    conjugateMatter := fun point =>
      let state := flow.pointState point
      spinPairDual ((spinScale : ℂ) * (dilution (state 0) : ℂ) * Complex.exp (Complex.I * (state 6 : ℂ)))
        ((spinScale : ℂ) * (dilution (state 0) : ℂ) * Complex.exp (-Complex.I * (state 6 : ℂ))) }

def Solution.configuration {initial : State} (flow : Solution initial) : StageNineHolonomicConfiguration :=
  algebraicCartanReduction positiveSmoothUnifiedSource flow.raw

theorem Solution.initial_state {initial : State} (flow : Solution initial)
    (point : BasePoint) (onSlice : point 0 = 0) : flow.pointState point = initial := by
  change flow.curve (point 0) = initial
  rw [onSlice, flow.starts]

theorem Solution.initial_fields {initial : State} (flow : Solution initial)
    (point : BasePoint) (onSlice : point 0 = 0) :
    flow.configuration.coframe point = diagonalCoframe (clock initial) (initial 0) ∧
    flow.configuration.gaugeConnection point = gaugePotential (initial 2) ∧
    flow.configuration.scalar point = direction + initial 4 • direction ∧
    flow.configuration.matter point =
      spinPairMatter ((dilution (initial 0) : ℂ) * Complex.exp (Complex.I * (initial 6 : ℂ)))
        ((dilution (initial 0) : ℂ) * Complex.exp (-Complex.I * (initial 6 : ℂ))) ∧
    flow.configuration.conjugateMatter point =
      spinPairDual ((spinScale : ℂ) * (dilution (initial 0) : ℂ) * Complex.exp (Complex.I * (initial 6 : ℂ)))
        ((spinScale : ℂ) * (dilution (initial 0) : ℂ) * Complex.exp (-Complex.I * (initial 6 : ℂ))) := by
  change diagonalCoframe (clock (flow.pointState point)) (flow.pointState point 0) = _ ∧
    gaugePotential (flow.pointState point 2) = _ ∧
    direction + flow.pointState point 4 • direction = _ ∧
    spinPairMatter _ _ = _ ∧ spinPairDual _ _ = _
  rw [flow.initial_state point onSlice]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Solution.coframe {initial : State} (flow : Solution initial) (point : BasePoint) :
    flow.configuration.coframe point =
      diagonalCoframe (clock (flow.pointState point)) (flow.pointState point 0) := rfl

theorem Solution.nondegenerate_at {initial : State} (flow : Solution initial) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    (flow.configuration.coframe point).det ≠ 0 := by
  rw [flow.coframe, diagonalCoframe_det]
  exact mul_ne_zero (ne_of_gt (clock_positive _ (flow.admissible _ inside)))
    (pow_ne_zero _ (ne_of_gt (flow.admissible _ inside).1))

theorem Solution.scalar_derivative {initial : State} (flow : Solution initial) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) (mu : LorentzianIndex) :
    fieldDirectionalDerivative flow.configuration.scalar point mu =
      (if mu = 0 then clock (flow.pointState point) * flow.pointState point 5 else 0) • direction := by
  have time := (flow.coordinate_derivative (point 0) inside 4).hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  have derivative := (hasFDerivAt_const (𝕜 := ℝ) direction point).add (time.smul_const direction)
  change HasFDerivAt (fun p : BasePoint => direction + flow.curve (p 0) 4 • direction) _ point at derivative
  unfold fieldDirectionalDerivative
  change fderiv ℝ (fun p : BasePoint => direction + flow.curve (p 0) 4 • direction) point _ = _
  rw [derivative.fderiv]
  change (0 : ScalarCoordinateCarrier) + ((coordinateDirection mu) 0 *
    (clock (flow.pointState point) * flow.pointState point 5)) • direction = _
  by_cases same : mu = 0
  · simp [same, coordinateDirection]
  · simp [same, coordinateDirection, Ne.symm same]

theorem radial_color_zero (amplitude : ℝ) (mu : LorentzianIndex) :
    scalarMotherLieAction (p286LieBlockEmbed (gaugePotential amplitude mu)) direction = 0 := by
  have spatial (index : Fin 3) :
      scalarMotherLieAction (p286LieBlockEmbed (amplitude • sourceColorP286Generator index)) direction = 0 := by
    rw [p286LieBlockEmbed_real_smul, scalarMotherLieAction_real_smul]
    change amplitude • scalarMotherLieAction _ (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0
    rw [sourceColorP286Generator_vacuum_zero, smul_zero]
  fin_cases mu
  · simp [gaugePotential, scalarMotherLieAction, p286LieBlockEmbed_zero]
  · exact spatial 0
  · exact spatial 1
  · exact spatial 2

theorem Solution.scalar_covariant {initial : State} (flow : Solution initial) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) (mu : LorentzianIndex) :
    holonomicScalarCovariantDerivative flow.configuration point mu =
      (if mu = 0 then clock (flow.pointState point) * flow.pointState point 5 else 0) • direction := by
  rw [holonomicScalarCovariantDerivative, flow.scalar_derivative point inside mu]
  change _ + scalarMotherLieAction (p286LieBlockEmbed (gaugePotential (flow.pointState point 2) mu))
    (direction + flow.pointState point 4 • direction) = _
  rw [scalarMotherLieAction_add_right, scalarMotherLieAction_real_smul_right,
    radial_color_zero, smul_zero, add_zero, add_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
