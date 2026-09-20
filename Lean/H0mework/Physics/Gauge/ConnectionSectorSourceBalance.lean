import H0mework.Physics.GaugeAction.P286GaugeConnectionPointwiseEquation
import H0mework.Physics.Lorentz.LorentzConnectionPointwiseEquation

/-!
# S9-C3f3: connection equations split into actual sector sources

The previously generated P286 and Lorentz pointwise Euler--Lagrange
coefficients each bundled several action sectors under one historical name.
This module exposes their exact source decomposition without changing either
equation and without accepting a current, spin, balance, or conservation
receipt.

On the P286 side the algebraic coefficient is split into gauge-BF, scalar,
and exterior-matter terms.  On the Lorentz side the historical
`lorentzConnectionAlgebraicSpinCurrentCoefficient` is proved to contain both
the gravity-BF algebraic term and the pure exterior-matter spin source; it is
therefore not itself renamed or interpreted as matter spin.

These are pointwise field-equation source balances.  They are not yet active
gauge/Lorentz Ward identities, covariant current conservation, stress--spin
balance, or a simultaneous solution producer.
-/

namespace SaturationMonoid.PhysicsCore.StageNineConnectionSectorSourceBalance

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionWeakEquation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionActionVariation
open StageNineLorentzConnectionWeakEquation
open StageNineLorentzConnectionPointwiseEquation

noncomputable section

/-! ## P286 gauge-BF, scalar-current, and matter-current sources -/

def p286GaugeBFAlgebraicCoefficient
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    p286GaugeBFCurvatureIncrementDensity
      (configuration.coframe point)
      (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
      (holonomicP286GaugeAuxiliaryCoordinate configuration point)
      (p286GaugeConnectionAlgebraicCurvatureDirection
        configuration direction point)

def p286ScalarCurrentCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point
      (toContinuumPointField configuration point)
      (holonomicScalarGaugeConnectionVariation configuration
        (fun _ => direction) point)

def p286MatterCurrentCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    matterGaugeConnectionFirstVariationDensity source 0 point
      (toContinuumPointField configuration point)
      (holonomicMatterGaugeConnectionVariation configuration
        (fun _ => direction) point)

def p286ChargedCurrentCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  p286ScalarCurrentCoefficient source configuration direction point +
    p286MatterCurrentCoefficient source configuration direction point

def p286GaugeBFBalanceCoefficient
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  p286GaugeBFAlgebraicCoefficient configuration direction point -
    p286GaugeConnectionBFDifferentialMomentumDivergence configuration
      direction point

theorem p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        direction point =
      p286GaugeBFAlgebraicCoefficient configuration direction point +
        p286ScalarCurrentCoefficient source configuration direction point +
        p286MatterCurrentCoefficient source configuration direction point := by
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
    p286GaugeConnectionFirstVariationDensity
    p286GaugeBFAlgebraicCoefficient p286ScalarCurrentCoefficient
    p286MatterCurrentCoefficient
  rw [show p286AuxiliaryCoordinate
      (toContinuumPointField configuration point) =
        holonomicP286GaugeAuxiliaryCoordinate configuration point by rfl]
  simp only [toContinuumPointField]
  ring

theorem p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionEulerLagrangeCoefficient source configuration
        direction point =
      p286GaugeBFBalanceCoefficient configuration direction point +
        p286ScalarCurrentCoefficient source configuration direction point +
        p286MatterCurrentCoefficient source configuration direction point := by
  rw [p286GaugeConnectionEulerLagrangeCoefficient,
    p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors]
  unfold p286GaugeBFBalanceCoefficient
  ring

theorem p286GaugeConnectionEulerLagrangeCoefficient_eq_bfBalance_add_charged
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionEulerLagrangeCoefficient source configuration
        direction point =
      p286GaugeBFBalanceCoefficient configuration direction point +
        p286ChargedCurrentCoefficient source configuration direction point := by
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance]
  unfold p286ChargedCurrentCoefficient
  ring

theorem canonicalP286GaugeConnectionPointwiseEquation_implies_sectorBalance
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (equation : CanonicalP286GaugeConnectionPointwiseEquation source
      configuration)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeBFBalanceCoefficient configuration direction point +
        p286ScalarCurrentCoefficient source configuration direction point +
        p286MatterCurrentCoefficient source configuration direction point = 0 := by
  have pointEquation := congrFun (equation direction) point
  rwa [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance] at pointEquation

theorem canonicalP286GaugeConnectionPointwiseEquation_implies_response_eq_chargedCurrent
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (equation : CanonicalP286GaugeConnectionPointwiseEquation source
      configuration)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentumDivergence configuration direction
          point -
        p286GaugeBFAlgebraicCoefficient configuration direction point =
      p286ChargedCurrentCoefficient source configuration direction point := by
  have balance :=
    canonicalP286GaugeConnectionPointwiseEquation_implies_sectorBalance
      source configuration equation direction point
  unfold p286GaugeBFBalanceCoefficient at balance
  unfold p286ChargedCurrentCoefficient
  linarith

theorem canonicalP286GaugeConnectionActionStationary_generates_sectorBalance
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CanonicalP286GaugeConnectionActionStationary source
      configuration)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeBFBalanceCoefficient configuration direction point +
        p286ScalarCurrentCoefficient source configuration direction point +
        p286MatterCurrentCoefficient source configuration direction point = 0 := by
  have weakEquation :=
    canonicalP286GaugeConnectionActionStationary_implies_weakEquation source
      configuration smooth nondegenerate densityIntegrable stationary
  have pointwiseEquation :=
    canonicalP286GaugeConnectionWeakEquation_implies_pointwiseEquation source
      configuration smooth nondegenerate weakEquation
  exact canonicalP286GaugeConnectionPointwiseEquation_implies_sectorBalance
    source configuration pointwiseEquation direction point

/-! ## Gravity-BF and pure exterior-matter spin sources -/

def lorentzGravityBFAlgebraicCoefficient
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    gravityBFCurvatureIncrementDensity
      (configuration.coframe point)
      (configuration.gravityAuxiliary point)
      (lorentzConnectionAlgebraicCurvatureDirection configuration direction
        point)

def lorentzMatterSpinSourceCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    matterGaugeConnectionFirstVariationDensity source 0 point
      (toContinuumPointField configuration point)
      (holonomicMatterLorentzConnectionVariation configuration
        (fun _ => direction) point)

def lorentzGravityBFBalanceCoefficient
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) : ℝ :=
  lorentzGravityBFAlgebraicCoefficient configuration direction point -
    lorentzConnectionBFDifferentialMomentumDivergence configuration direction
      point

theorem lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) :
    lorentzConnectionAlgebraicSpinCurrentCoefficient source configuration
        direction point =
      lorentzGravityBFAlgebraicCoefficient configuration direction point +
        lorentzMatterSpinSourceCoefficient source configuration direction
          point := by
  unfold lorentzConnectionAlgebraicSpinCurrentCoefficient
    lorentzConnectionFirstVariationDensity
    lorentzGravityBFAlgebraicCoefficient lorentzMatterSpinSourceCoefficient
  simp only [toContinuumPointField]
  ring

theorem lorentzConnectionEulerLagrangeCoefficient_eq_sectorBalance
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) :
    lorentzConnectionEulerLagrangeCoefficient source configuration direction
        point =
      lorentzGravityBFBalanceCoefficient configuration direction point +
        lorentzMatterSpinSourceCoefficient source configuration direction
          point := by
  rw [lorentzConnectionEulerLagrangeCoefficient,
    lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors]
  unfold lorentzGravityBFBalanceCoefficient
  ring

theorem canonicalLorentzConnectionPointwiseEquation_implies_sectorBalance
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (equation : CanonicalLorentzConnectionPointwiseEquation source
      configuration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) :
    lorentzGravityBFBalanceCoefficient configuration direction point +
        lorentzMatterSpinSourceCoefficient source configuration direction
          point = 0 := by
  have pointEquation := congrFun (equation direction) point
  rwa [lorentzConnectionEulerLagrangeCoefficient_eq_sectorBalance] at pointEquation

theorem canonicalLorentzConnectionPointwiseEquation_implies_gravityResponse_eq_matterSpin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (equation : CanonicalLorentzConnectionPointwiseEquation source
      configuration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) :
    lorentzConnectionBFDifferentialMomentumDivergence configuration direction
          point -
        lorentzGravityBFAlgebraicCoefficient configuration direction point =
      lorentzMatterSpinSourceCoefficient source configuration direction
        point := by
  have balance :=
    canonicalLorentzConnectionPointwiseEquation_implies_sectorBalance
      source configuration equation direction point
  unfold lorentzGravityBFBalanceCoefficient at balance
  linarith

theorem canonicalLorentzConnectionActionStationary_generates_sectorBalance
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CanonicalLorentzConnectionActionStationary source
      configuration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) :
    lorentzGravityBFBalanceCoefficient configuration direction point +
        lorentzMatterSpinSourceCoefficient source configuration direction
          point = 0 := by
  have weakEquation :=
    canonicalLorentzConnectionActionStationary_implies_weakEquation source
      configuration smooth nondegenerate densityIntegrable stationary
  have pointwiseEquation :=
    canonicalLorentzConnectionWeakEquation_implies_pointwiseEquation source
      configuration smooth nondegenerate weakEquation
  exact canonicalLorentzConnectionPointwiseEquation_implies_sectorBalance
    source configuration pointwiseEquation direction point

end

end SaturationMonoid.PhysicsCore.StageNineConnectionSectorSourceBalance
