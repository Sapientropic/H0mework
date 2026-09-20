/-
  Proposition 453: Standard-Model one-loop beta coefficients as carrier data.

  P451/P452 prove the saturation side:

      residual self-bump + eta = b0 * sigma  ==>  sigma' - sigma = -b0 sigma^2.

  This file pins the honest role of the physical carrier.  The scalar `b0` is
  not an external adjustable input: the block/generation carrier chooses the
  Standard-Model gauge factor and matter content, and the standard
  Lie-algebraic one-loop coefficient function then gives exact rational
  values.  What is not rederived here are the universal QFT coefficients
  `11/3`, `2/3`, `1/3`, or `1/6` themselves.

  Sign convention:
  - `asymptoticB0` is the coefficient in
        beta(g) = -(g^3 / 16*pi^2) * asymptoticB0.
    This is the coefficient used by P451's residual form
        sigma' - sigma = -b0 * sigma^2.
  - `standardBetaCoefficient = -asymptoticB0` is the common SM table convention
        beta(g) = (g^3 / 16*pi^2) * b_SM.
-/

import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.RepresentationSources.P452
import H0mework.Physics.Generation.P417
import H0mework.Physics.Lie.P286

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

/-! ## Standard one-loop input formulas -/

/-- Standard non-abelian one-loop coefficient for Dirac fermions and complex
scalars in a representation with Dynkin index `T_R`.

This is the standard Lie/QFT coefficient function; the carrier contribution is
to determine its gauge and representation arguments. -/
structure NonabelianDiracOneLoopInput where
  adjointCasimir : ℚ
  dynkinIndex : ℚ
  diracFermions : ℚ
  complexScalars : ℚ

namespace NonabelianDiracOneLoopInput

/-- `b_asym = (11/3)C_A - (4/3)T_R n_f - (1/3)T_R n_S`
for complex scalars. -/
def asymptoticB0 (I : NonabelianDiracOneLoopInput) : ℚ :=
  (11 / 3) * I.adjointCasimir -
    (4 / 3) * I.dynkinIndex * I.diracFermions -
    (1 / 3) * I.dynkinIndex * I.complexScalars

def standardBetaCoefficient (I : NonabelianDiracOneLoopInput) : ℚ :=
  -I.asymptoticB0

theorem standardBetaCoefficient_eq_neg_asymptoticB0
    (I : NonabelianDiracOneLoopInput) :
    I.standardBetaCoefficient = -I.asymptoticB0 := rfl

end NonabelianDiracOneLoopInput

/-- Gauge theory one-loop input in trace form:
`Σ_Weyl T(R)` and `Σ_complexScalar T(R)` have already included multiplicity
over colors/generations/weak components. -/
structure GaugeTraceOneLoopInput where
  adjointCasimir : ℚ
  weylDynkinTrace : ℚ
  scalarDynkinTrace : ℚ

namespace GaugeTraceOneLoopInput

/-- `b_asym = (11/3)C_A - (2/3)Σ_Weyl T(R) - (1/3)Σ_scalar T(R)`. -/
def asymptoticB0 (I : GaugeTraceOneLoopInput) : ℚ :=
  (11 / 3) * I.adjointCasimir -
    (2 / 3) * I.weylDynkinTrace -
    (1 / 3) * I.scalarDynkinTrace

def standardBetaCoefficient (I : GaugeTraceOneLoopInput) : ℚ :=
  -I.asymptoticB0

theorem standardBetaCoefficient_eq_neg_asymptoticB0
    (I : GaugeTraceOneLoopInput) :
    I.standardBetaCoefficient = -I.asymptoticB0 := rfl

end GaugeTraceOneLoopInput

/-! ## Standard-Model carrier instances -/

/-- The three gauge factors selected by the `diag(C,W,z,z^-1)` Standard-Model
block shape.  P286 supplies the concrete block-diagonal embedding; this finite
type is the coefficient-level projection of that shape. -/
inductive StandardModelGaugeFactor where
  | colorSU3
  | weakSU2
  | hyperchargeU1
  deriving DecidableEq, Repr, FintypeViaProxy

/-- P417 pins the finite generation carrier to the three 4D Poincare slots;
this theorem records the concrete three-generation count used by the matter
trace below. -/
theorem standardModel_generation_count_three :
    Fintype.card StandardModelFermionGeneration = 3 := by
  decide

/-- Six active quark Dirac flavors in the Standard-Model color sector. -/
def qcdSixFlavorInput : NonabelianDiracOneLoopInput where
  adjointCasimir := 3
  dynkinIndex := 1 / 2
  diracFermions := 6
  complexScalars := 0

/-- `b_asym(QCD) = (11/3)*3 - (4/3)*(1/2)*6 = 7`. -/
theorem qcdSixFlavor_asymptoticB0 :
    qcdSixFlavorInput.asymptoticB0 = 7 := by
  norm_num [qcdSixFlavorInput, NonabelianDiracOneLoopInput.asymptoticB0]

/-- In the common SM beta-table convention, `b_QCD = -7`. -/
theorem qcdSixFlavor_standardBetaCoefficient :
    qcdSixFlavorInput.standardBetaCoefficient = -7 := by
  norm_num [qcdSixFlavorInput, NonabelianDiracOneLoopInput.standardBetaCoefficient,
    NonabelianDiracOneLoopInput.asymptoticB0]

/-- Standard weak-sector traces:
12 weak Weyl doublets, each with `T(fundamental)=1/2`, so
`Σ_Weyl T(R)=6`; one Higgs doublet gives `Σ_scalar T(R)=1/2`. -/
def weakStandardModelInput : GaugeTraceOneLoopInput where
  adjointCasimir := 2
  weylDynkinTrace := 6
  scalarDynkinTrace := 1 / 2

/-- `b_asym(SU(2)) = 22/3 - 4 - 1/6 = 19/6`. -/
theorem weakStandardModel_asymptoticB0 :
    weakStandardModelInput.asymptoticB0 = 19 / 6 := by
  norm_num [weakStandardModelInput, GaugeTraceOneLoopInput.asymptoticB0]

/-- In the common SM beta-table convention, `b_2 = -19/6`. -/
theorem weakStandardModel_standardBetaCoefficient :
    weakStandardModelInput.standardBetaCoefficient = -(19 / 6) := by
  norm_num [weakStandardModelInput, GaugeTraceOneLoopInput.standardBetaCoefficient,
    GaugeTraceOneLoopInput.asymptoticB0]

/-- Hypercharge square traces in the usual SM normalization:
three generations give `Σ_Weyl Y² = 10`, and the Higgs doublet gives
`Σ_scalar Y² = 1/2`.  For `U(1)`, `C_A = 0`. -/
def hyperchargeStandardModelInput : GaugeTraceOneLoopInput where
  adjointCasimir := 0
  weylDynkinTrace := 10
  scalarDynkinTrace := 1 / 2

/-- In the residual/asymptotic sign convention, hypercharge has
`b_asym(U(1)_Y) = -41/6`. -/
theorem hyperchargeStandardModel_asymptoticB0 :
    hyperchargeStandardModelInput.asymptoticB0 = -(41 / 6) := by
  norm_num [hyperchargeStandardModelInput, GaugeTraceOneLoopInput.asymptoticB0]

/-- In the common SM beta-table convention, `b_1 = 41/6`. -/
theorem hyperchargeStandardModel_standardBetaCoefficient :
    hyperchargeStandardModelInput.standardBetaCoefficient = 41 / 6 := by
  norm_num [hyperchargeStandardModelInput, GaugeTraceOneLoopInput.standardBetaCoefficient,
    GaugeTraceOneLoopInput.asymptoticB0]

/-- The coefficient used by P451's residual one-loop saturation law. -/
def standardModelAsymptoticB0 : StandardModelGaugeFactor -> ℚ
  | .colorSU3 => qcdSixFlavorInput.asymptoticB0
  | .weakSU2 => weakStandardModelInput.asymptoticB0
  | .hyperchargeU1 => hyperchargeStandardModelInput.asymptoticB0

/-- The common SM beta-table coefficient. -/
def standardModelBetaCoefficient : StandardModelGaugeFactor -> ℚ
  | .colorSU3 => qcdSixFlavorInput.standardBetaCoefficient
  | .weakSU2 => weakStandardModelInput.standardBetaCoefficient
  | .hyperchargeU1 => hyperchargeStandardModelInput.standardBetaCoefficient

theorem standardModelAsymptoticB0_color :
    standardModelAsymptoticB0 .colorSU3 = 7 := by
  rw [standardModelAsymptoticB0, qcdSixFlavor_asymptoticB0]

theorem standardModelAsymptoticB0_weak :
    standardModelAsymptoticB0 .weakSU2 = 19 / 6 := by
  rw [standardModelAsymptoticB0, weakStandardModel_asymptoticB0]

theorem standardModelAsymptoticB0_hypercharge :
    standardModelAsymptoticB0 .hyperchargeU1 = -(41 / 6) := by
  rw [standardModelAsymptoticB0, hyperchargeStandardModel_asymptoticB0]

theorem standardModelBetaCoefficient_color :
    standardModelBetaCoefficient .colorSU3 = -7 := by
  rw [standardModelBetaCoefficient, qcdSixFlavor_standardBetaCoefficient]

theorem standardModelBetaCoefficient_weak :
    standardModelBetaCoefficient .weakSU2 = -(19 / 6) := by
  rw [standardModelBetaCoefficient, weakStandardModel_standardBetaCoefficient]

theorem standardModelBetaCoefficient_hypercharge :
    standardModelBetaCoefficient .hyperchargeU1 = 41 / 6 := by
  rw [standardModelBetaCoefficient, hyperchargeStandardModel_standardBetaCoefficient]

/-- A bundled certificate for the coefficient-level Standard-Model carrier.
The scalar `b0` is not a free parameter: it is forced after the carrier fixes
the gauge factors and matter traces. -/
structure StandardModelOneLoopB0Certificate where
  generation_count : Fintype.card StandardModelFermionGeneration = 3
  asym_color : standardModelAsymptoticB0 .colorSU3 = 7
  asym_weak : standardModelAsymptoticB0 .weakSU2 = 19 / 6
  asym_hypercharge : standardModelAsymptoticB0 .hyperchargeU1 = -(41 / 6)
  beta_color : standardModelBetaCoefficient .colorSU3 = -7
  beta_weak : standardModelBetaCoefficient .weakSU2 = -(19 / 6)
  beta_hypercharge : standardModelBetaCoefficient .hyperchargeU1 = 41 / 6

/-- The Standard-Model carrier supplies all three exact one-loop coefficients,
in both sign conventions. -/
theorem standardModelOneLoopB0Certificate :
    StandardModelOneLoopB0Certificate :=
  { generation_count := standardModel_generation_count_three
    asym_color := standardModelAsymptoticB0_color
    asym_weak := standardModelAsymptoticB0_weak
    asym_hypercharge := standardModelAsymptoticB0_hypercharge
    beta_color := standardModelBetaCoefficient_color
    beta_weak := standardModelBetaCoefficient_weak
    beta_hypercharge := standardModelBetaCoefficient_hypercharge }

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
