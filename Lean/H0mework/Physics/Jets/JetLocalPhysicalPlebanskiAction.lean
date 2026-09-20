import H0mework.Physics.Source.PhysicalIIPlusFrechetVariation

/-!
# Jet-local physical Plebanski action density

This module replaces two earlier surrogates at once:

* the connection coordinate is a genuine first jet and its curvature is
  `dω + ω∧ω`;
* the multiplier equation enforces the 36-component physical branch
  `B = *internal(e ∧ e)`, not `B=e`.

The BF term, auxiliary quadratic term, and physical branch multiplier belong
to one polynomial action density.  Mathlib proves its connection, bivector,
multiplier, and tetrad Fréchet derivatives.  In particular `deltaPhi = 0` is
proved equivalent to the physical `II+` substitution.

Boundary: this is a jet-local Lagrangian density.  It does not yet construct a
spacetime integral, perform connection integration by parts, prove a
source-selected stationary family, or combine the three empirical SM gauge
blocks into the same continuum action.  It must not be cited as completed
Einstein/Plebanski recovery.
-/

namespace SaturationMonoid.PhysicsCore.JetLocalPhysicalPlebanskiAction

open ProofFreeRicherAnholonomicSource
open PhysicalIIPlusFrechetVariation
open scoped RealInnerProductSpace

noncomputable section

abbrev OmegaValueIndex :=
  LorentzianIndex × LorentzianIndex × LorentzianIndex

abbrev OmegaDerivativeIndex :=
  LorentzianIndex × LorentzianIndex ×
    LorentzianIndex × LorentzianIndex

abbrev OmegaValue := EuclideanSpace ℝ OmegaValueIndex
abbrev OmegaDerivative := EuclideanSpace ℝ OmegaDerivativeIndex
abbrev ConnectionJet := OmegaValue × OmegaDerivative

def omegaValue
    (connection : ConnectionJet)
    (direction internalOut internalIn : LorentzianIndex) : ℝ :=
  connection.1 (direction, internalOut, internalIn)

def omegaDerivative
    (connection : ConnectionJet)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) : ℝ :=
  connection.2
    (derivativeDirection, formDirection, internalOut, internalIn)

/-- Genuine pointwise non-Abelian curvature `dω + ω∧ω`, projected to
the six internal and six spacetime oriented pairs. -/
def nonAbelianCurvature (connection : ConnectionJet) : BivectorVector :=
  WithLp.toLp 2 fun pair =>
    let internalPair := pair.1
    let spacetimePair := pair.2
    let internalOut := pairFirst internalPair
    let internalIn := pairSecond internalPair
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    minkowskiInternalSign internalOut *
      (omegaDerivative connection first second internalOut internalIn -
          omegaDerivative connection second first internalOut internalIn +
        ∑ middle,
          (omegaValue connection first internalOut middle *
              omegaValue connection second middle internalIn -
            omegaValue connection second internalOut middle *
              omegaValue connection first middle internalIn))

theorem nonAbelianCurvature_contDiff :
    ContDiff ℝ ⊤ nonAbelianCurvature := by
  unfold nonAbelianCurvature omegaDerivative omegaValue
  fun_prop

def spacetimeHodgeVector
    (bivector : BivectorVector) : BivectorVector :=
  WithLp.toLp 2 fun pair =>
    lorentzianCoframeHodge
      (fun sourceSpacetimePair => bivector (pair.1, sourceSpacetimePair))
      pair.2

theorem spacetimeHodgeVector_contDiff :
    ContDiff ℝ ⊤ spacetimeHodgeVector := by
  apply contDiff_piLp'
  rintro ⟨internalPair, spacetimePair⟩
  fin_cases spacetimePair <;>
    simp [spacetimeHodgeVector, lorentzianCoframeHodge]
  all_goals fun_prop

structure Configuration where
  connection : ConnectionJet
  bivector : BivectorVector
  multiplier : BivectorVector
  tetrad : TetradVector

namespace Configuration

def withConnection (q : Configuration) (connection : ConnectionJet) :
    Configuration :=
  { q with connection := connection }

def withBivector (q : Configuration) (bivector : BivectorVector) :
    Configuration :=
  { q with bivector := bivector }

def withMultiplier (q : Configuration) (multiplier : BivectorVector) :
    Configuration :=
  { q with multiplier := multiplier }

def withTetrad (q : Configuration) (tetrad : TetradVector) :
    Configuration :=
  { q with tetrad := tetrad }

end Configuration

/-- Jet-local first-order BF--Plebanski density.  The first term is the BF
pairing with non-Abelian curvature, the second is an auxiliary constitutive
quadratic term, and the multiplier enforces the exact physical `II+` branch.
-/
def masterAction (q : Configuration) : ℝ :=
  ⟪q.bivector, spacetimeHodgeVector (nonAbelianCurvature q.connection)⟫ -
      (1 / 2 : ℝ) * ‖q.bivector‖ ^ 2 +
    ⟪q.multiplier, q.bivector - physicalIIPlusMap q.tetrad⟫

theorem masterAction_connection_contDiff (q : Configuration) :
    ContDiff ℝ ⊤ (fun connection => masterAction (q.withConnection connection)) := by
  have hcurvature :
      ContDiff ℝ ⊤
        (fun connection =>
          spacetimeHodgeVector (nonAbelianCurvature connection)) :=
    spacetimeHodgeVector_contDiff.comp nonAbelianCurvature_contDiff
  have hbf :
      ContDiff ℝ ⊤
        (fun connection =>
          ⟪q.bivector,
            spacetimeHodgeVector (nonAbelianCurvature connection)⟫) :=
    contDiff_const.inner ℝ hcurvature
  simpa [masterAction, Configuration.withConnection] using
    (hbf.sub contDiff_const).add contDiff_const

theorem masterAction_bivector_contDiff (q : Configuration) :
    ContDiff ℝ ⊤ (fun bivector => masterAction (q.withBivector bivector)) := by
  have hbf :
      ContDiff ℝ ⊤
        (fun bivector : BivectorVector =>
          ⟪bivector,
            spacetimeHodgeVector (nonAbelianCurvature q.connection)⟫) :=
    contDiff_id.inner ℝ contDiff_const
  have hquadratic :
      ContDiff ℝ ⊤
        (fun bivector : BivectorVector =>
          (1 / 2 : ℝ) * ‖bivector‖ ^ 2) :=
    ContDiff.const_smul (R := ℝ) (1 / 2 : ℝ)
      (contDiff_id.norm_sq ℝ)
  have hmultiplier :
      ContDiff ℝ ⊤
        (fun bivector : BivectorVector =>
          ⟪q.multiplier, bivector - physicalIIPlusMap q.tetrad⟫) :=
    contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)
  simpa [masterAction, Configuration.withBivector] using
    (hbf.sub hquadratic).add hmultiplier

theorem masterAction_multiplier_contDiff (q : Configuration) :
    ContDiff ℝ ⊤ (fun multiplier => masterAction (q.withMultiplier multiplier)) := by
  have hmultiplier :
      ContDiff ℝ ⊤
        (fun multiplier : BivectorVector =>
          ⟪multiplier, q.bivector - physicalIIPlusMap q.tetrad⟫) :=
    contDiff_id.inner ℝ contDiff_const
  simpa [masterAction, Configuration.withMultiplier] using
    (contDiff_const.sub contDiff_const).add hmultiplier

theorem masterAction_tetrad_contDiff (q : Configuration) :
    ContDiff ℝ ⊤ (fun tetrad => masterAction (q.withTetrad tetrad)) := by
  have hmultiplier :
      ContDiff ℝ ⊤
        (fun tetrad : TetradVector =>
          ⟪q.multiplier, q.bivector - physicalIIPlusMap tetrad⟫) :=
    contDiff_const.inner ℝ
      (contDiff_const.sub physicalIIPlusMap_contDiff)
  simpa [masterAction, Configuration.withTetrad] using
    (contDiff_const.sub contDiff_const).add hmultiplier

def deltaOmega (q : Configuration) : ConnectionJet →L[ℝ] ℝ :=
  fderiv ℝ (fun connection => masterAction (q.withConnection connection))
    q.connection

def deltaB (q : Configuration) : BivectorVector →L[ℝ] ℝ :=
  fderiv ℝ (fun bivector => masterAction (q.withBivector bivector))
    q.bivector

def deltaPhi (q : Configuration) : BivectorVector →L[ℝ] ℝ :=
  innerSL ℝ (q.bivector - physicalIIPlusMap q.tetrad)

def deltaE (q : Configuration) : TetradVector →L[ℝ] ℝ :=
  fderiv ℝ (fun tetrad => masterAction (q.withTetrad tetrad)) q.tetrad

theorem actual_connection_derivative (q : Configuration) :
    HasFDerivAt
      (fun connection => masterAction (q.withConnection connection))
      (deltaOmega q) q.connection :=
  ((masterAction_connection_contDiff q).differentiable (by simp))
    |>.differentiableAt.hasFDerivAt

theorem actual_bivector_derivative (q : Configuration) :
    HasFDerivAt
      (fun bivector => masterAction (q.withBivector bivector))
      (deltaB q) q.bivector :=
  ((masterAction_bivector_contDiff q).differentiable (by simp))
    |>.differentiableAt.hasFDerivAt

theorem actual_multiplier_derivative (q : Configuration) :
    HasFDerivAt
      (fun multiplier => masterAction (q.withMultiplier multiplier))
      (deltaPhi q) q.multiplier := by
  have hinner :
      HasFDerivAt
        (fun multiplier : BivectorVector =>
          ⟪multiplier,
            q.bivector - physicalIIPlusMap q.tetrad⟫)
        (innerSL ℝ (q.bivector - physicalIIPlusMap q.tetrad))
        q.multiplier := by
    simpa only [coe_innerSL_apply, real_inner_comm] using
      (innerSL ℝ (q.bivector - physicalIIPlusMap q.tetrad)).hasFDerivAt
        (x := q.multiplier)
  simpa [masterAction, Configuration.withMultiplier, deltaPhi,
    add_assoc] using
      hinner.add_const
        (⟪q.bivector,
            spacetimeHodgeVector (nonAbelianCurvature q.connection)⟫ -
          (1 / 2 : ℝ) * ‖q.bivector‖ ^ 2)

theorem actual_tetrad_derivative (q : Configuration) :
    HasFDerivAt
      (fun tetrad => masterAction (q.withTetrad tetrad))
      (deltaE q) q.tetrad :=
  ((masterAction_tetrad_contDiff q).differentiable (by simp))
    |>.differentiableAt.hasFDerivAt

theorem deltaPhi_eq_zero_iff_physicalIIPlus (q : Configuration) :
    deltaPhi q = 0 ↔ q.bivector = physicalIIPlusMap q.tetrad := by
  constructor
  · intro hzero
    have hdefect : q.bivector - physicalIIPlusMap q.tetrad = 0 := by
      exact (innerSL_inj (𝕜 := ℝ) (E := BivectorVector)).mp (by
        simpa [deltaPhi] using hzero)
    exact sub_eq_zero.mp hdefect
  · intro heq
    simp [deltaPhi, heq]

theorem all_four_variations_from_one_action (q : Configuration) :
    HasFDerivAt
        (fun connection => masterAction (q.withConnection connection))
        (deltaOmega q) q.connection ∧
      HasFDerivAt
        (fun bivector => masterAction (q.withBivector bivector))
        (deltaB q) q.bivector ∧
      HasFDerivAt
        (fun multiplier => masterAction (q.withMultiplier multiplier))
        (deltaPhi q) q.multiplier ∧
      HasFDerivAt
        (fun tetrad => masterAction (q.withTetrad tetrad))
        (deltaE q) q.tetrad :=
  ⟨actual_connection_derivative q, actual_bivector_derivative q,
    actual_multiplier_derivative q, actual_tetrad_derivative q⟩

end
end SaturationMonoid.PhysicsCore.JetLocalPhysicalPlebanskiAction
