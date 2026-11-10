import H0mework.Arithmetic.SourceAtoms.CrystalBranchingSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.CompositeSourceSuccessorSteps

/-!
# Rank-one composite dynamics toy

This is a positive calibration for the source-dynamics side.

The source dynamics is the rank-one lowering string from
`CrystalBranchingSource`: source evidence is residual height, and lowering is
`k + 1 -> k`.  The endpoint-code formula is not a finite table.  It sends a
height through the parity-resolved composite source formula, so every endpoint
has an explicit non-prime multiplicative factorization certificate.

This deliberately does not target `NatMultiplicativelyAtomic`.  It proves that
the four structural fields can be produced by a genuine source dynamics for a
non-prime multiplicative family, while leaving the prime-like certificate
problem exposed.
-/

namespace RepresentationArithmeticAtomProjectionDefect
namespace CrystalBranchingSource
namespace RankOneCompositeDynamicsToy

open CompositeSourceFamily

/-- Rank-one height read into the parity-resolved composite endpoint formula.

The rank-one source evidence is a residual height.  The existing composite
source formula already knows how to produce a parity branch for every height,
so this is a source-code projection from the rank-one dynamics into endpoint
codes. -/
def rankOneCompositeEndpointCode (n height : Nat) :
    EndpointCodePair n :=
  sourceCode n (CompositeShellSource.sourceOfHeight height)

/-- Residual affine readout for the rank-one composite projection. -/
theorem rankOneCompositeEndpointCode_energy
    (n height : Nat) (hn : 6 ≤ n) :
    EndpointCodePair.energy (rankOneCompositeEndpointCode n height) =
      height := by
  dsimp [rankOneCompositeEndpointCode]
  rw [sourceCode_energy n _ hn]
  exact CompositeShellSource.sourceOfHeight_energy height

/-- Left endpoint certificates are transported by the composite formula. -/
theorem rankOneCompositeEndpointCode_left_atomic
    (n height : Nat) :
    CompositeAtom (rankOneCompositeEndpointCode n height).leftCode := by
  dsimp [rankOneCompositeEndpointCode]
  exact sourceCode_left_atomic n
    (CompositeShellSource.sourceOfHeight height)

/-- Right endpoint certificates are transported by the composite formula. -/
theorem rankOneCompositeEndpointCode_right_atomic
    (n height : Nat) (hn : 6 ≤ n) :
    CompositeAtom (rankOneCompositeEndpointCode n height).rightCode := by
  dsimp [rankOneCompositeEndpointCode]
  exact sourceCode_right_atomic n
    (CompositeShellSource.sourceOfHeight height) hn

/-- Certified code projection from rank-one source heights to composite
endpoint codes. -/
def rankOneCompositeCodeProjection
    (n : Nat) (hn : 6 ≤ n) :
    AtomicEndpointCodeProjection
      CompositeAtom Nat n rankOneResidualTransport where
  codeProjection := {
    projectCode := fun height =>
      some (rankOneCompositeEndpointCode n height)
    code_energy_faithful := by
      intro height code hproject
      cases hproject
      exact rankOneCompositeEndpointCode_energy n height hn
  }
  left_atomic := by
    intro height code hproject
    cases hproject
    exact rankOneCompositeEndpointCode_left_atomic n height
  right_atomic := by
    intro height code hproject
    cases hproject
    exact rankOneCompositeEndpointCode_right_atomic n height hn

/-- The rank-one source dynamics instantiated with a total composite
source-code projection.

Projection definedness lifts along every path because the projection is a
closed source formula.  Terminal absorption is impossible for the same reason:
terminal code silence contradicts total projection definedness. -/
def rankOneCompositeCodeProjectionCandidate
    (n : Nat) (hn : 6 ≤ n) :
    RankOneCrystalCodeProjectionCandidate CompositeAtom n where
  code_projection := rankOneCompositeCodeProjection n hn
  code_defined_lifts_along_path := by
    intro _source _target _hPath _hDefined
    dsimp [rankOneCompositeCodeProjection]
    simp
  absorbed_static := False
  headroom_nonzero := True
  headroom_witness := trivial
  nonzero_forbids_absorbed_static := by
    intro _ hAbsorbed
    exact hAbsorbed
  terminal_code_projection_undefined_absorbs := by
    intro _k demand hNone
    dsimp [rankOneCompositeCodeProjection] at hNone
    simp at hNone

/-- Positive extraction target: the rank-one composite dynamics produces an
atom-pair realization at every residual height. -/
theorem rankOneCompositeAtomPairRealizationOfHeight
    (n height : Nat) (hn : 6 ≤ n) :
    ∃ p : ArithmeticAtomPair CompositeAtom n,
      ArithmeticAtomPair.energy p = height := by
  exact
    atom_pair_realization_of_rank_one_height
      (n := n) (k := height)
      (rankOneCompositeCodeProjectionCandidate n hn)

/-- Factorized positive readout for the rank-one composite dynamics.

This is the construction paired with the affine atom-certificate no-go: the
source dynamics is allowed to produce explicit composite certificates, but it
does not pretend those certificates are prime-like Nat atoms. -/
theorem factorizedCompositeAtomPairRealizationOfRankOneDynamics
    (n height : Nat) (hn : 6 ≤ n) :
    FactorizedAtomPairRealization
      CompositeAtom compositeFactorizationCategory n height := by
  rcases rankOneCompositeAtomPairRealizationOfHeight n height hn with
    ⟨p, hEnergy⟩
  exact
    factorizedAtomPairRealizationOfPair
      compositeFactorizationCategory p hEnergy


end RankOneCompositeDynamicsToy
end CrystalBranchingSource
end RepresentationArithmeticAtomProjectionDefect
