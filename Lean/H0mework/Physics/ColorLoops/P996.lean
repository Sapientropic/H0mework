import H0mework.Physics.BranchSources.P993

/-!
# Proposition 996: P993 physical residual gives zero color-holonomy observable

This is the next bridge after P993.  It does not project to endpoint codes,
prime edges, raw-code shells, or arithmetic.  It only says that the full-orbit
incidence-normalizer zero residual, when read as a physical terminal cell,
also has no permanent color-holonomy observable.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-- Physical zero color-holonomy observable: there exists a physical terminal
branch cell whose residual readout is zero and whose permanent color holonomy
readout is false. -/
def ZeroColorHolonomyObservable (n : ℕ) : Prop :=
  ∃ cell : SU7TerminalPhysicalBranchCell n,
    terminalPhysicalResidual cell = 0 ∧
      ¬ terminalPhysicalPermanentColorHolonomy cell

/-- A generated zero-residual cell projects to a physical zero color-holonomy
observable. -/
theorem zeroColorHolonomyObservable_of_generated_zero
    {n : ℕ} {cell : SU7GeneratedTerminalColorCell n}
    (hzero : generatedTerminalColorResidual cell = 0) :
    ZeroColorHolonomyObservable n := by
  refine
    ⟨terminalPhysicalCellOfGeneratedColorCell cell, ?_, ?_⟩
  · simp [hzero]
  · intro hhol
    exact hhol hzero

/-- P996 main bridge: the P993 full-orbit incidence-normalizer producer gives
a physical terminal cell with zero residual and no permanent color holonomy. -/
theorem zeroColorHolonomyObservable_of_fullOrbitIncidenceNormalizer
    (n : ℕ) :
    ZeroColorHolonomyObservable n := by
  rcases zeroGeneratedColorResidual_of_fullOrbitIncidenceNormalizer n with
    ⟨cell, _hmem, hzero⟩
  exact zeroColorHolonomyObservable_of_generated_zero hzero

/-- The P996 observable still projects to the P993 physical residual theorem.
-/
theorem zeroTerminalPhysicalResidual_of_zeroColorHolonomyObservable
    {n : ℕ} (O : ZeroColorHolonomyObservable n) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      terminalPhysicalResidual cell = 0 :=
  by
    rcases O with ⟨cell, hzero, _hno⟩
    exact ⟨cell, hzero⟩

/-- P996 recovers the physical residual projection through the stronger
zero-holonomy observable, not through endpoint/raw-code adapters. -/
theorem zeroTerminalPhysicalResidual_via_zeroColorHolonomyObservable
    (n : ℕ) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      terminalPhysicalResidual cell = 0 :=
  zeroTerminalPhysicalResidual_of_zeroColorHolonomyObservable
    (zeroColorHolonomyObservable_of_fullOrbitIncidenceNormalizer n)


end
end StandardModelConstraint
end SaturationMonoid
