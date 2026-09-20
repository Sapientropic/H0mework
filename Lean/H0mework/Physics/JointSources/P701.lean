import H0mework.Physics.JointSources.P664
import H0mework.Physics.JointSources.P679
import H0mework.Computation.SelfReduction.P700

/-!
# Proposition 701: the Energy = Information = Mathematics = Physics diagonal

P662/P664/P678/P679 already proved the four grand-unification faces as
source-law projections, and P700 proved the phase-flow energy threshold-collapse
gate.  This file adds the missing diagonal statement.

The point is deliberately not to assert a literal type equality between
heterogeneous objects such as a Hilbert-energy guardrail, an information slot,
a sigma-zero mathematics spine, and a finite physics output.  The precise Lean
statement is stronger and cleaner: when any one of the four words is used as a
finite source-law readout, its admissible surface is exactly the same singleton
canonical output.  Therefore a valid reading on any face automatically lies on
the intersection of all four faces.

In slogan form:

* not four separately tuned tracks;
* one source-law finite readout;
* four projections;
* a singleton diagonal.

Boundary: this is the current finite/source-law diagonal theorem.  It does not
derive the smooth Standard-Model continuum, prove the final Euler/RH adapter
range, prove Goldbach/RH, prove `P = NP`, or prove that an arbitrary runtime
implements the P700 threshold policy.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open StandardModelConstraint
open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-! ## The four finite-readout faces -/

/-- The four words of the diagonal, used only as readout labels over the same
source-law finite output surface. -/
inductive EnergyInformationMathematicsPhysicsFace where
  | energy
  | information
  | mathematics
  | physics
  deriving DecidableEq, Repr

/-- The common finite readout surface of a face.

Each branch intentionally points to the same P679 source-law output surface:
the diagonal theorem below proves that the four labels have no independent
finite parameter freedom. -/
def EnergyInformationMathematicsPhysicsFaceSurface
    (face : EnergyInformationMathematicsPhysicsFace)
    (O : SourceLawFinitePhysicalOutput) : Prop :=
  match face with
  | .energy => SourceLawFinitePhysicalOutputSurface O
  | .information => SourceLawFinitePhysicalOutputSurface O
  | .mathematics => SourceLawFinitePhysicalOutputSurface O
  | .physics => SourceLawFinitePhysicalOutputSurface O

/-- The actual diagonal: a finite output lies simultaneously on all four
readout faces. -/
def EnergyInformationMathematicsPhysicsDiagonalSurface
    (O : SourceLawFinitePhysicalOutput) : Prop :=
  ∀ face : EnergyInformationMathematicsPhysicsFace,
    EnergyInformationMathematicsPhysicsFaceSurface face O

/-! ## Singleton diagonal theorems -/

/-- THEOREM 1: every face surface is exactly the canonical source-law finite
output. -/
theorem energyInformationMathematicsPhysicsFaceSurface_iff_canonical
    (face : EnergyInformationMathematicsPhysicsFace)
    (O : SourceLawFinitePhysicalOutput) :
    EnergyInformationMathematicsPhysicsFaceSurface face O ↔
      O = canonicalSourceLawFinitePhysicalOutput := by
  cases face <;>
    exact sourceLawFinitePhysicalOutputSurface_iff_canonical O

/-- THEOREM 2: the canonical finite output lies on every face. -/
theorem canonicalSourceLawFinitePhysicalOutput_on_face
    (face : EnergyInformationMathematicsPhysicsFace) :
    EnergyInformationMathematicsPhysicsFaceSurface face
      canonicalSourceLawFinitePhysicalOutput := by
  exact
    (energyInformationMathematicsPhysicsFaceSurface_iff_canonical
      face canonicalSourceLawFinitePhysicalOutput).2 rfl

/-- THEOREM 3: the diagonal intersection is exactly the canonical finite
source-law output. -/
theorem energyInformationMathematicsPhysicsDiagonalSurface_iff_canonical
    (O : SourceLawFinitePhysicalOutput) :
    EnergyInformationMathematicsPhysicsDiagonalSurface O ↔
      O = canonicalSourceLawFinitePhysicalOutput := by
  constructor
  · intro hO
    exact
      (energyInformationMathematicsPhysicsFaceSurface_iff_canonical
        .physics O).1 (hO .physics)
  · intro hO face
    rw [hO]
    exact canonicalSourceLawFinitePhysicalOutput_on_face face

/-- THEOREM 4: a valid readout on any one face automatically lies on the full
four-face diagonal. -/
theorem faceSurface_to_energyInformationMathematicsPhysicsDiagonal
    (face : EnergyInformationMathematicsPhysicsFace)
    (O : SourceLawFinitePhysicalOutput)
    (hO : EnergyInformationMathematicsPhysicsFaceSurface face O) :
    EnergyInformationMathematicsPhysicsDiagonalSurface O := by
  have hcanonical :
      O = canonicalSourceLawFinitePhysicalOutput :=
    (energyInformationMathematicsPhysicsFaceSurface_iff_canonical face O).1 hO
  exact
    (energyInformationMathematicsPhysicsDiagonalSurface_iff_canonical O).2
      hcanonical

/-- THEOREM 5: any two valid face readouts are the same finite output. -/
theorem energyInformationMathematicsPhysicsFaceOutputs_eq
    (face₁ face₂ : EnergyInformationMathematicsPhysicsFace)
    (O₁ O₂ : SourceLawFinitePhysicalOutput)
    (h₁ : EnergyInformationMathematicsPhysicsFaceSurface face₁ O₁)
    (h₂ : EnergyInformationMathematicsPhysicsFaceSurface face₂ O₂) :
    O₁ = O₂ := by
  have hO₁ :
      O₁ = canonicalSourceLawFinitePhysicalOutput :=
    (energyInformationMathematicsPhysicsFaceSurface_iff_canonical
      face₁ O₁).1 h₁
  have hO₂ :
      O₂ = canonicalSourceLawFinitePhysicalOutput :=
    (energyInformationMathematicsPhysicsFaceSurface_iff_canonical
      face₂ O₂).1 h₂
  rw [hO₁, hO₂]

/-! ## Packaged diagonal root -/

/-- P701 certificate: the central four-face projection, the finite source-law
no-free theorem, and the P700 phase-energy collapse surface are one diagonal
root. -/
structure EnergyInformationMathematicsPhysicsDiagonalCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  refined_central_root :
    RefinedInformationMathMatterEnergyUnifiedRootCertificate E
  source_law_no_free_root :
    SourceLawNoFreeUnifiedRootCertificate E
  phase_threshold_collapse_root :
    PhaseFlowThresholdCollapseUnifiedRootCertificate.{u, v, w, z} E
  face_surface_iff_canonical :
    ∀ (face : EnergyInformationMathematicsPhysicsFace)
      (O : SourceLawFinitePhysicalOutput),
      EnergyInformationMathematicsPhysicsFaceSurface face O ↔
        O = canonicalSourceLawFinitePhysicalOutput
  canonical_on_every_face :
    ∀ face : EnergyInformationMathematicsPhysicsFace,
      EnergyInformationMathematicsPhysicsFaceSurface face
        canonicalSourceLawFinitePhysicalOutput
  diagonal_surface_iff_canonical :
    ∀ O : SourceLawFinitePhysicalOutput,
      EnergyInformationMathematicsPhysicsDiagonalSurface O ↔
        O = canonicalSourceLawFinitePhysicalOutput
  any_face_to_diagonal :
    ∀ (face : EnergyInformationMathematicsPhysicsFace)
      (O : SourceLawFinitePhysicalOutput),
      EnergyInformationMathematicsPhysicsFaceSurface face O ->
        EnergyInformationMathematicsPhysicsDiagonalSurface O
  any_two_face_outputs_eq :
    ∀ (face₁ face₂ : EnergyInformationMathematicsPhysicsFace)
      (O₁ O₂ : SourceLawFinitePhysicalOutput),
      EnergyInformationMathematicsPhysicsFaceSurface face₁ O₁ ->
        EnergyInformationMathematicsPhysicsFaceSurface face₂ O₂ ->
          O₁ = O₂

/-- THEOREM 6: the current Energy = Information = Mathematics = Physics
diagonal root is inhabited. -/
def energyInformationMathematicsPhysicsDiagonalCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    EnergyInformationMathematicsPhysicsDiagonalCertificate.{u, v, w, z} E where
  refined_central_root :=
    refinedInformationMathMatterEnergyUnifiedRootCertificate (E := E)
  source_law_no_free_root :=
    sourceLawNoFreeUnifiedRootCertificate (E := E)
  phase_threshold_collapse_root :=
    phaseFlowThresholdCollapseUnifiedRootCertificate (E0 := E)
  face_surface_iff_canonical :=
    energyInformationMathematicsPhysicsFaceSurface_iff_canonical
  canonical_on_every_face :=
    canonicalSourceLawFinitePhysicalOutput_on_face
  diagonal_surface_iff_canonical :=
    energyInformationMathematicsPhysicsDiagonalSurface_iff_canonical
  any_face_to_diagonal :=
    faceSurface_to_energyInformationMathematicsPhysicsDiagonal
  any_two_face_outputs_eq :=
    energyInformationMathematicsPhysicsFaceOutputs_eq

end GrandUnification
end SaturationMonoid
