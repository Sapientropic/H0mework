import H0mework.Physics.Lorentz.PointwiseLorentzSpinConnectionRecovery
import H0mework.Physics.Geometry.RawSectionGluing

/-!
# Physical pointwise Lorentz omega gluing generated from a coframe jet

The generic section interface does not itself produce a Lorentz connection.
This module supplies the missing positive example on a concrete pointwise
geometry slice.  A raw coframe first jet computes its spin connection
`omega`; two chart restrictions are the same computed connection, overlap
maps are literal identity maps, glue is evaluation at the first chart, and
the transition is zero.

All four raw section laws are then theorems.  On the nondegenerate-coframe
slice the local sections additionally satisfy the tetrad postulate and the
`so(1,3)` skew law.  No compatibility proposition, descent certificate, or
reported connection is stored in the input.

Boundary: the construction is constant across a two-chart pointwise cover.
It is a physical Lorentz-connection gluing producer, but not yet a smooth
connection field, nonconstant chart transformation, curvature theorem, or
principal-bundle descent result.
-/

namespace SaturationMonoid
namespace PhysicsCore

noncomputable section

abbrev PointwiseLorentzOmegaCover :=
  SectionIndexedCover Bool PointwiseLorentzSpinConnection
    (fun _ => PointwiseLorentzSpinConnection)
    (fun _ _ => PointwiseLorentzSpinConnection)

abbrev PointwiseLorentzOmegaGluingSystem :=
  RawSectionTransitionInstance Bool PointwiseLorentzSpinConnection
    PointwiseLorentzSpinConnection PointwiseLorentzSpinConnection
    PointwiseLorentzSpinConnection

/-- Identity restrictions and overlaps for the computed pointwise Lorentz
connection. -/
def pointwiseLorentzOmegaCover : PointwiseLorentzOmegaCover where
  toLocal := fun _ global => global
  leftToOverlap := fun _ _ sectionValue => sectionValue
  rightToOverlap := fun _ _ sectionValue => sectionValue
  glue := fun localSections => localSections false

namespace PointwiseLorentzianCoframeJet

/-- Raw two-chart system generated from the spin connection of the coframe
jet.  The zero transition is data, not a supplied flatness certificate. -/
def pointwiseLorentzOmegaGluing
    (J : PointwiseLorentzianCoframeJet) :
    PointwiseLorentzOmegaGluingSystem where
  cover := pointwiseLorentzOmegaCover
  localFamily := fun _ => J.lorentzSpinConnection
  transition := fun _ _ => 0

theorem omegaGluing_overlapCompatible
    (J : PointwiseLorentzianCoframeJet) :
    J.pointwiseLorentzOmegaGluing.CurrentOverlapCompatible := by
  intro left right
  rfl

theorem omegaGluing_glueCorrect
    (J : PointwiseLorentzianCoframeJet) :
    J.pointwiseLorentzOmegaGluing.CurrentGlueCorrect := by
  intro index
  rfl

theorem omegaGluing_glueUnique
    (J : PointwiseLorentzianCoframeJet) :
    J.pointwiseLorentzOmegaGluing.CurrentGlueUnique := by
  intro global hrestricts
  have hfalse := hrestricts false
  simpa [pointwiseLorentzOmegaGluing, pointwiseLorentzOmegaCover]
    using hfalse

theorem omegaGluing_transitionFlat
    (J : PointwiseLorentzianCoframeJet) :
    J.pointwiseLorentzOmegaGluing.TransitionFlat := by
  intro left middle right
  simp [pointwiseLorentzOmegaGluing]

/-- The computed physical omega system satisfies all four raw gluing laws. -/
theorem omegaGluing_admissible
    (J : PointwiseLorentzianCoframeJet) :
    J.pointwiseLorentzOmegaGluing.SectionTransitionAdmissible :=
  ⟨J.omegaGluing_overlapCompatible,
    J.omegaGluing_glueCorrect,
    J.omegaGluing_glueUnique,
    J.omegaGluing_transitionFlat⟩

@[simp] theorem omegaGluing_globalSection
    (J : PointwiseLorentzianCoframeJet) :
    J.pointwiseLorentzOmegaGluing.cover.glue
        J.pointwiseLorentzOmegaGluing.localFamily =
      J.lorentzSpinConnection :=
  rfl

@[simp] theorem omegaGluing_localSection
    (J : PointwiseLorentzianCoframeJet) (index : Bool) :
    J.pointwiseLorentzOmegaGluing.localFamily index =
      J.lorentzSpinConnection :=
  rfl

/-- Every generated local section is the Lorentz-skew connection computed
from the same nondegenerate coframe jet. -/
theorem omegaGluing_local_lorentzSkew
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    ∀ index,
      LorentzSkew (J.pointwiseLorentzOmegaGluing.localFamily index) := by
  intro index
  exact J.lorentzSpinConnection_lorentzSkew hcoframe

/-- Every generated local section satisfies the tetrad postulate with the
same computed Levi-Civita connection. -/
theorem omegaGluing_local_tetradCompatible
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    ∀ index,
      TetradCompatible J J.leviCivitaConnection
        (J.pointwiseLorentzOmegaGluing.localFamily index) := by
  intro index
  exact J.leviCivita_lorentzSpinConnection_tetradCompatible hcoframe

/-- Certified output of the physical pointwise omega gluing producer. -/
structure LorentzOmegaGluingOutput
    (J : PointwiseLorentzianCoframeJet) where
  system : PointwiseLorentzOmegaGluingSystem
  system_eq : system = J.pointwiseLorentzOmegaGluing
  sectionAdmissible : system.SectionTransitionAdmissible
  localLorentzSkew : ∀ index, LorentzSkew (system.localFamily index)
  localTetradCompatible :
    ∀ index,
      TetradCompatible J J.leviCivitaConnection
        (system.localFamily index)

/-- A nondegenerate coframe jet produces a certified physical Lorentz omega
gluing system. -/
def produceLorentzOmegaGluing
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    LorentzOmegaGluingOutput J where
  system := J.pointwiseLorentzOmegaGluing
  system_eq := rfl
  sectionAdmissible := J.omegaGluing_admissible
  localLorentzSkew := J.omegaGluing_local_lorentzSkew hcoframe
  localTetradCompatible :=
    J.omegaGluing_local_tetradCompatible hcoframe

end PointwiseLorentzianCoframeJet

end
end PhysicsCore
end SaturationMonoid
