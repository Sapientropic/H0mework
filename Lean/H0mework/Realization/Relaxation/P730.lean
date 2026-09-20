import H0mework.Realization.Relaxation.P729

/-!
# Proposition 730: four relaxation-preserving faces force one common core

P729 classifies all relaxation-preserving observers as affine-linear.  P727
proves that linear projected face families automatically produce one common
residual core.

This file composes those two facts on the four-word spine

`information / energy / matter / mathematics`.

The result is not a singleton diagonal restatement.  It says that if four
face observers all respect the same target-general relaxation operation, then
their centered readouts are forced to be linear projections into one common
core.  Consequently all four faces inherit the same residual normal form,
same noisy-OR composition on the core, same cross-face synchronization law,
and the same scalar energy scaling law.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-- The four structural faces used by the common-core unification theorem. -/
inductive UnifiedProjectionFace where
  | information
  | energy
  | matter
  | mathematics
  deriving DecidableEq, Repr

variable {E : Type u} {Core : Type v} {Face : Type w}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup Core] [Module ℝ Core]

/-! ## Zero-based commuting observer families -/

/-- A face observer family whose observers already send zero to zero and
commute with every relaxation operation. -/
structure ZeroBasedRelaxCommutingFaceObserverFamily
    (E : Type u) (Core : Type v) (Face : Type w)
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup Core] [Module ℝ Core] where
  target : Core
  faceTarget : Face -> E
  observe : Face -> E -> Core
  zero : ∀ face : Face, observe face 0 = 0
  commutes : ∀ face : Face, CommutesWithRealRelaxModule (observe face)
  target_commutes :
    ∀ face : Face, observe face (faceTarget face) = target

/-- THEOREM 1: zero-based relaxation-commuting face observers reconstruct a
linear projected face family. -/
def ZeroBasedRelaxCommutingFaceObserverFamily.toLinearProjectedFaceFamily
    (F : ZeroBasedRelaxCommutingFaceObserverFamily E Core Face) :
    LinearProjectedFaceFamily ℝ E Core Face where
  target := F.target
  faceTarget := F.faceTarget
  toCore := fun face =>
    linearMapOfRelaxCommutingZero
      (F.observe face) (F.commutes face) (F.zero face)
  target_commutes := by
    intro face
    exact F.target_commutes face

/-- THEOREM 2: zero-based relaxation-commuting observers force the P727 common
residual core certificate. -/
theorem zeroBasedRelaxCommutingObservers_force_commonResidualCore
    (F : ZeroBasedRelaxCommutingFaceObserverFamily E Core Face) :
    LinearProjectedFaceFamilyCertificate
      F.toLinearProjectedFaceFamily :=
  linearProjectedFaceFamilyCertificate F.toLinearProjectedFaceFamily

/-- THEOREM 3: on a scalar common core, zero-based commuting observers force
the common scalar residual-energy certificate. -/
theorem zeroBasedRelaxCommutingObservers_force_commonScalarEnergy
    (F : ZeroBasedRelaxCommutingFaceObserverFamily E ℝ Face) :
    LinearProjectedFaceFamilyScalarEnergyCertificate
      F.toLinearProjectedFaceFamily :=
  linearProjectedFaceFamilyScalarEnergyCertificate
    F.toLinearProjectedFaceFamily

/-! ## General affine observer families via canonical centering -/

/-- A general face observer family.  The observers may have affine base
offsets; the target condition is therefore stated on their canonical centered
readouts. -/
structure RelaxCommutingFaceObserverFamily
    (E : Type u) (Core : Type v) (Face : Type w)
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup Core] [Module ℝ Core] where
  target : Core
  faceTarget : Face -> E
  observe : Face -> E -> Core
  commutes : ∀ face : Face, CommutesWithRealRelaxModule (observe face)
  centered_target_commutes :
    ∀ face : Face,
      centeredRelaxObserver (observe face) (faceTarget face) = target

/-- THEOREM 4: every relaxation-commuting face observer family canonically
centers to a zero-based family. -/
def RelaxCommutingFaceObserverFamily.toZeroBasedFamily
    (F : RelaxCommutingFaceObserverFamily E Core Face) :
    ZeroBasedRelaxCommutingFaceObserverFamily E Core Face where
  target := F.target
  faceTarget := F.faceTarget
  observe := fun face => centeredRelaxObserver (F.observe face)
  zero := fun face => centeredRelaxObserver_zero (F.observe face)
  commutes := fun face => centeredRelaxObserver_commutes
    (F.observe face) (F.commutes face)
  target_commutes := F.centered_target_commutes

/-- THEOREM 5: every relaxation-commuting face observer family forces a common
residual core after canonical centering. -/
theorem relaxCommutingObservers_force_commonResidualCore
    (F : RelaxCommutingFaceObserverFamily E Core Face) :
    LinearProjectedFaceFamilyCertificate
      F.toZeroBasedFamily.toLinearProjectedFaceFamily :=
  zeroBasedRelaxCommutingObservers_force_commonResidualCore
    F.toZeroBasedFamily

/-- THEOREM 6: on a scalar common core, every relaxation-commuting observer
family forces common scalar residual-energy scaling after canonical centering.
-/
theorem relaxCommutingObservers_force_commonScalarEnergy
    (F : RelaxCommutingFaceObserverFamily E ℝ Face) :
    LinearProjectedFaceFamilyScalarEnergyCertificate
      F.toZeroBasedFamily.toLinearProjectedFaceFamily :=
  zeroBasedRelaxCommutingObservers_force_commonScalarEnergy
    F.toZeroBasedFamily

/-! ## The four-face specialization -/

/-- THEOREM 7: the information / energy / matter / mathematics faces, once
they respect relaxation, are forced into one common residual core. -/
theorem fourFace_relaxCommutingObservers_force_commonResidualCore
    (F : RelaxCommutingFaceObserverFamily E Core UnifiedProjectionFace) :
    LinearProjectedFaceFamilyCertificate
      F.toZeroBasedFamily.toLinearProjectedFaceFamily :=
  relaxCommutingObservers_force_commonResidualCore F

/-- THEOREM 8: the four-face scalar core inherits the same residual-energy
scaling law. -/
theorem fourFace_relaxCommutingObservers_force_commonScalarEnergy
    (F : RelaxCommutingFaceObserverFamily E ℝ UnifiedProjectionFace) :
    LinearProjectedFaceFamilyScalarEnergyCertificate
      F.toZeroBasedFamily.toLinearProjectedFaceFamily :=
  relaxCommutingObservers_force_commonScalarEnergy F

/-! ## Certificate -/

/-- P730 certificate: relaxation-preserving face observers over the four-word
spine are forced into one common residual core by P729 + P727. -/
structure FourFaceRelaxationCommonCoreCertificate
    (E : Type u) (Core : Type v)
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup Core] [Module ℝ Core] : Prop where
  zero_based_to_linear_projected :
    ∀ F : ZeroBasedRelaxCommutingFaceObserverFamily E Core UnifiedProjectionFace,
      LinearProjectedFaceFamilyCertificate
        F.toLinearProjectedFaceFamily
  affine_centered_to_common_core :
    ∀ F : RelaxCommutingFaceObserverFamily E Core UnifiedProjectionFace,
      LinearProjectedFaceFamilyCertificate
        F.toZeroBasedFamily.toLinearProjectedFaceFamily
  hom_iff_affine :
    ∀ g : E -> Core, CommutesWithRealRelaxModule g ↔ IsAffineRealMap g

/-- THEOREM 9: every real module carrier pair supplies the four-face common
core certificate. -/
theorem fourFaceRelaxationCommonCoreCertificate :
    FourFaceRelaxationCommonCoreCertificate E Core where
  zero_based_to_linear_projected :=
    zeroBasedRelaxCommutingObservers_force_commonResidualCore
  affine_centered_to_common_core :=
    fourFace_relaxCommutingObservers_force_commonResidualCore
  hom_iff_affine :=
    commutesWithRelaxModule_iff_affineRealMap

/-- P730 scalar certificate: the four-face common core has the forced scalar
energy law whenever the common core is `ℝ`. -/
structure FourFaceRelaxationCommonScalarEnergyCertificate
    (E : Type u)
    [AddCommGroup E] [Module ℝ E] : Prop where
  common_core :
    FourFaceRelaxationCommonCoreCertificate E ℝ
  affine_centered_to_scalar_energy :
    ∀ F : RelaxCommutingFaceObserverFamily E ℝ UnifiedProjectionFace,
      LinearProjectedFaceFamilyScalarEnergyCertificate
        F.toZeroBasedFamily.toLinearProjectedFaceFamily

/-- THEOREM 10: every real module carrier supplies the four-face scalar-energy
certificate. -/
theorem fourFaceRelaxationCommonScalarEnergyCertificate :
    FourFaceRelaxationCommonScalarEnergyCertificate E where
  common_core := fourFaceRelaxationCommonCoreCertificate
  affine_centered_to_scalar_energy :=
    fourFace_relaxCommutingObservers_force_commonScalarEnergy

end AffineRelaxation
end SaturationMonoid
