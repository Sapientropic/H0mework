import H0mework.Versions.Y.Arithmetic.EulerDualBlock.GlobalComplexSpecialization
import H0mework.Versions.Y.Arithmetic.RiemannInverseFibre.GeneratedZeroRead

/-!
# Lawful determinant-line incidences over a generated zero read

The existing determinant-line zero fibre is not rebuilt.  This module only
records which installed chart exhibits the observed zero.  Both chart
constructors remain visible and reversal exchanges them.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization

noncomputable section

inductive LawfulPointZeroIncidence : Type 5
  | left (point : DeterminantLinePoint)
      (zero : generatedRiemannZeta ActualAnalyticOwner point.pair.1 = 0)
  | right (point : DeterminantLinePoint)
      (zero : generatedRiemannZeta ActualAnalyticOwner point.pair.2 = 0)

namespace LawfulPointZeroIncidence

def point : LawfulPointZeroIncidence → DeterminantLinePoint
  | .left point _ => point
  | .right point _ => point

def observation : LawfulPointZeroIncidence →
    GeneratedRiemannZeroObservation
  | .left point zero => .observe point.pair.1 zero
  | .right point zero => .observe point.pair.2 zero

def reversal : LawfulPointZeroIncidence → LawfulPointZeroIncidence
  | .left point zero => .right point.reversal zero
  | .right point zero => .left point.reversal zero

@[simp] theorem reversal_point (incidence : LawfulPointZeroIncidence) :
    incidence.reversal.point = incidence.point.reversal := by
  cases incidence <;> rfl

@[simp] theorem reversal_observation
    (incidence : LawfulPointZeroIncidence) :
    incidence.reversal.observation = incidence.observation := by
  cases incidence <;>
    apply GeneratedRiemannZeroObservation.ext <;> rfl

@[simp] theorem reversal_reversal
    (incidence : LawfulPointZeroIncidence) :
    incidence.reversal.reversal = incidence := by
  cases incidence with
  | left point zero =>
      cases point with
      | mk pair sectionZero =>
          cases pair
          rfl
  | right point zero =>
      cases point with
      | mk pair sectionZero =>
          cases pair
          rfl

end LawfulPointZeroIncidence

/-- Complete conditional preimage, not a chosen actual representative. -/
abbrev InverseZeroFibre (observation : GeneratedRiemannZeroObservation) :=
  {incidence : LawfulPointZeroIncidence //
    incidence.observation = observation}

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
