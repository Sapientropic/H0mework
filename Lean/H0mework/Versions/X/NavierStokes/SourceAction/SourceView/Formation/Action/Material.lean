import H0mework.Versions.X.NavierStokes.WindowPhysics.WindowJets
import H0mework.Physics.MotherLaws.RestrictionConsumer

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeWindowMotherActionMaterial

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressAction
open PhysicsCore.Stage10.SourceUniqueness MotherStreamLaws

noncomputable section

abbrev Row := (NonzeroIntegerWavevector × Coordinate) ⊕
  (IntegerWavevector × (Coordinate × Coordinate))

def coefficient (value : FullSpace) : Row → ℂ
  | .inl (wave, coordinate) => value.fst wave coordinate
  | .inr (wave, pair) => value.snd wave pair

theorem coefficient_injective : Function.Injective coefficient := by
  intro first last same
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · apply lp.ext
    funext wave
    apply PiLp.ext
    intro coordinate
    exact congrFun same (.inl (wave, coordinate))
  · apply lp.ext
    funext wave
    apply PiLp.ext
    intro pair
    exact congrFun same (.inr (wave, pair))

local instance rowCode : Encodable (Row × Bool) := Encodable.ofCountable _

def samples (value : FullSpace) : Stream := fun address =>
  match Encodable.decode (α := Row × Bool) address with
  | none => 0
  | some (row, imaginary) => if imaginary then (coefficient value row).im else (coefficient value row).re

theorem samples_real (value : FullSpace) (row : Row) :
    samples value (Encodable.encode (row, false)) = (coefficient value row).re := by
  simp only [samples, Encodable.encodek, Bool.false_eq_true, ↓reduceIte]

theorem samples_imaginary (value : FullSpace) (row : Row) :
    samples value (Encodable.encode (row, true)) = (coefficient value row).im := by
  simp only [samples, Encodable.encodek, ↓reduceIte]

theorem samples_injective : Function.Injective samples := by
  intro first last same
  apply coefficient_injective
  funext row
  apply Complex.ext
  · exact (samples_real first row).symm.trans
      ((congrFun same (Encodable.encode (row, false))).trans (samples_real last row))
  · exact (samples_imaginary first row).symm.trans
      ((congrFun same (Encodable.encode (row, true))).trans (samples_imaginary last row))

def restore : Stream → FullSpace := Function.invFun samples

theorem restore_samples (value : FullSpace) : restore (samples value) = value :=
  Function.leftInverse_invFun samples_injective value

def actionSamples (value : WholeRestartVelocityEndpointState) : Stream :=
  samples (WithLp.toLp 2 (value, (0 : NativeCompleteStressCarrier.Space)))

def restoreAction (value : Stream) : WholeRestartVelocityEndpointState := (restore value).fst

theorem restore_actionSamples (value : WholeRestartVelocityEndpointState) :
    restoreAction (actionSamples value) = value := by
  rw [restoreAction, actionSamples, restore_samples]
  rfl

end
end SaturationMonoid.NavierStokes.NativeWindowMotherActionMaterial
