import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Complex.Basic
import H0mework.Physics.Measurement.Units

/-!
# Dimensioned sinusoidal drive ports

A real two-quadrature phasor keeps the physical voltage/current dimension in
the Lean type.  Complex numbers are used only by the normalized signal
readout; the physical port itself cannot exchange volts and amperes.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Netlist
namespace Dissipative
namespace Dimensioned
namespace Driven
namespace Interface

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

@[ext] structure SIVoltagePhasor where
  cosine : SIVolt
  sine : SIVolt

@[ext] structure SICurrentPhasor where
  cosine : SIAmpere
  sine : SIAmpere

instance : Zero SIVoltagePhasor where
  zero := ⟨0, 0⟩

instance : Add SIVoltagePhasor where
  add left right :=
    ⟨left.cosine + right.cosine, left.sine + right.sine⟩

instance : Sub SIVoltagePhasor where
  sub left right :=
    ⟨left.cosine - right.cosine, left.sine - right.sine⟩

instance : Neg SIVoltagePhasor where
  neg phasor := ⟨-phasor.cosine, -phasor.sine⟩

instance : SMul ℝ SIVoltagePhasor where
  smul scalar phasor :=
    ⟨scalar • phasor.cosine, scalar • phasor.sine⟩

@[simp] theorem voltagePhasor_add_cosine
    (left right : SIVoltagePhasor) :
    (left + right).cosine = left.cosine + right.cosine := rfl

@[simp] theorem voltagePhasor_add_sine
    (left right : SIVoltagePhasor) :
    (left + right).sine = left.sine + right.sine := rfl

@[simp] theorem voltagePhasor_smul_cosine
    (scalar : ℝ) (phasor : SIVoltagePhasor) :
    (scalar • phasor).cosine = scalar • phasor.cosine := rfl

@[simp] theorem voltagePhasor_smul_sine
    (scalar : ℝ) (phasor : SIVoltagePhasor) :
    (scalar • phasor).sine = scalar • phasor.sine := rfl

def zeroVoltagePhasor : SIVoltagePhasor :=
  0

def voltagePhasorOfNormalized
    (voltageScale : SIVolt) (signal : ℂ) : SIVoltagePhasor where
  cosine := signal.re • voltageScale
  sine := signal.im • voltageScale

def normalizeVoltagePhasor
    (voltageScale : SIVolt) (phasor : SIVoltagePhasor) : ℂ :=
  ⟨phasor.cosine.value / voltageScale.value,
    phasor.sine.value / voltageScale.value⟩

theorem normalizeVoltagePhasor_ofNormalized
    (voltageScale : SIVolt) (voltageScale_ne : voltageScale.value ≠ 0)
    (signal : ℂ) :
    normalizeVoltagePhasor voltageScale
        (voltagePhasorOfNormalized voltageScale signal) = signal := by
  apply Complex.ext
  · simp [normalizeVoltagePhasor, voltagePhasorOfNormalized, voltageScale_ne]
  · simp [normalizeVoltagePhasor, voltagePhasorOfNormalized, voltageScale_ne]

def voltagePhasorMagnitudeSq (phasor : SIVoltagePhasor) :
    SIQuantity (voltageDimension + voltageDimension) :=
  SIQuantity.square phasor.cosine + SIQuantity.square phasor.sine

def currentPhasorMagnitudeSq (phasor : SICurrentPhasor) :
    SIQuantity (currentDimension + currentDimension) :=
  SIQuantity.square phasor.cosine + SIQuantity.square phasor.sine

@[simp] theorem voltagePhasorMagnitudeSq_value (phasor : SIVoltagePhasor) :
    (voltagePhasorMagnitudeSq phasor).value =
      phasor.cosine.value ^ 2 + phasor.sine.value ^ 2 := by
  simp [voltagePhasorMagnitudeSq]

@[simp] theorem currentPhasorMagnitudeSq_value (phasor : SICurrentPhasor) :
    (currentPhasorMagnitudeSq phasor).value =
      phasor.cosine.value ^ 2 + phasor.sine.value ^ 2 := by
  simp [currentPhasorMagnitudeSq]

def voltageWaveformAt
    (frequency : SIHertz) (phasor : SIVoltagePhasor)
    (physicalTime : SISecond) : SIVolt :=
  Real.cos (frequency.value * physicalTime.value) • phasor.cosine +
    Real.sin (frequency.value * physicalTime.value) • phasor.sine

def currentWaveformAt
    (frequency : SIHertz) (phasor : SICurrentPhasor)
    (physicalTime : SISecond) : SIAmpere :=
  Real.cos (frequency.value * physicalTime.value) • phasor.cosine +
    Real.sin (frequency.value * physicalTime.value) • phasor.sine

@[simp] theorem voltageWaveformAt_value
    (frequency : SIHertz) (phasor : SIVoltagePhasor)
    (physicalTime : SISecond) :
    (voltageWaveformAt frequency phasor physicalTime).value =
      Real.cos (frequency.value * physicalTime.value) * phasor.cosine.value +
        Real.sin (frequency.value * physicalTime.value) * phasor.sine.value := by
  rfl

@[simp] theorem currentWaveformAt_value
    (frequency : SIHertz) (phasor : SICurrentPhasor)
    (physicalTime : SISecond) :
    (currentWaveformAt frequency phasor physicalTime).value =
      Real.cos (frequency.value * physicalTime.value) * phasor.cosine.value +
        Real.sin (frequency.value * physicalTime.value) * phasor.sine.value := by
  rfl

end

end Interface
end Driven
end Dimensioned
end Dissipative
end Netlist
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface.normalizeVoltagePhasor_ofNormalized
