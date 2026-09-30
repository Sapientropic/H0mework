import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Non-collapsing SI-dimension quantities

Physical dimensions are exponent vectors over the seven SI base dimensions.
A quantity is an indexed structure, not an alias for `ℝ`; addition is available
only inside one dimension, while multiplication and division change the type
index.  Raw real values remain an explicit readout and never constitute a
cross-dimension cast.
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
namespace Units
namespace Interface

noncomputable section

/-- The free-abelian exponent vector on all seven SI base dimensions. -/
structure SIDimension where
  mass : ℤ
  length : ℤ
  time : ℤ
  electricCurrent : ℤ
  thermodynamicTemperature : ℤ
  amountOfSubstance : ℤ
  luminousIntensity : ℤ
  deriving DecidableEq, Repr

instance : Zero SIDimension where
  zero := ⟨0, 0, 0, 0, 0, 0, 0⟩

instance : Add SIDimension where
  add left right :=
    ⟨left.mass + right.mass,
      left.length + right.length,
      left.time + right.time,
      left.electricCurrent + right.electricCurrent,
      left.thermodynamicTemperature + right.thermodynamicTemperature,
      left.amountOfSubstance + right.amountOfSubstance,
      left.luminousIntensity + right.luminousIntensity⟩

instance : Neg SIDimension where
  neg dimension :=
    ⟨-dimension.mass,
      -dimension.length,
      -dimension.time,
      -dimension.electricCurrent,
      -dimension.thermodynamicTemperature,
      -dimension.amountOfSubstance,
      -dimension.luminousIntensity⟩

instance : Sub SIDimension where
  sub left right := left + -right

def dimensionless : SIDimension := 0
def massDimension : SIDimension := ⟨1, 0, 0, 0, 0, 0, 0⟩
def lengthDimension : SIDimension := ⟨0, 1, 0, 0, 0, 0, 0⟩
def timeDimension : SIDimension := ⟨0, 0, 1, 0, 0, 0, 0⟩
def currentDimension : SIDimension := ⟨0, 0, 0, 1, 0, 0, 0⟩
def temperatureDimension : SIDimension := ⟨0, 0, 0, 0, 1, 0, 0⟩
def amountDimension : SIDimension := ⟨0, 0, 0, 0, 0, 1, 0⟩
def luminousIntensityDimension : SIDimension := ⟨0, 0, 0, 0, 0, 0, 1⟩

def frequencyDimension : SIDimension := ⟨0, 0, -1, 0, 0, 0, 0⟩
def chargeDimension : SIDimension := ⟨0, 0, 1, 1, 0, 0, 0⟩
def voltageDimension : SIDimension := ⟨1, 2, -3, -1, 0, 0, 0⟩
def resistanceDimension : SIDimension := ⟨1, 2, -3, -2, 0, 0, 0⟩
def capacitanceDimension : SIDimension := ⟨-1, -2, 4, 2, 0, 0, 0⟩
def inductanceDimension : SIDimension := ⟨1, 2, -2, -2, 0, 0, 0⟩
def energyDimension : SIDimension := ⟨1, 2, -2, 0, 0, 0, 0⟩
def powerDimension : SIDimension := ⟨1, 2, -3, 0, 0, 0, 0⟩

theorem voltageDimension_ne_currentDimension :
    voltageDimension ≠ currentDimension := by decide

theorem resistanceDimension_ne_dimensionless :
    resistanceDimension ≠ dimensionless := by decide

theorem energyDimension_ne_powerDimension :
    energyDimension ≠ powerDimension := by decide

theorem capacitance_voltageRate_dimension :
    capacitanceDimension + (voltageDimension - timeDimension) =
      currentDimension := by decide

theorem inductance_currentRate_dimension :
    inductanceDimension + (currentDimension - timeDimension) =
      voltageDimension := by decide

theorem resistance_current_dimension :
    resistanceDimension + currentDimension = voltageDimension := by decide

theorem inductance_currentSquare_dimension :
    inductanceDimension + (currentDimension + currentDimension) =
      energyDimension := by decide

theorem capacitance_voltageSquare_dimension :
    capacitanceDimension + (voltageDimension + voltageDimension) =
      energyDimension := by decide

theorem resistance_currentSquare_dimension :
    resistanceDimension + (currentDimension + currentDimension) =
      powerDimension := by decide

theorem energyRate_dimension :
    energyDimension - timeDimension = powerDimension := by decide

theorem frequency_charge_dimension :
    frequencyDimension + chargeDimension = currentDimension := by decide

theorem frequency_capacitance_voltage_dimension :
    frequencyDimension + (capacitanceDimension + voltageDimension) =
      currentDimension := by decide

theorem current_time_div_voltage_dimension :
    currentDimension + timeDimension - voltageDimension =
      capacitanceDimension := by decide

theorem voltage_time_div_current_dimension :
    voltageDimension + timeDimension - currentDimension =
      inductanceDimension := by decide

theorem voltage_div_current_dimension :
    voltageDimension - currentDimension = resistanceDimension := by decide

theorem dimensionless_div_time_dimension :
    dimensionless - timeDimension = frequencyDimension := by decide

theorem current_time_dimension :
    currentDimension + timeDimension = chargeDimension := by decide

theorem voltage_current_time_dimension :
    voltageDimension + currentDimension + timeDimension =
      energyDimension := by decide

theorem voltage_current_dimension :
    voltageDimension + currentDimension = powerDimension := by decide

theorem wrong_capacitance_without_time_dimension_ne :
    currentDimension - voltageDimension ≠ capacitanceDimension := by decide

theorem wrong_capacitance_inverse_time_dimension_ne :
    currentDimension - (timeDimension + voltageDimension) ≠
      capacitanceDimension := by decide

theorem resistance_div_inductance_dimension :
    resistanceDimension - inductanceDimension = frequencyDimension := by decide

theorem inverse_inductance_capacitance_dimension :
    dimensionless - (inductanceDimension + capacitanceDimension) =
      frequencyDimension + frequencyDimension := by decide

/-- The index is part of the Lean type.  In particular, voltage and current
cannot be added or compared without an explicit proof that their dimensions
are equal. -/
@[ext] structure SIQuantity (dimension : SIDimension) where
  value : ℝ

instance {dimension : SIDimension} : Zero (SIQuantity dimension) where
  zero := ⟨0⟩

instance {dimension : SIDimension} : Add (SIQuantity dimension) where
  add left right := ⟨left.value + right.value⟩

instance {dimension : SIDimension} : Sub (SIQuantity dimension) where
  sub left right := ⟨left.value - right.value⟩

instance {dimension : SIDimension} : Neg (SIQuantity dimension) where
  neg quantity := ⟨-quantity.value⟩

instance {dimension : SIDimension} : SMul ℝ (SIQuantity dimension) where
  smul scalar quantity := ⟨scalar * quantity.value⟩

namespace SIQuantity

def dimensionlessValue (value : ℝ) : SIQuantity dimensionless :=
  ⟨value⟩

def scale {dimension : SIDimension} (scalar : ℝ)
    (quantity : SIQuantity dimension) : SIQuantity dimension :=
  scalar • quantity

def castDimension {source target : SIDimension}
    (sameDimension : source = target) :
    SIQuantity source → SIQuantity target := by
  intro quantity
  subst target
  exact quantity

@[simp] theorem castDimension_value
    {source target : SIDimension} (sameDimension : source = target)
    (quantity : SIQuantity source) :
    (castDimension sameDimension quantity).value = quantity.value := by
  subst target
  rfl

def mul {leftDimension rightDimension : SIDimension}
    (left : SIQuantity leftDimension)
    (right : SIQuantity rightDimension) :
    SIQuantity (leftDimension + rightDimension) :=
  ⟨left.value * right.value⟩

def div {numeratorDimension denominatorDimension : SIDimension}
    (numerator : SIQuantity numeratorDimension)
    (denominator : SIQuantity denominatorDimension) :
    SIQuantity (numeratorDimension - denominatorDimension) :=
  ⟨numerator.value / denominator.value⟩

def square {dimension : SIDimension} (quantity : SIQuantity dimension) :
    SIQuantity (dimension + dimension) :=
  mul quantity quantity

def sameDimensionRatio {dimension : SIDimension}
    (numerator denominator : SIQuantity dimension) : SIQuantity dimensionless :=
  ⟨numerator.value / denominator.value⟩

@[simp] theorem zero_value {dimension : SIDimension} :
    (0 : SIQuantity dimension).value = 0 := rfl

@[simp] theorem add_value {dimension : SIDimension}
    (left right : SIQuantity dimension) :
    (left + right).value = left.value + right.value := rfl

@[simp] theorem sub_value {dimension : SIDimension}
    (left right : SIQuantity dimension) :
    (left - right).value = left.value - right.value := rfl

@[simp] theorem neg_value {dimension : SIDimension}
    (quantity : SIQuantity dimension) :
    (-quantity).value = -quantity.value := rfl

@[simp] theorem smul_value {dimension : SIDimension}
    (scalar : ℝ) (quantity : SIQuantity dimension) :
    (scalar • quantity).value = scalar * quantity.value := rfl

@[simp] theorem mul_value {leftDimension rightDimension : SIDimension}
    (left : SIQuantity leftDimension)
    (right : SIQuantity rightDimension) :
    (mul left right).value = left.value * right.value := rfl

@[simp] theorem div_value {numeratorDimension denominatorDimension : SIDimension}
    (numerator : SIQuantity numeratorDimension)
    (denominator : SIQuantity denominatorDimension) :
    (div numerator denominator).value = numerator.value / denominator.value := rfl

@[simp] theorem square_value {dimension : SIDimension}
    (quantity : SIQuantity dimension) :
    (square quantity).value = quantity.value ^ 2 := by
  simp [square, pow_two]

@[simp] theorem dimensionlessValue_value (value : ℝ) :
    (dimensionlessValue value).value = value := rfl

@[simp] theorem scale_value {dimension : SIDimension}
    (scalar : ℝ) (quantity : SIQuantity dimension) :
    (scale scalar quantity).value = scalar * quantity.value := rfl

@[simp] theorem sameDimensionRatio_value {dimension : SIDimension}
    (numerator denominator : SIQuantity dimension) :
    (sameDimensionRatio numerator denominator).value =
      numerator.value / denominator.value := rfl

end SIQuantity

abbrev DimensionlessQuantity := SIQuantity dimensionless
abbrev TimeQuantity := SIQuantity timeDimension
abbrev FrequencyQuantity := SIQuantity frequencyDimension
abbrev ChargeQuantity := SIQuantity chargeDimension
abbrev CurrentQuantity := SIQuantity currentDimension
abbrev VoltageQuantity := SIQuantity voltageDimension
abbrev ResistanceQuantity := SIQuantity resistanceDimension
abbrev CapacitanceQuantity := SIQuantity capacitanceDimension
abbrev InductanceQuantity := SIQuantity inductanceDimension
abbrev EnergyQuantity := SIQuantity energyDimension
abbrev PowerQuantity := SIQuantity powerDimension
abbrev VoltageRateQuantity := SIQuantity (voltageDimension - timeDimension)
abbrev CurrentRateQuantity := SIQuantity (currentDimension - timeDimension)

abbrev SISecond := TimeQuantity
abbrev SIHertz := FrequencyQuantity
abbrev SICoulomb := ChargeQuantity
abbrev SIAmpere := CurrentQuantity
abbrev SIVolt := VoltageQuantity
abbrev SIOhm := ResistanceQuantity
abbrev SIFarad := CapacitanceQuantity
abbrev SIHenry := InductanceQuantity
abbrev SIJoule := EnergyQuantity
abbrev SIWatt := PowerQuantity

def oneSISecond : SISecond := ⟨1⟩
def oneSIHertz : SIHertz := ⟨1⟩
def oneSICoulomb : SICoulomb := ⟨1⟩
def oneSIAmpere : SIAmpere := ⟨1⟩
def oneSIVolt : SIVolt := ⟨1⟩
def oneSIOhm : SIOhm := ⟨1⟩
def oneSIFarad : SIFarad := ⟨1⟩
def oneSIHenry : SIHenry := ⟨1⟩
def oneSIJoule : SIJoule := ⟨1⟩
def oneSIWatt : SIWatt := ⟨1⟩

def capacitanceTimesVoltageRate
    (capacitance : CapacitanceQuantity)
    (voltageRate : VoltageRateQuantity) : CurrentQuantity :=
  SIQuantity.castDimension capacitance_voltageRate_dimension
    (SIQuantity.mul capacitance voltageRate)

def inductanceTimesCurrentRate
    (inductance : InductanceQuantity)
    (currentRate : CurrentRateQuantity) : VoltageQuantity :=
  SIQuantity.castDimension inductance_currentRate_dimension
    (SIQuantity.mul inductance currentRate)

def resistanceTimesCurrent
    (resistance : ResistanceQuantity)
    (current : CurrentQuantity) : VoltageQuantity :=
  SIQuantity.castDimension resistance_current_dimension
    (SIQuantity.mul resistance current)

def inductiveEnergy
    (inductance : InductanceQuantity)
    (current : CurrentQuantity) : EnergyQuantity :=
  SIQuantity.castDimension inductance_currentSquare_dimension
    (SIQuantity.mul inductance (SIQuantity.square current))

def capacitiveEnergy
    (capacitance : CapacitanceQuantity)
    (voltage : VoltageQuantity) : EnergyQuantity :=
  SIQuantity.castDimension capacitance_voltageSquare_dimension
    (SIQuantity.mul capacitance (SIQuantity.square voltage))

def resistivePower
    (resistance : ResistanceQuantity)
    (current : CurrentQuantity) : PowerQuantity :=
  SIQuantity.castDimension resistance_currentSquare_dimension
    (SIQuantity.mul resistance (SIQuantity.square current))

def frequencyTimesCharge
    (frequency : FrequencyQuantity)
    (charge : ChargeQuantity) : CurrentQuantity :=
  SIQuantity.castDimension frequency_charge_dimension
    (SIQuantity.mul frequency charge)

def frequencyTimesCapacitanceVoltage
    (frequency : FrequencyQuantity)
    (capacitance : CapacitanceQuantity)
    (voltage : VoltageQuantity) : CurrentQuantity :=
  SIQuantity.castDimension frequency_capacitance_voltage_dimension
    (SIQuantity.mul frequency (SIQuantity.mul capacitance voltage))

@[simp] theorem capacitanceTimesVoltageRate_value
    (capacitance : CapacitanceQuantity)
    (voltageRate : VoltageRateQuantity) :
    (capacitanceTimesVoltageRate capacitance voltageRate).value =
      capacitance.value * voltageRate.value := by
  simp [capacitanceTimesVoltageRate]

@[simp] theorem inductanceTimesCurrentRate_value
    (inductance : InductanceQuantity)
    (currentRate : CurrentRateQuantity) :
    (inductanceTimesCurrentRate inductance currentRate).value =
      inductance.value * currentRate.value := by
  simp [inductanceTimesCurrentRate]

@[simp] theorem resistanceTimesCurrent_value
    (resistance : ResistanceQuantity)
    (current : CurrentQuantity) :
    (resistanceTimesCurrent resistance current).value =
      resistance.value * current.value := by
  simp [resistanceTimesCurrent]

@[simp] theorem inductiveEnergy_value
    (inductance : InductanceQuantity)
    (current : CurrentQuantity) :
    (inductiveEnergy inductance current).value =
      inductance.value * current.value ^ 2 := by
  simp [inductiveEnergy]

@[simp] theorem capacitiveEnergy_value
    (capacitance : CapacitanceQuantity)
    (voltage : VoltageQuantity) :
    (capacitiveEnergy capacitance voltage).value =
      capacitance.value * voltage.value ^ 2 := by
  simp [capacitiveEnergy]

@[simp] theorem resistivePower_value
    (resistance : ResistanceQuantity)
    (current : CurrentQuantity) :
    (resistivePower resistance current).value =
      resistance.value * current.value ^ 2 := by
  simp [resistivePower]

@[simp] theorem frequencyTimesCharge_value
    (frequency : FrequencyQuantity)
    (charge : ChargeQuantity) :
    (frequencyTimesCharge frequency charge).value =
      frequency.value * charge.value := by
  simp [frequencyTimesCharge]

@[simp] theorem frequencyTimesCapacitanceVoltage_value
    (frequency : FrequencyQuantity)
    (capacitance : CapacitanceQuantity)
    (voltage : VoltageQuantity) :
    (frequencyTimesCapacitanceVoltage frequency capacitance voltage).value =
      frequency.value * (capacitance.value * voltage.value) := by
  simp [frequencyTimesCapacitanceVoltage]

/-- Derivative with respect to an explicitly dimensioned scalar coordinate.
The derivative index is the output dimension minus the input dimension; the
kernel-level derivative is taken only after reading both coordinates in their
declared SI units. -/
structure HasSIQuantityDerivAt
    {inputDimension outputDimension : SIDimension}
    (function : SIQuantity inputDimension → SIQuantity outputDimension)
    (derivative : SIQuantity (outputDimension - inputDimension))
    (point : SIQuantity inputDimension) : Prop where
  valueHasDerivAt : HasDerivAt
    (fun coordinate : ℝ => (function ⟨coordinate⟩).value)
    derivative.value point.value

end

end Interface
end Units
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface.voltageDimension_ne_currentDimension
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface.capacitance_voltageRate_dimension
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface.energyRate_dimension
