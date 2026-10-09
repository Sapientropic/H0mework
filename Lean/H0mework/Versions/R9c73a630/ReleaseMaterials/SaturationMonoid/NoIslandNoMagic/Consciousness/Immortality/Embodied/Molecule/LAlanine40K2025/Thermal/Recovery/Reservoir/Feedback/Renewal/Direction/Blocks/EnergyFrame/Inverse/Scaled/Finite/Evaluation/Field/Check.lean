import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Field.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.ListBounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
open Spectral Propagation.Interface

def clockNumerator : Int := 15625000000000
def clockDenominator : Int := 36212777618028463
def fieldScale : Int := 10^42
def coefficientScale : Int := 10^24

def identityColumn (j : Nat) : List Int := (List.range 98).map (fun i => if i=j then coefficientScale else 0)
def stepDenominator (n : Nat) : Int := (n+1 : Nat)*clockDenominator*fieldScale

def residualRow (n : Nat) (previous current : List Int) : List Int :=
  ((Dense.fieldRows.map (fun row => clockNumerator*Rows.dot row previous)).zip current).map
    (fun pair => pair.1-stepDenominator n*pair.2)

def Check (n : Nat) (previous current : List Int) : Prop :=
  (residualRow n previous current |>.map abs).all (· ≤ stepDenominator n)=true

instance (n : Nat) (previous current : List Int) : Decidable (Check n previous current) :=
  inferInstanceAs (Decidable ((residualRow n previous current |>.map abs).all (· ≤ stepDenominator n)=true))

theorem checked_entry (n : Nat) (previous current : List Int) (length : current.length=98)
    (checked : Check n previous current) (i : Basis) :
    |clockNumerator*Rows.dot (Rows.rowAt Dense.fieldRows i) previous-stepDenominator n*Rows.read current i| ≤ stepDenominator n := by
  have residualLength : (residualRow n previous current).length=98 := by
    simp only [residualRow,List.length_map,List.length_zip,Dense.fieldRows_length,length,min_self]
  have bound := all_abs_bound (residualRow n previous current) residualLength (stepDenominator n) checked i
  have leftLength : (Dense.fieldRows.map (fun row => clockNumerator*Rows.dot row previous)).length=98 := by
    rw [List.length_map,Dense.fieldRows_length]
  have left : i.val < (Dense.fieldRows.map (fun row => clockNumerator*Rows.dot row previous)).length := by rw [leftLength]; exact i.isLt
  have right : i.val < current.length := by rw [length]; exact i.isLt
  have entry : Rows.read (residualRow n previous current) i=
      clockNumerator*Rows.dot (Rows.rowAt Dense.fieldRows i) previous-stepDenominator n*Rows.read current i := by
    change (residualRow n previous current)[i.val]! = _
    rw [getElem!_pos _ _ (by rw [residualLength]; exact i.isLt)]
    simp only [residualRow,List.getElem_map,List.getElem_zip]
    have rowsBound : i.val < Dense.fieldRows.length := by rw [Dense.fieldRows_length]; exact i.isLt
    simp only [Rows.read,Rows.rowAt,getElem!_pos Dense.fieldRows i.val rowsBound,getElem!_pos current i.val right]

  rw [entry] at bound
  exact bound

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
