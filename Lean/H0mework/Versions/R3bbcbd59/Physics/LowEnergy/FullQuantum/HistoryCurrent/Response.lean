import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryCurrent.Dual
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.SpatialResponse.Readback

/-! The original two propagation legs generate an ordered current commutator before any readout. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryVariation PerturbedGreen SpatialResponse
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "U" => familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "D" => responseOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
attribute [local irreducible] fullOperator familyOperator responseOperator

def returnedReader (reader : SpatialOperators) (epsilon time : ℝ) : SpatialOperators :=
  U epsilon time 0 * reader * U epsilon 0 time

def relativeResponse (time : ℝ) : SpatialOperators := U 0 time 0 * D time

local notation "B" => returnedReader gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "K" => relativeResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection

theorem returnedReader_twoLeg_derivative (reader : SpatialOperators) (time : ℝ) :
    HasDerivAt (fun epsilon : ℝ => B reader epsilon time)
      (-(U 0 time 0 * D time * U 0 time 0) * reader * U 0 0 time+
        U 0 time 0 * reader * D time) 0 := by
  have forward := familyOperator_derivative gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection time
  have reverse := reverse_derivative gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection time
  exact (reverse.mul_const reader).mul forward

theorem returnedReader_derivative (reader : SpatialOperators) (time : ℝ) :
    HasDerivAt (fun epsilon : ℝ => B reader epsilon time)
      (B reader 0 time * K time-K time * B reader 0 time) 0 := by
  have cancel : U 0 0 time * U 0 time 0=1 :=
    (familyUnit gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection 0 time).val_inv
  have collapse : U 0 time 0 * reader * U 0 0 time * (U 0 time 0 * D time)=U 0 time 0 * reader * D time := by
    simp only [mul_assoc]
    rw [← mul_assoc (U 0 0 time) (U 0 time 0) (D time),cancel,one_mul]
  have identified : -(U 0 time 0 * D time * U 0 time 0) * reader * U 0 0 time+
      U 0 time 0 * reader * D time=B reader 0 time * K time-K time * B reader 0 time := by
    dsimp only [returnedReader,relativeResponse]
    rw [collapse]
    noncomm_ring
  rw [← identified]
  exact returnedReader_twoLeg_derivative gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection reader time

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
