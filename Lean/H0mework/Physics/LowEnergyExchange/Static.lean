import H0mework.Physics.LowEnergyExchange.Current

/-! Completing the source zero-momentum weak block with its original currents. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Exchange
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource
open DiracCliffordRepresentation DiracExteriorMatterAction SU7MotherLieAlgebra
open StageNineDynamicBreakingVacuum
noncomputable section

def weakQuadratic (field : Fin 4 → ℝ) : ℝ :=
  -(field 0)^2/lapse + lapse*∑ axis : Fin 3, (field axis.succ)^2

def weakSourcePairing (field source : Fin 4 → ℝ) : ℝ := ∑ mu, source mu*field mu

def inducedWeakField (source : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![lapse*source 0/2, -source 1/(2*lapse), -source 2/(2*lapse), -source 3/(2*lapse)]

def weakExchange (source : Fin 4 → ℝ) : ℝ :=
  lapse*(source 0)^2/4 - (∑ axis : Fin 3, (source axis.succ)^2)/(4*lapse)

theorem weak_completion (field source : Fin 4 → ℝ) :
    weakQuadratic field + weakSourcePairing field source =
      weakQuadratic (field-inducedWeakField source) + weakExchange source := by
  simp only [weakQuadratic, weakSourcePairing, inducedWeakField, weakExchange,
    Fin.sum_univ_four, Fin.sum_univ_three, Pi.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ]
  dsimp
  field_simp [ne_of_gt lapse_pos]
  ring

theorem induced_exchange (source : Fin 4 → ℝ) :
    weakQuadratic (inducedWeakField source) + weakSourcePairing (inducedWeakField source) source =
      weakExchange source := by
  rw [weak_completion]
  simp [weakQuadratic]

def sourceWeakExchange (coframe : LorentzianCoframe) (matter : DiracExteriorMatterCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (matrix : P286LieBlockData) : ℝ :=
  weakExchange (fun mu => current coframe matter dual mu matrix)

theorem original_current_exchange (coframe : LorentzianCoframe) (matter : DiracExteriorMatterCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (matrix : P286LieBlockData) :
    let source := fun mu => current coframe matter dual mu matrix
    weakQuadratic (inducedWeakField source) + weakSourcePairing (inducedWeakField source) source =
      sourceWeakExchange coframe matter dual matrix :=
  induced_exchange _

theorem scalar_source_completion (field source : ℝ) :
    -2*lapse*field^2 + source*field =
      -2*lapse*(field-source/(4*lapse))^2 + source^2/(8*lapse) := by
  field_simp [ne_of_gt lapse_pos]
  ring

theorem scalar_induced_exchange (source : ℝ) :
    -2*lapse*(source/(4*lapse))^2 + source*(source/(4*lapse)) = source^2/(8*lapse) := by
  rw [scalar_source_completion]
  ring

def sourceQuintetExchange (coframe : LorentzianCoframe) (matter : DiracExteriorMatterCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (matrix : P286LieBlockData)
    (scalarDirection : ScalarCoordinateCarrier) : ℝ :=
  sourceWeakExchange coframe matter dual matrix +
    (yukawaSource coframe matter dual scalarDirection)^2/(8*lapse)

theorem original_quintet_exchange (coframe : LorentzianCoframe) (matter : DiracExteriorMatterCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (matrix : P286LieBlockData)
    (scalarDirection : ScalarCoordinateCarrier) :
    let j := fun mu => current coframe matter dual mu matrix
    let z := yukawaSource coframe matter dual scalarDirection
    weakQuadratic (inducedWeakField j) + weakSourcePairing (inducedWeakField j) j -
      2*lapse*(z/(4*lapse))^2 + z*(z/(4*lapse)) =
        sourceQuintetExchange coframe matter dual matrix scalarDirection := by
  dsimp
  rw [original_current_exchange]
  unfold sourceQuintetExchange
  have scalar := scalar_induced_exchange (yukawaSource coframe matter dual scalarDirection)
  linarith

end
end SaturationMonoid.PhysicsCore.LowEnergy.Exchange
