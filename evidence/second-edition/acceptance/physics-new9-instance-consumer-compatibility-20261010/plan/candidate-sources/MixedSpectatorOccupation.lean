import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorCandidate
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterSector
import H0mework.Physics.LowEnergyFermion.Charge
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore QuantizationCheck.Fermion
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance h0R9c73a630MixedSpectatorOccupationLocal1 : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

def fiberCharge (q : Mode → ℂ) : Module.End ℂ FockFiber :=
  fiberCoordinates.symm.toLinearMap.comp
    ((LowEnergy.Fermion.occupationCharge q).comp fiberCoordinates.toLinearMap)

private theorem create_coordinates (i : Mode) (x : FockFiber) :
    fiberCoordinates (GaussCARHistory.createFiber i x) =
      LowEnergy.Fermion.creation i (fiberCoordinates x) := by
  change fiberCoordinates (SourceCARBound.createOp i x) = _
  rw [SourceCARBound.createOp, SourceCARBound.coordinates_liftOp]

private theorem charge_create (q : Mode → ℂ) (dual : Bool) (i : NamedMode) (x : FockFiber) :
    fiberCharge q (GaussCARHistory.createFiber (rootMode dual i) x) =
      GaussCARHistory.createFiber (rootMode dual i) (fiberCharge q x) +
        q (rootMode dual i) • GaussCARHistory.createFiber (rootMode dual i) x := by
  apply fiberCoordinates.injective
  have h := LinearMap.congr_fun (LowEnergy.Fermion.occupationCharge_creation q (rootMode dual i))
    (fiberCoordinates x)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h
  simpa only [fiberCharge, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, map_add, map_smul, create_coordinates] using h

private theorem charge_vacuum (q : Mode → ℂ) (dual : Bool) :
    fiberCharge q (occupationFiber dual ∅) = 0 := by
  apply fiberCoordinates.injective
  change LowEnergy.Fermion.occupationCharge q (fiberCoordinates (occupationFiber dual ∅)) = _
  funext word
  simp [occupationFiber, occupation, fiberCoordinates, LowEnergy.Fermion.occupationCharge,
    EuclideanSpace.single, Pi.single_apply]
  intro hw
  subst word
  simp

theorem actual_triple_charge (q : Mode → ℂ) (dual : Bool) (i j k : NamedMode) :
    fiberCharge q (orderedTriple dual i j k) =
      (q (rootMode dual i) + q (rootMode dual j) + q (rootMode dual k)) •
        orderedTriple dual i j k := by
  rw [orderedTriple, charge_create, charge_create, charge_create, charge_vacuum]
  simp only [map_zero, zero_add, map_add, map_smul]
  module

/-- Exact occupation reader on the fixed three-body source; hypotheses are
one-mode readout values, not a desired particle identity or selection rule. -/
theorem actual_candidate_constant_mode_charge (q : Mode → ℂ) (dual : Bool) (v : ℂ)
    (hq : ∀ i : NamedMode, q (rootMode dual i) = v) :
    fiberCharge q (candidate dual) = (3*v) • candidate dual := by
  have he (spins : Fin 3 → Fin 4) : fiberCharge q (epsilon dual spins) =
      (3*v) • epsilon dual spins := by
    simp only [epsilon, map_sum, map_smul, actual_triple_charge, hq, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    module
  rw [candidate, map_smul, map_sub, he, he]
  module


theorem actual_candidate_number (dual : Bool) :
    fiberNumber (candidate dual) = (3 : ℂ) • candidate dual := by
  have h := actual_candidate_constant_mode_charge (fun _ => 1) dual 1 (fun _ => rfl)
  apply fiberCoordinates.injective
  have hc := congrArg fiberCoordinates h
  change SourceFockRaising.total (fiberCoordinates (candidate dual)) = _
  simpa only [SourceFockRaising.total, fiberCharge, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, map_smul, mul_one] using hc

theorem actual_candidate_grade_zero (dual : Bool) :
    GaussYukawaGrade.fiberGrade (candidate dual) = 0 := by
  have outside (i : NamedMode) : rootMode dual i ∉ SourceQuantumFockGrade56.target := by
    cases dual <;> simp [rootMode, SourceQuantumFockGrade56.mem_target_left,
      SourceQuantumFockGrade56.mem_target_right, SourceQuantumFockGrade56.isSix, rootIndex]
  have h := actual_candidate_constant_mode_charge
    (fun i => if i ∈ SourceQuantumFockGrade56.target then 1 else 0) dual 0
    (fun i => if_neg (outside i))
  apply fiberCoordinates.injective
  rw [GaussYukawaGrade.fiber_coordinates_grade]
  have hc := congrArg fiberCoordinates h
  simpa only [SourceFockRaising.grade, fiberCharge, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, mul_zero, zero_smul, map_zero] using hc

theorem actual_candidate_bottom_sector (dual : Bool) :
    GaussCoreLabel.fiberPiece (3,0) (candidate dual) = candidate dual := by
  apply (NamedColorQtNext.actual_fiber_sector 3 0 _).mpr
  exact ⟨actual_candidate_number dual, by simpa using actual_candidate_grade_zero dual⟩

end LowEnergy.MixedSpectatorCandidate
