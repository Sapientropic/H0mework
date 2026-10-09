import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorColorAction
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourcePhaseGaugeLieActual
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair StageNineHolonomicField
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorMatterRestriction SU7ExteriorMatterRepresentation
open DiracExteriorMatterAction SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumScalarChart QuantizationCheck.Fermion GaussComposite
open PreparationPhysicalPhaseGaugeRealization
open scoped BigOperators InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance h0R71eMixedSpectatorPhaseChargeLocal1 : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq
local instance h0R71eMixedSpectatorPhaseChargeLocal2 : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

theorem actual_spectator_weight (c : Fin 3) (h : Fin 2) :
    exteriorHyperchargeWeight (internalBasis c h) = if h = 0 then 1 else 0 := by
  fin_cases c <;> fin_cases h <;> decide

private theorem hyper_column (i : NamedMode) :
    diracExteriorMotherLieAction (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection)
      (LowEnergy.Quantum.wholeBasis (rootIndex i)) =
      (if i.2.2 = 0 then Complex.I else 0) • LowEnergy.Quantum.wholeBasis (rootIndex i) := by
  funext sigma
  simp only [LowEnergy.Quantum.wholeBasis, Pi.basis_apply, rootIndex,
    diracExteriorMotherLieAction, internalMatterLinearAction, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.smul_apply]
  by_cases hs : i.1 = sigma
  · subst sigma
    by_cases hi : i.2.2 = 0 <;>
      simp [hi, LowEnergy.Quantum.internalBasis, exteriorSpinorMotherLieAction,
      Stage10.HyperchargeResponse.exterior_charge_basis, actual_spectator_weight]
  · simp [hs]

def hyperCoefficient (dual : Bool) (i : NamedMode) : ℂ :=
  if i.2.2 = 0 then (if dual then -Complex.I else Complex.I) else 0

private theorem hyper_primal_entry (i : NamedMode) (j : LowEnergy.Quantum.Index) :
    GaussNativeMatter.nativePrimal nativeY j (rootIndex i) =
      (if i.2.2 = 0 then Complex.I else 0) * (if j = rootIndex i then 1 else 0) := by
  have h := congrArg LowEnergy.Quantum.coordinates (hyper_column i)
  rw [←LowEnergy.Quantum.matrix_action, map_smul] at h
  rw [show LowEnergy.Quantum.coordinates (LowEnergy.Quantum.wholeBasis (rootIndex i)) =
      Pi.single (rootIndex i) 1 from actual_named_column_coordinates i] at h
  have he := congrFun h j
  have hm : GaussNativeMatter.nativePrimal nativeY =
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction
        (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection)) := by
    change LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction
      (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv
        Stage10.HyperchargeResponse.chargeDirection)))) = _
    rw [p286CoordinateEquiv.symm_apply_apply]
  rw [hm]
  simpa only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Pi.smul_apply, smul_eq_mul] using he

theorem actual_hyper_full_column (dual : Bool) (i : NamedMode) (j : Mode) :
    GaussNativeMatter.nativeFull nativeY j (rootMode dual i) =
      hyperCoefficient dual i * (if j = rootMode dual i then 1 else 0) := by
  cases dual with
  | false =>
    cases j with
    | inl j => simpa [GaussNativeMatter.nativeFull, rootMode, hyperCoefficient]
        using hyper_primal_entry i j
    | inr j => simp [GaussNativeMatter.nativeFull, rootMode]
  | true =>
    cases j with
    | inl j => simp [GaussNativeMatter.nativeFull, rootMode]
    | inr j =>
      have h := congrArg star (hyper_primal_entry i j)
      by_cases hi : i.2.2 = 0 <;> by_cases hj : j = rootIndex i <;>
        simpa [GaussNativeMatter.nativeFull, rootMode, hyperCoefficient, hi, hj] using h

private theorem hyper_create (dual : Bool) (i : NamedMode) (x : FockFiber) :
    GaussNativeMatter.nativeFock nativeY (GaussCARHistory.createFiber (rootMode dual i) x) =
      GaussCARHistory.createFiber (rootMode dual i) (GaussNativeMatter.nativeFock nativeY x) +
      hyperCoefficient dual i • GaussCARHistory.createFiber (rootMode dual i) x := by
  apply fiberCoordinates.injective
  have h := LinearMap.congr_fun
    (LowEnergy.FullQuantum.NativeHistory.CurrentCAR.creation_quantize
      (GaussNativeMatter.nativeFull nativeY) (rootMode dual i)) (fiberCoordinates x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h
  simp_rw [actual_hyper_full_column] at h
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  simp only [map_add, map_smul]
  change LowEnergy.Fermion.quantize (GaussNativeMatter.nativeFull nativeY)
      (LowEnergy.Fermion.creation (rootMode dual i) (fiberCoordinates x)) =
    LowEnergy.Fermion.creation (rootMode dual i)
      (LowEnergy.Fermion.quantize (GaussNativeMatter.nativeFull nativeY) (fiberCoordinates x)) +
      hyperCoefficient dual i • LowEnergy.Fermion.creation (rootMode dual i) (fiberCoordinates x)
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

private theorem hyper_vacuum (dual : Bool) :
    GaussNativeMatter.nativeFock nativeY (occupationFiber dual ∅) = 0 := by
  apply fiberCoordinates.injective
  have hv : fiberCoordinates (occupationFiber dual ∅) = (vacuum : Fock Mode) := by
    funext s
    simp [occupationFiber, occupation, fiberCoordinates, EuclideanSpace.single, QuantizationCheck.Fermion.vacuum, occupationBasis]
  change LowEnergy.Fermion.quantize (GaussNativeMatter.nativeFull nativeY)
    (fiberCoordinates (occupationFiber dual ∅)) = fiberCoordinates 0
  rw [hv, map_zero]
  simp only [LowEnergy.Fermion.quantize, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, LowEnergy.Fermion.annihilation_apply, annihilate_vacuum,
    map_zero, smul_zero, Finset.sum_const_zero]

theorem actual_hyper_epsilon (dual : Bool) (spins : Fin 3 → Fin 4) :
    GaussNativeMatter.nativeFock nativeY (epsilon dual spins) =
      (if dual then -2*Complex.I else 2*Complex.I) • epsilon dual spins := by
  simp only [epsilon, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [orderedTriple, hyper_create, hyper_create, hyper_create, hyper_vacuum]
  cases dual <;> simp [hyperCoefficient, map_smul, smul_smul] <;> module

private theorem actual_color_direction :
    SourceQuantumResidualGaugeSlice.colorGenerator 2 = colorNative (sourceColorP286Generator 2).1 := by
  unfold SourceQuantumResidualGaugeSlice.colorGenerator colorNative colorData
  congr 1
  exact Prod.ext rfl (Prod.ext (sourceColorP286Generator_weak_zero 2)
    (sourceColorP286Generator_hypercharge_zero 2))

def phaseCharge : FockFiber →L[ℂ] FockFiber :=
  Complex.I • GaussNativeMatter.nativeFock actualSourcePhaseGaugeLie

theorem actual_epsilon_phase_charge (dual : Bool) (spins : Fin 3 → Fin 4) :
    phaseCharge (epsilon dual spins) =
      (if dual then (-1 : ℂ) else 1) • epsilon dual spins := by
  simp only [phaseCharge, smul_apply, actualSourcePhaseGaugeLie_literal,
    GaussNativeMatter.nativeFock.map_sub, GaussNativeMatter.nativeFock.map_neg,
    GaussNativeMatter.nativeFock.map_smul, _root_.sub_apply, _root_.neg_apply,
    actual_color_direction, actual_color_epsilon, actual_hyper_epsilon]
  cases dual <;> simp
  all_goals (match_scalars; ring_nf; norm_num [Complex.I_sq])

theorem actual_candidate_phase_charge (dual : Bool) :
    phaseCharge (candidate dual) = (if dual then (-1 : ℂ) else 1) • candidate dual := by
  rw [candidate, map_smul, map_sub, actual_epsilon_phase_charge, actual_epsilon_phase_charge]
  module

end LowEnergy.MixedSpectatorCandidate
