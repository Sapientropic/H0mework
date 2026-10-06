import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeVertex
import H0mework.Versions.AB.Physics.MotherSource.HyperchargeResponse.Scalar

/-! The existing native Y time-current acts on the original composite mode.
The unit is obtained from the original exterior action, not a minimum weight. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open SaturationMonoid.PhysicsCore
open LowEnergy.Electromagnetic.Identification
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction SU7ExteriorMatterRepresentation
open DiracExteriorMatterAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussQuantumMultiplier CanonicalGradedCurrent
open scoped Matrix BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance chargeModeDecision : DecidableEq Mode := LinearOrder.toDecidableEq
local instance chargeIndexDecision : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

def nativeY : NativeLie := p286CoordinateEquiv Stage10.HyperchargeResponse.chargeDirection

def matterIndex (spin : Fin 2) (color : Fin 3) : LowEnergy.Quantum.Index :=
  ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis color))⟩

theorem original_matter_mode_charge (spin : Fin 2) (color : Fin 3) :
    diracExteriorMotherLieAction (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection)
      (LowEnergy.Quantum.wholeBasis (matterIndex spin color)) =
      Complex.I • LowEnergy.Quantum.wholeBasis (matterIndex spin color) := by
  funext sigma
  simp only [LowEnergy.Quantum.wholeBasis,Pi.basis_apply,matterIndex,
    diracExteriorMotherLieAction,internalMatterLinearAction,LinearMap.coe_mk,AddHom.coe_mk,
    Pi.smul_apply]
  by_cases h : (spin.castLE (by decide) : Fin 4)=sigma
  · subst sigma
    simp [LowEnergy.Quantum.internalBasis,exteriorSpinorMotherLieAction,
      Stage10.HyperchargeResponse.exterior_charge_basis,Composite.matter_weight]
  · simp [h]

theorem primal_charge_column (spin : Fin 2) (color : Fin 3) :
    GaussNativeMatter.nativePrimal nativeY *ᵥ Pi.single (matterIndex spin color) 1 =
      Complex.I • Pi.single (matterIndex spin color) 1 := by
  have h := congrArg LowEnergy.Quantum.coordinates (original_matter_mode_charge spin color)
  rw [←LowEnergy.Quantum.matrix_action,map_smul] at h
  have basis : LowEnergy.Quantum.coordinates (LowEnergy.Quantum.wholeBasis (matterIndex spin color)) =
      Pi.single (matterIndex spin color) 1 := by
    simp [LowEnergy.Quantum.coordinates]
    funext i
    simp [Finsupp.single_apply,Pi.single_apply,eq_comm]
  rw [basis] at h
  change LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction
    (p286LieBlockEmbed (p286CoordinateEquiv.symm nativeY))) *ᵥ _ = _
  simpa only [nativeY,p286CoordinateEquiv.symm_apply_apply] using h

def nativeChargeMatrix : Matrix Mode Mode ℂ := Complex.I • GaussNativeMatter.nativeFull nativeY

theorem native_charge_matrix_hermitian : nativeChargeMatrix.conjTranspose=nativeChargeMatrix :=
  CanonicalGradedGaugeVariation.gaugeMatrix_hermitian GaussHistoryHilbert.sourcePoint .temporal nativeY

theorem native_charge_column (spin : Fin 2) (color : Fin 3) (output : Mode) :
    nativeChargeMatrix output (mode spin color) = if output=mode spin color then -1 else 0 := by
  have primal (i : LowEnergy.Quantum.Index) :
      GaussNativeMatter.nativePrimal nativeY i (matterIndex spin color) =
        if i=matterIndex spin color then Complex.I else 0 := by
    have h := congrFun (primal_charge_column spin color) i
    simpa [Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite] using h
  cases output with
  | inl i =>
    change Complex.I*GaussNativeMatter.nativePrimal nativeY i (matterIndex spin color) = _
    rw [primal]
    by_cases h : i=matterIndex spin color
    · simp [h,mode,matterIndex,Complex.I_mul_I]
    · simp [mode,matterIndex] at *
  | inr i => simp [nativeChargeMatrix,GaussNativeMatter.nativeFull,mode]

theorem native_charge_row (spin : Fin 2) (color : Fin 3) (input : Mode) :
    nativeChargeMatrix (mode spin color) input = if input=mode spin color then -1 else 0 := by
  have h := congrFun (congrFun native_charge_matrix_hermitian (mode spin color)) input
  change star (nativeChargeMatrix input (mode spin color)) = _ at h
  rw [←h,native_charge_column]
  by_cases hi : input=mode spin color <;> simp [hi]

theorem native_creation_column (spin : Fin 2) (color : Fin 3) :
    creationColumn nativeChargeMatrix (mode spin color) = -GaussCARHistory.createFiber (mode spin color) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro word
  simp only [creationColumn,sum_apply,smul_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    native_charge_column,smul_eq_mul,neg_apply,PiLp.neg_apply]
  simp only [ite_mul,neg_one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem native_annihilation_row (spin : Fin 2) (color : Fin 3) :
    annihilationRow nativeChargeMatrix (mode spin color) = -GaussCARHistory.annihilateFiber (mode spin color) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro word
  simp only [annihilationRow,sum_apply,smul_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    native_charge_row,smul_eq_mul,neg_apply,PiLp.neg_apply]
  simp only [ite_mul,neg_one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem creation_vertex_native_charge (channel spin : Fin 2)
    (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
    creationVertexMatrix .temporal nativeY channel spin z =
      -fiberCreation channel spin (GaussNativePotential.scalarField z) := by
  change (∑ color : Fin 3, star (coefficient channel color z) •
    creationColumn nativeChargeMatrix (mode spin color)) = _
  simp only [native_creation_column,smul_neg,Finset.sum_neg_distrib,fiberCreation,coefficient]

theorem annihilation_vertex_native_charge (channel spin : Fin 2)
    (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
    annihilationVertexMatrix .temporal nativeY channel spin z =
      fiberAnnihilation channel spin (GaussNativePotential.scalarField z) := by
  change -(∑ color : Fin 3, coefficient channel color z •
    annihilationRow nativeChargeMatrix (mode spin color)) = _
  simp only [native_annihilation_row,smul_neg,Finset.sum_neg_distrib,neg_neg,fiberAnnihilation,coefficient]

theorem scalar_coefficient_native_neutral (channel : Fin 2) (color : Fin 3) (phi : Scalar) :
    scalarCoefficient channel color
      (scalarMotherLieAction (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection) phi)=0 := by
  have neutral : (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color)
      (exteriorMotherLieAction 4 (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection)
        (scalarCoordinateEquiv.symm phi))=0 := by
    rw [←(su7ExteriorBasis 4).sum_repr (scalarCoordinateEquiv.symm phi)]
    simp only [map_sum,map_smul,Stage10.HyperchargeResponse.exterior_charge_basis,
      Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul,
      mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [Composite.scalar_weight,Int.cast_zero,zero_mul,mul_zero]
  change (if color=1 then (-1 : ℂ) else 1) •
    (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color)
      (scalarCoordinateEquiv.symm (scalarMotherLieAction
        (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection) phi)) = 0
  rw [scalarMotherLieAction,LinearEquiv.symm_apply_apply,neutral,smul_zero]

end LowEnergy.GaussComposite
