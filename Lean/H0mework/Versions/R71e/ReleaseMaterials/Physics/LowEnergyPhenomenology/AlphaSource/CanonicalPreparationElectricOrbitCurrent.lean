import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationTemporalGlobalCharge

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectricConstraint
open SaturationMonoid.PhysicsCore
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumResidualGaugeSlice
open SourceQuantumFockGauge GaussCoreHilbert GaussCoreDifferential GaussLiveMomentum
open GaussHistoryHilbert
open GaussNativeForm GaussNativeMatter GaussQuantumMultiplier CanonicalGradedCharge
open PreparationVacuumTemporalCharge PreparationVacuumLowerClassical
open scoped ContDiff Topology BigOperators RealInnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

def scalarOrbit (a : NativeLie) (j : ScalarIndex) (z : SourceCoordinateSlice) : ℝ :=
  ⟪scalarBasis j,(orbitMap z a).1⟫

def electricOrbit (a : NativeLie) (i : Fin 3) (j : LieIndex) (z : SourceCoordinateSlice) : ℝ :=
  ⟪lieBasis j,gaugeCoordinates (orbitMap z a).2 i⟫

theorem orbit_smooth (a : NativeLie) : ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>orbitMap z a) := by
  have affine : (fun z : SourceCoordinateSlice=>orbitMap z a)=
      fun z=>(splitL 0+variationL z) (a,0) := by
    funext z
    rw [←split_affine]
    simp [splitL,splitMap,sliceMap]
  rw [affine]
  have hv : ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>variationL z) :=
    ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=SourceCoordinateSlice) (F:=Split →L[ℝ] Ambient) variationL
  have hl : ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>splitL 0+variationL z) := contDiff_const.add hv
  exact hl.clm_apply (contDiff_const (c := ((a,0) : Split)))

theorem scalarOrbit_smooth (a : NativeLie) (j : ScalarIndex) : ContDiff ℝ ∞ (scalarOrbit a j) :=
  contDiff_const.inner ℝ (orbit_smooth a).fst

theorem electricOrbit_smooth (a : NativeLie) (i : Fin 3) (j : LieIndex) :
    ContDiff ℝ ∞ (electricOrbit a i j) := by
  exact contDiff_const.inner ℝ ((contDiff_apply ℝ NativeLie i).comp
    (gaugeCoordinates.toContinuousLinearEquiv.contDiff.comp (orbit_smooth a).snd))

theorem ambient_expansion (v : Ambient) :
    (∑ j : ScalarIndex,⟪scalarBasis j,v.1⟫ • scalarDirection j)+
      (∑ i : Fin 3,∑ j : LieIndex,⟪lieBasis j,gaugeCoordinates v.2 i⟫ • gaugeDirection i j)=v := by
  apply Prod.ext
  · simp only [Prod.fst_add,Prod.fst_sum]
    change (∑ j : ScalarIndex,⟪scalarBasis j,v.1⟫ • scalarBasis j)+
      (∑ i : Fin 3,∑ j : LieIndex,⟪lieBasis j,gaugeCoordinates v.2 i⟫ • (0 : Scalar))=v.1
    simp only [smul_zero,Finset.sum_const_zero,add_zero]
    exact scalarBasis.sum_repr' _
  · apply gaugeCoordinates.injective
    funext i
    change (gaugeCoordinates ((∑ j : ScalarIndex,⟪scalarBasis j,v.1⟫ • scalarDirection j)+
      (∑ k : Fin 3,∑ j : LieIndex,⟪lieBasis j,gaugeCoordinates v.2 k⟫ • gaugeDirection k j)).2) i=_
    simp only [Prod.snd_add,Prod.snd_sum]
    change gaugeCoordinates ((∑ j : ScalarIndex,⟪scalarBasis j,v.1⟫ • (0 : Gauge))+
      (∑ k : Fin 3,∑ j : LieIndex,⟪lieBasis j,gaugeCoordinates v.2 k⟫ • (gaugeDirection k j).2)) i=_
    simp only [smul_zero,Finset.sum_const_zero,zero_add,map_sum,map_smul]
    change (∑ k : Fin 3,∑ j : LieIndex,⟪lieBasis j,gaugeCoordinates v.2 k⟫ •
      (Pi.single k (lieBasis j) : Fin 3 → NativeLie)) i=gaugeCoordinates v.2 i
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_ite,smul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    exact lieBasis.sum_repr' _

def pointMomentum (z : SourceCoordinateSlice) (f : QuantumTest) : Ambient →ₗ[ℝ] FockFiber where
  toFun v:=covariantMomentum v f z
  map_add' v w:=by
    simp only [covariantMomentum_apply,map_add,Prod.fst_add,Prod.snd_add,add_apply]
    rw [show ((0,(inverseL z v).2+(inverseL z w).2) : SourceCoordinateSlice)=
      (0,(inverseL z v).2)+(0,(inverseL z w).2) by simp,map_add]
    simp only [smul_add]
    abel
  map_smul' r v:=by
    simp only [covariantMomentum_apply,map_smul,RingHom.id_apply]
    change (-Complex.I) • ((fderiv ℝ f z) (0,r • (inverseL z v).2)+
      nativeFock (r • (inverseL z v).1) (f z))=r • _
    rw [map_smul,smul_apply]
    rw [show ((0,r • (inverseL z v).2) : SourceCoordinateSlice)=r • (0,(inverseL z v).2) by simp,map_smul]
    rw [←smul_add,smul_comm]

def scalarOrbitAction (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  ∑ j : ScalarIndex,(multiply (scalarOrbit a j) (fun _=>(scalarOrbit_smooth a j).contDiffAt)).comp
    (covariantMomentum (scalarDirection j))

def electricOrbitAction (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  ∑ i : Fin 3,∑ j : LieIndex,(multiply (electricOrbit a i j) (fun _=>(electricOrbit_smooth a i j).contDiffAt)).comp
    (covariantMomentum (gaugeDirection i j))

def orbitAction (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  scalarOrbitAction a+electricOrbitAction a

theorem orbitAction_apply (a : NativeLie) (f : QuantumTest) (z : SourceCoordinateSlice) :
    orbitAction a f z=covariantMomentum (orbitMap z a) f z := by
  have expanded:=congrArg (pointMomentum z f) (ambient_expansion (orbitMap z a))
  simp only [map_add,map_sum,map_smul] at expanded
  let ev : QuantumTest →ₗ[ℂ] FockFiber :=
    { toFun:=fun g=>g z,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
  change ev (orbitAction a f)=_
  simp only [orbitAction,scalarOrbitAction,electricOrbitAction,LinearMap.add_apply,
    LinearMap.sum_apply,LinearMap.comp_apply,map_add,map_sum]
  change (∑ j : ScalarIndex,(scalarOrbit a j z:ℂ) • covariantMomentum (scalarDirection j) f z)+
    (∑ i : Fin 3,∑ j : LieIndex,(electricOrbit a i j z:ℂ) • covariantMomentum (gaugeDirection i j) f z)=_
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),pointMomentum,LinearMap.coe_mk,AddHom.coe_mk] at expanded
  convert! expanded using 1

theorem chargeAction_fock (a : NativeLie) (f : QuantumTest) (z : SourceCoordinateSlice) :
    chargeAction a f z=Complex.I • nativeFock a (f z) := by
  change quantizer (Complex.I • nativeFull a) (f z)=_
  rw [map_smul,smul_apply]
  rfl

theorem original_gauss_constraint (a : NativeLie) : orbitAction a= -chargeAction a := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  rw [orbitAction_apply]
  by_cases hz : z∈physicalChart
  · rw [covariantMomentum_orbit ⟨z,hz⟩ a f]
    change _= -(chargeAction a f z)
    rw [chargeAction_fock,neg_smul]
  · have outside : z∉tsupport f:=fun h=>hz (f.tsupport_subset h)
    simp only [covariantMomentum_apply,fderiv_of_notMem_tsupport ℝ outside,
      image_eq_zero_of_notMem_tsupport outside,map_zero,zero_apply,zero_add,smul_zero]
    change 0= -(chargeAction a f z)
    rw [chargeAction_fock,image_eq_zero_of_notMem_tsupport outside,map_zero,smul_zero,neg_zero]

theorem electric_scalar_charge_balance (a : NativeLie) (f : QuantumTest) :
    electricOrbitAction a f+scalarOrbitAction a f+chargeAction a f=0 := by
  have h:=LinearMap.congr_fun (original_gauss_constraint a) f
  change scalarOrbitAction a f+electricOrbitAction a f= -chargeAction a f at h
  rw [add_comm (electricOrbitAction a f),h,neg_add_cancel]

theorem temporal_constraint_source (a : Fin 12) (f : QuantumTest) :
    embed (orbitAction (originalUnit a) f)= -globalReader a (embed f) := by
  rw [original_gauss_constraint,LinearMap.neg_apply,map_neg,CanonicalGradedCharge.chargeReader_core]

end LowEnergy.PreparationVacuumElectricConstraint
