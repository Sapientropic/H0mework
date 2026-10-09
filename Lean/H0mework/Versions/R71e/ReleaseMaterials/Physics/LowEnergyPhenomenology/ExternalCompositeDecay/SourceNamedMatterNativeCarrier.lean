import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterSpinCasimir
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.GaugeLift
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore NamedMatterWedgeQt
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction SU7ExteriorMatterRepresentation DiracExteriorMatterAction
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open StageNineHolonomicField QuantizationCheck.Fermion
open scoped BigOperators InnerProductSpace Matrix ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=SourceRealScalarFock.branchOrder.toDecidableEq
local instance : DecidableEq LowEnergy.Quantum.Index:=Classical.decEq _

def nativeData(a:NativeLie):P286LieBlockData:=p286CoordinateEquiv.symm a
def nativeHyper(dual:Bool)(a:NativeLie):ℂ:=
  if dual then star (nativeData a).2.2.1 else (nativeData a).2.2.1

private theorem original_triplet_index(c:Fin 3):
    LowEnergy.ActiveSector.colorTripletIndex c=LowEnergy.Electromagnetic.Identification.Composite.matterBasis c:=by
  fin_cases c <;> decide

private theorem named_column_value(i:NamedMode):
    namedColumn i=Pi.single i.1 (LowEnergy.ActiveSector.colorTripletMatter i.2):=by
  rw [namedColumn,LowEnergy.Quantum.wholeBasis,Pi.basis_apply]
  congr 1
  apply Prod.ext
  · simp [LowEnergy.Quantum.internalBasis,rootIndex,LowEnergy.ActiveSector.colorTripletMatter]
  · apply Prod.ext <;> simp [LowEnergy.Quantum.internalBasis,rootIndex,
      LowEnergy.ActiveSector.colorTripletMatter,original_triplet_index]

private theorem internal_single(T:Module.End ℂ SU7ExteriorSpinorMatterCarrier)(s:Fin 4)
    (x:SU7ExteriorSpinorMatterCarrier):
    internalMatterLinearAction T (Pi.single s x)=Pi.single s (T x):=by
  funext t
  by_cases h:t=s <;> simp [internalMatterLinearAction,h,map_zero]

/-- Every original P286 direction acts on the same named twelve source columns; weak and hyper blocks are retained until this return. -/
theorem actual_native_dirac_column(a:NativeLie)(i:NamedMode):
    diracExteriorMotherLieAction (p286LieBlockEmbed (nativeData a)) (namedColumn i)=
      (∑r:Fin 3,(nativeData a).1.val r i.2 • namedColumn (i.1,r))+
      (nativeData a).2.2.1 • namedColumn i:=by
  rw [named_column_value,diracExteriorMotherLieAction,internal_single,
    LowEnergy.MatterSpace.p286_colorTripletMatter]
  simp_rw [named_column_value]
  funext j
  by_cases h:j=i.1 <;> simp [h,Finset.sum_apply,Pi.smul_apply]

private theorem native_matrix_column(a:NativeLie)(i:NamedMode):
    GaussNativeMatter.nativePrimal a*ᵥPi.single (rootIndex i) 1=
      (∑r:Fin 3,(nativeData a).1.val r i.2 • Pi.single (rootIndex (i.1,r)) 1)+
      (nativeData a).2.2.1 • Pi.single (rootIndex i) 1:=by
  rw [←actual_named_column_coordinates]
  change LowEnergy.Quantum.operatorMatrix
    (diracExteriorMotherLieAction (p286LieBlockEmbed (nativeData a)))*ᵥLowEnergy.Quantum.coordinates (namedColumn i)=_
  rw [LowEnergy.Quantum.matrix_action,actual_native_dirac_column,map_add,map_sum]
  simp_rw [map_smul,actual_named_column_coordinates]

private theorem native_matrix_entry(a:NativeLie)(i:NamedMode)(j:LowEnergy.Quantum.Index):
    GaussNativeMatter.nativePrimal a j (rootIndex i)=
      (∑r:Fin 3,(nativeData a).1.val r i.2*(if j=rootIndex (i.1,r) then 1 else 0))+
      (nativeData a).2.2.1*(if j=rootIndex i then 1 else 0):=by
  have h:=congrFun (native_matrix_column a i) j
  simpa only [Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.add_apply] using h

theorem actual_full_native_column(dual:Bool)(a:NativeLie)(i:NamedMode)(j:Mode):
    GaussNativeMatter.nativeFull a j (rootMode dual i)=
      (∑r:Fin 3,colorEntry dual (nativeData a).1 r i.2*(if j=rootMode dual (i.1,r) then 1 else 0))+
      nativeHyper dual a*(if j=rootMode dual i then 1 else 0):=by
  cases dual with
  | false=>
    cases j with
    | inl j=>simpa [GaussNativeMatter.nativeFull,rootMode,colorEntry,nativeHyper] using native_matrix_entry a i j
    | inr j=>simp [GaussNativeMatter.nativeFull,rootMode,colorEntry,nativeHyper]
  | true=>
    cases j with
    | inl j=>simp [GaussNativeMatter.nativeFull,rootMode,colorEntry,nativeHyper]
    | inr j=>
      have h:=congrArg star (native_matrix_entry a i j)
      simpa [GaussNativeMatter.nativeFull,rootMode,colorEntry,nativeHyper,star_add,star_sum,star_mul,apply_ite] using h

private def residualMatrix(a:NativeLie):Matrix Mode Mode ℂ:=
  GaussNativeMatter.nativeFull a-GaussNativeMatter.nativeFull (colorNative (nativeData a).1)
private def residualFock(a:NativeLie):FockFiber→L[ℂ]FockFiber:=GaussQuantumMultiplier.quantized (residualMatrix a)

private theorem residual_column(dual:Bool)(a:NativeLie)(i:NamedMode)(j:Mode):
    residualMatrix a j (rootMode dual i)=nativeHyper dual a*(if j=rootMode dual i then 1 else 0):=by
  rw [residualMatrix,Matrix.sub_apply,actual_full_native_column,actual_full_color_matrix_column]
  ring_nf!

private theorem residual_create(dual:Bool)(a:NativeLie)(i:NamedMode)(x:FockFiber):
    residualFock a (GaussCARHistory.createFiber (rootMode dual i) x)=
      GaussCARHistory.createFiber (rootMode dual i) (residualFock a x)+
      nativeHyper dual a • GaussCARHistory.createFiber (rootMode dual i) x:=by
  apply fiberCoordinates.injective
  have h:=LinearMap.congr_fun
    (LowEnergy.FullQuantum.NativeHistory.CurrentCAR.creation_quantize
      (residualMatrix a) (rootMode dual i)) (fiberCoordinates x)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.sum_apply,LinearMap.smul_apply] at h
  simp_rw [residual_column] at h
  simp only [mul_ite,mul_one,mul_zero,ite_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
  simp only [map_add,map_smul]
  change LowEnergy.Fermion.quantize (residualMatrix a)
      (LowEnergy.Fermion.creation (rootMode dual i) (fiberCoordinates x))=
    LowEnergy.Fermion.creation (rootMode dual i)
      (LowEnergy.Fermion.quantize (residualMatrix a) (fiberCoordinates x))+
      nativeHyper dual a • LowEnergy.Fermion.creation (rootMode dual i) (fiberCoordinates x)
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

private theorem residual_vacuum(dual:Bool)(a:NativeLie):residualFock a (occupationFiber dual ∅)=0:=by
  apply fiberCoordinates.injective
  have hv:fiberCoordinates (occupationFiber dual ∅)=(vacuum:Fock Mode):=by
    funext s
    simp [occupationFiber,occupation,fiberCoordinates,EuclideanSpace.single,QuantizationCheck.Fermion.vacuum,occupationBasis]
  change LowEnergy.Fermion.quantize (residualMatrix a)
    (fiberCoordinates (occupationFiber dual ∅))=fiberCoordinates 0
  rw [hv,map_zero]
  simp only [LowEnergy.Fermion.quantize,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    LowEnergy.Fermion.annihilation_apply,annihilate_vacuum,map_zero,smul_zero,Finset.sum_const_zero]

private theorem residual_triple(dual:Bool)(a:NativeLie)(i j k:NamedMode):
    residualFock a (orderedTriple dual i j k)=(3*nativeHyper dual a) • orderedTriple dual i j k:=by
  rw [orderedTriple,residual_create,residual_create,residual_create,residual_vacuum]
  simp only [map_zero,zero_add,map_add,map_smul]
  module

private theorem residual_return(a:NativeLie):
    residualFock a=GaussNativeMatter.nativeFock a-GaussNativeMatter.nativeFock (colorNative (nativeData a).1):=by
  exact map_sub GaussQuantumMultiplier.quantizer _ _

/-- The complete original P286 charge on the generated epsilon source is its forced three-fold hypercharge. -/
theorem actual_native_epsilon(dual:Bool)(a:NativeLie)(s:SpinTriple):
    GaussNativeMatter.nativeFock a (epsilonFiber dual s)=(3*nativeHyper dual a) • epsilonFiber dual s:=by
  have h:residualFock a (epsilonFiber dual s)=(3*nativeHyper dual a) • epsilonFiber dual s:=by
    simp only [epsilonFiber,epsilonTerm,map_sum,map_smul,residual_triple,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    exact smul_comm _ _ _
  rw [residual_return,_root_.sub_apply,actual_color_epsilon,sub_zero] at h
  exact h

theorem actual_native_normalized_epsilon(dual:Bool)(a:NativeLie)(s:SpinTriple):
    GaussNativeMatter.nativeFock a (normalizedEpsilon dual s)=
      (3*nativeHyper dual a) • normalizedEpsilon dual s:=by
  rw [normalizedEpsilon,map_smul,actual_native_epsilon]
  exact smul_comm _ _ _

private theorem epsilon20_fiber(dual:Bool)(e:Epsilon20):
    wedgeFiber dual (epsilon20Coordinates dual e)=∑s:SpinTriple,e s • normalizedEpsilon dual s:=by
  simp only [epsilon20Coordinates,wedgeFiber,WithLp.ofLp_sum,Finset.sum_apply,
    PiLp.smul_apply,Finset.sum_smul,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [←actual_epsilon_coordinates_return,wedgeFiber,Finset.smul_sum]
  simp only [smul_smul]

/-- Full native connection return on the original normalized epsilon20 fiber, for every native source direction. -/
theorem actual_native_epsilon20(dual:Bool)(a:NativeLie)(e:Epsilon20):
    GaussNativeMatter.nativeFock a (wedgeFiber dual (epsilon20Coordinates dual e))=
      (3*nativeHyper dual a) • wedgeFiber dual (epsilon20Coordinates dual e):=by
  simp only [epsilon20_fiber,map_sum,map_smul,actual_native_normalized_epsilon,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact smul_comm _ _ _

/-- The live inverseL connection coefficient is generated inside the actual Gauss quantum test, not supplied as a scalar-charge premise. -/
theorem actual_epsilon20_connection(dual:Bool)(v:GaussLiveMomentum.Ambient)(e:Epsilon20)
    (f:GaussDensityCore.ScalarTest)(z:SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice):
    GaussCoreDifferential.connection v z (epsilon20Test dual e f z)=
      (3*nativeHyper dual (GaussLiveMomentum.inverseL z v).1) • epsilon20Test dual e f z:=by
  change GaussNativeMatter.nativeFock (GaussLiveMomentum.inverseL z v).1 (epsilon20Test dual e f z)=_
  rw [epsilon20Test,actual_wedge_test_value,map_smul,actual_native_epsilon20]
  exact smul_comm _ _ _

end LowEnergy.NamedColorQtNext
