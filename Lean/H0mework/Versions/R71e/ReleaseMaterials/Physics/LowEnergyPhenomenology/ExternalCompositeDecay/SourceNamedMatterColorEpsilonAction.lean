import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterColorMatrix
import H0mework.Physics.LowEnergy.FullQuantum.NativeHistory.CurrentCAR
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore
open NamedMatterWedgeQt SU7MotherLieAlgebra QuantizationCheck.Fermion
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoreDifferential GaussCoreHilbert GaussDensityCore
open scoped BigOperators InnerProductSpace Matrix ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=SourceRealScalarFock.branchOrder.toDecidableEq

private theorem collapse_column {V:Type*}[AddCommGroup V][Module ℂ V]
    {ι:Type*}[Fintype ι][DecidableEq ι](roots:Fin 3→ι)(b:Fin 3→ℂ)(X:ι→V):
    (∑j:ι,(∑r:Fin 3,b r*(if j=roots r then 1 else 0)) • X j)=∑r:Fin 3,b r • X (roots r):=by
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [mul_ite,mul_one,mul_zero,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

private theorem color_create(A:SU3BlockLieMatrix)(dual:Bool)(i:NamedMode)(x:FockFiber):
    GaussNativeMatter.nativeFock (colorNative A) (GaussCARHistory.createFiber (rootMode dual i) x)=
      GaussCARHistory.createFiber (rootMode dual i) (GaussNativeMatter.nativeFock (colorNative A) x)+
        ∑r:Fin 3,colorEntry dual A r i.2 • GaussCARHistory.createFiber (rootMode dual (i.1,r)) x:=by
  apply fiberCoordinates.injective
  have h:=LinearMap.congr_fun
    (LowEnergy.FullQuantum.NativeHistory.CurrentCAR.creation_quantize
      (GaussNativeMatter.nativeFull (colorNative A)) (rootMode dual i)) (fiberCoordinates x)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.sum_apply,LinearMap.smul_apply] at h
  simp_rw [actual_full_color_matrix_column] at h
  let : DecidableEq Mode:=SourceQuantumConfigurationHilbert.mode_decidableEq
  have hc:=collapse_column (fun r:Fin 3=>rootMode dual (i.1,r))
    (fun r=>colorEntry dual A r i.2)
    (fun j:Mode=>LowEnergy.Fermion.creation j (fiberCoordinates x))
  have hfinal:=h.trans hc
  simp only [map_add,map_sum,map_smul]
  change LowEnergy.Fermion.quantize (GaussNativeMatter.nativeFull (colorNative A))
      (LowEnergy.Fermion.creation (rootMode dual i) (fiberCoordinates x))=
    LowEnergy.Fermion.creation (rootMode dual i)
      (LowEnergy.Fermion.quantize (GaussNativeMatter.nativeFull (colorNative A)) (fiberCoordinates x))+
      ∑r:Fin 3,colorEntry dual A r i.2 • LowEnergy.Fermion.creation (rootMode dual (i.1,r)) (fiberCoordinates x)
  exact sub_eq_iff_eq_add.mp hfinal |>.trans (add_comm _ _)

private theorem color_vacuum(A:SU3BlockLieMatrix)(dual:Bool):
    GaussNativeMatter.nativeFock (colorNative A) (occupationFiber dual ∅)=0:=by
  apply fiberCoordinates.injective
  have hv:fiberCoordinates (occupationFiber dual ∅)=(vacuum:Fock Mode):=by
    funext s
    simp [occupationFiber,occupation,fiberCoordinates,EuclideanSpace.single,vacuum,occupationBasis]
  change LowEnergy.Fermion.quantize (GaussNativeMatter.nativeFull (colorNative A))
    (fiberCoordinates (occupationFiber dual ∅))=fiberCoordinates 0
  rw [hv,map_zero]
  simp only [LowEnergy.Fermion.quantize,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    LowEnergy.Fermion.annihilation_apply,annihilate_vacuum,map_zero,smul_zero,Finset.sum_const_zero]

theorem actual_color_ordered_triple(A:SU3BlockLieMatrix)(dual:Bool)(i j k:NamedMode):
    GaussNativeMatter.nativeFock (colorNative A) (orderedTriple dual i j k)=
      (∑r:Fin 3,colorEntry dual A r i.2 • orderedTriple dual (i.1,r) j k)+
      (∑r:Fin 3,colorEntry dual A r j.2 • orderedTriple dual i (j.1,r) k)+
      (∑r:Fin 3,colorEntry dual A r k.2 • orderedTriple dual i j (k.1,r)):=by
  rw [orderedTriple,color_create,color_create,color_create,color_vacuum]
  simp only [map_zero,zero_add,map_add,map_sum,map_smul,orderedTriple]
  abel

private theorem epsilon_trace {V:Type*}[AddCommGroup V][Module ℂ V]
    (M:Matrix (Fin 3) (Fin 3) ℂ)(T:Fin 3→Fin 3→Fin 3→V):
    (∑p:Fin 6,colorSign p •
      ((∑r:Fin 3,M r (colorPerm p 0) • T r (colorPerm p 1) (colorPerm p 2))+
       (∑r:Fin 3,M r (colorPerm p 1) • T (colorPerm p 0) r (colorPerm p 2))+
       (∑r:Fin 3,M r (colorPerm p 2) • T (colorPerm p 0) (colorPerm p 1) r)))=
      Matrix.trace M • ∑p:Fin 6,colorSign p • T (colorPerm p 0) (colorPerm p 1) (colorPerm p 2):=by
  norm_num [Fin.sum_univ_six,Fin.sum_univ_three,Matrix.trace,Matrix.diag,colorSign,colorPerm]
  simp +decide only [ite_false]
  module

private theorem color_trace_zero(dual:Bool)(A:SU3BlockLieMatrix):Matrix.trace (colorEntry dual A)=0:=by
  cases dual
  · exact A.property.2
  · have h:=congrArg star A.property.2
    simpa only [colorEntry,ite_true,Matrix.trace,Matrix.diag,star_sum,star_zero] using h

/-- The full original 504-mode color action annihilates each actual epsilon CAR source. -/
theorem actual_color_epsilon(A:SU3BlockLieMatrix)(dual:Bool)(s:SpinTriple):
    GaussNativeMatter.nativeFock (colorNative A) (epsilonFiber dual s)=0:=by
  simp only [epsilonFiber,map_sum,map_smul,epsilonTerm,actual_color_ordered_triple]
  have h:=epsilon_trace (colorEntry dual A)
    (fun a b c=>orderedTriple dual (s.val 0,a) (s.val 1,b) (s.val 2,c))
  rw [color_trace_zero,zero_smul] at h
  exact h

theorem actual_color_normalized_epsilon(A:SU3BlockLieMatrix)(dual:Bool)(s:SpinTriple):
    GaussNativeMatter.nativeFock (colorNative A) (normalizedEpsilon dual s)=0:=by
  rw [normalizedEpsilon,map_smul,actual_color_epsilon,smul_zero]

private theorem epsilon20_fiber(dual:Bool)(a:Epsilon20):
    wedgeFiber dual (epsilon20Coordinates dual a)=∑s:SpinTriple,a s • normalizedEpsilon dual s:=by
  simp only [epsilon20Coordinates,wedgeFiber,WithLp.ofLp_sum,Finset.sum_apply,
    PiLp.smul_apply,Finset.sum_smul,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [←actual_epsilon_coordinates_return,wedgeFiber,Finset.smul_sum]
  simp only [smul_smul]

def colorCore(A:SU3BlockLieMatrix):QuantumTest→ₗ[ℂ]QuantumTest:=
  localMultiplier (fun _=>GaussNativeMatter.nativeFock (colorNative A)) (fun _=>contDiffAt_const)

/-- Original mother color invariance reaches every scalar-profile section of the actual normalized ε20 Qt carrier. -/
theorem actual_color_epsilon20_core(A:SU3BlockLieMatrix)(dual:Bool)(a:Epsilon20)(f:ScalarTest):
    colorCore A (epsilon20Test dual a f)=0:=by
  apply DFunLike.ext
  intro z
  change GaussNativeMatter.nativeFock (colorNative A) (epsilon20Test dual a f z)=0
  rw [epsilon20Test,actual_wedge_test_value,epsilon20_fiber,map_smul,map_sum]
  simp only [map_smul,actual_color_normalized_epsilon,smul_zero,Finset.sum_const_zero]

end LowEnergy.NamedColorQtNext
