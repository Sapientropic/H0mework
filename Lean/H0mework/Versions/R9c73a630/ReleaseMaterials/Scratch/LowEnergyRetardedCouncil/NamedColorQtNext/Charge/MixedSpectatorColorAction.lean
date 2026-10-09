import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorColorMatrix
import H0mework.Physics.LowEnergy.FullQuantum.NativeHistory.CurrentCAR
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SaturationMonoid SaturationMonoid.PhysicsCore
open MixedSpectatorCandidate SU7MotherLieAlgebra QuantizationCheck.Fermion
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
        ∑r:Fin 3,colorEntry dual A r i.2.1 • GaussCARHistory.createFiber (rootMode dual (i.1,r,i.2.2)) x:=by
  apply fiberCoordinates.injective
  have h:=LinearMap.congr_fun
    (LowEnergy.FullQuantum.NativeHistory.CurrentCAR.creation_quantize
      (GaussNativeMatter.nativeFull (colorNative A)) (rootMode dual i)) (fiberCoordinates x)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.sum_apply,LinearMap.smul_apply] at h
  simp_rw [actual_full_color_matrix_column] at h
  let : DecidableEq Mode:=SourceQuantumConfigurationHilbert.mode_decidableEq
  have hc:=collapse_column (fun r:Fin 3=>rootMode dual (i.1,r,i.2.2))
    (fun r=>colorEntry dual A r i.2.1)
    (fun j:Mode=>LowEnergy.Fermion.creation j (fiberCoordinates x))
  have hfinal:=h.trans hc
  simp only [map_add,map_sum,map_smul]
  change LowEnergy.Fermion.quantize (GaussNativeMatter.nativeFull (colorNative A))
      (LowEnergy.Fermion.creation (rootMode dual i) (fiberCoordinates x))=
    LowEnergy.Fermion.creation (rootMode dual i)
      (LowEnergy.Fermion.quantize (GaussNativeMatter.nativeFull (colorNative A)) (fiberCoordinates x))+
      ∑r:Fin 3,colorEntry dual A r i.2.1 • LowEnergy.Fermion.creation (rootMode dual (i.1,r,i.2.2)) (fiberCoordinates x)
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
      (∑r:Fin 3,colorEntry dual A r i.2.1 • orderedTriple dual (i.1,r,i.2.2) j k)+
      (∑r:Fin 3,colorEntry dual A r j.2.1 • orderedTriple dual i (j.1,r,j.2.2) k)+
      (∑r:Fin 3,colorEntry dual A r k.2.1 • orderedTriple dual i j (k.1,r,k.2.2)):=by
  rw [orderedTriple,color_create,color_create,color_create,color_vacuum]
  simp only [map_zero,zero_add,map_add,map_sum,map_smul,orderedTriple]
  abel

private theorem epsilon_trace {V:Type*}[AddCommGroup V][Module ℂ V]
    (M:Matrix (Fin 3) (Fin 3) ℂ)(T:Fin 3→Fin 3→Fin 3→V):
    (∑p:Fin 6,NamedMatterWedgeQt.colorSign p •
      ((∑r:Fin 3,M r (NamedMatterWedgeQt.colorPerm p 0) • T r (NamedMatterWedgeQt.colorPerm p 1) (NamedMatterWedgeQt.colorPerm p 2))+
       (∑r:Fin 3,M r (NamedMatterWedgeQt.colorPerm p 1) • T (NamedMatterWedgeQt.colorPerm p 0) r (NamedMatterWedgeQt.colorPerm p 2))+
       (∑r:Fin 3,M r (NamedMatterWedgeQt.colorPerm p 2) • T (NamedMatterWedgeQt.colorPerm p 0) (NamedMatterWedgeQt.colorPerm p 1) r)))=
      Matrix.trace M • ∑p:Fin 6,NamedMatterWedgeQt.colorSign p • T (NamedMatterWedgeQt.colorPerm p 0) (NamedMatterWedgeQt.colorPerm p 1) (NamedMatterWedgeQt.colorPerm p 2):=by
  norm_num [Fin.sum_univ_six,Fin.sum_univ_three,Matrix.trace,Matrix.diag,NamedMatterWedgeQt.colorSign,NamedMatterWedgeQt.colorPerm]
  simp +decide only [ite_false]
  module

private theorem color_trace_zero(dual:Bool)(A:SU3BlockLieMatrix):Matrix.trace (colorEntry dual A)=0:=by
  cases dual
  · exact A.property.2
  · have h:=congrArg star A.property.2
    simpa only [colorEntry,ite_true,Matrix.trace,Matrix.diag,star_sum,star_zero] using h

theorem actual_color_epsilon (A : SU3BlockLieMatrix) (dual : Bool) (spins : Fin 3 → Fin 4) :
    GaussNativeMatter.nativeFock (colorNative A) (epsilon dual spins) = 0 := by
  simp only [epsilon, map_sum, map_smul, actual_color_ordered_triple]
  have h := epsilon_trace (colorEntry dual A)
    (fun a b c => orderedTriple dual (spins 0,a,0) (spins 1,b,0) (spins 2,c,1))
  rw [color_trace_zero, zero_smul] at h
  exact h

theorem actual_candidate_color_singlet (A : SU3BlockLieMatrix) (dual : Bool) :
    GaussNativeMatter.nativeFock (colorNative A) (candidate dual) = 0 := by
  rw [candidate, map_smul, map_sub, actual_color_epsilon, actual_color_epsilon]
  simp

end LowEnergy.MixedSpectatorCandidate
