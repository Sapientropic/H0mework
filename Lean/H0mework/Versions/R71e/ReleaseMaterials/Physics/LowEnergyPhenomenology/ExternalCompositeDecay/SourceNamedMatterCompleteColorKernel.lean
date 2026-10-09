import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterBalancedColorCarrier
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore
open NamedMatterWedgeQt SU7MotherLieAlgebra
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace Matrix

def mixingMatrix(k:Fin 2):Matrix (Fin 3) (Fin 3) ℂ:=
  fun r c=>if k=0 then (if r=0 ∧ c=1 then 1 else if r=1 ∧ c=0 then -1 else 0)
    else (if r=1 ∧ c=2 then 1 else if r=2 ∧ c=1 then -1 else 0)
def sourceMixing(k:Fin 2):SU3BlockLieMatrix:=⟨mixingMatrix k,by
  constructor
  · ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      norm_num [mixingMatrix,Matrix.star_apply] <;> simp +decide
  · fin_cases k <;> norm_num [mixingMatrix,Matrix.trace,Matrix.diag,Fin.sum_univ_three] <;> simp +decide⟩

private theorem mixing_entry(dual:Bool)(k:Fin 2)(r c:Fin 3):
    colorEntry dual (sourceMixing k) r c=mixingMatrix k r c:=by
  cases dual <;> fin_cases k <;> fin_cases r <;> fin_cases c <;>
    norm_num [colorEntry,sourceMixing,mixingMatrix] <;> simp +decide

theorem actual_mixing_zero(dual:Bool)(t:ColorSpinAssignment):
    GaussNativeMatter.nativeFock (colorNative (sourceMixing 0)) (balancedFiber dual t)=
      orderedTriple dual (t 0,0) (t 1,0) (t 2,2)-
      orderedTriple dual (t 0,1) (t 1,1) (t 2,2):=by
  rw [balancedFiber,actual_color_ordered_triple]
  simp only [mixing_entry]
  norm_num [mixingMatrix,Fin.sum_univ_three]
  simp +decide only [ite_false,add_zero]
  abel

theorem actual_mixing_one(dual:Bool)(t:ColorSpinAssignment):
    GaussNativeMatter.nativeFock (colorNative (sourceMixing 1)) (balancedFiber dual t)=
      orderedTriple dual (t 0,0) (t 1,1) (t 2,1)-
      orderedTriple dual (t 0,0) (t 1,2) (t 2,2):=by
  rw [balancedFiber,actual_color_ordered_triple]
  simp only [mixing_entry]
  norm_num [mixingMatrix,Fin.sum_univ_three]
  simp +decide only [ite_false,add_zero,zero_add]
  abel

private def spinK(x y:Fin 4):ℂ:=if x=y then 1 else 0
private theorem delta_split(x y:Fin 4)(c d:Fin 3):
    delta (x,c) (y,d)=if c=d then spinK x y else 0:=by
  by_cases h:c=d <;> simp [delta,spinK,Prod.mk.injEq,h]
private theorem assignment_delta(x y z:Fin 4)(t:ColorSpinAssignment):
    spinK x (t 0)*spinK y (t 1)*spinK z (t 2)=if t=![x,y,z] then 1 else 0:=by
  have he:t=![x,y,z] ↔ t 0=x ∧ t 1=y ∧ t 2=z:=by
    simp [funext_iff,Fin.forall_fin_succ]
  simp only [he]
  by_cases h0:t 0=x <;> by_cases h1:t 1=y <;> by_cases h2:t 2=z <;>
    simp_all [spinK,eq_comm]

private theorem mixing_pair_zero(dual:Bool)(x y z:Fin 4)(t:ColorSpinAssignment):
    inner ℂ (orderedTriple dual (x,0) (y,0) (z,2))
      (GaussNativeMatter.nativeFock (colorNative (sourceMixing 0)) (balancedFiber dual t))=
      (if t=![x,y,z] then 1 else 0)-(if t=![y,x,z] then 1 else 0):=by
  rw [actual_mixing_zero,inner_sub_right,actual_ordered_triple_pair,actual_ordered_triple_pair]
  simp +decide only [tripleGram,delta_split,ite_true,ite_false,
    zero_mul,mul_zero,sub_zero,add_zero]
  rw [←assignment_delta,←assignment_delta]
  ring

private theorem mixing_pair_one(dual:Bool)(x y z:Fin 4)(t:ColorSpinAssignment):
    inner ℂ (orderedTriple dual (x,0) (y,1) (z,1))
      (GaussNativeMatter.nativeFock (colorNative (sourceMixing 1)) (balancedFiber dual t))=
      (if t=![x,y,z] then 1 else 0)-(if t=![x,z,y] then 1 else 0):=by
  rw [actual_mixing_one,inner_sub_right,actual_ordered_triple_pair,actual_ordered_triple_pair]
  simp +decide only [tripleGram,delta_split,ite_true,ite_false,
    zero_mul,mul_zero,sub_zero,add_zero]
  rw [←assignment_delta,←assignment_delta]
  ring

/-- The two original off-diagonal mother generators force the actual balanced coefficients to be symmetric. -/
theorem actual_color_kernel_spin_symmetry(dual:Bool)(b:BalancedFiber)
    (h:∀A:SU3BlockLieMatrix,GaussNativeMatter.nativeFock (colorNative A) (balancedLift dual b)=0):
    (∀x y z:Fin 4,b ![x,y,z]=b ![y,x,z]) ∧
    (∀x y z:Fin 4,b ![x,y,z]=b ![x,z,y]):=by
  classical
  constructor
  · intro x y z
    have he:=congrArg (fun v:FockFiber=>inner ℂ (orderedTriple dual (x,0) (y,0) (z,2)) v)
      (h (sourceMixing 0))
    simp only [inner_zero_right] at he
    change inner ℂ _ (GaussNativeMatter.nativeFock _ (∑t,b t • balancedFiber dual t))=0 at he
    simp only [map_sum,map_smul,inner_sum,inner_smul_right,mixing_pair_zero] at he
    simp only [mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true] at he
    exact sub_eq_zero.mp he
  · intro x y z
    have he:=congrArg (fun v:FockFiber=>inner ℂ (orderedTriple dual (x,0) (y,1) (z,1)) v)
      (h (sourceMixing 1))
    simp only [inner_zero_right] at he
    change inner ℂ _ (GaussNativeMatter.nativeFock _ (∑t,b t • balancedFiber dual t))=0 at he
    simp only [map_sum,map_smul,inner_sum,inner_smul_right,mixing_pair_one] at he
    simp only [mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true] at he
    exact sub_eq_zero.mp he

def symmetricCarrier:Submodule ℂ BalancedFiber where
  carrier:={b | (∀x y z:Fin 4,b ![x,y,z]=b ![y,x,z]) ∧
    (∀x y z:Fin 4,b ![x,y,z]=b ![x,z,y])}
  zero_mem':=by simp
  add_mem' ha hb:=by
    constructor
    · intro x y z
      simp only [PiLp.add_apply,ha.1 x y z,hb.1 x y z]
    · intro x y z
      simp only [PiLp.add_apply,ha.2 x y z,hb.2 x y z]
  smul_mem' c b hb:=by
    constructor
    · intro x y z
      simp only [PiLp.smul_apply,hb.1 x y z]
    · intro x y z
      simp only [PiLp.smul_apply,hb.2 x y z]

private theorem assignment_eta(t:ColorSpinAssignment):![t 0,t 1,t 2]=t:=by
  funext i
  fin_cases i <;> rfl

private theorem symmetric_permutation(b:BalancedFiber)(hb:b∈symmetricCarrier)
    (t:ColorSpinAssignment)(p:Fin 6):b (fun i=>t (colorPerm p i))=b t:=by
  rw [←assignment_eta (fun i=>t (colorPerm p i))]
  conv_rhs=>rw [←assignment_eta t]
  fin_cases p
  · rfl
  · exact hb.2 _ _ _
  · exact hb.1 _ _ _
  · exact (hb.2 _ _ _).trans (hb.1 _ _ _)
  · exact (hb.1 _ _ _).trans (hb.2 _ _ _)
  · exact (hb.1 _ _ _).trans ((hb.2 _ _ _).trans (hb.1 _ _ _))

private theorem sorted_permutation:∀t:ColorSpinAssignment,∃p:Fin 6,
    t (colorPerm p 0)≤t (colorPerm p 1) ∧ t (colorPerm p 1)≤t (colorPerm p 2):=by decide

private def sortedEvaluation:symmetricCarrier→ₗ[ℂ]Epsilon20 where
  toFun b:=WithLp.toLp 2 (fun s:SpinTriple=>b.val s.val)
  map_add' a b:=by rfl
  map_smul' c a:=by rfl

private theorem sorted_evaluation_injective:Function.Injective sortedEvaluation:=by
  intro a b hab
  apply Subtype.ext
  apply PiLp.ext
  intro t
  obtain ⟨p,hp⟩:=sorted_permutation t
  let s:SpinTriple:=⟨fun i=>t (colorPerm p i),hp⟩
  have he:=congrArg (fun v:Epsilon20=>v s) hab
  change a.val s.val=b.val s.val at he
  rw [symmetric_permutation a.val a.property t p,
    symmetric_permutation b.val b.property t p] at he
  exact he

/-- The original off-diagonal constraints generate a twenty-dimensional upper bound internally. -/
theorem actual_symmetric_finrank_le:Module.finrank ℂ symmetricCarrier≤20:=by
  have h:=LinearMap.finrank_le_finrank_of_injective sorted_evaluation_injective
  simpa only [Epsilon20,finrank_euclideanSpace,actual_spin_triple_card] using h

private def normalizedBalanced(dual:Bool)(s:SpinTriple):BalancedFiber:=
  Classical.choose (actual_color_kernel_balanced_carrier dual (epsilonCoordinates dual s)
    (by intro A; rw [actual_epsilon_coordinates_return,actual_color_normalized_epsilon]))

private theorem normalized_balanced_return(dual:Bool)(s:SpinTriple):
    balancedLift dual (normalizedBalanced dual s)=normalizedEpsilon dual s:=by
  have h:=Classical.choose_spec (actual_color_kernel_balanced_carrier dual (epsilonCoordinates dual s)
    (by intro A; rw [actual_epsilon_coordinates_return,actual_color_normalized_epsilon]))
  exact h.trans (actual_epsilon_coordinates_return dual s)

private theorem normalized_balanced_pair(dual:Bool)(s t:SpinTriple):
    inner ℂ (normalizedBalanced dual s) (normalizedBalanced dual t)=if s=t then 1 else 0:=by
  rw [←actual_balanced_lift_pair dual,normalized_balanced_return,normalized_balanced_return,
    actual_normalized_epsilon_pair]

def epsilonBalancedLift(dual:Bool):Epsilon20→ₗ[ℂ]BalancedFiber where
  toFun a:=∑s:SpinTriple,a s • normalizedBalanced dual s
  map_add' a b:=by simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c a:=by simp only [PiLp.smul_apply,smul_eq_mul,smul_smul,Finset.smul_sum,RingHom.id_apply]

private theorem epsilon_balanced_lift_pair(dual:Bool)(a b:Epsilon20):
    inner ℂ (epsilonBalancedLift dual a) (epsilonBalancedLift dual b)=inner ℂ a b:=by
  classical
  change inner ℂ (∑s,a s • normalizedBalanced dual s) (∑t,b t • normalizedBalanced dual t)=_
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,normalized_balanced_pair,starRingEnd_apply]
  simp [mul_ite,PiLp.inner_apply,RCLike.inner_apply,mul_comm]

private theorem epsilon_balanced_injective(dual:Bool):Function.Injective (epsilonBalancedLift dual):=by
  intro a b hab
  have h:inner ℂ (a-b) (a-b)=0:=by
    rw [←epsilon_balanced_lift_pair dual,map_sub,hab,sub_self,inner_zero_left]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h)

private theorem epsilon_balanced_kernel(dual:Bool)(a:Epsilon20)(A:SU3BlockLieMatrix):
    GaussNativeMatter.nativeFock (colorNative A) (balancedLift dual (epsilonBalancedLift dual a))=0:=by
  change GaussNativeMatter.nativeFock (colorNative A)
    (balancedLift dual (∑s:SpinTriple,a s • normalizedBalanced dual s))=0
  simp only [map_sum,map_smul,normalized_balanced_return,actual_color_normalized_epsilon,
    smul_zero,Finset.sum_const_zero]

/-- The actual twenty epsilon columns exhaust the symmetric carrier; no rank or projector is supplied. -/
theorem actual_epsilon_balanced_range(dual:Bool):LinearMap.range (epsilonBalancedLift dual)=symmetricCarrier:=by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro b ⟨a,rfl⟩
    exact actual_color_kernel_spin_symmetry dual _ (epsilon_balanced_kernel dual a)
  · rw [LinearMap.finrank_range_of_inj (epsilon_balanced_injective dual)]
    simpa only [Epsilon20,finrank_euclideanSpace,actual_spin_triple_card] using actual_symmetric_finrank_le

private theorem epsilon_fiber_return(dual:Bool)(a:Epsilon20):
    balancedLift dual (epsilonBalancedLift dual a)=wedgeFiber dual (epsilon20Coordinates dual a):=by
  change balancedLift dual (∑s:SpinTriple,a s • normalizedBalanced dual s)=_
  simp only [map_sum,map_smul,normalized_balanced_return]
  symm
  simp only [epsilon20Coordinates,wedgeFiber,WithLp.ofLp_sum,Finset.sum_apply,
    PiLp.smul_apply,Finset.sum_smul,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [←actual_epsilon_coordinates_return,wedgeFiber,Finset.smul_sum]
  simp only [smul_smul]

/-- The complete original mother-color kernel on all 220 named occupations is exactly the generated epsilon20 source. -/
theorem actual_complete_color_kernel(dual:Bool)(a:WedgeFiber):
    (∀A:SU3BlockLieMatrix,GaussNativeMatter.nativeFock (colorNative A) (wedgeFiber dual a)=0) ↔
    ∃b:Epsilon20,wedgeFiber dual a=wedgeFiber dual (epsilon20Coordinates dual b):=by
  constructor
  · intro h
    obtain ⟨b,hb⟩:=actual_color_kernel_balanced_carrier dual a h
    have hs:b∈symmetricCarrier:=actual_color_kernel_spin_symmetry dual b (by intro A; rw [hb,h])
    rw [←actual_epsilon_balanced_range dual] at hs
    obtain ⟨c,hc⟩:=hs
    refine ⟨c,?_⟩
    rw [←hb,←hc,epsilon_fiber_return]
  · rintro ⟨b,hb⟩ A
    rw [hb,←epsilon_fiber_return]
    exact epsilon_balanced_kernel dual b A

end LowEnergy.NamedColorQtNext
