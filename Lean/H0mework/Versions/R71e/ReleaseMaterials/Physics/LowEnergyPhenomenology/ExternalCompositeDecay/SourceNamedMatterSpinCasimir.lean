import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterSpinCoefficient
import Mathlib.LinearAlgebra.Trace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore NamedMatterWedgeQt
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace Matrix

def exchangedSpin(x y:Fin 4):Fin 4:=⟨2*(x.val/2)+y.val%2,by omega⟩

private theorem rotation_row_0(dual:Bool)(x:Fin 4)(f:Fin 4→ℂ):
    (∑r:Fin 4,rotationEntry dual 0 x r*f r)=((if dual then 1 else -1)/2:ℂ)*f (flipSpin x):=by
  cases dual <;> fin_cases x <;>
    norm_num [rotationEntry,flipSpin,bitSign,Fin.sum_univ_four,
      Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three] <;>
    (try simp +decide)

private theorem rotation_row_1(dual:Bool)(x:Fin 4)(f:Fin 4→ℂ):
    (∑r:Fin 4,rotationEntry dual 1 x r*f r)=(Complex.I/2)*(bitSign x:ℂ)*f (flipSpin x):=by
  cases dual <;> fin_cases x <;>
    norm_num [rotationEntry,flipSpin,bitSign,Fin.sum_univ_four,
      Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three] <;>
    (try simp +decide) <;> ring

private theorem rotation_row_2(dual:Bool)(x:Fin 4)(f:Fin 4→ℂ):
    (∑r:Fin 4,rotationEntry dual 2 x r*f r)=((if dual then 1 else -1)/2:ℂ)*(bitSign x:ℂ)*f x:=by
  cases dual <;> fin_cases x <;>
    norm_num [rotationEntry,flipSpin,bitSign,Fin.sum_univ_four,
      Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three] <;>
    (try simp +decide)

private theorem same_slot_contraction(dual:Bool)(x:Fin 4)(f:Fin 4→ℂ):
    (∑k:Fin 3,∑r:Fin 4,∑s:Fin 4,
      rotationEntry dual k x r*rotationEntry dual k r s*f s)=(3/4:ℂ)*f x:=by
  simp only [Fin.sum_univ_three,mul_assoc,←Finset.mul_sum,
    rotation_row_0,rotation_row_1,rotation_row_2]
  cases dual <;> fin_cases x <;>
    norm_num [flipSpin,bitSign,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring!

private theorem two_slot_contraction(dual:Bool)(x y:Fin 4)(f:Fin 4→Fin 4→ℂ):
    (∑k:Fin 3,∑r:Fin 4,∑s:Fin 4,
      rotationEntry dual k x r*rotationEntry dual k y s*f r s)=
      (1/2:ℂ)*f (exchangedSpin x y) (exchangedSpin y x)-(1/4:ℂ)*f x y:=by
  simp only [Fin.sum_univ_three,mul_assoc,←Finset.mul_sum,
    rotation_row_0,rotation_row_1,rotation_row_2]
  cases dual <;> fin_cases x <;> fin_cases y <;>
    norm_num [flipSpin,bitSign,exchangedSpin,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring!

def spinCasimir(dual:Bool):BalancedFiber→ₗ[ℂ]BalancedFiber:=
  ∑k:Fin 3,spinBalancedAction dual (rotationAxis k)*spinBalancedAction dual (rotationAxis k)

/-- The original three rotation currents give the exact spin-bit exchange Casimir on the entire balanced carrier. -/
theorem actual_spin_casimir_row(dual:Bool)(b:BalancedFiber)(x y z:Fin 4):
    spinCasimir dual b ![x,y,z]=(3/4:ℂ)*b ![x,y,z]+
      b ![exchangedSpin x y,exchangedSpin y x,z]+
      b ![exchangedSpin x z,y,exchangedSpin z x]+
      b ![x,exchangedSpin y z,exchangedSpin z y]:=by
  change (∑k:Fin 3,spinBalancedAction dual (rotationAxis k)
    (spinBalancedAction dual (rotationAxis k) b)) ![x,y,z]=_
  simp only [WithLp.ofLp_sum,Finset.sum_apply,actual_spin_row,actual_rotation_entry]
  simp only [Finset.mul_sum,mul_add,Finset.sum_add_distrib,←mul_assoc]
  simp only [same_slot_contraction,two_slot_contraction]
  ring

def spinExchange(p:Fin 3)(t:ColorSpinAssignment):ColorSpinAssignment:=
  if p=0 then ![exchangedSpin (t 0) (t 1),exchangedSpin (t 1) (t 0),t 2]
  else if p=1 then ![exchangedSpin (t 0) (t 2),t 1,exchangedSpin (t 2) (t 0)]
  else ![t 0,exchangedSpin (t 1) (t 2),exchangedSpin (t 2) (t 1)]

private theorem assignment_eta(t:ColorSpinAssignment):![t 0,t 1,t 2]=t:=by
  funext p
  fin_cases p <;> rfl

theorem actual_spin_casimir_coefficient(dual:Bool)(b:BalancedFiber)(t:ColorSpinAssignment):
    spinCasimir dual b t=(3/4:ℂ)*b t+∑p:Fin 3,b (spinExchange p t):=by
  conv_lhs=>rw [←assignment_eta t]
  rw [actual_spin_casimir_row]
  simp +decide only [Fin.sum_univ_three,spinExchange,ite_true,ite_false]
  rw [assignment_eta]
  ring

private theorem exchange_word_permutation:∀t:ColorSpinAssignment,
    [spinExchange 0 (spinExchange 0 t),spinExchange 1 (spinExchange 0 t),spinExchange 2 (spinExchange 0 t),
     spinExchange 0 (spinExchange 1 t),spinExchange 1 (spinExchange 1 t),spinExchange 2 (spinExchange 1 t),
     spinExchange 0 (spinExchange 2 t),spinExchange 1 (spinExchange 2 t),spinExchange 2 (spinExchange 2 t)].Perm
    [spinExchange 0 t,spinExchange 1 t,spinExchange 2 t,
     spinExchange 0 t,spinExchange 1 t,spinExchange 2 t,
     spinExchange 0 t,spinExchange 1 t,spinExchange 2 t]:=by decide

private theorem exchange_square(b:BalancedFiber)(t:ColorSpinAssignment):
    (∑p:Fin 3,∑q:Fin 3,b (spinExchange q (spinExchange p t)))=
      (3:ℂ)*(∑p:Fin 3,b (spinExchange p t)):=by
  have h:=List.Perm.sum_eq ((exchange_word_permutation t).map (fun u=>b u))
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at h
  simp only [Fin.sum_univ_three]
  linear_combination h

/-- This full source Casimir polynomial is generated from the literal gamma/CAR action, before any spin projection. -/
theorem actual_spin_casimir_polynomial(dual:Bool)(b:BalancedFiber):
    spinCasimir dual (spinCasimir dual b)-(9/2:ℂ) • spinCasimir dual b+(45/16:ℂ) • b=0:=by
  apply PiLp.ext
  intro t
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,
    actual_spin_casimir_coefficient]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  rw [exchange_square]
  ring

/-- Sorting is a coordinate evaluation on the same symmetric carrier, not normalized epsilon coordinates. -/
def sortedSpin(t:ColorSpinAssignment):SpinTriple:=
  if h01:t 0≤t 1 then
    if h12:t 1≤t 2 then ⟨![t 0,t 1,t 2],h01,h12⟩
    else if h02:t 0≤t 2 then ⟨![t 0,t 2,t 1],h02,by change t 2≤t 1; omega⟩
    else ⟨![t 2,t 0,t 1],by change t 2≤t 0; omega,h01⟩
  else if h02:t 0≤t 2 then ⟨![t 1,t 0,t 2],by change t 1≤t 0; omega,h02⟩
  else if h12:t 1≤t 2 then ⟨![t 1,t 2,t 0],h12,by change t 2≤t 0; omega⟩
  else ⟨![t 2,t 1,t 0],by change t 2≤t 1; omega,by change t 1≤t 0; omega⟩

private theorem sorted_spin_self:∀s:SpinTriple,sortedSpin s.val=s:=by decide
private theorem sorted_spin_swap_zero:∀x y z:Fin 4,sortedSpin ![x,y,z]=sortedSpin ![y,x,z]:=by decide
private theorem sorted_spin_swap_one:∀x y z:Fin 4,sortedSpin ![x,y,z]=sortedSpin ![x,z,y]:=by decide
private theorem sorted_spin_permutation:∀t:ColorSpinAssignment,∃p:Fin 6,
    (sortedSpin t).val=(fun i=>t (colorPerm p i)):=by decide

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

private theorem symmetric_sorted_value(b:BalancedFiber)(hb:b∈symmetricCarrier)(t:ColorSpinAssignment):
    b (sortedSpin t).val=b t:=by
  obtain ⟨p,hp⟩:=sorted_spin_permutation t
  rw [hp]
  exact symmetric_permutation b hb t p

abbrev SortedSpinFiber:=EuclideanSpace ℂ SpinTriple
def sortedSpinLift:SortedSpinFiber→ₗ[ℂ]BalancedFiber where
  toFun a:=WithLp.toLp 2 (fun t=>a (sortedSpin t))
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
def sortedSpinRead:BalancedFiber→ₗ[ℂ]SortedSpinFiber where
  toFun b:=WithLp.toLp 2 (fun s=>b s.val)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

private theorem sorted_lift_symmetric(a:SortedSpinFiber):sortedSpinLift a∈symmetricCarrier:=by
  constructor
  · intro x y z
    change a (sortedSpin ![x,y,z])=a (sortedSpin ![y,x,z])
    rw [sorted_spin_swap_zero]
  · intro x y z
    change a (sortedSpin ![x,y,z])=a (sortedSpin ![x,z,y])
    rw [sorted_spin_swap_one]
private theorem sorted_read_lift(a:SortedSpinFiber):sortedSpinRead (sortedSpinLift a)=a:=by
  apply PiLp.ext
  intro s
  change a (sortedSpin s.val)=a s
  rw [sorted_spin_self]
private theorem sorted_lift_read(b:BalancedFiber)(hb:b∈symmetricCarrier):sortedSpinLift (sortedSpinRead b)=b:=by
  apply PiLp.ext
  intro t
  exact symmetric_sorted_value b hb t

private theorem casimir_symmetric(dual:Bool)(b:BalancedFiber)(hb:b∈symmetricCarrier):
    spinCasimir dual b∈symmetricCarrier:=by
  change (∑k:Fin 3,spinBalancedAction dual (rotationAxis k) (spinBalancedAction dual (rotationAxis k) b))∈_
  apply Submodule.sum_mem
  intro k _
  exact actual_spin_symmetric dual _ _ (actual_spin_symmetric dual _ b hb)

def sortedSpinCasimir:SortedSpinFiber→ₗ[ℂ]SortedSpinFiber where
  toFun a:=WithLp.toLp 2 (fun s=>(3/4:ℂ)*a s+∑p:Fin 3,a (sortedSpin (spinExchange p s.val)))
  map_add' a b:=by
    apply PiLp.ext
    intro s
    simp only [PiLp.add_apply,mul_add,Finset.sum_add_distrib]
    ring
  map_smul' c a:=by
    apply PiLp.ext
    intro s
    simp only [PiLp.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [←Finset.mul_sum]
    ring

private theorem sorted_casimir_read(dual:Bool)(a:SortedSpinFiber):
    sortedSpinRead (spinCasimir dual (sortedSpinLift a))=sortedSpinCasimir a:=by
  apply PiLp.ext
  intro s
  change spinCasimir dual (sortedSpinLift a) s.val=_
  rw [actual_spin_casimir_coefficient]
  change (3/4:ℂ)*a (sortedSpin s.val)+(∑p:Fin 3,a (sortedSpin (spinExchange p s.val)))=_
  rw [sorted_spin_self]
  rfl

/-- The twenty-coordinate Casimir is returned by the same original spin operator, in both branches. -/
theorem actual_sorted_casimir_return(dual:Bool)(a:SortedSpinFiber):
    spinCasimir dual (sortedSpinLift a)=sortedSpinLift (sortedSpinCasimir a):=by
  rw [←sorted_casimir_read dual a]
  exact (sorted_lift_read _ (casimir_symmetric dual _ (sorted_lift_symmetric a))).symm

private theorem sorted_casimir_polynomial(a:SortedSpinFiber):
    sortedSpinCasimir (sortedSpinCasimir a)-(9/2:ℂ) • sortedSpinCasimir a+(45/16:ℂ) • a=0:=by
  have h:=congrArg sortedSpinRead (actual_spin_casimir_polynomial false (sortedSpinLift a))
  simpa only [actual_sorted_casimir_return,map_add,map_sub,map_smul,map_zero,sorted_read_lift] using h

def sortedSpinHalf:SortedSpinFiber→ₗ[ℂ]SortedSpinFiber:=(5/4:ℂ) • 1-(1/3:ℂ) • sortedSpinCasimir
def sortedSpinThreeHalf:SortedSpinFiber→ₗ[ℂ]SortedSpinFiber:=1-sortedSpinHalf

theorem actual_sorted_spin_half_idempotent:IsIdempotentElem sortedSpinHalf:=by
  apply LinearMap.ext
  intro a
  apply PiLp.ext
  intro s
  have h:=congrArg (fun b:SortedSpinFiber=>b s) (sorted_casimir_polynomial a)
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul] at h
  simp only [sortedSpinHalf,Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply,map_sub,map_smul,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
  linear_combination (1/9:ℂ)*h

theorem actual_sorted_spin_three_half_idempotent:IsIdempotentElem sortedSpinThreeHalf:=by
  change (1-sortedSpinHalf)*(1-sortedSpinHalf)=1-sortedSpinHalf
  have h:=actual_sorted_spin_half_idempotent
  change sortedSpinHalf*sortedSpinHalf=sortedSpinHalf at h
  noncomm_ring [h]

private theorem source_exchange_trace:
    (∑s:SpinTriple,∑p:Fin 3,if sortedSpin (spinExchange p s.val)=s then (1:ℤ) else 0)=48:=by decide

private theorem sorted_trace(L:SortedSpinFiber→ₗ[ℂ]SortedSpinFiber):
    LinearMap.trace ℂ SortedSpinFiber L=∑s:SpinTriple,(L (EuclideanSpace.single s 1)) s:=by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun SpinTriple ℂ).toBasis]
  simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply]
  change (∑s:SpinTriple,L (EuclideanSpace.basisFun SpinTriple ℂ s) s)=_
  simp only [EuclideanSpace.basisFun_apply]

/-- The exact trace is calculated from the original spin-bit exchange word on all twenty sorted source assignments. -/
theorem actual_sorted_casimir_trace:LinearMap.trace ℂ SortedSpinFiber sortedSpinCasimir=63:=by
  rw [sorted_trace]
  have h:(∑s:SpinTriple,∑p:Fin 3,if sortedSpin (spinExchange p s.val)=s then (1:ℂ) else 0)=48:=by
    exact_mod_cast source_exchange_trace
  change (∑s:SpinTriple,((3/4:ℂ)*(EuclideanSpace.single s (1:ℂ)) s+
    ∑p:Fin 3,(EuclideanSpace.single s (1:ℂ)) (sortedSpin (spinExchange p s.val))))=63
  simp only [PiLp.single_apply,ite_true,mul_one,Finset.sum_add_distrib]
  rw [h]
  norm_num [actual_spin_triple_card]

theorem actual_sorted_spin_multiplicities:
    Module.finrank ℂ (LinearMap.range sortedSpinHalf)=4 ∧
    Module.finrank ℂ (LinearMap.range sortedSpinThreeHalf)=16:=by
  have ht:LinearMap.trace ℂ SortedSpinFiber sortedSpinHalf=4:=by
    simp only [sortedSpinHalf,map_sub,map_smul,Module.End.one_eq_id,LinearMap.trace_id,
      finrank_euclideanSpace,actual_spin_triple_card,actual_sorted_casimir_trace]
    norm_num
  have hu:LinearMap.trace ℂ SortedSpinFiber sortedSpinThreeHalf=16:=by
    simp only [sortedSpinThreeHalf,map_sub,Module.End.one_eq_id,LinearMap.trace_id,
      finrank_euclideanSpace,actual_spin_triple_card,ht]
    norm_num
  constructor
  · have h:=(LinearMap.IsIdempotentElem.isProj_range _ actual_sorted_spin_half_idempotent).trace
    rw [ht] at h
    exact_mod_cast h.symm
  · have h:=(LinearMap.IsIdempotentElem.isProj_range _ actual_sorted_spin_three_half_idempotent).trace
    rw [hu] at h
    exact_mod_cast h.symm

def originalSpinCasimir:FockFiber→L[ℂ]FockFiber:=
  ∑k:Fin 3,GaussQuantumMultiplier.quantized (GaussCoframeSpin.full (rotationAxis k))*
    GaussQuantumMultiplier.quantized (GaussCoframeSpin.full (rotationAxis k))
def sortedOriginalSource(dual:Bool):SortedSpinFiber→ₗ[ℂ]FockFiber:=(balancedLift dual).comp sortedSpinLift
def originalSpinHalfSource(dual:Bool):SortedSpinFiber→ₗ[ℂ]FockFiber:=(sortedOriginalSource dual).comp sortedSpinHalf
def originalSpinThreeHalfSource(dual:Bool):SortedSpinFiber→ₗ[ℂ]FockFiber:=(sortedOriginalSource dual).comp sortedSpinThreeHalf

/-- The generated sorted source fills the same complete symmetric/color kernel carrier. -/
theorem actual_sorted_source_range(dual:Bool):
    LinearMap.range (sortedOriginalSource dual)=symmetricCarrier.map (balancedLift dual):=by
  have h:LinearMap.range sortedSpinLift=symmetricCarrier:=by
    apply le_antisymm
    · rintro b ⟨a,rfl⟩
      exact sorted_lift_symmetric a
    · intro b hb
      exact ⟨sortedSpinRead b,sorted_lift_read b hb⟩
  rw [sortedOriginalSource,LinearMap.range_comp,h]

private theorem sorted_source_injective(dual:Bool):Function.Injective (sortedOriginalSource dual):=by
  intro a b hab
  change balancedLift dual (sortedSpinLift a)=balancedLift dual (sortedSpinLift b) at hab
  have h:inner ℂ (sortedSpinLift a-sortedSpinLift b) (sortedSpinLift a-sortedSpinLift b)=0:=by
    rw [←actual_balanced_lift_pair dual,map_sub,hab,sub_self,inner_zero_left]
  have he:=congrArg sortedSpinRead (sub_eq_zero.mp (inner_self_eq_zero.mp h))
  simpa only [sorted_read_lift] using he

/-- Exact original full504 CAR Casimir return, before any projection. -/
theorem actual_original_spin_casimir_return(dual:Bool)(a:SortedSpinFiber):
    originalSpinCasimir (sortedOriginalSource dual a)=sortedOriginalSource dual (sortedSpinCasimir a):=by
  simp only [originalSpinCasimir,_root_.sum_apply,mul_apply_eq_comp]
  change (∑k:Fin 3,GaussQuantumMultiplier.quantized (GaussCoframeSpin.full (rotationAxis k))
    (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full (rotationAxis k))
      (balancedLift dual (sortedSpinLift a))))=_
  simp only [actual_spin_balanced_source]
  rw [←map_sum]
  change balancedLift dual (spinCasimir dual (sortedSpinLift a))=_
  rw [actual_sorted_casimir_return]
  rfl

private theorem sorted_half_eigen(a:SortedSpinFiber):
    sortedSpinCasimir (sortedSpinHalf a)=(3/4:ℂ) • sortedSpinHalf a:=by
  apply PiLp.ext
  intro s
  have h:=congrArg (fun b:SortedSpinFiber=>b s) (sorted_casimir_polynomial a)
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul] at h
  simp only [sortedSpinHalf,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    map_sub,map_smul,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
  linear_combination (-1/3:ℂ)*h

private theorem sorted_three_half_eigen(a:SortedSpinFiber):
    sortedSpinCasimir (sortedSpinThreeHalf a)=(15/4:ℂ) • sortedSpinThreeHalf a:=by
  rw [sortedSpinThreeHalf,LinearMap.sub_apply,Module.End.one_apply,map_sub,sorted_half_eigen]
  apply PiLp.ext
  intro s
  simp only [sortedSpinHalf,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
  ring

/-- Both source branches carry the original Casimir eigenvalues and retain the full complementary twenty-dimensional source. -/
theorem actual_original_spin_spectral_split(dual:Bool)(a:SortedSpinFiber):
    originalSpinCasimir (originalSpinHalfSource dual a)=(3/4:ℂ) • originalSpinHalfSource dual a ∧
    originalSpinCasimir (originalSpinThreeHalfSource dual a)=(15/4:ℂ) • originalSpinThreeHalfSource dual a ∧
    originalSpinHalfSource dual a+originalSpinThreeHalfSource dual a=sortedOriginalSource dual a:=by
  constructor
  · change originalSpinCasimir (sortedOriginalSource dual (sortedSpinHalf a))=_
    rw [actual_original_spin_casimir_return,sorted_half_eigen,map_smul]
    rfl
  constructor
  · change originalSpinCasimir (sortedOriginalSource dual (sortedSpinThreeHalf a))=_
    rw [actual_original_spin_casimir_return,sorted_three_half_eigen,map_smul]
    rfl
  · change sortedOriginalSource dual (sortedSpinHalf a)+
      sortedOriginalSource dual (sortedSpinThreeHalf a)=_
    rw [←map_add,sortedSpinThreeHalf,LinearMap.sub_apply,Module.End.one_apply,add_sub_cancel]

/-- The four and sixteen dimensions are those of the actual original mother-Fock source ranges. -/
theorem actual_original_spin_multiplicities(dual:Bool):
    Module.finrank ℂ (LinearMap.range (originalSpinHalfSource dual))=4 ∧
    Module.finrank ℂ (LinearMap.range (originalSpinThreeHalfSource dual))=16:=by
  constructor
  · rw [originalSpinHalfSource,LinearMap.range_comp,
      ←(Submodule.equivMapOfInjective (sortedOriginalSource dual) (sorted_source_injective dual)
        (LinearMap.range sortedSpinHalf)).finrank_eq]
    exact actual_sorted_spin_multiplicities.1
  · rw [originalSpinThreeHalfSource,LinearMap.range_comp,
      ←(Submodule.equivMapOfInjective (sortedOriginalSource dual) (sorted_source_injective dual)
        (LinearMap.range sortedSpinThreeHalf)).finrank_eq]
    exact actual_sorted_spin_multiplicities.2

end LowEnergy.NamedColorQtNext
