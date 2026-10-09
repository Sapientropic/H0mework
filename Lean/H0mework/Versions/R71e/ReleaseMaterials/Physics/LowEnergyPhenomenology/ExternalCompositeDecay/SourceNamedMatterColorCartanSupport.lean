import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterColorEpsilonAction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore
open NamedMatterWedgeQt SU7MotherLieAlgebra
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace Matrix

def cartanWeight(k:Fin 2)(c:Fin 3):ℤ:=
  if k=0 then (if c=0 then 1 else if c=1 then -1 else 0)
  else (if c=1 then 1 else if c=2 then -1 else 0)

def sourceCartan(k:Fin 2):SU3BlockLieMatrix:=
  ⟨Matrix.diagonal (fun c=>(cartanWeight k c:ℂ)*Complex.I),by
    constructor
    · ext i j
      by_cases h:i=j <;> simp [Matrix.star_apply,h,eq_comm,Complex.conj_I]
    · fin_cases k <;> norm_num [Matrix.trace,Fin.sum_univ_three,cartanWeight] <;> simp +decide⟩

private def dualI(dual:Bool):ℂ:=if dual then -Complex.I else Complex.I

private theorem cartan_entry(dual:Bool)(k:Fin 2)(r c:Fin 3):
    colorEntry dual (sourceCartan k) r c=
      if r=c then dualI dual*(cartanWeight k c:ℂ) else 0:=by
  cases dual <;> by_cases h:r=c <;>
    simp [colorEntry,sourceCartan,h,dualI,mul_comm]

def occupationWeight(k:Fin 2)(w:WedgeIndex):ℤ:=
  ∑p:Fin 3,cartanWeight k (tripleIndex w p).2
def colorBalanced(w:WedgeIndex):Prop:=
  (tripleIndex w 0).2≠(tripleIndex w 1).2 ∧
  (tripleIndex w 0).2≠(tripleIndex w 2).2 ∧
  (tripleIndex w 1).2≠(tripleIndex w 2).2

private theorem named_cartan_eigen(dual:Bool)(k:Fin 2)(w:WedgeIndex):
    GaussNativeMatter.nativeFock (colorNative (sourceCartan k)) (namedCARBasis dual w)=
      (dualI dual*(occupationWeight k w:ℂ)) • namedCARBasis dual w:=by
  rw [namedCARBasis,actual_color_ordered_triple]
  simp_rw [cartan_entry]
  simp only [ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [occupationWeight,Fin.sum_univ_three,Int.cast_add,mul_add,add_smul]

private theorem fiber_from_CAR(dual:Bool)(w:WedgeIndex):
    fiberBasis dual w=sourcePhase dual w • namedCARBasis dual w:=by
  rw [actual_named_CAR_basis,smul_smul,actual_source_phase_square,one_smul]

/-- Original Cartan weights act on all 220 mother occupations, with the actual CAR phase eliminated internally. -/
theorem actual_color_cartan_eigen(dual:Bool)(k:Fin 2)(w:WedgeIndex):
    GaussNativeMatter.nativeFock (colorNative (sourceCartan k)) (fiberBasis dual w)=
      (dualI dual*(occupationWeight k w:ℂ)) • fiberBasis dual w:=by
  rw [fiber_from_CAR,map_smul,named_cartan_eigen]
  exact smul_comm _ _ _

private theorem weight_pattern:∀c:Fin 3→Fin 3,
    ((∑p:Fin 3,cartanWeight 0 (c p))=0 ∧ (∑p:Fin 3,cartanWeight 1 (c p))=0) ↔
      (c 0≠c 1 ∧ c 0≠c 2 ∧ c 1≠c 2):=by decide

theorem actual_color_balanced_weights(w:WedgeIndex):
    (occupationWeight 0 w=0 ∧ occupationWeight 1 w=0) ↔ colorBalanced w:=
  weight_pattern (fun p=>(tripleIndex w p).2)

private theorem charge_ne_zero(dual:Bool)(n:ℤ)(hn:n≠0):dualI dual*(n:ℂ)≠0:=by
  apply mul_ne_zero
  · cases dual <;> simp [dualI,Complex.I_ne_zero]
  · exact_mod_cast hn

private theorem cartan_pair_column(dual:Bool)(k:Fin 2)(a:WedgeFiber)(w:WedgeIndex):
    inner ℂ (fiberBasis dual w)
      (GaussNativeMatter.nativeFock (colorNative (sourceCartan k)) (wedgeFiber dual a))=
      (dualI dual*(occupationWeight k w:ℂ))*a w:=by
  classical
  simp only [wedgeFiber,map_sum,map_smul,actual_color_cartan_eigen,inner_sum,inner_smul_right,
    actual_fiber_pair]
  simp [mul_ite,mul_comm]

/-- The actual common mother-color kernel has no occupation outside the one-of-each-color sector. -/
theorem actual_color_kernel_balanced_support(dual:Bool)(a:WedgeFiber)
    (h:∀A:SU3BlockLieMatrix,GaussNativeMatter.nativeFock (colorNative A) (wedgeFiber dual a)=0)
    (w:WedgeIndex)(hw:¬colorBalanced w):a w=0:=by
  have hweight:∃k:Fin 2,occupationWeight k w≠0:=by
    by_contra! hn
    exact hw ((actual_color_balanced_weights w).mp ⟨hn 0,hn 1⟩)
  obtain ⟨k,hk⟩:=hweight
  have he:=cartan_pair_column dual k a w
  rw [h,inner_zero_right] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (charge_ne_zero dual _ hk)

end LowEnergy.NamedColorQtNext
