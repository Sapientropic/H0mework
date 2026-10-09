import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterTripleGram
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
namespace LowEnergy.NamedColorQtNext
open NamedMatterWedgeQt SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace

def intDelta(i j:NamedMode):ℤ:=if i=j then 1 else 0
def intTripleGram(i j k a b c:NamedMode):ℤ:=
  intDelta i a*(intDelta j b*intDelta k c-intDelta j c*intDelta k b)-
  intDelta i b*(intDelta j a*intDelta k c-intDelta j c*intDelta k a)+
  intDelta i c*(intDelta j a*intDelta k b-intDelta j b*intDelta k a)
def intColorSign(p:Fin 6):ℤ:=if p=0 ∨ p=3 ∨ p=4 then 1 else -1
def spinMultiplicity(s:SpinTriple):ℕ:=
  if s.val 0=s.val 2 then 6 else if s.val 0=s.val 1 ∨ s.val 1=s.val 2 then 2 else 1
def intEpsilonGram(s t:SpinTriple):ℤ:=
  ∑p:Fin 6,∑q:Fin 6,intColorSign p*intColorSign q*
    intTripleGram (s.val 0,colorPerm p 0) (s.val 1,colorPerm p 1) (s.val 2,colorPerm p 2)
      (t.val 0,colorPerm q 0) (t.val 1,colorPerm q 1) (t.val 2,colorPerm q 2)

def spinDelta(i j:Fin 4):ℤ:=if i=j then 1 else 0
def spinPermanent(s t:SpinTriple):ℤ:=
  spinDelta (s.val 0) (t.val 0)*spinDelta (s.val 1) (t.val 1)*spinDelta (s.val 2) (t.val 2)+
  spinDelta (s.val 0) (t.val 0)*spinDelta (s.val 1) (t.val 2)*spinDelta (s.val 2) (t.val 1)+
  spinDelta (s.val 0) (t.val 1)*spinDelta (s.val 1) (t.val 0)*spinDelta (s.val 2) (t.val 2)+
  spinDelta (s.val 0) (t.val 1)*spinDelta (s.val 1) (t.val 2)*spinDelta (s.val 2) (t.val 0)+
  spinDelta (s.val 0) (t.val 2)*spinDelta (s.val 1) (t.val 0)*spinDelta (s.val 2) (t.val 1)+
  spinDelta (s.val 0) (t.val 2)*spinDelta (s.val 1) (t.val 1)*spinDelta (s.val 2) (t.val 0)
private theorem epsilon_permanent(s t:SpinTriple):intEpsilonGram s t=6*spinPermanent s t:=by
  simp +decide only [intEpsilonGram,intTripleGram,intColorSign,intDelta,colorPerm,spinPermanent,spinDelta,
    Fin.sum_univ_six,Prod.mk.injEq,Fin.ext_iff,ite_true,ite_false,and_true,and_false,
    zero_mul,mul_zero,add_zero,zero_add,
    sub_zero,zero_sub,one_mul,mul_one,neg_mul,mul_neg,neg_neg]
  ring
private theorem permanent_all:∀s t:SpinTriple,
    spinPermanent s t=if s=t then (spinMultiplicity s:ℤ) else 0:=by decide
private theorem integer_gram_all(s t:SpinTriple):
    intEpsilonGram s t=if s=t then 6*(spinMultiplicity s:ℤ) else 0:=by
  rw [epsilon_permanent,permanent_all]
  split_ifs <;> ring

noncomputable section
private theorem delta_cast(i j:NamedMode):(intDelta i j:ℂ)=delta i j:=by
  by_cases h:i=j <;> simp [intDelta,delta,h]
private theorem triple_gram_cast(i j k a b c:NamedMode):
    (intTripleGram i j k a b c:ℂ)=tripleGram i j k a b c:=by
  simp only [intTripleGram,tripleGram,Int.cast_add,Int.cast_sub,Int.cast_mul,delta_cast]
private theorem color_sign_cast(p:Fin 6):(intColorSign p:ℂ)=colorSign p:=by
  unfold intColorSign colorSign
  split_ifs <;> norm_num
private theorem color_sign_star(p:Fin 6):star (colorSign p)=colorSign p:=by
  unfold colorSign
  split_ifs <;> norm_num

/-- All six original color permutations pay their own multiplicity; the actual mother CAR Gram is generated internally. -/
theorem actual_epsilon_gram(dual:Bool)(s t:SpinTriple):
    inner ℂ (epsilonFiber dual s) (epsilonFiber dual t)=
      if s=t then (6*(spinMultiplicity s:ℕ):ℂ) else 0:=by
  have he:(intEpsilonGram s t:ℂ)=inner ℂ (epsilonFiber dual s) (epsilonFiber dual t):=by
    rw [actual_epsilon_pair_expansion]
    simp only [intEpsilonGram,Int.cast_sum,Int.cast_mul,color_sign_cast,triple_gram_cast,color_sign_star]
  rw [←he,integer_gram_all]
  split_ifs <;> push_cast <;> rfl

theorem actual_epsilon_multiplicity_positive(s:SpinTriple):0<spinMultiplicity s:=by
  unfold spinMultiplicity
  split_ifs <;> norm_num

def epsilonScale(s:SpinTriple):ℝ:=Real.sqrt (6*(spinMultiplicity s:ℝ))
def normalizedEpsilon(dual:Bool)(s:SpinTriple):FockFiber:=
  (epsilonScale s:ℂ)⁻¹ • epsilonFiber dual s

theorem actual_epsilon_scale_positive(s:SpinTriple):0<epsilonScale s:=by
  apply Real.sqrt_pos.mpr
  exact mul_pos (by norm_num) (by exact_mod_cast actual_epsilon_multiplicity_positive s)

/-- Twenty normalized epsilon source states are orthonormal in the unchanged full 504-mode Fock carrier. -/
theorem actual_normalized_epsilon_pair(dual:Bool)(s t:SpinTriple):
    inner ℂ (normalizedEpsilon dual s) (normalizedEpsilon dual t)=if s=t then 1 else 0:=by
  rw [normalizedEpsilon,normalizedEpsilon,inner_smul_left,inner_smul_right,actual_epsilon_gram]
  by_cases h:s=t
  · subst t
    simp only [ite_true,map_inv₀,Complex.conj_ofReal]
    have hs:epsilonScale s^2=6*(spinMultiplicity s:ℝ):=Real.sq_sqrt (by positivity)
    have hn:(epsilonScale s:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (actual_epsilon_scale_positive s).ne'
    have hc:(epsilonScale s:ℂ)^2=(6*(spinMultiplicity s:ℕ):ℂ):=by exact_mod_cast hs
    rw [←hc]
    field_simp [hn]
  · simp [h]

end
end LowEnergy.NamedColorQtNext
