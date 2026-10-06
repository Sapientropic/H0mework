import H0mework.Versions.AC.Checks.Physics.IndependentBell.NistReal.NominalReplay.GaussianWindow.Gaussiansource
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Source-generated elimination for the named Gaussian vacuum readout. -/

set_option autoImplicit false

namespace P23.ObservableClosure

open P23.GaussianWindow
open scoped BigOperators
noncomputable section

structure Snapshot where
  nH : ℝ
  nV : ℝ
  etaA : ℝ
  etaB : ℝ
  delta : ℝ
  lam : ℝ
  nH_nonneg : 0 ≤ nH
  nV_nonneg : 0 ≤ nV
  nV_le_nH : nV ≤ nH
  etaA_pos : 0 < etaA
  etaA_le_one : etaA ≤ 1
  etaB_pos : 0 < etaB
  etaB_le_one : etaB ≤ 1
  lam_nonneg : 0 ≤ lam
  lam_le_one : lam ≤ 1

def nativeKernel (s : Snapshot) : RawKernel where
  tH := s.nH/(1+s.nH)
  tV := s.nV/(1+s.nV)
  phase := 1
  tH_nonneg := div_nonneg s.nH_nonneg (by linarith [s.nH_nonneg])
  tH_lt_one := (div_lt_one (by linarith [s.nH_nonneg])).2 (by linarith)
  tV_nonneg := div_nonneg s.nV_nonneg (by linarith [s.nV_nonneg])
  tV_lt_one := (div_lt_one (by linarith [s.nV_nonneg])).2 (by linarith)
  phase_unit := by norm_num

theorem native_mean_readback (s : Snapshot) :
    meanNumber (nativeKernel s).tH = s.nH ∧ meanNumber (nativeKernel s).tV = s.nV := by
  have hh : 1+s.nH ≠ 0 := ne_of_gt (by linarith [s.nH_nonneg])
  have hv : 1+s.nV ≠ 0 := ne_of_gt (by linarith [s.nV_nonneg])
  constructor <;> dsimp [meanNumber,nativeKernel] <;> field_simp [hh,hv] <;> ring

def e (s : Snapshot) : ℝ := s.etaA
def ratio (s : Snapshot) : ℝ := s.etaA/s.etaB
def h (s : Snapshot) : ℝ := s.etaA*s.nH
def v (s : Snapshot) : ℝ := s.etaA*s.nV
def coherence (s : Snapshot) : ℝ := 1-2*s.lam

theorem ratio_pos (s : Snapshot) : 0 < ratio s := div_pos s.etaA_pos s.etaB_pos

theorem snapshot_scaled_readback (s : Snapshot) :
    h s/e s = s.nH ∧ v s/e s = s.nV ∧ e s/ratio s = s.etaB ∧
    0 < e s ∧ e s ≤ 1 ∧ e s ≤ ratio s ∧ -1 ≤ coherence s ∧ coherence s ≤ 1 := by
  have ha := ne_of_gt s.etaA_pos
  have hb := ne_of_gt s.etaB_pos
  refine ⟨?_,?_,?_,s.etaA_pos,s.etaA_le_one,?_,?_,?_⟩
  · dsimp [h,e]; field_simp [ha]
  · dsimp [v,e]; field_simp [ha]
  · dsimp [ratio,e]; field_simp [ha,hb]
  · dsimp [e,ratio]
    apply (le_div_iff₀ s.etaB_pos).2
    nlinarith [s.etaA_pos,s.etaB_le_one]
  · dsimp [coherence]; linarith [s.lam_le_one]
  · dsimp [coherence]; linarith [s.lam_nonneg]

@[ext] structure Cell where
  a : ℝ
  b : ℝ

def U (s : Snapshot) (c : Cell) : ℝ := Real.sin (c.a-s.delta)*Real.sin (c.b-s.delta)
def V (s : Snapshot) (c : Cell) : ℝ := Real.cos (c.a-s.delta)*Real.cos (c.b-s.delta)
def meanA (s : Snapshot) (a : ℝ) : ℝ :=
  s.etaA*(s.nH*Real.sin (a-s.delta)^2+s.nV*Real.cos (a-s.delta)^2)
def meanB (s : Snapshot) (b : ℝ) : ℝ :=
  s.etaB*(s.nH*Real.sin (b-s.delta)^2+s.nV*Real.cos (b-s.delta)^2)
def D (s : Snapshot) (c : Cell) : ℝ := (1+meanA s c.a)*(1+meanB s c.b)

def kH (s : Snapshot) : ℝ := Real.sqrt (s.etaA*s.nH)*Real.sqrt (s.etaB*(1+s.nH))
def kV (s : Snapshot) : ℝ := Real.sqrt (s.etaA*s.nV)*Real.sqrt (s.etaB*(1+s.nV))
def kappa (s : Snapshot) (c : Cell) (phase : ℝ) : ℝ := kH s*U s c+phase*kV s*V s c
def phaseDen (s : Snapshot) (c : Cell) (phase : ℝ) : ℝ := D s c-kappa s c phase^2
def pulse00 (s : Snapshot) (c : Cell) : ℝ :=
  (1-s.lam)/phaseDen s c 1+s.lam/phaseDen s c (-1)

theorem meanA_nonneg (s : Snapshot) (a : ℝ) : 0 ≤ meanA s a := by
  exact mul_nonneg s.etaA_pos.le (add_nonneg
    (mul_nonneg s.nH_nonneg (sq_nonneg _)) (mul_nonneg s.nV_nonneg (sq_nonneg _)))
theorem meanB_nonneg (s : Snapshot) (b : ℝ) : 0 ≤ meanB s b := by
  exact mul_nonneg s.etaB_pos.le (add_nonneg
    (mul_nonneg s.nH_nonneg (sq_nonneg _)) (mul_nonneg s.nV_nonneg (sq_nonneg _)))

theorem two_term_cauchy (x y z w : ℝ) : (x*z+y*w)^2 ≤ (x^2+y^2)*(z^2+w^2) := by
  nlinarith [sq_nonneg (x*w-y*z)]

theorem phase_cauchy (s : Snapshot) (c : Cell) (phase : ℝ) (hp : phase^2=1) :
    kappa s c phase^2 ≤ meanA s c.a*(s.etaB+meanB s c.b) := by
  let x := Real.sqrt (s.etaA*s.nH)*Real.sin (c.a-s.delta)
  let y := Real.sqrt (s.etaA*s.nV)*Real.cos (c.a-s.delta)
  let z := Real.sqrt (s.etaB*(1+s.nH))*Real.sin (c.b-s.delta)
  let w := phase*Real.sqrt (s.etaB*(1+s.nV))*Real.cos (c.b-s.delta)
  have hA : x^2+y^2 = meanA s c.a := by
    dsimp [x,y,meanA]
    simp only [mul_pow,Real.sq_sqrt (mul_nonneg s.etaA_pos.le s.nH_nonneg),
      Real.sq_sqrt (mul_nonneg s.etaA_pos.le s.nV_nonneg)]
    ring
  have hB : z^2+w^2 = s.etaB+meanB s c.b := by
    dsimp [z,w,meanB]
    simp only [mul_pow,hp,one_mul,
      Real.sq_sqrt (mul_nonneg s.etaB_pos.le (by linarith [s.nH_nonneg] : 0 ≤ 1+s.nH)),
      Real.sq_sqrt (mul_nonneg s.etaB_pos.le (by linarith [s.nV_nonneg] : 0 ≤ 1+s.nV))]
    linear_combination s.etaB*(Real.sin_sq_add_cos_sq (c.b-s.delta))
  have hk : x*z+y*w = kappa s c phase := by dsimp [x,y,z,w,kappa,kH,kV,U,V]; ring
  simpa [hA,hB,hk] using two_term_cauchy x y z w

theorem phaseDen_pos (s : Snapshot) (c : Cell) (phase : ℝ) (hp : phase^2=1) :
    0 < phaseDen s c phase := by
  have hc := phase_cauchy s c phase hp
  have hle := mul_le_mul_of_nonneg_left
    (add_le_add_right s.etaB_le_one (meanB s c.b)) (meanA_nonneg s c.a)
  have hb := meanB_nonneg s c.b
  dsimp [phaseDen,D]
  nlinarith

theorem kH_scaled_sq (s : Snapshot) : kH s^2 = h s*(h s+e s)/ratio s := by
  dsimp [kH,h,e,ratio]
  rw [mul_pow,Real.sq_sqrt (mul_nonneg s.etaA_pos.le s.nH_nonneg),
    Real.sq_sqrt (mul_nonneg s.etaB_pos.le (by linarith [s.nH_nonneg] : 0 ≤ 1+s.nH))]
  field_simp [ne_of_gt s.etaA_pos,ne_of_gt s.etaB_pos]
  ring

theorem kV_scaled_sq (s : Snapshot) : kV s^2 = v s*(v s+e s)/ratio s := by
  dsimp [kV,v,e,ratio]
  rw [mul_pow,Real.sq_sqrt (mul_nonneg s.etaA_pos.le s.nV_nonneg),
    Real.sq_sqrt (mul_nonneg s.etaB_pos.le (by linarith [s.nV_nonneg] : 0 ≤ 1+s.nV))]
  field_simp [ne_of_gt s.etaA_pos,ne_of_gt s.etaB_pos]
  ring

def T (s : Snapshot) : ℝ := ratio s*kH s*kV s
def T2 (s : Snapshot) (loss : ℝ) : ℝ := h s*v s*(h s+loss)*(v s+loss)
def g (s : Snapshot) (c : Cell) : ℝ := 2*U s c*V s c/ratio s
def L (s : Snapshot) (c : Cell) (loss : ℝ) : ℝ :=
  D s c-(h s*(h s+loss)*U s c^2+v s*(v s+loss)*V s c^2)/ratio s
def E (s : Snapshot) (c : Cell) (loss : ℝ) : ℝ := L s c loss^2-g s c^2*T2 s loss
def H (s : Snapshot) (c : Cell) (loss : ℝ) : ℝ := pulse00 s c*E s c loss-L s c loss

theorem T_sq (s : Snapshot) : T s^2=T2 s (e s) := by
  dsimp [T]
  rw [mul_pow,mul_pow,kH_scaled_sq,kV_scaled_sq]
  dsimp [T2]
  field_simp [ne_of_gt (ratio_pos s)]

theorem T_nonneg (s : Snapshot) : 0 ≤ T s := by
  have hr := (ratio_pos s).le
  dsimp [T,kH,kV]
  positivity
theorem T_eq_sqrt (s : Snapshot) : T s=Real.sqrt (T2 s (e s)) := by
  rw [← T_sq,Real.sqrt_sq (T_nonneg s)]

theorem phaseDen_scaled (s : Snapshot) (c : Cell) (phase : ℝ) (hp : phase^2=1) :
    phaseDen s c phase=L s c (e s)-phase*g s c*T s := by
  dsimp [phaseDen,kappa,L]
  simp only [add_sq,mul_pow,hp,one_mul,kH_scaled_sq,kV_scaled_sq]
  dsimp [g,T]
  field_simp [ne_of_gt (ratio_pos s)]
  ring

theorem E_factor (s : Snapshot) (c : Cell) :
    E s c (e s)=phaseDen s c 1*phaseDen s c (-1) := by
  rw [phaseDen_scaled s c 1 (by norm_num),phaseDen_scaled s c (-1) (by norm_num)]
  dsimp [E]
  rw [← T_sq]
  ring

theorem E_pos (s : Snapshot) (c : Cell) : 0 < E s c (e s) := by
  rw [E_factor]
  exact mul_pos (phaseDen_pos s c 1 (by norm_num)) (phaseDen_pos s c (-1) (by norm_num))

theorem source_H (s : Snapshot) (c : Cell) : H s c (e s)=coherence s*g s c*T s := by
  have hp := ne_of_gt (phaseDen_pos s c 1 (by norm_num))
  have hm := ne_of_gt (phaseDen_pos s c (-1) (by norm_num))
  dsimp [H,pulse00]
  rw [E_factor]
  field_simp [hp,hm]
  rw [phaseDen_scaled s c 1 (by norm_num),phaseDen_scaled s c (-1) (by norm_num)]
  dsimp [coherence]
  ring

def lConst (s : Snapshot) (c : Cell) : ℝ := D s c-(h s^2*U s c^2+v s^2*V s c^2)/ratio s
def lSlope (s : Snapshot) (c : Cell) : ℝ := (h s*U s c^2+v s*V s c^2)/ratio s

theorem L_affine (s : Snapshot) (c : Cell) (loss : ℝ) :
    L s c loss=lConst s c-lSlope s c*loss := by dsimp [L,lConst,lSlope]; ring

structure Quadratic where
  q0 : ℝ
  q1 : ℝ
  q2 : ℝ

def Quadratic.value (q : Quadratic) (x : ℝ) : ℝ := q.q2*x^2+q.q1*x+q.q0
def Quadratic.polynomial (q : Quadratic) : Polynomial ℝ :=
  Polynomial.C q.q2*Polynomial.X^2+Polynomial.C q.q1*Polynomial.X+Polynomial.C q.q0

theorem Quadratic.degree_le (q : Quadratic) : q.polynomial.natDegree ≤ 2 :=
  Polynomial.natDegree_quadratic_le

theorem Quadratic.eval_eq (q : Quadratic) (x : ℝ) : q.polynomial.eval x=q.value x := by
  simp [Quadratic.polynomial,Quadratic.value]

def hQuadratic (s : Snapshot) (c : Cell) : Quadratic where
  q0 := pulse00 s c*(lConst s c^2-g s c^2*h s^2*v s^2)-lConst s c
  q1 := pulse00 s c*(-2*lConst s c*lSlope s c-g s c^2*h s*v s*(h s+v s))+lSlope s c
  q2 := pulse00 s c*(lSlope s c^2-g s c^2*h s*v s)

theorem hQuadratic_value (s : Snapshot) (c : Cell) (loss : ℝ) :
    (hQuadratic s c).value loss=H s c loss := by
  dsimp [H,E]
  rw [L_affine]
  dsimp [hQuadratic,Quadratic.value,T2]
  ring

def linearCombination (a : ℝ) (p : Quadratic) (b : ℝ) (q : Quadratic) : Quadratic :=
  ⟨a*p.q0-b*q.q0,a*p.q1-b*q.q1,a*p.q2-b*q.q2⟩

theorem combination_value (a : ℝ) (p : Quadratic) (b : ℝ) (q : Quadratic) (x : ℝ) :
    (linearCombination a p b q).value x=a*p.value x-b*q.value x := by
  dsimp [linearCombination,Quadratic.value]; ring

def trainingF (s : Snapshot) (c0 c1 : Cell) : Quadratic :=
  linearCombination (g s c1) (hQuadratic s c0) (g s c0) (hQuadratic s c1)

theorem same_source_quadratic_root (s : Snapshot) (c0 c1 : Cell) :
    (trainingF s c0 c1).polynomial.natDegree ≤ 2 ∧
    (trainingF s c0 c1).polynomial.eval (e s)=0 := by
  refine ⟨Quadratic.degree_le _,?_⟩
  rw [Quadratic.eval_eq,trainingF,combination_value,hQuadratic_value,hQuadratic_value,
    source_H,source_H]
  ring

def closurePulse (s : Snapshot) (seed c : Cell) : ℝ :=
  (L s c (e s)+(g s c/g s seed)*H s seed (e s))/E s c (e s)

theorem same_source_cell_closure (s : Snapshot) (seed c : Cell) (hg : g s seed ≠ 0) :
    closurePulse s seed c=pulse00 s c := by
  have he := ne_of_gt (E_pos s c)
  dsimp [closurePulse]
  rw [source_H]
  apply (div_eq_iff he).2
  have hc := source_H s c
  dsimp [H] at hc
  field_simp [hg]
  nlinarith [hc]

def cellRelation (s : Snapshot) (seed c : Cell) : Quadratic :=
  linearCombination (g s c) (hQuadratic s seed) (g s seed) (hQuadratic s c)

theorem same_source_cell_relation (s : Snapshot) (seed c : Cell) :
    (cellRelation s seed c).value (e s)=0 := by
  rw [cellRelation,combination_value,hQuadratic_value,hQuadratic_value,source_H,source_H]
  ring

def sylvester (p q : Quadratic) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![p.q2,p.q1,p.q0,0],![0,p.q2,p.q1,p.q0],![q.q2,q.q1,q.q0,0],![0,q.q2,q.q1,q.q0]]

theorem common_root_sylvester_zero (p q : Quadratic) (x : ℝ)
    (hp : p.value x=0) (hq : q.value x=0) : (sylvester p q).det=0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨![x^3,x^2,x,1],?_,?_⟩
  · intro hz
    have ht := congrFun hz (3 : Fin 4)
    change (1 : ℝ)=0 at ht
    norm_num at ht
  · ext i
    dsimp [Quadratic.value] at hp hq
    fin_cases i <;> simp [sylvester,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    · linear_combination x*hp
    · linear_combination hp
    · linear_combination x*hq
    · linear_combination hq

theorem source_resultant_necessary (s : Snapshot) (c0 c1 c : Cell) :
    (sylvester (trainingF s c0 c1) (cellRelation s c0 c)).det=0 := by
  apply common_root_sylvester_zero _ _ (e s)
  · rw [← Quadratic.eval_eq]
    exact (same_source_quadratic_root s c0 c1).2
  · exact same_source_cell_relation s c0 c

def mirror (a : ℝ) : Cell := ⟨a,-a⟩

theorem mirror_U (s : Snapshot) (a : ℝ) :
    U s (mirror a)=(Real.cos (2*a)-Real.cos (2*s.delta))/2 := by
  have ht := Real.two_mul_sin_mul_sin (a-s.delta) (-a-s.delta)
  have hx : (a-s.delta)-(-a-s.delta)=2*a := by ring
  have hy : (a-s.delta)+(-a-s.delta)=-(2*s.delta) := by ring
  rw [hx,hy,Real.cos_neg] at ht
  dsimp [U,mirror]
  linarith

theorem mirror_V (s : Snapshot) (a : ℝ) :
    V s (mirror a)=(Real.cos (2*a)+Real.cos (2*s.delta))/2 := by
  have ht := Real.two_mul_cos_mul_cos (a-s.delta) (-a-s.delta)
  have hx : (a-s.delta)-(-a-s.delta)=2*a := by ring
  have hy : (a-s.delta)+(-a-s.delta)=-(2*s.delta) := by ring
  rw [hx,hy,Real.cos_neg] at ht
  dsimp [V,mirror]
  linarith

theorem mirror_g (s : Snapshot) (a : ℝ) :
    g s (mirror a)=(Real.cos (2*a)^2-Real.cos (2*s.delta)^2)/(2*ratio s) := by
  rw [g,mirror_U,mirror_V]
  ring

theorem mirror_training_informative (s : Snapshot) (a0 a1 : ℝ)
    (ha : Real.cos (2*a0)^2 ≠ Real.cos (2*a1)^2) :
    g s (mirror a0) ≠ 0 ∨ g s (mirror a1) ≠ 0 := by
  by_contra hn
  have hh := not_or.mp hn
  have h0 : g s (mirror a0)=0 := not_ne_iff.mp hh.1
  have h1 : g s (mirror a1)=0 := not_ne_iff.mp hh.2
  rw [mirror_g] at h0 h1
  have hd : 2*ratio s ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt (ratio_pos s))
  have hc0 := (div_eq_zero_iff.mp h0).resolve_right hd
  have hc1 := (div_eq_zero_iff.mp h1).resolve_right hd
  apply ha
  linarith

end
end P23.ObservableClosure
