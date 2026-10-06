import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockInverseJets
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineFiltration

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineSmooth
open PreparationActualFactor PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry
open PreparationVacuumClockJacobian PreparationVacuumClockSymbol PreparationVacuumEngineSource
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

def SmoothSymbol (f : Symbol) : Prop := ContDiffOn ℝ ∞ f poleDomain

theorem smoothSymbol_const (c : ℝ) : SmoothSymbol (fun _ => c) := contDiffOn_const

theorem smoothSymbol_zero : SmoothSymbol (0 : Symbol) := contDiffOn_const

theorem smoothSymbol_add {f g : Symbol} (hf : SmoothSymbol f) (hg : SmoothSymbol g) :
    SmoothSymbol (f+g) := hf.add hg

theorem smoothSymbol_sub {f g : Symbol} (hf : SmoothSymbol f) (hg : SmoothSymbol g) :
    SmoothSymbol (f-g) := hf.sub hg

theorem smoothSymbol_mul {f g : Symbol} (hf : SmoothSymbol f) (hg : SmoothSymbol g) :
    SmoothSymbol (f*g) := hf.mul hg

theorem smoothSymbol_neg {f : Symbol} (hf : SmoothSymbol f) : SmoothSymbol (-f) := hf.neg

theorem smoothSymbol_sum {ι : Type*} (s : Finset ι) (F : ι → Symbol)
    (hf : ∀ i∈s, SmoothSymbol (F i)) : SmoothSymbol (∑ i∈s,F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smoothSymbol_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact smoothSymbol_add (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem smoothSymbol_jet (r : ℕ) (w : Word r) {f : Symbol} (hf : SmoothSymbol f) :
    SmoothSymbol (fun x => jet r f w x) := by
  intro x hx
  have germ : (fun y => jet r f w y)=ᶠ[𝓝 x]
      listJet (List.ofFn (fun a => slotDirection (w a))) f := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact (listJet_ofFn poleDomain_open hf r (fun a => slotDirection (w a)) y hy).symm
  exact ((listJet_smooth _ ((hf x hx).contDiffAt (poleDomain_open.mem_nhds hx))).congr_of_eventuallyEq
    germ).contDiffWithinAt

theorem smoothSymbol_contraction (r : ℕ) {f g : Symbol} (hf : SmoothSymbol f) (hg : SmoothSymbol g) :
    SmoothSymbol (fun x => contraction r f g x) := by
  unfold contraction
  apply ContDiffOn.sum
  intro w _
  exact ((smoothSymbol_const (wordSign w)).mul (smoothSymbol_jet r w hf)).mul
    (smoothSymbol_jet r (wordSwap r w) hg)

theorem scalarJordan_real (r : ℕ) (f g : Symbol) (x : Phase) :
    scalarJordan r f g x=
      (((Complex.I/2)^r/(r.factorial : ℂ)).re/2)*
        (contraction r f g x+contraction r g f x) := by
  simp only [scalarJordan,jordan,coefficient,div_eq_mul_inv,Complex.mul_re,Complex.add_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  norm_num
  ring

theorem smoothSymbol_scalarJordan (r : ℕ) {f g : Symbol} (hf : SmoothSymbol f) (hg : SmoothSymbol g) :
    SmoothSymbol (scalarJordan r f g) := by
  change ContDiffOn ℝ ∞ (fun x => scalarJordan r f g x) poleDomain
  simp_rw [scalarJordan_real]
  exact contDiffOn_const.mul ((smoothSymbol_contraction r hf hg).add
    (smoothSymbol_contraction r hg hf))

def SmoothPolynomial (P : AngularPolynomial) : Prop :=
  ∀ u : AngularExponent, SmoothSymbol (MvPolynomial.coeff u P)

theorem smoothPolynomial_zero : SmoothPolynomial 0 := by
  intro u
  simpa using smoothSymbol_zero

theorem smoothPolynomial_constant {f : Symbol} (hf : SmoothSymbol f) :
    SmoothPolynomial (MvPolynomial.C f) := by
  intro u
  by_cases same : u=0
  · subst u
    simpa using hf
  · simpa [MvPolynomial.coeff_C,same,eq_comm] using smoothSymbol_zero

theorem smoothPolynomial_monomial (u : AngularExponent) {f : Symbol} (hf : SmoothSymbol f) :
    SmoothPolynomial (MvPolynomial.monomial u f) := by
  intro v
  by_cases same : u=v
  · subst v
    simpa using hf
  · simpa [MvPolynomial.coeff_monomial,same,eq_comm] using smoothSymbol_zero

theorem smoothPolynomial_add {P Q : AngularPolynomial} (hp : SmoothPolynomial P) (hq : SmoothPolynomial Q) :
    SmoothPolynomial (P+Q) := by
  intro u
  simpa only [MvPolynomial.coeff_add] using smoothSymbol_add (hp u) (hq u)

theorem smoothPolynomial_sub {P Q : AngularPolynomial} (hp : SmoothPolynomial P) (hq : SmoothPolynomial Q) :
    SmoothPolynomial (P-Q) := by
  intro u
  simpa only [MvPolynomial.coeff_sub] using smoothSymbol_sub (hp u) (hq u)

theorem smoothPolynomial_sum {ι : Type*} (s : Finset ι) (P : ι → AngularPolynomial)
    (hp : ∀ i∈s, SmoothPolynomial (P i)) : SmoothPolynomial (∑ i∈s,P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smoothPolynomial_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact smoothPolynomial_add (hp i (Finset.mem_insert_self i s))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem smoothPolynomial_weighted (r : ℕ) {P Q : AngularPolynomial}
    (hp : SmoothPolynomial P) (hq : SmoothPolynomial Q) : SmoothPolynomial (weighted r P Q) := by
  unfold weighted
  apply smoothPolynomial_sum
  intro u _
  apply smoothPolynomial_sum
  intro v _
  exact smoothPolynomial_monomial _ (smoothSymbol_scalarJordan r (hp u) (hq v))

theorem smoothPolynomial_mul {P Q : AngularPolynomial} (hp : SmoothPolynomial P) (hq : SmoothPolynomial Q) :
    SmoothPolynomial (P*Q) := by
  rw [←weighted_zero]
  exact smoothPolynomial_weighted 0 hp hq

theorem smoothPolynomial_X (i : Fin 3) : SmoothPolynomial (MvPolynomial.X i) := by
  rw [MvPolynomial.X]
  exact smoothPolynomial_monomial _ (smoothSymbol_const 1)

theorem smoothPolynomial_average {P : AngularPolynomial} (hp : SmoothPolynomial P) :
    SmoothSymbol (average P) := by
  unfold average
  apply smoothSymbol_sum
  intro u _
  exact (smoothSymbol_const (angularMoment u)).mul (hp u)

theorem sourceClock_smooth : SmoothSymbol sourceClock := by
  intro x hx
  exact (actualC_smooth x hx.1).contDiffWithinAt

theorem sourceClock_inverse_smooth : SmoothSymbol (fun x => (sourceClock x)⁻¹) := by
  intro x hx
  exact ((actualC_smooth x hx.1).inv (C_positive hx.1).ne').contDiffWithinAt

theorem source_engineInverse_smooth (a b : Fin 4) :
    SmoothSymbol (fun x => (principalForceJacobian x)⁻¹ a b) := by
  intro x hx
  have germ : (fun q => (principalForceJacobian q)⁻¹ a b)=ᶠ[𝓝 x]
      (fun q => sourceInverse q a b) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with q hq
    exact congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M a b)
      (sourceInverse_native q hq.1 hq.2)
  exact ((sourceInverse_smooth x hx a b).congr_of_eventuallyEq germ).contDiffWithinAt

theorem engineSource_smooth (filtration : ℕ) (slot : Fin 13) :
    SmoothSymbol (engineSource filtration slot) := by
  intro x hx
  cases filtration with
  | zero =>
    change ContDiffWithinAt ℝ ∞
      (fun q => PreparationVacuumEnergyTail.originalEnginePrincipalLeaves
        (nativePhase q).1 (nativePhase q).2 slot) poleDomain x
    have c := actualC_smooth x hx.1
    have t := actualT_smooth x hx.1.1
    have s := actualS_smooth x hx.1.1
    have leading := t.div (contDiffAt_const.mul (c.pow 2))
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 (C_positive hx.1).ne'))
    fin_cases slot
    all_goals first
      | exact leading.contDiffWithinAt
      | exact (s _ _).contDiffWithinAt
      | exact ((t.sub (s 0 0)).sub (s 1 1)).contDiffWithinAt
      | exact contDiffWithinAt_const
  | succ n =>
    cases n with
    | zero =>
      rw [engineSource_first]
      exact (originalLeaf_smooth 1 (Fin.castSucc slot) x hx.1.1).contDiffWithinAt
    | succ n =>
      cases n with
      | zero =>
        rw [engineSource_zero]
        exact (originalLeaf_smooth 0 (Fin.castSucc slot) x hx.1.1).contDiffWithinAt
      | succ n =>
        rw [engineSource_padding]
        exact contDiffWithinAt_const

theorem engineTrace_smooth (filtration : ℕ) : SmoothSymbol (engineTrace filtration) := by
  unfold engineTrace
  exact ((engineSource_smooth filtration 4).add (engineSource_smooth filtration 5)).add
    (engineSource_smooth filtration 6)

end LowEnergy.PreparationVacuumEngineSmooth
