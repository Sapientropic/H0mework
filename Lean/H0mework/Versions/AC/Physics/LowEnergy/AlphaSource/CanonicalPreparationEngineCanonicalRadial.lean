import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockInverseJets
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineFirstEnergy
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineSmoothSymbols

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineHomogeneity
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumEngineSource
open PreparationVacuumClockSymbol
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

abbrev SourcePhase := PreparationVacuumCanonicalMoyal.Phase
def RadialLaw (d : ℤ) (f : PreparationVacuumCanonicalMoyal.Symbol) : Prop :=
  ∀ r : ℝ, r≠0 → ∀ x∈poleDomain,f (radial r x)=r^d*f x

def radialLinear (r : ℝ) : SourcePhase →L[ℝ] SourcePhase :=
  (ContinuousLinearMap.fst ℝ FlatConfiguration PhysicalMomentum).prod
    (r • ContinuousLinearMap.snd ℝ FlatConfiguration PhysicalMomentum)

theorem radialLinear_apply (r : ℝ) (x : SourcePhase) : radialLinear r x=radial r x := rfl

theorem radialLinear_slot (r : ℝ) (s : Slot) :
    radialLinear r (slotDirection s)=(if s.2 then r else 1) • slotDirection s := by
  rcases s with ⟨i,b⟩
  cases b <;> simp [radialLinear,slotDirection,pDirection,qDirection]

def canonicalD (s : Slot) (f : PreparationVacuumCanonicalMoyal.Symbol) :
    PreparationVacuumCanonicalMoyal.Symbol := fun x => fderiv ℝ f x (slotDirection s)

theorem canonicalD_smooth (s : Slot) (f : PreparationVacuumCanonicalMoyal.Symbol) (x : SourcePhase)
    (smooth : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (canonicalD s f) x :=
  (smooth.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem canonicalD_radial (d : ℤ) (s : Slot) (f : PreparationVacuumCanonicalMoyal.Symbol)
    (smooth : ∀ x∈poleDomain,ContDiffAt ℝ ∞ f x) (law : RadialLaw d f) :
    RadialLaw (d-(if s.2 then 1 else 0)) (canonicalD s f) := by
  intro r rn x hx
  have hr := radial_admitted r rn x hx
  have leftDiff : DifferentiableAt ℝ f (radialLinear r x) := (smooth _ hr).differentiableAt (by simp)
  have rightDiff := (smooth x hx).differentiableAt (by simp)
  have germ : (fun y => f (radialLinear r y)) =ᶠ[𝓝 x] (fun y => r^d*f y) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact law r rn y hy
  have derivative := congrArg (fun L : SourcePhase →L[ℝ] ℝ => L (slotDirection s)) germ.fderiv_eq
  rw [fderiv_fun_comp x leftDiff (radialLinear r).differentiableAt,
    (radialLinear r).fderiv,fderiv_const_mul rightDiff] at derivative
  simp only [ContinuousLinearMap.comp_apply,radialLinear_slot,map_smul,
    smul_apply,smul_eq_mul] at derivative
  unfold canonicalD
  change fderiv ℝ f (radialLinear r x) (slotDirection s)=_
  cases b : s.2
  · simp only [b,Bool.false_eq_true,if_false,sub_zero,one_mul] at derivative ⊢
    exact derivative
  · simp only [b,ite_true] at derivative ⊢
    have power : r^(d-1)*r=r^d := by
      calc
        r^(d-1)*r=r^(d-1)*r^(1 : ℤ) := by rw [zpow_one]
        _=r^d := by
          rw [←zpow_add₀ rn]
          congr 1
          omega
    apply (mul_left_cancel₀ rn)
    rw [derivative]
    rw [←mul_assoc,mul_comm r (r^(d-1)),power]

def momentumCount (vs : List Slot) : ℕ := vs.countP (fun s => s.2)

theorem listJet_radial (d : ℤ) (vs : List Slot) (f : PreparationVacuumCanonicalMoyal.Symbol)
    (smooth : ∀ x∈poleDomain,ContDiffAt ℝ ∞ f x) (law : RadialLaw d f) :
    RadialLaw (d-(momentumCount vs : ℤ)) (listJet (vs.map slotDirection) f) := by
  induction vs with
  | nil => simpa [momentumCount,listJet] using law
  | cons s vs ih =>
    have lowerSmooth : ∀ x∈poleDomain,ContDiffAt ℝ ∞ (listJet (vs.map slotDirection) f) x :=
      fun x hx => listJet_smooth _ (smooth x hx)
    have step := canonicalD_radial (d-(momentumCount vs : ℤ)) s _ lowerSmooth ih
    change RadialLaw (d-(momentumCount (s::vs) : ℤ)) (canonicalD s (listJet (vs.map slotDirection) f))
    convert step using 1
    unfold momentumCount
    cases h : s.2
    · simp [h]
    · simp [h]
      omega


theorem momentumCount_swap (vs : List Slot) :
    momentumCount vs+momentumCount (vs.map slotSwap)=vs.length := by
  induction vs with
  | nil => rfl
  | cons s vs ih =>
    rcases s with ⟨i,b⟩
    cases b <;> simp [momentumCount,slotSwap] at ih ⊢ <;> omega

theorem jet_radial (d : ℤ) (r : ℕ) (w : Word r) (f : PreparationVacuumCanonicalMoyal.Symbol)
    (smooth : ∀ x∈poleDomain,ContDiffAt ℝ ∞ f x) (law : RadialLaw d f) :
    RadialLaw (d-(momentumCount (List.ofFn w) : ℤ)) (jet r f w) := by
  have result := listJet_radial d (List.ofFn w) f smooth law
  have smoothOn : ContDiffOn ℝ ∞ f poleDomain := fun x hx => (smooth x hx).contDiffWithinAt
  intro scale hn x hx
  have scaled := radial_admitted scale hn x hx
  have value := result scale hn x hx
  simp only [List.map_ofFn] at value
  rw [listJet_ofFn poleDomain_open smoothOn r _ _ scaled,
    listJet_ofFn poleDomain_open smoothOn r _ _ hx] at value
  exact value

theorem contraction_radial (df dg : ℤ) (r : ℕ) (f g : PreparationVacuumCanonicalMoyal.Symbol)
    (sf : ∀ x∈poleDomain,ContDiffAt ℝ ∞ f x) (sg : ∀ x∈poleDomain,ContDiffAt ℝ ∞ g x)
    (hf : RadialLaw df f) (hg : RadialLaw dg g) :
    RadialLaw (df+dg-(r : ℤ)) (contraction r f g) := by
  intro scale hn x hx
  unfold contraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [jet_radial df r w f sf hf scale hn x hx,
    jet_radial dg r (wordSwap r w) g sg hg scale hn x hx]
  have count : momentumCount (List.ofFn w)+momentumCount (List.ofFn (wordSwap r w))=r := by
    have value := momentumCount_swap (List.ofFn w)
    have same : wordSwap r w=(fun a => slotSwap (w a)) := rfl
    rw [same]
    simpa only [List.map_ofFn,List.length_ofFn,Function.comp_def] using value
  have exponent : df-(momentumCount (List.ofFn w) : ℤ)+(dg-(momentumCount (List.ofFn (wordSwap r w)) : ℤ))=df+dg-r := by
    omega
  have power : scale^(df-(momentumCount (List.ofFn w) : ℤ))*scale^(dg-(momentumCount (List.ofFn (wordSwap r w)) : ℤ))=scale^(df+dg-(r : ℤ)) := by
    rw [←zpow_add₀ hn,exponent]
  calc
    _=(scale^(df-(momentumCount (List.ofFn w) : ℤ))*scale^(dg-(momentumCount (List.ofFn (wordSwap r w)) : ℤ)))*
      (wordSign w*jet r f w x*jet r g (wordSwap r w) x) := by ring
    _=_ := by rw [power]

theorem scalarJordan_radial (df dg : ℤ) (r : ℕ) (f g : PreparationVacuumCanonicalMoyal.Symbol)
    (sf : ∀ x∈poleDomain,ContDiffAt ℝ ∞ f x) (sg : ∀ x∈poleDomain,ContDiffAt ℝ ∞ g x)
    (hf : RadialLaw df f) (hg : RadialLaw dg g) :
    RadialLaw (df+dg-(r : ℤ)) (scalarJordan r f g) := by
  intro scale hn x hx
  have left := contraction_radial df dg r f g sf sg hf hg scale hn x hx
  have right := contraction_radial dg df r g f sg sf hg hf scale hn x hx
  rw [add_comm dg df] at right
  simp only [PreparationVacuumEngineSmooth.scalarJordan_real,left,right]
  ring

end LowEnergy.PreparationVacuumEngineHomogeneity
