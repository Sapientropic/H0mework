import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Coulomb.Runtime.Consumers

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
noncomputable section

-- Fixed installed input: this is the joint 19q/local4q occurrence.
def input := Coulomb.Runtime.readMaterial Coulomb.Runtime.afterFirst Coulomb.Runtime.first_ready
def initialMomentum (i : Coordinate) : ℝ := input.joint.body.frame.momentum i.1 i.2

def onTime (t : ℝ) : ℝ := t-(2/duration)*t^2+(1/duration^2)*t^3
def onRate (t : ℝ) : ℝ := 1-(4/duration)*t+(3/duration^2)*t^2
def offTime (t : ℝ) : ℝ := -(1/duration)*t^2+(1/duration^2)*t^3
def offRate (t : ℝ) : ℝ := -(2/duration)*t+(3/duration^2)*t^2

theorem duration_positive : 0 < duration := Runtime.elapsed_strictly_forward

theorem on_time_derivative (t : ℝ) : HasDerivAt onTime (onRate t) t := by
  convert ((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).const_mul (2/duration))).add
    (((hasDerivAt_id t).pow 3).const_mul (1/duration^2)) using 1
  all_goals first | rfl | (dsimp [onTime,onRate]; ring)

theorem off_time_derivative (t : ℝ) : HasDerivAt offTime (offRate t) t := by
  convert ((((hasDerivAt_id t).pow 2).const_mul (1/duration)).neg).add
    (((hasDerivAt_id t).pow 3).const_mul (1/duration^2)) using 1
  all_goals first | rfl | (funext x; dsimp [offTime]; ring) | (dsimp [offRate]; ring)

theorem ramp_endpoints :
    onTime 0=0 ∧ onTime duration=0 ∧ onRate 0=1 ∧ onRate duration=0 ∧
    offTime 0=0 ∧ offTime duration=0 ∧ offRate 0=0 ∧ offRate duration=1 := by
  have hn := ne_of_gt duration_positive
  dsimp [onTime,onRate,offTime,offRate]
  field_simp
  norm_num
  ring

-- This is a finite clock-dependent control of the original force germ.
def rampMomentum (p : Configuration) (s : ℝ) (i : Coordinate) : ℝ :=
  p i+sourceForce i*s

def rampPosition (p : Configuration) (s : ℝ) (i : Coordinate) : ℝ :=
  sourcePosition i+(p i*s+sourceForce i*s^2/2)/mass i

def vectorControl (p : Configuration) (s h : ℝ) : Configuration :=
  fun i => (1-h)*rampMomentum p s i

def forcePairing (r : Configuration) : ℝ :=
  ∑ i, sourceForce i*(r i-sourcePosition i)

-- The stored control energy is explicit, including its nonzero plateau value.
def scalarControl (p : Configuration) (s h : ℝ) : ℝ :=
  nuclearKinetic p-h^2*nuclearKinetic (rampMomentum p s)+h*forcePairing (rampPosition p s)

def rampHamiltonian (p : Configuration) (s h : ℝ) (r momentum : Configuration) : ℝ :=
  nuclearKinetic (momentum-vectorControl p s h)+sourcePotential-h*forcePairing r+scalarControl p s h

theorem ramp_momentum_zero (p : Configuration) : rampMomentum p 0=p := by
  funext i; simp [rampMomentum]

theorem ramp_position_zero (p : Configuration) : rampPosition p 0=sourcePosition := by
  funext i; simp [rampPosition]

theorem kinetic_scale (p : Configuration) (a : ℝ) :
    nuclearKinetic (fun i => a*p i)=a^2*nuclearKinetic p := by
  unfold nuclearKinetic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem ramp_energy (p : Configuration) (s h : ℝ) :
    rampHamiltonian p s h (rampPosition p s) (rampMomentum p s)=nuclearKinetic p+sourcePotential := by
  have velocity : rampMomentum p s-vectorControl p s h=fun i => h*rampMomentum p s i := by
    funext i; simp only [Pi.sub_apply,vectorControl]; ring
  rw [rampHamiltonian,velocity,kinetic_scale,scalarControl]
  ring

theorem ramp_control_off (p r momentum : Configuration) :
    rampHamiltonian p 0 1 r momentum=baselineHamiltonian r momentum := by
  have hv : vectorControl p 0 1=0 := by funext i; simp [vectorControl]
  rw [rampHamiltonian,hv,sub_zero]
  simp only [scalarControl,ramp_momentum_zero,ramp_position_zero,one_pow,one_mul,sub_self,
    forcePairing,Finset.sum_const_zero,mul_zero,add_zero,baselineHamiltonian,sourcePotentialGerm]
  ring

theorem ramp_control_held (p r momentum : Configuration) :
    rampHamiltonian p 0 0 r momentum=nuclearKinetic (momentum-p)+sourcePotential+nuclearKinetic p := by
  have hv : vectorControl p 0 0=p := by
    funext i; simp [vectorControl,rampMomentum]
  rw [rampHamiltonian,hv]
  simp [scalarControl]

theorem ramp_momentum_derivative (p : Configuration) (h t : ℝ) (clock : ℝ → ℝ)
    (generated : HasDerivAt clock h t) (i : Coordinate) :
    HasDerivAt (fun time => rampMomentum p (clock time) i) (h*sourceForce i) t := by
  simpa only [rampMomentum,mul_comm] using (generated.const_mul (sourceForce i)).const_add (p i)

theorem ramp_position_derivative (p : Configuration) (s h t : ℝ) (clock : ℝ → ℝ)
    (generated : HasDerivAt clock h t) (at_time : clock t=s) (i : Coordinate) :
    HasDerivAt (fun time => rampPosition p (clock time) i)
      (h*rampMomentum p s i/mass i) t := by
  have hd : HasDerivAt (fun time => rampPosition p (clock time) i)
      ((p i*h+sourceForce i*(2*clock t*h)/2)/mass i) t := by
    simpa [rampPosition] using!
      (((generated.const_mul (p i)).add (((generated.pow 2).const_mul (sourceForce i)).div_const 2)).div_const (mass i)).const_add (sourcePosition i)
  convert hd using 1
  rw [at_time]
  unfold rampMomentum
  ring

theorem input_body : input.joint.body=Runtime.sourceOutput := by
  unfold input
  rw [Coulomb.Runtime.actual_material]
  rfl

theorem input_position (i : Coordinate) :
    (input.joint.body.frame.position i.1 i.2 : ℝ)=sourcePosition i := by
  rw [input_body]
  rfl

theorem input_momentum (i : Coordinate) : initialMomentum i=2*sourceMomentum i := by
  rw [initialMomentum,input_body]
  change (boostedMomentum i.1 i.2 : ℝ)=_
  simp [boostedMomentum,sourceMomentum]

theorem ramp_normal_form (p r momentum : Configuration) (s h : ℝ) :
    rampHamiltonian p s h r momentum=nuclearKinetic p+sourcePotential+
      ∑ i, ((momentum i-rampMomentum p s i)^2/(2*mass i)+
        h*rampMomentum p s i*(momentum i-rampMomentum p s i)/mass i-
        h*sourceForce i*(r i-rampPosition p s i)) := by
  have kinetic : nuclearKinetic (momentum-vectorControl p s h)-h^2*nuclearKinetic (rampMomentum p s)=
      ∑ i, ((momentum i-rampMomentum p s i)^2/(2*mass i)+
        h*rampMomentum p s i*(momentum i-rampMomentum p s i)/mass i) := by
    unfold nuclearKinetic
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply,vectorControl]
    ring
  have potential : h*forcePairing (rampPosition p s)-h*forcePairing r=
      ∑ i, -(h*sourceForce i*(r i-rampPosition p s i)) := by
    unfold forcePairing
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [rampHamiltonian,scalarControl]
  calc
    _ = nuclearKinetic p+sourcePotential+
      (nuclearKinetic (momentum-vectorControl p s h)-h^2*nuclearKinetic (rampMomentum p s))+
      (h*forcePairing (rampPosition p s)-h*forcePairing r) := by ring
    _ = _ := by rw [kinetic,potential,add_assoc,← Finset.sum_add_distrib]; rfl

theorem ramp_clock_derivative (p : Configuration) (clock rate : ℝ → ℝ) (t s h ds dh : ℝ)
    (hs : HasDerivAt clock ds t) (hh : HasDerivAt rate dh t)
    (vs : clock t=s) (vh : rate t=h) :
    HasDerivAt (fun time => rampHamiltonian p (clock time) (rate time)
      (rampPosition p s) (rampMomentum p s)) 0 t := by
  have each (i : Coordinate) : HasDerivAt (fun time =>
      (rampMomentum p s i-rampMomentum p (clock time) i)^2/(2*mass i)+
      rate time*rampMomentum p (clock time) i*
        (rampMomentum p s i-rampMomentum p (clock time) i)/mass i-
      rate time*sourceForce i*(rampPosition p s i-rampPosition p (clock time) i)) 0 t := by
    have hp := ramp_momentum_derivative p ds t clock hs i
    have hr := ramp_position_derivative p s ds t clock hs vs i
    have dp := (hasDerivAt_const t (rampMomentum p s i)).sub hp
    have dr := (hasDerivAt_const t (rampPosition p s i)).sub hr
    have hd := (((dp.pow 2).div_const (2*mass i)).add
      (((hh.mul hp).mul dp).div_const (mass i))).sub ((hh.mul_const (sourceForce i)).mul dr)
    convert hd using 1 <;> try rfl
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    simp only [vs,vh,sub_self,mul_zero,zero_sub]
    ring
  simp_rw [ramp_normal_form]
  simpa only [Finset.sum_const_zero] using!
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => each i)).const_add (nuclearKinetic p+sourcePotential)

theorem ramp_position_partial (p : Configuration) (s h : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => rampHamiltonian p s h
      (Function.update (rampPosition p s) i (rampPosition p s i+x)) (rampMomentum p s))
        (-h*sourceForce i) 0 := by
  have normal (x : ℝ) : rampHamiltonian p s h
      (Function.update (rampPosition p s) i (rampPosition p s i+x)) (rampMomentum p s)=
      nuclearKinetic p+sourcePotential-h*sourceForce i*x := by
    rw [ramp_normal_form]
    have entry (j : Coordinate) :
        (rampMomentum p s j-rampMomentum p s j)^2/(2*mass j)+
        h*rampMomentum p s j*(rampMomentum p s j-rampMomentum p s j)/mass j-
        h*sourceForce j*((Function.update (rampPosition p s) i (rampPosition p s i+x)) j-rampPosition p s j)=
        if j=i then -h*sourceForce i*x else 0 := by
      by_cases same : j=i
      · subst j; simp
      · simp [same]
    simp_rw [entry]
    simp
    ring
  simp_rw [normal]
  simpa using! (hasDerivAt_const (0 : ℝ) (nuclearKinetic p+sourcePotential)).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul (h*sourceForce i))

theorem ramp_momentum_partial (p : Configuration) (s h : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => rampHamiltonian p s h (rampPosition p s)
      (Function.update (rampMomentum p s) i (rampMomentum p s i+x)))
        (h*rampMomentum p s i/mass i) 0 := by
  have normal (x : ℝ) : rampHamiltonian p s h (rampPosition p s)
      (Function.update (rampMomentum p s) i (rampMomentum p s i+x))=
      nuclearKinetic p+sourcePotential+x^2/(2*mass i)+h*rampMomentum p s i*x/mass i := by
    rw [ramp_normal_form]
    have entry (j : Coordinate) :
        ((Function.update (rampMomentum p s) i (rampMomentum p s i+x)) j-rampMomentum p s j)^2/(2*mass j)+
        h*rampMomentum p s j*((Function.update (rampMomentum p s) i (rampMomentum p s i+x)) j-rampMomentum p s j)/mass j-
        h*sourceForce j*(rampPosition p s j-rampPosition p s j)=
        if j=i then x^2/(2*mass i)+h*rampMomentum p s i*x/mass i else 0 := by
      by_cases same : j=i
      · subst j; simp
      · simp [same]
    simp_rw [entry]
    simp
    ring
  simp_rw [normal]
  simpa using! ((((hasDerivAt_id (0 : ℝ)).pow 2).div_const (2*mass i)).const_add
    (nuclearKinetic p+sourcePotential)).add
      (((hasDerivAt_id (0 : ℝ)).const_mul (h*rampMomentum p s i)).div_const (mass i))

def initialKinetic : ℝ := nuclearKinetic initialMomentum
def initialReceiver : ℝ := input.joint.body.resource.momentum

theorem initial_kinetic_positive : 0 < initialKinetic := by
  have same : initialMomentum=fun i => 2*sourceMomentum i := funext input_momentum
  rw [initialKinetic,same,kinetic_scale,nuclear_kinetic_source]
  exact mul_pos (by norm_num) (Rat.cast_pos.mpr exact_kinetic_budget.1)

theorem initial_receiver_positive : 0 < initialReceiver := by
  rw [initialReceiver,input_body]
  exact receiver_target_positive

theorem initial_kinetic_exact : initialKinetic=(boostedKinetic : ℝ) := by
  have same : initialMomentum=fun i => 2*sourceMomentum i := funext input_momentum
  rw [initialKinetic,same,kinetic_scale,nuclear_kinetic_source,boosted_kinetic_exact]
  push_cast
  ring

-- A rational reserve is certified against this current's already-debited stock.
def reserveFloorQ : ℚ := 2/25-3*Reentry.Producer.targetMomentumKinetic
def reserveFloor : ℝ := reserveFloorQ

theorem reserve_floor_positive : 0 < reserveFloor := by
  apply Rat.cast_pos.mpr
  unfold reserveFloorQ
  linarith only [exact_kinetic_budget.2]

theorem reserve_floor_current : reserveFloor < initialReceiver := by
  have actual : initialReceiver=receiverTarget := by
    rw [initialReceiver,input_body]
    rfl
  rw [actual]
  have debit := receiver_target_debit
  rw [boosted_kinetic_exact] at debit
  push_cast at debit
  unfold reserveFloor reserveFloorQ
  push_cast
  linarith only [debit,receiver_initial_positive]

def gainQ : ℚ := reserveFloorQ/(8*(boostedKinetic+reserveFloorQ+1))
def gain : ℝ := gainQ

theorem gain_value : gain=reserveFloor/(8*(initialKinetic+reserveFloor+1)) := by
  rw [initial_kinetic_exact]
  unfold gain gainQ reserveFloor
  push_cast
  rfl

theorem gain_positive : 0 < gain := by
  rw [gain_value]
  exact div_pos reserve_floor_positive (by nlinarith [initial_kinetic_positive,reserve_floor_positive])

theorem gain_lt_one : gain < 1 := by
  rw [gain_value]
  apply (div_lt_one (by nlinarith [initial_kinetic_positive,reserve_floor_positive])).2
  nlinarith [initial_kinetic_positive,reserve_floor_positive]

theorem gain_balance : gain*(8*(initialKinetic+reserveFloor+1))=reserveFloor := by
  rw [gain_value]
  exact div_mul_cancel₀ _ (ne_of_gt (by nlinarith [initial_kinetic_positive,reserve_floor_positive]))

def plateauMomentum (fraction : ℝ) : Configuration := fun i => (1+gain*fraction)*initialMomentum i
def plateauReceiver (fraction : ℝ) : ℝ :=
  initialReceiver+initialKinetic-nuclearKinetic (plateauMomentum fraction)

theorem plateau_kinetic (fraction : ℝ) :
    nuclearKinetic (plateauMomentum fraction)=(1+gain*fraction)^2*initialKinetic :=
  kinetic_scale initialMomentum (1+gain*fraction)

theorem target_debit_positive_and_bounded :
    0 < nuclearKinetic (plateauMomentum 1)-initialKinetic ∧
      nuclearKinetic (plateauMomentum 1)-initialKinetic < initialReceiver/2 := by
  rw [plateau_kinetic]
  simp only [mul_one]
  have gp := gain_positive
  have kp := initial_kinetic_positive
  have g1 := gain_lt_one
  have g2 : gain^2 ≤ gain := by nlinarith
  have g2k := mul_le_mul_of_nonneg_right g2 kp.le
  have small : 8*gain*initialKinetic < initialReceiver := by
    have other : 0 < gain*(reserveFloor+1) := mul_pos gp (by linarith [reserve_floor_positive])
    nlinarith [gain_balance,reserve_floor_current]
  constructor
  · have growth : 0 < ((1+gain)^2-1)*initialKinetic :=
      mul_pos (by nlinarith) kp
    nlinarith
  · calc
      (1+gain)^2*initialKinetic-initialKinetic ≤ 3*gain*initialKinetic := by nlinarith
      _ < initialReceiver/2 := by linarith [initial_receiver_positive]

theorem plateau_receiver_positive (fraction : ℝ) (lo : 0 ≤ fraction) (hi : fraction ≤ 1) :
    initialReceiver/2 < plateauReceiver fraction := by
  have gp := gain_positive
  have kp := initial_kinetic_positive
  have gl : 0 ≤ gain*fraction := mul_nonneg gp.le lo
  have gh : gain*fraction ≤ gain := by nlinarith
  have sq : (1+gain*fraction)^2 ≤ (1+gain)^2 := by nlinarith
  have capped := mul_le_mul_of_nonneg_right sq kp.le
  have terminal := target_debit_positive_and_bounded.2
  rw [plateau_kinetic] at terminal
  simp only [mul_one] at terminal
  rw [plateauReceiver,plateau_kinetic]
  linarith

def progress (t : ℝ) : ℝ := 3*(t/duration)^2-2*(t/duration)^3

theorem progress_endpoints : progress 0=0 ∧ progress duration=1 := by
  norm_num [progress,ne_of_gt duration_positive]

theorem progress_range (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ duration) :
    0 ≤ progress t ∧ progress t ≤ 1 := by
  have xlo : 0 ≤ t/duration := div_nonneg lo duration_positive.le
  have xhi : t/duration ≤ 1 := (div_le_one duration_positive).2 hi
  have lower : 0 ≤ (t/duration)^2*(3-2*(t/duration)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have upper : 0 ≤ (1-t/duration)^2*(1+2*(t/duration)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  unfold progress
  constructor <;> nlinarith

theorem finite_plateau_stock (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ duration) :
    initialReceiver/2 < plateauReceiver (progress t) :=
  plateau_receiver_positive _ (progress_range t lo hi).1 (progress_range t lo hi).2

theorem on_clock_derivative (p : Configuration) (t : ℝ) :
    HasDerivAt (fun time => rampHamiltonian p (onTime time) (onRate time)
      (rampPosition p (onTime t)) (rampMomentum p (onTime t))) 0 t := by
  have rate : DifferentiableAt ℝ onRate t := by unfold onRate; fun_prop
  exact ramp_clock_derivative p onTime onRate t _ _ _ _
    (on_time_derivative t) rate.hasDerivAt rfl rfl

theorem off_clock_derivative (p : Configuration) (t : ℝ) :
    HasDerivAt (fun time => rampHamiltonian p (offTime time) (offRate time)
      (rampPosition p (offTime t)) (rampMomentum p (offTime t))) 0 t := by
  have rate : DifferentiableAt ℝ offRate t := by unfold offRate; fun_prop
  exact ramp_clock_derivative p offTime offRate t _ _ _ _
    (off_time_derivative t) rate.hasDerivAt rfl rfl

theorem actual_on_equations (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => rampPosition initialMomentum (onTime time) i)
      (onRate t*rampMomentum initialMomentum (onTime t) i/mass i) t ∧
    HasDerivAt (fun time => rampMomentum initialMomentum (onTime time) i)
      (onRate t*sourceForce i) t ∧
    rampHamiltonian initialMomentum (onTime t) (onRate t)
      (rampPosition initialMomentum (onTime t)) (rampMomentum initialMomentum (onTime t))=
        initialKinetic+sourcePotential :=
  ⟨ramp_position_derivative _ _ _ _ _ (on_time_derivative t) rfl i,
   ramp_momentum_derivative _ _ _ _ (on_time_derivative t) i,ramp_energy _ _ _⟩

def targetMomentumQ (i : Coordinate) : ℚ :=
  (1+gainQ)*input.joint.body.frame.momentum i.1 i.2

theorem target_momentum_rational (i : Coordinate) :
    plateauMomentum 1 i=(targetMomentumQ i : ℝ) := by
  simp [plateauMomentum,targetMomentumQ,gain,initialMomentum]

theorem ramp_junctions (p r momentum : Configuration) :
    rampHamiltonian p (onTime 0) (onRate 0) r momentum=baselineHamiltonian r momentum ∧
    rampHamiltonian p (onTime duration) (onRate duration) r momentum=
      nuclearKinetic (momentum-p)+sourcePotential+nuclearKinetic p ∧
    rampHamiltonian p (offTime 0) (offRate 0) r momentum=
      nuclearKinetic (momentum-p)+sourcePotential+nuclearKinetic p ∧
    rampHamiltonian p (offTime duration) (offRate duration) r momentum=baselineHamiltonian r momentum := by
  rcases ramp_endpoints with ⟨a,b,c,d,e,f,g,h⟩
  rw [a,b,c,d,e,f,g,h]
  exact ⟨ramp_control_off _ _ _,ramp_control_held _ _ _,ramp_control_held _ _ _,ramp_control_off _ _ _⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
