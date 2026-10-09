import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Fock
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.JetRecovery

/-!
The actual Gaussian Coulomb kernels respect source-field relations. Continuous
Gaussian representatives recover pointwise zero from L² zero; the paid source
integrability then carries finite contractions through the literal integrals.
The full raw Fock action consequently factors through its generated normed frame.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace CPS1ReactiveFieldDynamics.KernelRecovery
noncomputable section
open CPS1ElectronicSource MeasureTheory InnerProductSpace
open CPS1ReactiveFieldDynamics.JetRecovery
open scoped BigOperators Matrix InnerProductSpace
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement
open SourceGaussianModel (raise)
variable {ι : Type*} [Fintype ι]

def primitiveValue (source : Primitive) (jet : Fin 3 → Nat) (spin : Bool) (x : Point) : ℂ :=
  if source.spin = spin then orbitalValue source.centre source.mode jet x else 0

omit [Fintype ι] in
theorem primitive_jet_value (source : Primitive) (jet : Fin 3 → Nat) (spin : Bool) :
    source.jet jet spin =ᵐ[volume] primitiveValue source jet spin := by
  by_cases same : source.spin = spin
  · subst spin
    filter_upwards [orbital_field_source source.centre source.mode jet] with x actual
    simpa [CPS1ReactiveField.Carried.Primitive.jet, primitiveValue] using actual
  · filter_upwards [] with x
    simp [CPS1ReactiveField.Carried.Primitive.jet, primitiveValue, same]

omit [Fintype ι] in
theorem primitive_value_continuous (source : Primitive) (jet : Fin 3 → Nat) (spin : Bool) :
    Continuous (primitiveValue source jet spin) := by
  change Continuous (fun x : Point => primitiveValue source jet spin x)
  by_cases same : source.spin = spin
  · simpa only [primitiveValue, if_pos same] using orbital_continuous source.centre source.mode jet
  · simp only [primitiveValue, if_neg same]
    exact continuous_const

theorem weighted_jet_value (source : ι → Primitive) (weights : ι → ℂ)
    (jet : Fin 3 → Nat) (spin : Bool) :
    weightedJet source weights jet spin =ᵐ[volume]
      fun x => ∑ index, weights index * primitiveValue (source index) jet spin x := by
  have each (index : ι) :
      (fun x : Point => (weights index • (source index).jet jet spin) x) =ᵐ[volume]
        fun x => weights index * primitiveValue (source index) jet spin x := by
    filter_upwards [Lp.coeFn_smul (weights index) ((source index).jet jet spin),
      primitive_jet_value (source index) jet spin] with x scalar sourceAt
    simpa only [Pi.smul_apply, smul_eq_mul, sourceAt] using scalar
  have component : weightedJet source weights jet spin =
      ∑ index, weights index • (source index).jet jet spin := by
    change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => SpatialLp) spin)
      (∑ index, weights index • (source index).jet jet) = _
    simp only [map_sum, map_smul, PiLp.proj_apply]
  rw [component]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun index => weights index • (source index).jet jet spin),
    Filter.eventually_all.mpr each] with x summed scalar
  exact summed.trans (Finset.sum_congr rfl (fun index _ => scalar index))

/-- The actual continuous Gaussian representatives recover a source L² null relation. -/
theorem weighted_value_zero (source : ι → Primitive) (weights : ι → ℂ)
    (jet : Fin 3 → Nat) (zero : weightedJet source weights jet = 0)
    (spin : Bool) (x : Point) :
    (∑ index, weights index * primitiveValue (source index) jet spin x) = 0 := by
  have sourceEq := weighted_jet_value source weights jet spin
  rw [zero] at sourceEq
  have almostZero : (fun x : Point => ∑ index, weights index * primitiveValue (source index) jet spin x)
      =ᵐ[volume] (fun _ : Point => (0 : ℂ)) :=
    sourceEq.symm.trans (Lp.coeFn_zero ℂ 2 (volume : Measure Point))
  have regular : Continuous (fun x : Point =>
      ∑ index, weights index * primitiveValue (source index) jet spin x) :=
    continuous_finsetSum Finset.univ (fun index _ =>
      continuous_const.mul (primitive_value_continuous (source index) jet spin))
  exact congrFun ((Continuous.ae_eq_iff_eq (volume : Measure Point) regular continuous_const).mp almostZero) x

def nuclearIntegrand (state : Snapshot) (p q : state.PrimitiveIndex)
    (spin : Bool) (nuclear x : Point) : ℂ :=
  (SourceCoulomb.kernel (x - nuclear) : ℂ) *
    star (primitiveValue (state.primitive p) 0 spin x) * primitiveValue (state.primitive q) 0 spin x

def pairIntegrand (state : Snapshot) (p q r s : state.PrimitiveIndex)
    (spin secondSpin : Bool) (z : Point × Point) : ℂ :=
  (SourceCoulomb.kernel (z.1 - z.2) : ℂ) *
    star (primitiveValue (state.primitive p) 0 spin z.1) * primitiveValue (state.primitive q) 0 spin z.1 *
    star (primitiveValue (state.primitive r) 0 secondSpin z.2) * primitiveValue (state.primitive s) 0 secondSpin z.2

omit [Fintype ι] in
theorem nuclear_integrable (state : Snapshot) (p q : state.PrimitiveIndex) (spin : Bool) (nuclear : Point) :
    Integrable (nuclearIntegrand state p q spin nuclear) volume := by
  change Integrable (fun x : Point => nuclearIntegrand state p q spin nuclear x) volume
  by_cases first : (state.primitive p).spin = spin <;>
    by_cases second : (state.primitive q).spin = spin
  · simpa only [nuclearIntegrand, primitiveValue, if_pos first, if_pos second] using
      CPS1MolecularFrame.multicentre_nuclear_integrable (state.primitive p).centre (state.primitive q).centre
        (state.primitive p).mode (state.primitive q).mode nuclear 0 0
  all_goals simp [nuclearIntegrand, primitiveValue, first, second]

omit [Fintype ι] in
theorem pair_integrable (state : Snapshot) (p q r s : state.PrimitiveIndex) (spin secondSpin : Bool) :
    Integrable (pairIntegrand state p q r s spin secondSpin) ((volume : Measure Point).prod volume) := by
  change Integrable (fun z : Point × Point => pairIntegrand state p q r s spin secondSpin z)
    ((volume : Measure Point).prod volume)
  by_cases first : (state.primitive p).spin = spin <;>
    by_cases second : (state.primitive q).spin = spin <;>
    by_cases third : (state.primitive r).spin = secondSpin <;>
    by_cases fourth : (state.primitive s).spin = secondSpin
  · simpa only [pairIntegrand, primitiveValue, if_pos first, if_pos second, if_pos third, if_pos fourth] using
      CPS1MolecularFrame.multicentre_pair_integrable (state.primitive p).centre (state.primitive q).centre
        (state.primitive r).centre (state.primitive s).centre (state.primitive p).mode (state.primitive q).mode
        (state.primitive r).mode (state.primitive s).mode 0 0 0 0
  all_goals simp [pairIntegrand, primitiveValue, first, second, third, fourth]

omit [Fintype ι] in
theorem nuclear_integral (state : Snapshot) (p q : state.PrimitiveIndex) (spin : Bool) (nuclear : Point) :
    (∫ x : Point, nuclearIntegrand state p q spin nuclear x) = state.nuclearIntegral p q spin nuclear := by
  by_cases first : (state.primitive p).spin = spin <;>
    by_cases second : (state.primitive q).spin = spin <;>
    simp [nuclearIntegrand, primitiveValue, CPS1ReactiveField.Carried.Snapshot.nuclearIntegral,
      first, second, CPS1MolecularFrame.primitiveNuclearIntegral]

omit [Fintype ι] in
theorem pair_integral (state : Snapshot) (p q r s : state.PrimitiveIndex) (spin secondSpin : Bool) :
    (∫ z : Point × Point, pairIntegrand state p q r s spin secondSpin z
      ∂(volume : Measure Point).prod volume) = state.pairIntegral p q r s spin secondSpin := by
  by_cases first : (state.primitive p).spin = spin <;>
    by_cases second : (state.primitive q).spin = spin <;>
    by_cases third : (state.primitive r).spin = secondSpin <;>
    by_cases fourth : (state.primitive s).spin = secondSpin <;>
    simp [pairIntegrand, primitiveValue, CPS1ReactiveField.Carried.Snapshot.pairIntegral,
      first, second, third, fourth, CPS1MolecularFrame.primitivePairIntegral]

omit [Fintype ι] in
theorem nuclear_null_right (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (p : state.PrimitiveIndex)
    (spin : Bool) (nuclear : Point) :
    (∑ q, weights q * state.nuclearIntegral p q spin nuclear) = 0 := by
  calc
    _ = ∫ x : Point, ∑ q, weights q * nuclearIntegrand state p q spin nuclear x := by
      rw [integral_finsetSum Finset.univ (fun q _ =>
        (nuclear_integrable state p q spin nuclear).const_mul (weights q))]
      simp only [integral_const_mul, nuclear_integral]
    _ = 0 := by
      have integrandZero : (fun x : Point => ∑ q, weights q * nuclearIntegrand state p q spin nuclear x) =
          (fun _ : Point => (0 : ℂ)) := by
        funext x
        calc
          _ = ((SourceCoulomb.kernel (x - nuclear) : ℂ) *
              star (primitiveValue (state.primitive p) 0 spin x)) *
              (∑ q, weights q * primitiveValue (state.primitive q) 0 spin x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            unfold nuclearIntegrand
            ring
          _ = 0 := by rw [weighted_value_zero state.primitive weights 0 zero spin x, mul_zero]
      rw [integrandZero, integral_zero]

omit [Fintype ι] in
theorem nuclear_null_left (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (q : state.PrimitiveIndex)
    (spin : Bool) (nuclear : Point) :
    (∑ p, star (weights p) * state.nuclearIntegral p q spin nuclear) = 0 := by
  have generated := congrArg star (nuclear_null_right state weights zero q spin nuclear)
  simpa only [star_sum, star_mul, nuclear_star, star_zero, mul_comm] using generated

omit [Fintype ι] in
theorem pair_null_second (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (p r s : state.PrimitiveIndex)
    (spin secondSpin : Bool) :
    (∑ q, weights q * state.pairIntegral p q r s spin secondSpin) = 0 := by
  calc
    _ = ∫ z : Point × Point, ∑ q, weights q * pairIntegrand state p q r s spin secondSpin z
        ∂(volume : Measure Point).prod volume := by
      rw [integral_finsetSum Finset.univ (fun q _ =>
        (pair_integrable state p q r s spin secondSpin).const_mul (weights q))]
      simp only [integral_const_mul, pair_integral]
    _ = 0 := by
      have integrandZero : (fun z : Point × Point => ∑ q, weights q * pairIntegrand state p q r s spin secondSpin z) =
          (fun _ : Point × Point => (0 : ℂ)) := by
        funext z
        calc
          _ = ((SourceCoulomb.kernel (z.1 - z.2) : ℂ) *
              star (primitiveValue (state.primitive p) 0 spin z.1) *
              star (primitiveValue (state.primitive r) 0 secondSpin z.2) *
              primitiveValue (state.primitive s) 0 secondSpin z.2) *
              (∑ q, weights q * primitiveValue (state.primitive q) 0 spin z.1) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            unfold pairIntegrand
            ring
          _ = 0 := by rw [weighted_value_zero state.primitive weights 0 zero spin z.1, mul_zero]
      rw [integrandZero, integral_zero]

omit [Fintype ι] in
theorem pair_null_first (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (q r s : state.PrimitiveIndex)
    (spin secondSpin : Bool) :
    (∑ p, star (weights p) * state.pairIntegral p q r s spin secondSpin) = 0 := by
  have generated := congrArg star (pair_null_second state weights zero q s r spin secondSpin)
  simpa only [star_sum, star_mul, pair_star, star_zero, mul_comm] using generated

omit [Fintype ι] in
theorem pair_null_fourth (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (p q r : state.PrimitiveIndex)
    (spin secondSpin : Bool) :
    (∑ s, weights s * state.pairIntegral p q r s spin secondSpin) = 0 := by
  have same : (∑ s, weights s * state.pairIntegral p q r s spin secondSpin) =
      ∑ s, weights s * state.pairIntegral r s p q secondSpin spin := by
    apply Finset.sum_congr rfl
    intro s _
    rw [pair_swap]
  rw [same]
  exact pair_null_second state weights zero r p q secondSpin spin

omit [Fintype ι] in
theorem pair_null_third (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (p q s : state.PrimitiveIndex)
    (spin secondSpin : Bool) :
    (∑ r, star (weights r) * state.pairIntegral p q r s spin secondSpin) = 0 := by
  have generated := congrArg star (pair_null_fourth state weights zero q p s spin secondSpin)
  simpa only [star_sum, star_mul, pair_star, star_zero, mul_comm] using generated

omit [Fintype ι] in
theorem kinetic_null_right (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (p : state.PrimitiveIndex) :
    (∑ q, weights q * rawKinetic state p q) = 0 := by
  have innerZero (axis : Fin 3) : (∑ q, weights q *
      inner ℂ ((state.primitive p).jet (raise 0 axis)) ((state.primitive q).jet (raise 0 axis))) = 0 := by
    have generated := congrArg (inner ℂ ((state.primitive p).jet (raise 0 axis)))
      (weighted_jet_all_zero state.primitive weights zero (raise 0 axis))
    simpa only [weightedJet, inner_sum, inner_smul_right, inner_zero_right] using generated
  calc
    _ = ((1 / (2 * state.electronInertia) : ℝ) : ℂ) * ∑ axis : Fin 3, ∑ q,
        weights q * inner ℂ ((state.primitive p).jet (raise 0 axis)) ((state.primitive q).jet (raise 0 axis)) := by
      simp only [rawKinetic, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro axis _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = 0 := by simp only [innerZero, Finset.sum_const_zero, mul_zero]

omit [Fintype ι] in
theorem attraction_null_right (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (p : state.PrimitiveIndex) :
    (∑ q, weights q * rawAttraction state p q) = 0 := by
  have nodeZero (nuclear : CPS1AtomicDynamics.Body.Node) :
      (∑ q, weights q * (-(nuclear.particle.charge : ℂ) *
        ∑ spin : Bool, state.nuclearIntegral p q spin (Geometry.nucleusPosition nuclear))) = 0 := by
    calc
      _ = -(nuclear.particle.charge : ℂ) * ∑ spin : Bool, ∑ q,
          weights q * state.nuclearIntegral p q spin (Geometry.nucleusPosition nuclear) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro spin _
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = 0 := by simp only [nuclear_null_right state weights zero, Finset.sum_const_zero, mul_zero]
  have nodesZero (nodes : List CPS1AtomicDynamics.Body.Node) :
      (∑ q, weights q * (nodes.map (fun nuclear => -(nuclear.particle.charge : ℂ) *
        ∑ spin : Bool, state.nuclearIntegral p q spin (Geometry.nucleusPosition nuclear))).sum) = 0 := by
    induction nodes with
    | nil => simp only [List.map_nil, List.sum_nil, mul_zero, Finset.sum_const_zero]
    | cons node rest previous =>
      simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, nodeZero, previous, zero_add]
  exact nodesZero state.nuclei

omit [Fintype ι] in
theorem core_null_right (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (p : state.PrimitiveIndex) :
    (∑ q, weights q * rawCore state p q) = 0 := by
  simp only [rawCore, mul_add, Finset.sum_add_distrib,
    kinetic_null_right state weights zero, attraction_null_right state weights zero, zero_add]

omit [Fintype ι] in
theorem tensor_null_third (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (p j l : state.PrimitiveIndex) :
    (∑ k, weights k * rawTensor state p j k l) = 0 := by
  simp only [rawTensor, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro spin _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro secondSpin _
  exact pair_null_second state weights zero p j l spin secondSpin

omit [Fintype ι] in
theorem tensor_null_fourth (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (p j l : state.PrimitiveIndex) :
    (∑ k, weights k * rawTensor state p j l k) = 0 := by
  simp only [rawTensor, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro spin _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro secondSpin _
  exact pair_null_fourth state weights zero p l j spin secondSpin

omit [Fintype ι] in
/-- The complete actual Fock action annihilates every zeroth source-field null relation. -/
theorem raw_fock_null_right (state : Snapshot) (weights : state.PrimitiveIndex → ℂ)
    (zero : weightedJet state.primitive weights 0 = 0) (p : state.PrimitiveIndex) :
    (∑ k, weights k * rawFock state p k) = 0 := by
  have pairZero : (∑ k, weights k * ∑ j, ∑ l,
      rawDensity state l j * (rawTensor state p j k l - rawTensor state p j l k)) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro l _
    calc
      _ = rawDensity state l j * ((∑ k, weights k * rawTensor state p j k l) -
          (∑ k, weights k * rawTensor state p j l k)) := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> ring
      _ = 0 := by rw [tensor_null_third state weights zero, tensor_null_fourth state weights zero,
        sub_self, mul_zero]
  simp only [rawFock, CPS1Deformation.FiniteVariation.fock, CPS1Deformation.FiniteVariation.interaction,
    mul_add, Finset.sum_add_distrib, core_null_right state weights zero, pairZero, zero_add]

omit [Fintype ι] in
/-- The source-generated frame recovers the action on the literal stored coefficients. -/
theorem raw_fock_current_coordinates (state : Snapshot) :
    rawFock state * state.occupied = rawFock state * sourceCoefficient state * coordinates state := by
  rw [Matrix.mul_assoc]
  ext p slot
  let weights : state.PrimitiveIndex → ℂ := fun q =>
    state.occupied q slot - (sourceCoefficient state * coordinates state) q slot
  have zero : weightedJet state.primitive weights 0 = 0 := by
    simp only [weightedJet, weights, sub_smul, Finset.sum_sub_distrib]
    change state.fields slot - CPS1ElectronicEvolution.fields (raw state)
      (sourceCoefficient state * coordinates state) slot = 0
    rw [CPS1Deformation.fields_mul]
    have synthesis : CPS1ElectronicEvolution.fields (raw state) (sourceCoefficient state) = basis state :=
      funext (basis_jet_zero state)
    rw [synthesis, current_coordinates, sub_self]
  have generated := raw_fock_null_right state weights zero p
  have right : (∑ q, rawFock state p q *
      (state.occupied q slot - (sourceCoefficient state * coordinates state) q slot)) = 0 := by
    simpa only [weights, mul_comm] using generated
  simp only [mul_sub, Finset.sum_sub_distrib] at right
  exact sub_eq_zero.mp right

end
end CPS1ReactiveFieldDynamics.KernelRecovery
