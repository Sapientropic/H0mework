import H0mework.Physics.LowEnergy.Quantum.WavepacketInteraction

/-! Matter currents on the continuous configuration carrier. Only the matter
coefficients commute: the scalar field endomorphisms are kept separate. -/
set_option autoImplicit false
namespace SourceWavepacketCurrent
open SourceWavepacketInteraction
open scoped BigOperators
noncomputable section
variable {M I B : Type*} [Fintype I] [DecidableEq I]
variable [AddCommGroup B] [Module ℂ B] {N : ℕ}

omit [DecidableEq I] in
theorem same_line_zero (target : Finset I) (s t : M → M)
    (K L : M → I → I → Module.End ℂ B)
    (hK : ∀ p i j, K p i j ≠ 0 → i ∈ target ∧ j ∉ target)
    (hL : ∀ p i j, L p i j ≠ 0 → i ∈ target ∧ j ∉ target)
    (line : Fin N) : lineAction s K line * lineAction t L line = 0 := by
  apply LinearMap.ext
  intro ψ
  funext x
  simp only [Module.End.mul_apply, lineAction, LinearMap.coe_mk, AddHom.coe_mk,
    Function.update_self, map_sum, LinearMap.zero_apply, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  by_cases emptyK : K (x line).1 (x line).2 j = 0
  · simp [emptyK]
  · have incoming := (hK _ _ _ emptyK).2
    have emptyL : L (s (x line).1) j k = 0 := by
      by_contra nonzero
      exact incoming (hL _ _ _ nonzero).1
    simp [emptyL]

omit [DecidableEq I] in
theorem distinct_lines_commute (s t : M → M) (W V : M → Matrix I I ℂ)
    (a b : Fin N) (different : a ≠ b) :
    Commute (lineAction s (scalarKernel W (1 : Module.End ℂ B)) a)
      (lineAction t (scalarKernel V (1 : Module.End ℂ B)) b) := by
  change _ * _ = _ * _
  apply LinearMap.ext
  intro ψ
  funext x
  simp only [Module.End.mul_apply, lineAction, scalarKernel, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.smul_apply, Module.End.one_apply,
    Function.update_of_ne different, Function.update_of_ne different.symm,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [Function.update_comm different, smul_comm]

def current (shift : M → M) (W : M → Matrix I I ℂ) :
    Module.End ℂ (Wave M I B N) := interaction shift (scalarKernel W 1)

theorem currents_commute (target : Finset I) (s t : M → M)
    (W V : M → Matrix I I ℂ)
    (hW : ∀ p i j, ((if i ∈ target then 1 else 0 : ℂ) -
      (if j ∈ target then 1 else 0 : ℂ) - 1) * W p i j = 0)
    (hV : ∀ p i j, ((if i ∈ target then 1 else 0 : ℂ) -
      (if j ∈ target then 1 else 0 : ℂ) - 1) * V p i j = 0) :
    Commute (current (B := B) (N := N) s W) (current t V) := by
  change _ * _ = _ * _
  simp only [current, interaction, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases same : a = b
  · subst b
    rw [same_line_zero target s t _ _ (scalarKernel_support target W 1 hW)
        (scalarKernel_support target V 1 hV),
      same_line_zero target t s _ _ (scalarKernel_support target V 1 hV)
        (scalarKernel_support target W 1 hW)]
  · exact distinct_lines_commute s t W V a b same

def onBoson (Q : Module.End ℂ B) : Module.End ℂ (Wave M I B N) where
  toFun ψ x := Q (ψ x)
  map_add' _ _ := by ext x; exact Q.map_add _ _
  map_smul' c ψ := by ext x; exact Q.map_smul c (ψ x)

omit [DecidableEq I] in
theorem boson_commutes_current (Q : Module.End ℂ B) (s : M → M)
    (W : M → Matrix I I ℂ) :
    Commute (onBoson (M := M) (I := I) (N := N) Q) (current s W) := by
  change _ * _ = _ * _
  apply LinearMap.ext
  intro ψ
  funext x
  simp [onBoson, current, interaction, lineAction, scalarKernel,
    Finset.sum_apply, map_sum, map_smul]

omit [DecidableEq I] in
theorem boson_current_factor (Q : Module.End ℂ B) (s : M → M)
    (W : M → Matrix I I ℂ) :
    onBoson Q * current (N := N) s W = interaction s (scalarKernel W Q) := by
  apply LinearMap.ext
  intro ψ
  funext x
  simp [onBoson, current, interaction, lineAction, scalarKernel,
    Finset.sum_apply, map_sum, map_smul]

omit [Fintype I] [DecidableEq I] in
theorem onBoson_CCR (Q P : Module.End ℂ B) (d : ℂ)
    (source_CCR : Q * P - P * Q = d • 1) :
    onBoson (M := M) (I := I) (N := N) Q * onBoson P -
      onBoson P * onBoson Q = d • 1 := by
  apply LinearMap.ext
  intro ψ
  funext x
  have law := congrArg (fun U : Module.End ℂ B => U (ψ x)) source_CCR
  simpa [onBoson, Module.End.mul_apply] using law

end
end SourceWavepacketCurrent
