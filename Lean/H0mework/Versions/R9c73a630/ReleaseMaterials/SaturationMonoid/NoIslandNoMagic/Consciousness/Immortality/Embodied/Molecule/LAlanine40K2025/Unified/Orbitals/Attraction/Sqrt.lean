import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Enclosure
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceSignedEvaluator

/-- An exact integer square root of the rational floor. -/
def rationalRootFloor (q : ℚ) : ℕ := Nat.sqrt (⌊q⌋ : ℤ).toNat

theorem rational_root_floor_bounds (q : ℚ) (hq : 0 ≤ q) :
    ((rationalRootFloor q : ℚ)^2 ≤ q) ∧
      q < ((rationalRootFloor q + 1 : ℕ) : ℚ)^2 := by
  let n : ℕ := (⌊q⌋ : ℤ).toNat
  have floorNonneg : (0 : ℤ) ≤ ⌊q⌋ := Int.floor_nonneg.mpr hq
  have nFloor : (n : ℤ) = ⌊q⌋ := Int.toNat_of_nonneg floorNonneg
  have nFloorQ : (n : ℚ) = (⌊q⌋ : ℤ) := by exact_mod_cast nFloor
  have sqrtLow : (Nat.sqrt n : ℚ)^2 ≤ (n : ℚ) := by
    have h := Nat.sqrt_le n
    have hh : (Nat.sqrt n : ℚ) * (Nat.sqrt n : ℚ) ≤ (n : ℚ) := by exact_mod_cast h
    simpa only [pow_two] using hh
  have sqrtHigh : (n : ℚ) + 1 ≤ ((Nat.sqrt n + 1 : ℕ) : ℚ)^2 := by
    have h := Nat.lt_succ_sqrt n
    have h' : n + 1 ≤ (Nat.sqrt n + 1) ^ 2 := by nlinarith
    exact_mod_cast h'
  change (Nat.sqrt n : ℚ)^2 ≤ q ∧ q < ((Nat.sqrt n + 1 : ℕ) : ℚ)^2
  constructor
  · exact sqrtLow.trans (nFloorQ.trans_le (Int.floor_le q))
  · exact (Int.lt_floor_add_one q) |>.trans_le (by rw [← nFloorQ]; exact sqrtHigh)

/-- The same dyadic precision used by the original AO radial reifier, now
    justified uniformly for every positive rational argument. -/
def certifiedSqrtProposal (gamma : ℚ) : SqrtMaterial :=
  let scale : ℚ := 2^80
  { gamma := gamma
    interval := ((rationalRootFloor (piLower/gamma*scale^2) : ℚ)/scale,
      ((rationalRootFloor (piUpper/gamma*scale^2)+1 : ℕ) : ℚ)/scale) }

theorem certified_sqrt_proposal_computed (gamma : ℚ) (hgamma : 0 < gamma) :
    SqrtComputed (certifiedSqrtProposal gamma) := by
  let scale : ℚ := 2^80
  let qL : ℚ := piLower/gamma*scale^2
  let qU : ℚ := piUpper/gamma*scale^2
  let mL : ℚ := (rationalRootFloor qL : ℚ)
  let mU : ℚ := ((rationalRootFloor qU+1 : ℕ) : ℚ)
  have scalePos : 0 < scale := by dsimp [scale]; positivity
  have qLnonneg : 0 ≤ qL := by dsimp [qL,piLower]; positivity
  have qUnonneg : 0 ≤ qU := by dsimp [qU,piUpper]; positivity
  have low := (rational_root_floor_bounds qL qLnonneg).1
  have high := (rational_root_floor_bounds qU qUnonneg).2
  have low' : (mL/scale)^2*gamma ≤ piLower := by
    have mulPos : 0 ≤ gamma/scale^2 := by positivity
    have step := mul_le_mul_of_nonneg_right low mulPos
    have rearrange : (mL/scale)^2*gamma = mL^2*(gamma/scale^2) := by ring
    rw [rearrange]
    calc
      _ ≤ qL*(gamma/scale^2) := step
      _ = piLower := by dsimp [qL]; field_simp
  have high' : piUpper ≤ (mU/scale)^2*gamma := by
    have mulPos : 0 ≤ gamma/scale^2 := by positivity
    have step := mul_lt_mul_of_pos_right high (by positivity : 0 < gamma/scale^2)
    have rearrange : (mU/scale)^2*gamma = mU^2*(gamma/scale^2) := by ring
    rw [rearrange]
    have ident : qU*(gamma/scale^2) = piUpper := by dsimp [qU]; field_simp
    exact le_of_lt (ident ▸ step)
  refine ⟨hgamma, ?_, ?_, ?_⟩
  · change 0 ≤ mU/scale
    positivity
  · change (mL/scale)^2*gamma ≤ piLower
    exact low'
  · change piUpper ≤ (mU/scale)^2*gamma
    exact high'

theorem certified_sqrt_contains (gamma : ℚ) (hgamma : 0 < gamma) :
    Holds (certifiedSqrtProposal gamma).interval
      (Real.sqrt (Real.pi/gamma)) :=
  sqrt_material_contains _ (certified_sqrt_proposal_computed gamma hgamma)

end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
