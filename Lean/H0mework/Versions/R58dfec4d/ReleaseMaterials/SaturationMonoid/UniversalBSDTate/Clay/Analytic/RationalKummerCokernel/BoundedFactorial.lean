import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Integral.Inventory
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel.CompletionExact

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.UniversalBSDRationalKummerCokernel

open CategoryTheory CategoryTheory.Limits
open UniversalBSDGeometricGalois UniversalBSDRationalKummerCohomology
open UniversalBSDRationalKummerCohomology.RationalKummerBoundaryCochainData
open UniversalBSDRationalMordellWeilHeight (rationalNaiveHeight)
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CofinalAllPrimeTopology

open private point_evaluation_injective stageKummer kummer_kernel level level_pos from
  H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel

abbrev RationalKummerFamily (source : RationalEllipticCurveSource) :=
  (p : Nat.Primes) → PrimePowerTorsionCompletion (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) p

variable (source : RationalEllipticCurveSource) (family : RationalKummerFamily source)

private def sourceKummerFamily : AllPrimeCompletion (RationalPoints source) :=
  fun p => (cokernelConnectingAtLimit (pointEvaluation source) (point_evaluation_injective source) p).toFun (family p)

/-- An original coherent evaluator-cokernel family supplies its actual Kummer class at each stage. -/
def rationalKummerFamilyClass (p : Nat.Primes) (j : Nat) : GlobalKummerH1 source (level p j) :=
  (cokernelKummer source p j).toFun
    ((torsionCompletionRestriction (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) p j).hom.toFun (family p))

private theorem point_kummer_family_read (point : RationalPoints source) (p : Nat.Primes) (j : Nat) :
    sourceGeneratedRationalKummerClass source (level p j) (level_pos p j) point = rationalKummerFamilyClass source family p j ↔
      stageProjection p j point = (restriction (L := RationalPoints source) p j).hom (sourceKummerFamily source family p) := by
  let read := stageKummer source p j
  have faithful : Function.Injective read :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ (kummer_kernel source p j))
  have native : read (stageProjection p j point) = sourceGeneratedRationalKummerClass source (level p j) (level_pos p j) point :=
    (congrArg read (actual_kummer_division_reads_source source p j point)).symm.trans
      (actual_kummer_cokernel_class source p j point)
  have supplied : read ((restriction (L := RationalPoints source) p j).hom (sourceKummerFamily source family p)) =
      rationalKummerFamilyClass source family p j :=
    congrArg read (cokernel_connecting_limit_restriction (pointEvaluation source)
      (point_evaluation_injective source) p j (family p))
  exact ⟨fun same => faithful (native.trans (same.trans supplied.symm)),
    fun same => native.symm.trans ((congrArg read same).trans supplied)⟩

/-- The actual Kummer classes at all prime powers of a factorial modulus. -/
def rationalKummerMatchesAt (address : Nat) (point : RationalPoints source) : Prop :=
  let modulus := factorialModulus address
  ∀ p : modulusPrimes modulus,
    sourceGeneratedRationalKummerClass source (level p.val (modulusDepth modulus p))
      (level_pos p.val (modulusDepth modulus p)) point = rationalKummerFamilyClass source family p.val (modulusDepth modulus p)

private theorem rational_kummer_factorial_read (address : Nat) (point : RationalPoints source) :
    rationalKummerMatchesAt source family address point ↔
      modulusProjection (factorialModulus address) point =
        (factorialRestriction (L := RationalPoints source) address).hom (factorialFromPrimes (sourceKummerFamily source family)) := by
  let modulus := factorialModulus address
  let primeFamily := sourceKummerFamily source family
  have written := factorial_from_primes_restriction address primeFamily
  have finite := modulus_projection_eq_iff modulus (factorial_modulus_ne_zero address) point primeFamily
  constructor
  · intro same
    have all := funext (fun p : modulusPrimes modulus =>
      (point_kummer_family_read source family point p.val (modulusDepth modulus p)).1 (same p))
    exact (finite.2 all).trans written.symm
  · intro same p
    have all := finite.1 (same.trans written)
    exact (point_kummer_family_read source family point p.val (modulusDepth modulus p)).2 (congrFun all p)

private theorem rational_kummer_factorial_exact (point : RationalPoints source) :
    factorialCanonicalMap point = factorialFromPrimes (sourceKummerFamily source family) ↔
      ∀ p j, sourceGeneratedRationalKummerClass source (level p j) (level_pos p j) point = rationalKummerFamilyClass source family p j := by
  let primeFamily := sourceKummerFamily source family
  constructor
  · intro same p j
    have all : allPrimeMap point = primeFamily := (factorialCompletionEquiv (L := RationalPoints source)).injective
      ((factorial_from_primes_canonical point).trans same)
    exact (point_kummer_family_read source family point p j).2
      ((allPrime_restriction p j point).symm.trans (congrArg (restriction (L := RationalPoints source) p j).hom (congrFun all p)))
  · intro same
    have all : allPrimeMap point = primeFamily := by
      funext p
      apply Concrete.limit_ext (tower (L := RationalPoints source) p)
      rintro ⟨j⟩
      exact (allPrime_restriction p j point).trans ((point_kummer_family_read source family point p j).1 (same p j))
    exact (factorial_from_primes_canonical point).symm.trans (congrArg factorialFromPrimes all)

/-- The original Northcott inventory reads the entire rational-point fibre of the Kummer family. -/
theorem actual_kummer_bounded_factorial_fibre (bound : ℝ) :
    ∃ base : Nat, ∀ address ≥ base, ∀ point : RationalPoints source, rationalNaiveHeight source point ≤ bound →
      (rationalKummerMatchesAt source family address point ↔
        ∀ p j, sourceGeneratedRationalKummerClass source (level p j) (level_pos p j) point = rationalKummerFamilyClass source family p j) := by
  classical
  let inventory := (Northcott.finite_le (h := rationalNaiveHeight source) bound).toFinset
  obtain ⟨base, fibre⟩ := factorial_integral_inventory_fibre inventory (factorialFromPrimes (sourceKummerFamily source family))
  refine ⟨base, fun address later point bounded => ?_⟩
  have stocked : point ∈ inventory := by simpa only [inventory, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using bounded
  exact (rational_kummer_factorial_read source family address point).trans
    ((fibre address later point stocked).trans (rational_kummer_factorial_exact source family point))

/-- Same-curve Kummer lifts with a common height bound give one rational point for the whole family. -/
theorem actual_kummer_bounded_factorial_source (bound : ℝ)
    (tail : ∃ base : Nat, ∀ address ≥ base, ∃ point : RationalPoints source,
      rationalNaiveHeight source point ≤ bound ∧ rationalKummerMatchesAt source family address point) :
    ∃ point : RationalPoints source, rationalNaiveHeight source point ≤ bound ∧
      ∀ p j, sourceGeneratedRationalKummerClass source (level p j) (level_pos p j) point = rationalKummerFamilyClass source family p j := by
  obtain ⟨start, each⟩ := tail
  obtain ⟨base, fibre⟩ := actual_kummer_bounded_factorial_fibre source family bound
  let address := max start base
  obtain ⟨point, bounded, actual⟩ := each address (le_max_left _ _)
  exact ⟨point, bounded, (fibre address (le_max_right _ _) point bounded).1 actual⟩

end SaturationMonoid.UniversalBSDRationalKummerCokernel
