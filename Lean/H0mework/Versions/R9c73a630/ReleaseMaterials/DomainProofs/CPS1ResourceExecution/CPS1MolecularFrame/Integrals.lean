import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Coulomb
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Fields
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open MeasureTheory CPS1ElectronicSource
open scoped BigOperators InnerProductSpace Matrix
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement
open SourceGaussianModel (raise)
variable {frame : CPS1Recycling.Frame}

abbrev MolecularIndex (source : CPS1ElectronicSource.State frame) :=
  FiniteNormed.Index (𝕜 := ℂ) (rawField source)

def basisCoefficient (source : CPS1ElectronicSource.State frame) :
    Matrix (PrimitiveIndex source) (MolecularIndex source) ℂ :=
  FiniteNormed.coefficients (𝕜 := ℂ) (rawField source)

def rawValue (source : CPS1ElectronicSource.State frame) (primitive : PrimitiveIndex source)
    (jet : Fin 3 → Nat) (spin : Bool) (x : CPS1ElectronicSource.Point) : ℂ :=
  if primitive.2 = spin then orbitalValue (position source primitive.1.1) primitive.1.2.val jet x else 0

def basisJet (source : CPS1ElectronicSource.State frame) (jet : Fin 3 → Nat)
    (index : MolecularIndex source) : SpinSpace :=
  ∑ primitive, basisCoefficient source primitive index • rawJet source primitive jet

def basisValue (source : CPS1ElectronicSource.State frame) (index : MolecularIndex source)
    (jet : Fin 3 → Nat) (spin : Bool) (x : CPS1ElectronicSource.Point) : ℂ :=
  ∑ primitive, basisCoefficient source primitive index * rawValue source primitive jet spin x

theorem basis_jet_zero (source : CPS1ElectronicSource.State frame) (index : MolecularIndex source) :
    basisJet source 0 index = FiniteNormed.field (𝕜 := ℂ) (rawField source) index :=
  (FiniteNormed.field_synthesis (𝕜 := ℂ) (rawField source) index).symm

theorem raw_jet_value (source : CPS1ElectronicSource.State frame) (primitive : PrimitiveIndex source)
    (jet : Fin 3 → Nat) (spin : Bool) :
    rawJet source primitive jet spin =ᵐ[volume] rawValue source primitive jet spin := by
  by_cases same : primitive.2 = spin
  · subst spin
    filter_upwards [orbital_field_source (position source primitive.1.1) primitive.1.2.val jet] with x actual
    simpa [rawJet,rawValue] using actual
  · filter_upwards [] with x
    simp [rawJet,rawValue,same]

theorem basis_jet_value (source : CPS1ElectronicSource.State frame) (index : MolecularIndex source)
    (jet : Fin 3 → Nat) (spin : Bool) :
    basisJet source jet index spin =ᵐ[volume] basisValue source index jet spin := by
  have each (primitive : PrimitiveIndex source) :
      (fun x : CPS1ElectronicSource.Point =>
        (basisCoefficient source primitive index • rawJet source primitive jet spin) x) =ᵐ[volume]
        fun x => basisCoefficient source primitive index * rawValue source primitive jet spin x := by
    filter_upwards [Lp.coeFn_smul (basisCoefficient source primitive index) (rawJet source primitive jet spin),
      raw_jet_value source primitive jet spin] with x scalar raw
    simpa only [Pi.smul_apply,smul_eq_mul,raw] using scalar
  have coordinate : basisJet source jet index spin =
      ∑ primitive, basisCoefficient source primitive index • rawJet source primitive jet spin := by
    change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => SpatialLp) spin)
      (∑ primitive, basisCoefficient source primitive index • rawJet source primitive jet) = _
    simp only [map_sum,map_smul,PiLp.proj_apply]
  rw [coordinate]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun primitive =>
      basisCoefficient source primitive index • rawJet source primitive jet spin),
    Filter.eventually_all.mpr each] with x summed scalar
  exact summed.trans (Finset.sum_congr rfl (fun primitive _ => scalar primitive))

def kinetic (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source) : ℂ :=
  ((1/(2*source.geometry.electronInertia) : ℝ) : ℂ) *
    ∑ axis : Fin 3, inner ℂ (basisJet source (raise 0 axis) i) (basisJet source (raise 0 axis) j)

def nuclearIntegral (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source)
    (nuclear : CPS1ElectronicSource.Point) : ℂ :=
  ∑ spin : Bool, ∫ x : CPS1ElectronicSource.Point, (SourceCoulomb.kernel (x-nuclear) : ℂ) *
    star (basisValue source i 0 spin x) * basisValue source j 0 spin x

def attraction (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source) : ℂ :=
  (source.geometry.nuclei.map (fun nucleus => -(nucleus.particle.charge : ℂ) *
    nuclearIntegral source i j (Geometry.nucleusPosition nucleus))).sum

def core (source : CPS1ElectronicSource.State frame) : Matrix (MolecularIndex source) (MolecularIndex source) ℂ :=
  fun i j => kinetic source i j+attraction source i j

def pairIntegral (source : CPS1ElectronicSource.State frame) (i j k l : MolecularIndex source)
    (spin firstSpin : Bool) : ℂ :=
  ∫ z : CPS1ElectronicSource.Point × CPS1ElectronicSource.Point,
    (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
    star (basisValue source i 0 spin z.1) * basisValue source j 0 spin z.1 *
    star (basisValue source k 0 firstSpin z.2) * basisValue source l 0 firstSpin z.2
    ∂(volume : Measure CPS1ElectronicSource.Point).prod volume

def twoBody (source : CPS1ElectronicSource.State frame) (i j k l : MolecularIndex source) : ℂ :=
  ∑ spin : Bool, ∑ secondSpin : Bool, pairIntegral source i k j l spin secondSpin

def fock (source : CPS1ElectronicSource.State frame)
    (density : Matrix (MolecularIndex source) (MolecularIndex source) ℂ) :
    Matrix (MolecularIndex source) (MolecularIndex source) ℂ :=
  fun i k => core source i k+∑ j, ∑ l,
    density l j * (twoBody source i j k l-twoBody source i j l k)

def electronicEnergy (source : CPS1ElectronicSource.State frame)
    (density : Matrix (MolecularIndex source) (MolecularIndex source) ℂ) : ℝ :=
  (Matrix.trace (core source * density)).re+(1/2)*
    (∑ i, ∑ j, ∑ k, ∑ l, density k i*density l j *
      (twoBody source i j k l-twoBody source i j l k)).re

def totalEnergy (source : CPS1ElectronicSource.State frame)
    (density : Matrix (MolecularIndex source) (MolecularIndex source) ℂ) : ℝ :=
  source.geometry.nuclearEnergy+electronicEnergy source density

theorem kinetic_star (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source) :
    star (kinetic source i j) = kinetic source j i := by
  unfold kinetic
  simp only [Complex.star_def,map_mul,map_sum,Complex.conj_ofReal]
  apply congrArg (fun z : ℂ => ((1/(2*source.geometry.electronInertia) : ℝ) : ℂ)*z)
  apply Finset.sum_congr rfl
  intro axis _
  exact inner_conj_symm _ _

theorem nuclear_star (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source)
    (nuclear : CPS1ElectronicSource.Point) :
    star (nuclearIntegral source i j nuclear) = nuclearIntegral source j i nuclear := by
  unfold nuclearIntegral
  simp only [star_sum]
  apply Finset.sum_congr rfl
  intro spin _
  rw [Complex.star_def,← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj]
    ring

theorem attraction_star (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source) :
    star (attraction source i j) = attraction source j i := by
  unfold attraction
  induction source.geometry.nuclei with
  | nil => simp
  | cons nucleus rest ih =>
    simp only [List.map_cons,List.sum_cons,star_add,star_mul,star_neg]
    rw [ih,nuclear_star]
    have realCharge : star (nucleus.particle.charge : ℂ) = (nucleus.particle.charge : ℂ) := by simp
    rw [realCharge]
    ring

theorem core_hermitian (source : CPS1ElectronicSource.State frame) : (core source).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [core,star_add,kinetic_star,attraction_star]

theorem pair_star (source : CPS1ElectronicSource.State frame) (i j k l : MolecularIndex source) (spin secondSpin : Bool) :
    star (pairIntegral source i j k l spin secondSpin) = pairIntegral source j i l k spin secondSpin := by
  unfold pairIntegral
  rw [Complex.star_def,← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj]
    ring

theorem pair_swap (source : CPS1ElectronicSource.State frame) (i j k l : MolecularIndex source) (spin secondSpin : Bool) :
    pairIntegral source i j k l spin secondSpin = pairIntegral source k l i j secondSpin spin := by
  unfold pairIntegral
  rw [← integral_prod_swap]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change (SourceCoulomb.kernel (z.2-z.1) : ℂ) *
      star (basisValue source i 0 spin z.2) * basisValue source j 0 spin z.2 *
      star (basisValue source k 0 secondSpin z.1) * basisValue source l 0 secondSpin z.1 = _
    rw [CPS1ElectronicSource.coulomb_kernel_sub_comm z.2 z.1]
    ring

theorem twoBody_star (source : CPS1ElectronicSource.State frame) (i j k l : MolecularIndex source) :
    star (twoBody source i j k l) = twoBody source k l i j := by
  simp only [twoBody,star_sum,pair_star]

theorem twoBody_swap (source : CPS1ElectronicSource.State frame) (i j k l : MolecularIndex source) :
    twoBody source i j k l = twoBody source j i l k := by
  unfold twoBody
  simp only [pair_swap]
  rw [Finset.sum_comm]

theorem fock_hermitian (source : CPS1ElectronicSource.State frame)
    (density : Matrix (MolecularIndex source) (MolecularIndex source) ℂ) (hermitian : density.IsHermitian) :
    (fock source density).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i k
  have coreStar : star (core source k i) = core source i k := (core_hermitian source).apply i k
  have densityStar (j l : MolecularIndex source) : star (density l j) = density j l := hermitian.apply j l
  simp only [fock,star_add,star_sum,star_mul,star_sub,coreStar,densityStar,twoBody_star]
  rw [Finset.sum_comm]
  apply congrArg (fun z : ℂ => core source i k+z)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [twoBody_swap source j i k l]
  ring

theorem raw_nuclear_integrable (source : CPS1ElectronicSource.State frame)
    (p q : PrimitiveIndex source) (jetP jetQ : Fin 3 → Nat) (spin : Bool) (nuclear : CPS1ElectronicSource.Point) :
    Integrable (fun x : CPS1ElectronicSource.Point => (SourceCoulomb.kernel (x-nuclear) : ℂ) *
      star (rawValue source p jetP spin x) * rawValue source q jetQ spin x) volume := by
  by_cases first : p.2 = spin <;> by_cases second : q.2 = spin
  · simpa only [rawValue,if_pos first,if_pos second] using
      multicentre_nuclear_integrable (position source p.1.1) (position source q.1.1)
        p.1.2.val q.1.2.val nuclear jetP jetQ
  all_goals simp [rawValue,first,second]

theorem raw_pair_integrable (source : CPS1ElectronicSource.State frame)
    (p q r s : PrimitiveIndex source) (jetP jetQ jetR jetS : Fin 3 → Nat) (spin secondSpin : Bool) :
    Integrable (fun z : CPS1ElectronicSource.Point × CPS1ElectronicSource.Point =>
      (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
      star (rawValue source p jetP spin z.1) * rawValue source q jetQ spin z.1 *
      star (rawValue source r jetR secondSpin z.2) * rawValue source s jetS secondSpin z.2)
      ((volume : Measure CPS1ElectronicSource.Point).prod volume) := by
  by_cases first : p.2 = spin <;> by_cases second : q.2 = spin <;>
    by_cases third : r.2 = secondSpin <;> by_cases fourth : s.2 = secondSpin
  · simpa only [rawValue,if_pos first,if_pos second,if_pos third,if_pos fourth] using
      multicentre_pair_integrable (position source p.1.1) (position source q.1.1)
        (position source r.1.1) (position source s.1.1) p.1.2.val q.1.2.val r.1.2.val s.1.2.val
        jetP jetQ jetR jetS
  all_goals simp [rawValue,first,second,third,fourth]

theorem basis_nuclear_pointwise (source : CPS1ElectronicSource.State frame)
    (i j : MolecularIndex source) (jetI jetJ : Fin 3 → Nat) (spin : Bool)
    (nuclear x : CPS1ElectronicSource.Point) :
    (SourceCoulomb.kernel (x-nuclear) : ℂ) * star (basisValue source i jetI spin x) * basisValue source j jetJ spin x =
      ∑ p, ∑ q, (star (basisCoefficient source p i)*basisCoefficient source q j) *
        ((SourceCoulomb.kernel (x-nuclear) : ℂ) * star (rawValue source p jetI spin x) * rawValue source q jetJ spin x) := by
  simp only [basisValue,star_sum,star_mul]
  rw [mul_assoc,Finset.sum_mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

private theorem ordered_four_products {I : Type*} [Fintype I] (a b c d e f g h : I → ℂ) (kernel : ℂ) :
 kernel * (∑ p, a p*b p) * (∑ q, c q*d q) * (∑ r, e r*f r) * (∑ s, g s*h s) =
 ∑ p, ∑ q, ∑ r, ∑ s, (a p*c q*e r*g s)*(kernel*b p*d q*f r*h s) := by
 rw [Finset.mul_sum Finset.univ (fun p => a p*b p) kernel,Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro p _
 rw [Finset.mul_sum Finset.univ (fun q => c q*d q) (kernel*(a p*b p)),Finset.sum_mul,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro q _
 rw [Finset.mul_sum Finset.univ (fun r => e r*f r) ((kernel*(a p*b p))*(c q*d q)),Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro r _
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro s _
 ring

theorem basis_pair_pointwise (source : CPS1ElectronicSource.State frame)
    (i j k l : MolecularIndex source) (spin secondSpin : Bool)
    (z : CPS1ElectronicSource.Point × CPS1ElectronicSource.Point) :
    (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
      star (basisValue source i 0 spin z.1) * basisValue source j 0 spin z.1 *
      star (basisValue source k 0 secondSpin z.2) * basisValue source l 0 secondSpin z.2 =
    ∑ p, ∑ q, ∑ r, ∑ s,
      (star (basisCoefficient source p i)*basisCoefficient source q j*
        star (basisCoefficient source r k)*basisCoefficient source s l) *
      ((SourceCoulomb.kernel (z.1-z.2) : ℂ) * star (rawValue source p 0 spin z.1) * rawValue source q 0 spin z.1 *
        star (rawValue source r 0 secondSpin z.2) * rawValue source s 0 secondSpin z.2) := by
  simpa only [basisValue,star_sum,star_mul,mul_comm] using
    ordered_four_products
      (fun p => star (basisCoefficient source p i)) (fun p => star (rawValue source p 0 spin z.1))
      (fun q => basisCoefficient source q j) (fun q => rawValue source q 0 spin z.1)
      (fun r => star (basisCoefficient source r k)) (fun r => star (rawValue source r 0 secondSpin z.2))
      (fun s => basisCoefficient source s l) (fun s => rawValue source s 0 secondSpin z.2)
      (SourceCoulomb.kernel (z.1-z.2) : ℂ)

theorem basis_nuclear_integrable (source : CPS1ElectronicSource.State frame)
    (i j : MolecularIndex source) (jetI jetJ : Fin 3 → Nat) (spin : Bool) (nuclear : CPS1ElectronicSource.Point) :
    Integrable (fun x : CPS1ElectronicSource.Point => (SourceCoulomb.kernel (x-nuclear) : ℂ) *
      star (basisValue source i jetI spin x) * basisValue source j jetJ spin x) volume := by
  have paid := integrable_finsetSum Finset.univ (fun p _ => integrable_finsetSum Finset.univ (fun q _ =>
    (raw_nuclear_integrable source p q jetI jetJ spin nuclear).const_mul
      (star (basisCoefficient source p i)*basisCoefficient source q j)))
  convert! paid using 1
  funext x
  exact basis_nuclear_pointwise source i j jetI jetJ spin nuclear x

theorem basis_pair_integrable (source : CPS1ElectronicSource.State frame)
    (i j k l : MolecularIndex source) (spin secondSpin : Bool) :
    Integrable (fun z : CPS1ElectronicSource.Point × CPS1ElectronicSource.Point => (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
      star (basisValue source i 0 spin z.1) * basisValue source j 0 spin z.1 *
      star (basisValue source k 0 secondSpin z.2) * basisValue source l 0 secondSpin z.2)
      ((volume : Measure CPS1ElectronicSource.Point).prod volume) := by
  have paid := integrable_finsetSum Finset.univ (fun p _ => integrable_finsetSum Finset.univ (fun q _ =>
    integrable_finsetSum Finset.univ (fun r _ => integrable_finsetSum Finset.univ (fun s _ =>
      (raw_pair_integrable source p q r s 0 0 0 0 spin secondSpin).const_mul
        (star (basisCoefficient source p i)*basisCoefficient source q j*
          star (basisCoefficient source r k)*basisCoefficient source s l)))))
  convert! paid using 1
  funext z
  exact basis_pair_pointwise source i j k l spin secondSpin z

def rawNuclearIntegral (source : CPS1ElectronicSource.State frame) (p q : PrimitiveIndex source)
    (jetP jetQ : Fin 3 → Nat) (spin : Bool) (nuclear : CPS1ElectronicSource.Point) : ℂ :=
  if p.2 = spin ∧ q.2 = spin then
    primitiveNuclearIntegral (position source p.1.1) (position source q.1.1)
      p.1.2.val q.1.2.val nuclear jetP jetQ else 0

def rawPairIntegral (source : CPS1ElectronicSource.State frame) (p q r s : PrimitiveIndex source)
    (spin secondSpin : Bool) : ℂ :=
  if p.2 = spin ∧ q.2 = spin ∧ r.2 = secondSpin ∧ s.2 = secondSpin then
    primitivePairIntegral (position source p.1.1) (position source q.1.1)
      (position source r.1.1) (position source s.1.1) p.1.2.val q.1.2.val r.1.2.val s.1.2.val
      0 0 0 0 else 0

theorem raw_nuclear_integral (source : CPS1ElectronicSource.State frame) (p q : PrimitiveIndex source)
    (jetP jetQ : Fin 3 → Nat) (spin : Bool) (nuclear : CPS1ElectronicSource.Point) :
    (∫ x : CPS1ElectronicSource.Point, (SourceCoulomb.kernel (x-nuclear) : ℂ) *
      star (rawValue source p jetP spin x) * rawValue source q jetQ spin x) =
      rawNuclearIntegral source p q jetP jetQ spin nuclear := by
  by_cases first : p.2 = spin <;> by_cases second : q.2 = spin <;>
    simp [rawValue,rawNuclearIntegral,first,second,primitiveNuclearIntegral]

theorem raw_pair_integral (source : CPS1ElectronicSource.State frame) (p q r s : PrimitiveIndex source)
    (spin secondSpin : Bool) :
    (∫ z : CPS1ElectronicSource.Point × CPS1ElectronicSource.Point,
      (SourceCoulomb.kernel (z.1-z.2) : ℂ) * star (rawValue source p 0 spin z.1) * rawValue source q 0 spin z.1 *
        star (rawValue source r 0 secondSpin z.2) * rawValue source s 0 secondSpin z.2
      ∂(volume : Measure CPS1ElectronicSource.Point).prod volume) = rawPairIntegral source p q r s spin secondSpin := by
  by_cases first : p.2 = spin <;> by_cases second : q.2 = spin <;>
    by_cases third : r.2 = secondSpin <;> by_cases fourth : s.2 = secondSpin <;>
    simp [rawValue,rawPairIntegral,first,second,third,fourth,primitivePairIntegral]

theorem nuclear_integral_expansion (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source)
    (nuclear : CPS1ElectronicSource.Point) :
    nuclearIntegral source i j nuclear = ∑ spin : Bool, ∑ p, ∑ q,
      (star (basisCoefficient source p i)*basisCoefficient source q j)*rawNuclearIntegral source p q 0 0 spin nuclear := by
  unfold nuclearIntegral
  apply Finset.sum_congr rfl
  intro spin _
  have term (p q : PrimitiveIndex source) :=
    (raw_nuclear_integrable source p q 0 0 spin nuclear).const_mul
      (star (basisCoefficient source p i)*basisCoefficient source q j)
  rw [show (fun x : CPS1ElectronicSource.Point => (SourceCoulomb.kernel (x-nuclear) : ℂ) *
      star (basisValue source i 0 spin x)*basisValue source j 0 spin x) =
      (fun x => ∑ p, ∑ q, (star (basisCoefficient source p i)*basisCoefficient source q j)*
        ((SourceCoulomb.kernel (x-nuclear) : ℂ)*star (rawValue source p 0 spin x)*rawValue source q 0 spin x)) from
    funext (basis_nuclear_pointwise source i j 0 0 spin nuclear)]
  rw [integral_finsetSum Finset.univ (fun p _ => integrable_finsetSum Finset.univ (fun q _ => term p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum Finset.univ (fun q _ => term p q)]
  simp only [integral_const_mul,raw_nuclear_integral]

theorem pair_integral_expansion (source : CPS1ElectronicSource.State frame) (i j k l : MolecularIndex source)
    (spin secondSpin : Bool) : pairIntegral source i j k l spin secondSpin =
    ∑ p, ∑ q, ∑ r, ∑ s,
      (star (basisCoefficient source p i)*basisCoefficient source q j*
        star (basisCoefficient source r k)*basisCoefficient source s l)*rawPairIntegral source p q r s spin secondSpin := by
  have term (p q r s : PrimitiveIndex source) :=
    (raw_pair_integrable source p q r s 0 0 0 0 spin secondSpin).const_mul
      (star (basisCoefficient source p i)*basisCoefficient source q j*
        star (basisCoefficient source r k)*basisCoefficient source s l)
  unfold pairIntegral
  rw [show (fun z : CPS1ElectronicSource.Point × CPS1ElectronicSource.Point =>
      (SourceCoulomb.kernel (z.1-z.2) : ℂ)*star (basisValue source i 0 spin z.1)*basisValue source j 0 spin z.1*
        star (basisValue source k 0 secondSpin z.2)*basisValue source l 0 secondSpin z.2) =
      (fun z => ∑ p, ∑ q, ∑ r, ∑ s,
        (star (basisCoefficient source p i)*basisCoefficient source q j*star (basisCoefficient source r k)*basisCoefficient source s l)*
          ((SourceCoulomb.kernel (z.1-z.2) : ℂ)*star (rawValue source p 0 spin z.1)*rawValue source q 0 spin z.1*
            star (rawValue source r 0 secondSpin z.2)*rawValue source s 0 secondSpin z.2)) from
    funext (basis_pair_pointwise source i j k l spin secondSpin)]
  rw [integral_finsetSum Finset.univ (fun p _ => integrable_finsetSum Finset.univ (fun q _ =>
    integrable_finsetSum Finset.univ (fun r _ => integrable_finsetSum Finset.univ (fun s _ => term p q r s))))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum Finset.univ (fun q _ => integrable_finsetSum Finset.univ (fun r _ =>
    integrable_finsetSum Finset.univ (fun s _ => term p q r s)))]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_finsetSum Finset.univ (fun r _ => integrable_finsetSum Finset.univ (fun s _ => term p q r s))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum Finset.univ (fun s _ => term p q r s)]
  simp only [integral_const_mul,raw_pair_integral]

theorem orbital_inner_literal (left right : CPS1ElectronicSource.Point) (i j : Nat)
    (jetI jetJ : Fin 3 → Nat) :
    inner ℂ (orbitalField left i jetI) (orbitalField right j jetJ) =
      primitiveKineticIntegral left right i j jetI jetJ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [orbital_field_source left i jetI,orbital_field_source right j jetJ] with x first second
  rw [first,second,RCLike.inner_apply']
  rfl

def rawKineticIntegral (source : CPS1ElectronicSource.State frame) (p q : PrimitiveIndex source)
    (jetP jetQ : Fin 3 → Nat) : ℂ :=
  if p.2 = q.2 then primitiveKineticIntegral (position source p.1.1) (position source q.1.1)
    p.1.2.val q.1.2.val jetP jetQ else 0

theorem raw_jet_inner (source : CPS1ElectronicSource.State frame) (p q : PrimitiveIndex source)
    (jetP jetQ : Fin 3 → Nat) :
    inner ℂ (rawJet source p jetP) (rawJet source q jetQ) = rawKineticIntegral source p q jetP jetQ := by
  cases first : p.2 <;> cases second : q.2 <;>
    simp [rawJet,rawKineticIntegral,PiLp.inner_apply,PiLp.single_apply,first,second,orbital_inner_literal]

theorem basis_kinetic_integrable (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source)
    (jetI jetJ : Fin 3 → Nat) (spin : Bool) :
    Integrable (fun x : CPS1ElectronicSource.Point =>
      star (basisValue source i jetI spin x)*basisValue source j jetJ spin x) volume := by
  apply (L2.integrable_inner (𝕜 := ℂ) (basisJet source jetI i spin) (basisJet source jetJ j spin)).congr
  filter_upwards [basis_jet_value source i jetI spin,basis_jet_value source j jetJ spin] with x first second
  rw [first,second,RCLike.inner_apply']
  rfl

theorem basis_jet_inner_literal (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source)
    (jetI jetJ : Fin 3 → Nat) :
    inner ℂ (basisJet source jetI i) (basisJet source jetJ j) =
      ∑ spin : Bool, ∫ x : CPS1ElectronicSource.Point,
        star (basisValue source i jetI spin x)*basisValue source j jetJ spin x := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro spin _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [basis_jet_value source i jetI spin,basis_jet_value source j jetJ spin] with x first second
  rw [first,second,RCLike.inner_apply']
  rfl

theorem basis_jet_inner_expansion (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source)
    (jetI jetJ : Fin 3 → Nat) :
    inner ℂ (basisJet source jetI i) (basisJet source jetJ j) =
      ∑ p, ∑ q, (star (basisCoefficient source p i)*basisCoefficient source q j)*
        rawKineticIntegral source p q jetI jetJ := by
  simp only [basisJet,sum_inner,inner_sum,inner_smul_left,inner_smul_right,raw_jet_inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [starRingEnd_apply]
  ring

theorem kinetic_integral_expansion (source : CPS1ElectronicSource.State frame) (i j : MolecularIndex source) :
    kinetic source i j = ((1/(2*source.geometry.electronInertia) : ℝ) : ℂ)*
      ∑ axis : Fin 3, ∑ p, ∑ q, (star (basisCoefficient source p i)*basisCoefficient source q j)*
        rawKineticIntegral source p q (raise 0 axis) (raise 0 axis) := by
  simp only [kinetic,basis_jet_inner_expansion]

end
end CPS1MolecularFrame
