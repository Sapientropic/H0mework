import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMQuantumFieldBalance
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMClockDispersion
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open SourcePropagationNativeActionHessian ActualEMAction ActualDressedEMQuantumThreshold
open ActualDressedZeroClockVector ActualDressedEMZeroClockColumns ActualDressedZeroClockFrequency
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalHessian emOriginalJacobi nativeJetBasis

def nativePhysicalClockZero (k : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  emOriginalJacobi (physicalFrequencyMomentum 0 k)

def nativePhysicalClockFirst (k : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  (1/2 : ℂ) • (emOriginalJacobi (physicalFrequencyMomentum 1 k)-emOriginalJacobi (physicalFrequencyMomentum (-1) k))

def nativePhysicalClockSecond (k : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  (1/2 : ℂ) • (emOriginalJacobi (physicalFrequencyMomentum 1 k)+emOriginalJacobi (physicalFrequencyMomentum (-1) k))-
    nativePhysicalClockZero k

private theorem jet_clock_affine (sign : ℂ) (slot : Option (Fin 4)) (omega : ℝ) (k : PhysicalMomentum) :
    jetSymbol slot (fun mu => sign*physicalFrequencyMomentum omega k mu)=
      jetSymbol slot (fun mu => sign*physicalFrequencyMomentum 0 k mu)+
      (omega : ℂ)*(jetSymbol slot (fun mu => sign*physicalFrequencyMomentum 1 k mu)-
        jetSymbol slot (fun mu => sign*physicalFrequencyMomentum 0 k mu)) := by
  cases slot with
  | none => simp only [jetSymbol,sub_self,mul_zero,add_zero]
  | some mu =>
    refine Fin.cases ?_ (fun i => ?_) mu
    · simp only [jetSymbol,physicalFrequencyMomentum,Fin.cases_zero,Complex.ofReal_zero,Complex.ofReal_one]
      ring
    · simp only [jetSymbol,physicalFrequencyMomentum,Fin.cases_succ]
      ring

private theorem jet_clock_quadratic (h : ℂ) (left right : Option (Fin 4)) (omega : ℝ) (k : PhysicalMomentum) :
    h*jetSymbol left (-physicalFrequencyMomentum omega k)*jetSymbol right (physicalFrequencyMomentum omega k)=
      h*jetSymbol left (-physicalFrequencyMomentum 0 k)*jetSymbol right (physicalFrequencyMomentum 0 k)+
      (omega : ℂ)*(1/2 : ℂ)*
        (h*jetSymbol left (-physicalFrequencyMomentum 1 k)*jetSymbol right (physicalFrequencyMomentum 1 k)-
          h*jetSymbol left (-physicalFrequencyMomentum (-1) k)*jetSymbol right (physicalFrequencyMomentum (-1) k))+
      (omega : ℂ)^2*((1/2 : ℂ)*
        (h*jetSymbol left (-physicalFrequencyMomentum 1 k)*jetSymbol right (physicalFrequencyMomentum 1 k)+
          h*jetSymbol left (-physicalFrequencyMomentum (-1) k)*jetSymbol right (physicalFrequencyMomentum (-1) k))-
        h*jetSymbol left (-physicalFrequencyMomentum 0 k)*jetSymbol right (physicalFrequencyMomentum 0 k)) := by
  have negative (w : ℝ) : (fun mu => -physicalFrequencyMomentum w k mu) = -physicalFrequencyMomentum w k := by
    funext mu
    rfl
  have L (w : ℝ) : jetSymbol left (-physicalFrequencyMomentum w k)=
      jetSymbol left (-physicalFrequencyMomentum 0 k)+(w : ℂ)*
        (jetSymbol left (-physicalFrequencyMomentum 1 k)-jetSymbol left (-physicalFrequencyMomentum 0 k)) := by
    simpa only [neg_one_mul,negative] using jet_clock_affine (-1) left w k
  have R (w : ℝ) : jetSymbol right (physicalFrequencyMomentum w k)=
      jetSymbol right (physicalFrequencyMomentum 0 k)+(w : ℂ)*
        (jetSymbol right (physicalFrequencyMomentum 1 k)-jetSymbol right (physicalFrequencyMomentum 0 k)) := by
    simpa only [one_mul] using jet_clock_affine 1 right w k
  rw [L omega,R omega,L (-1),R (-1)]
  simp only [Complex.ofReal_neg,Complex.ofReal_one]
  ring

private theorem hessian_clock_quadratic
    (H : NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ) (omega : ℝ) (k : PhysicalMomentum) :
    nativeFourierHessian H (physicalFrequencyMomentum omega k)=
      nativeFourierHessian H (physicalFrequencyMomentum 0 k)+
      (omega : ℂ) • ((1/2 : ℂ) •
        (nativeFourierHessian H (physicalFrequencyMomentum 1 k)-
          nativeFourierHessian H (physicalFrequencyMomentum (-1) k)))+
      (omega : ℂ)^2 • ((1/2 : ℂ) •
        (nativeFourierHessian H (physicalFrequencyMomentum 1 k)+
          nativeFourierHessian H (physicalFrequencyMomentum (-1) k))-
        nativeFourierHessian H (physicalFrequencyMomentum 0 k)) := by
  ext i j
  let T (w : ℝ) (left right : Option (Fin 4)) : ℂ :=
    (H (nativeJetBasis (left,i)) (nativeJetBasis (right,j)) : ℂ)*
      jetSymbol left (-physicalFrequencyMomentum w k)*jetSymbol right (physicalFrequencyMomentum w k)
  have each (left right : Option (Fin 4)) :
      T omega left right=T 0 left right+(omega : ℂ)*(1/2 : ℂ)*(T 1 left right-T (-1) left right)+
        (omega : ℂ)^2*((1/2 : ℂ)*(T 1 left right+T (-1) left right)-T 0 left right) :=
    jet_clock_quadratic _ _ _ _ _
  have total : (∑left,∑right,T omega left right)=
      ∑left,∑right, (T 0 left right+(omega : ℂ)*(1/2 : ℂ)*(T 1 left right-T (-1) left right)+
        (omega : ℂ)^2*((1/2 : ℂ)*(T 1 left right+T (-1) left right)-T 0 left right)) := by
    apply Finset.sum_congr rfl
    intro left _
    apply Finset.sum_congr rfl
    intro right _
    exact each left right
  change (∑left,∑right,T omega left right)=
    (∑left,∑right,T 0 left right)+(omega : ℂ)*((1/2 : ℂ)*
      ((∑left,∑right,T 1 left right)-(∑left,∑right,T (-1) left right)))+
    (omega : ℂ)^2*((1/2 : ℂ)*((∑left,∑right,T 1 left right)+(∑left,∑right,T (-1) left right))-
      (∑left,∑right,T 0 left right))
  rw [total]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

/-- All original source fields and mixed Hessian entries retain their exact physical clock degree. -/
theorem actual_native_physical_clock_quadratic (omega : ℝ) (k : PhysicalMomentum) :
    emOriginalJacobi (physicalFrequencyMomentum omega k)=nativePhysicalClockZero k+
      (omega : ℂ) • nativePhysicalClockFirst k+(omega : ℂ)^2 • nativePhysicalClockSecond k := by
  simp only [nativePhysicalClockZero,nativePhysicalClockFirst,nativePhysicalClockSecond,emOriginalJacobi]
  exact hessian_clock_quadratic emOriginalHessian omega k

def nativePhysicalClockJet (omega : ℝ) (k : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  nativePhysicalClockFirst k+(2*(omega : ℂ)) • nativePhysicalClockSecond k

/-- This derivative belongs to the original physical frequency, without a scaled-sheet normalizer. -/
theorem actual_native_physical_clock_derivative (omega : ℝ) (k : PhysicalMomentum) :
    HasDerivAt (fun w : ℝ => emOriginalJacobi (physicalFrequencyMomentum w k))
      (nativePhysicalClockJet omega k) omega := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have w : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) omega := (hasDerivAt_id omega).ofReal_comp
  have exactJet := ((hasDerivAt_const omega (nativePhysicalClockZero k i j)).add
    (w.mul_const (nativePhysicalClockFirst k i j))).add
      ((w.pow 2).mul_const (nativePhysicalClockSecond k i j))
  convert exactJet using 1
  · funext r
    exact congrFun (congrFun (actual_native_physical_clock_quadratic r k) i) j
  · simp only [nativePhysicalClockJet,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      one_mul,zero_add,Nat.cast_ofNat,mul_one]
    norm_num

theorem actual_physical_frequency_ray (eps s : ℝ) (n : PhysicalMomentum) :
    physicalFrequencyMomentum (sourceFrequency eps s) ((eps^2 : ℝ) • n)=frequencyRay eps s n := by
  funext mu
  refine Fin.cases ?_ (fun i => ?_) mu
  all_goals simp [physicalFrequencyMomentum,sourceFrequency,frequencyRay,Pi.smul_apply,smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_pow]
  all_goals ring

/-- The complete native quadratic clock now consumes the same actual EM mode and its source quantum balance. -/
theorem actual_em_native_physical_dispersion (event : ActualDressedFullCoulomb.DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈LowEnergy.ActualDressedVisiblePole.visibleRoots
      (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let v := actualEMZeroClockMode event eps n nu (s : ℂ)
    let k := (eps^2 : ℝ) • n
    let omega := sourceFrequency eps s
    (nativePhysicalClockZero k+(omega : ℂ) • nativePhysicalClockFirst k+
      (omega : ℂ)^2 • nativePhysicalClockSecond k)*ᵥv=zeroClockQuantumResponse event eps s n*ᵥv := by
  dsimp only
  rw [← actual_native_physical_clock_quadratic,actual_physical_frequency_ray]
  exact actual_zero_clock_em_original_balance event eps s n mu nu balanced finite regular root

end LowEnergy.GaussComposite.ActualDressedEMClockDispersion
