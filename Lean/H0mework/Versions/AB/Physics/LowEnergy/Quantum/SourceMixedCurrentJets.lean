import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceNativeMixedCurrent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceMixedNativeReturn
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussCoframeForm GaussDiagonalHistory
open GaussYukawaCoefficient GaussRadialDomain GaussLiveMomentum GaussQuantumMultiplier
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolumeCurrent SourceCoframeDilation SourceEulerCore
open SourceDilationRemainder SourceHamiltonianScaleJet SourceDilationAlgebra SourceCutoffDilationWard
open SourceClosedCostNativeProbe SourceJointScaleBudget SourceEscapeCurrent
open FullYSourceResolventGraphSplice GaussUnitaryHistory SourceRelativePowerTail
open scoped ContDiff InnerProductSpace RealInnerProductSpace


section JetAlgebra
variable {R : Type*} [Ring R]

def inverseJet1 (r a : R) : R := -r*a*r
def inverseJet2 (r a b : R) : R := 2*r*a*r*a*r-r*b*r
def inverseJet3 (r a b c : R) : R :=
  -6*r*a*r*a*r*a*r+3*r*b*r*a*r+3*r*a*r*b*r-r*c*r

def commJet0 (l t : R) : R := l*t-t*l
def commJet1 (l a t u : R) : R := a*t+l*u-u*l-t*a
def commJet2 (l a b t u v : R) : R := b*t+2*a*u+l*v-v*l-2*u*a-t*b
def commJet3 (l a b c t u v w : R) : R :=
  c*t+3*b*u+3*a*v+l*w-w*l-3*v*a-3*u*b-t*c

def sandwichJet0 (r b : R) : R := r*b*r
def sandwichJet1 (r r1 b b1 : R) : R := r1*b*r+r*b1*r+r*b*r1
def sandwichJet2 (r r1 r2 b b1 b2 : R) : R :=
  r2*b*r+2*r1*b1*r+2*r1*b*r1+r*b2*r+2*r*b1*r1+r*b*r2
def sandwichJet3 (r r1 r2 r3 b b1 b2 b3 : R) : R :=
  r3*b*r+3*r2*b1*r+3*r2*b*r1+3*r1*b2*r+6*r1*b1*r1+3*r1*b*r2+
    r*b3*r+3*r*b2*r1+3*r*b1*r2+r*b*r3

def endpointJet0 (r t : R) : R := t*r-r*t
def endpointJet1 (r r1 t u : R) : R := u*r+t*r1-r1*t-r*u
def endpointJet2 (r r1 r2 t u v : R) : R := v*r+2*u*r1+t*r2-r2*t-2*r1*u-r*v
def endpointJet3 (r r1 r2 r3 t u v w : R) : R :=
  w*r+3*v*r1+3*u*r2+t*r3-r3*t-3*r2*u-3*r1*v-r*w

private theorem jet_endpoint_return (l r a b c t u v w : R)
    (hl : l*r=1) (hr : r*l=1) :
    sandwichJet0 r (commJet0 l t)=endpointJet0 r t ∧
    sandwichJet1 r (inverseJet1 r a) (commJet0 l t) (commJet1 l a t u)=
      endpointJet1 r (inverseJet1 r a) t u ∧
    sandwichJet2 r (inverseJet1 r a) (inverseJet2 r a b)
      (commJet0 l t) (commJet1 l a t u) (commJet2 l a b t u v)=
      endpointJet2 r (inverseJet1 r a) (inverseJet2 r a b) t u v ∧
    sandwichJet3 r (inverseJet1 r a) (inverseJet2 r a b) (inverseJet3 r a b c)
      (commJet0 l t) (commJet1 l a t u) (commJet2 l a b t u v) (commJet3 l a b c t u v w)=
      endpointJet3 r (inverseJet1 r a) (inverseJet2 r a b) (inverseJet3 r a b c) t u v w := by
  have hrx (x : R) : r*(l*x)=x := by rw [←mul_assoc,hr,one_mul]
  have hlx (x : R) : l*(r*x)=x := by rw [←mul_assoc,hl,one_mul]
  constructor
  · unfold sandwichJet0 commJet0 endpointJet0
    noncomm_ring [hrx,hlx,hl]
  constructor
  · unfold sandwichJet1 commJet0 commJet1 endpointJet1 inverseJet1
    noncomm_ring [hrx,hlx,hl]
  constructor
  · unfold sandwichJet2 commJet0 commJet1 commJet2 endpointJet2 inverseJet1 inverseJet2
    noncomm_ring [hrx,hlx,hl]
  · unfold sandwichJet3 commJet0 commJet1 commJet2 commJet3 endpointJet3 inverseJet1 inverseJet2 inverseJet3
    noncomm_ring [hrx,hlx,hl]

/-- Terms in which at least one resolvent is differentiated, with every multiplicity retained. -/
def leibnizOther (r r1 r2 r3 b b1 b2 : R) : R :=
  r3*b*r+3*r2*b1*r+3*r2*b*r1+3*r1*b2*r+6*r1*b1*r1+3*r1*b*r2+
    3*r*b2*r1+3*r*b1*r2+r*b*r3+
  12*(r2*b*r+2*r1*b1*r+2*r1*b*r1+2*r*b1*r1+r*b*r2)+
  44*(r1*b*r+r*b*r1)

private theorem sandwich_polynomial (r r1 r2 r3 b b1 b2 b3 : R) :
    sandwichJet3 r r1 r2 r3 b b1 b2 b3+12*sandwichJet2 r r1 r2 b b1 b2+
      44*sandwichJet1 r r1 b b1+48*sandwichJet0 r b=
    r*(b3+12*b2+44*b1+48*b)*r+leibnizOther r r1 r2 r3 b b1 b2 := by
  unfold sandwichJet3 sandwichJet2 sandwichJet1 sandwichJet0 leibnizOther
  noncomm_ring
end JetAlgebra



def compressionJet (F : Index) (j : ℕ) : H →L[ℂ] H := sourceCompression F (jet j diagonalAction)

private theorem compression_jet_zero (F : Index) :
    compressionJet F 0=GaussGradedCompression.compression F := by
  change sourceCompression F diagonalAction=_
  simpa only [scaledCompression,source_scale_one] using actual_compression_return F

def primitiveJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (j : ℕ) : H →L[ℂ] H :=
  ((-3 : ℂ)^j) • sourceRead F g (primitive sharp m ell)

def inverseJet (F : Index) (z : ℂ) : Fin 4 → H →L[ℂ] H :=
  ![finiteResolvent F z,
    inverseJet1 (finiteResolvent F z) (compressionJet F 1),
    inverseJet2 (finiteResolvent F z) (compressionJet F 1) (compressionJet F 2),
    inverseJet3 (finiteResolvent F z) (compressionJet F 1) (compressionJet F 2) (compressionJet F 3)]

def currentJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) :
    Fin 4 → H →L[ℂ] H :=
  ![Complex.I • commJet0 (GaussGradedCompression.compression F-z • 1) (primitiveJet sharp m ell F g 0),
    Complex.I • commJet1 (GaussGradedCompression.compression F-z • 1) (compressionJet F 1)
      (primitiveJet sharp m ell F g 0) (primitiveJet sharp m ell F g 1),
    Complex.I • commJet2 (GaussGradedCompression.compression F-z • 1) (compressionJet F 1)
      (compressionJet F 2) (primitiveJet sharp m ell F g 0) (primitiveJet sharp m ell F g 1)
      (primitiveJet sharp m ell F g 2),
    Complex.I • commJet3 (GaussGradedCompression.compression F-z • 1) (compressionJet F 1)
      (compressionJet F 2) (compressionJet F 3) (primitiveJet sharp m ell F g 0)
      (primitiveJet sharp m ell F g 1) (primitiveJet sharp m ell F g 2) (primitiveJet sharp m ell F g 3)]

/-- Raw source product, input-span escape and actual grade-pinching remain in each coefficient. -/
def omegaJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ)
    (j : Fin 4) : H →L[ℂ] H := rawJet sharp m ell F g j-currentJet sharp m ell F g z j

private theorem current_zero (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) :
    currentJet sharp m ell F g z 0=Complex.I •
      (GaussGradedCompression.compression F*sourceRead F g (primitive sharp m ell)-
        sourceRead F g (primitive sharp m ell)*GaussGradedCompression.compression F) := by
  simp only [currentJet,Matrix.cons_val_zero,commJet0,primitiveJet,pow_zero,one_smul,sub_mul,mul_sub,
    smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  module

/-- The first actual flux is generated from H0, T and C_F on q_F, with no orthogonality premise. -/
theorem actual_omega_zero (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    omegaJet sharp m ell F g z 0 (finiteResolvent F z (g : H))=
      embed (force diagonalAction (primitive sharp m ell) (coreEquiv.symm (sourceCore F z hz g)))-
      Complex.I • (GaussGradedCompression.compression F
        (embed (primitive sharp m ell (coreEquiv.symm (sourceCore F z hz g))))-
        sourceRead F g (primitive sharp m ell)
          (GaussGradedCompression.compression F (finiteResolvent F z (g : H)))) := by
  change sourceRead F g (force diagonalAction (primitive sharp m ell))
    (finiteResolvent F z (g : H))-currentJet sharp m ell F g z 0
      (finiteResolvent F z (g : H))=_
  rw [current_zero]
  change sourceRead F g (force diagonalAction (primitive sharp m ell))
    (finiteResolvent F z (g : H))-
    Complex.I • (GaussGradedCompression.compression F
      (sourceRead F g (primitive sharp m ell) (finiteResolvent F z (g : H)))-
      sourceRead F g (primitive sharp m ell)
        (GaussGradedCompression.compression F (finiteResolvent F z (g : H))))=_
  have h0 := source_read_resolvent F g (force diagonalAction (primitive sharp m ell)) z hz
  have hT := source_read_resolvent F g (primitive sharp m ell) z hz
  simpa only using! congrArg₂ (fun x y : H => x-Complex.I •
    (GaussGradedCompression.compression F y-sourceRead F g (primitive sharp m ell)
      (GaussGradedCompression.compression F (finiteResolvent F z (g : H))))) h0 hT

def sandwichPolynomial {R : Type*} [Ring R] (r b : Fin 4 → R) : R :=
  sandwichJet3 (r 0) (r 1) (r 2) (r 3) (b 0) (b 1) (b 2) (b 3)+
    12*sandwichJet2 (r 0) (r 1) (r 2) (b 0) (b 1) (b 2)+
    44*sandwichJet1 (r 0) (r 1) (b 0) (b 1)+48*sandwichJet0 (r 0) (b 0)

private theorem sandwich_smul {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (r b : Fin 4 → R) (c : ℂ) :
    sandwichPolynomial r (fun j => c • b j)=c • sandwichPolynomial r b := by
  unfold sandwichPolynomial sandwichJet0 sandwichJet1 sandwichJet2 sandwichJet3
  simp only [mul_smul_comm,smul_mul_assoc,←smul_add]

private theorem sandwich_split {R : Type*} [Ring R] (r b c : Fin 4 → R) :
    sandwichPolynomial r b=sandwichPolynomial r c+sandwichPolynomial r (fun j => b j-c j) := by
  unfold sandwichPolynomial sandwichJet0 sandwichJet1 sandwichJet2 sandwichJet3
  noncomm_ring

private theorem forced_endpoint {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (l r a b c t u v w : R) (hl : l*r=1) (hr : r*l=1) :
    sandwichJet0 r (Complex.I • commJet0 l t)=Complex.I • endpointJet0 r t ∧
    sandwichJet1 r (inverseJet1 r a) (Complex.I • commJet0 l t) (Complex.I • commJet1 l a t u)=
      Complex.I • endpointJet1 r (inverseJet1 r a) t u ∧
    sandwichJet2 r (inverseJet1 r a) (inverseJet2 r a b)
      (Complex.I • commJet0 l t) (Complex.I • commJet1 l a t u) (Complex.I • commJet2 l a b t u v)=
      Complex.I • endpointJet2 r (inverseJet1 r a) (inverseJet2 r a b) t u v ∧
    sandwichJet3 r (inverseJet1 r a) (inverseJet2 r a b) (inverseJet3 r a b c)
      (Complex.I • commJet0 l t) (Complex.I • commJet1 l a t u)
      (Complex.I • commJet2 l a b t u v) (Complex.I • commJet3 l a b c t u v w)=
      Complex.I • endpointJet3 r (inverseJet1 r a) (inverseJet2 r a b) (inverseJet3 r a b c) t u v w := by
  have h := jet_endpoint_return l r a b c t u v w hl hr
  constructor
  · convert congrArg (fun A => Complex.I • A) h.1 using 1
    simp only [sandwichJet0,smul_mul_assoc,mul_smul_comm]
  constructor
  · convert congrArg (fun A => Complex.I • A) h.2.1 using 1
    simp only [sandwichJet1,smul_mul_assoc,mul_smul_comm,←smul_add]
  constructor
  · convert congrArg (fun A => Complex.I • A) h.2.2.1 using 1
    simp only [sandwichJet2,smul_mul_assoc,mul_smul_comm,←smul_add]
  · convert congrArg (fun A => Complex.I • A) h.2.2.2 using 1
    simp only [sandwichJet3,smul_mul_assoc,mul_smul_comm,←smul_add]

private theorem scalar_polynomial {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (c : ℂ) (a b d e : R) :
    c • a+12*(c • b)+44*(c • d)+48*(c • e)=c • (a+12*b+44*d+48*e) := by
  simp only [mul_smul_comm,←smul_add]

def endpointPolynomial (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : H →L[ℂ] H :=
  Complex.I •
    (endpointJet3 (inverseJet F z 0) (inverseJet F z 1) (inverseJet F z 2) (inverseJet F z 3)
      (primitiveJet sharp m ell F g 0) (primitiveJet sharp m ell F g 1)
      (primitiveJet sharp m ell F g 2) (primitiveJet sharp m ell F g 3)+
    12*endpointJet2 (inverseJet F z 0) (inverseJet F z 1) (inverseJet F z 2)
      (primitiveJet sharp m ell F g 0) (primitiveJet sharp m ell F g 1) (primitiveJet sharp m ell F g 2)+
    44*endpointJet1 (inverseJet F z 0) (inverseJet F z 1)
      (primitiveJet sharp m ell F g 0) (primitiveJet sharp m ell F g 1)+
    48*endpointJet0 (inverseJet F z 0) (primitiveJet sharp m ell F g 0))

def omegaResponse (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : H →L[ℂ] H :=
  sandwichPolynomial (inverseJet F z) (omegaJet sharp m ell F g z)

def leibnizResponse (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : H →L[ℂ] H :=
  leibnizOther (inverseJet F z 0) (inverseJet F z 1) (inverseJet F z 2) (inverseJet F z 3)
    (rawJet sharp m ell F g 0) (rawJet sharp m ell F g 1) (rawJet sharp m ell F g 2)

end LowEnergy.SourceMixedNativeReturn
