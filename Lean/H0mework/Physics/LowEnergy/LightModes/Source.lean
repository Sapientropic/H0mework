import H0mework.Physics.LowEnergy.LightModes.Root

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightModes
noncomputable section

inductive Branch where
  | vectorReal | vectorPhase | axialPhase | quadraticPair
  deriving DecidableEq

def sourceRoot : Branch → RootSource
  | .vectorReal =>
    { center := -5/3
      terms := [⟨2,0,-25/54⟩, ⟨1,0,-25/27⟩, ⟨0,0,-25/54⟩]
      center_bound := by norm_num }
  | .vectorPhase =>
    { center := -55/67
      terms := [⟨5,3,-2519424/5234375⟩, ⟨4,3,-2519424/1046875⟩, ⟨4,2,67250736/130859375⟩, ⟨3,3,-5038848/1046875⟩, ⟨3,2,359702208/130859375⟩, ⟨3,1,4326129/1046875⟩, ⟨2,3,-5038848/1046875⟩, ⟨2,2,675602208/130859375⟩, ⟨2,1,11158803/1046875⟩, ⟨2,0,-107359/25125⟩, ⟨1,3,-2519424/1046875⟩, ⟨1,2,541100736/130859375⟩, ⟨1,1,9339219/1046875⟩, ⟨1,0,-188474/25125⟩, ⟨0,3,-2519424/5234375⟩, ⟨0,2,50544/41875⟩, ⟨0,1,501309/209375⟩, ⟨0,0,-16223/5025⟩]
      center_bound := by norm_num }
  | .axialPhase =>
    { center := 125/162
      terms := [⟨6,4,-2187/2125000⟩, ⟨5,4,-1491/1700000⟩, ⟨5,3,1403703/106250000⟩, ⟨4,4,3215509/114750000⟩, ⟨4,3,-2450663887/34425000000⟩, ⟨4,2,2822517/26562500⟩, ⟨3,4,5059643/1458000000⟩, ⟨3,3,18772391743/464737500000⟩, ⟨3,2,-1764314081/3227343750⟩, ⟨3,1,15866/53125⟩, ⟨2,4,-7963/93312⟩, ⟨2,3,-114562693999/803066400000⟩, ⟨2,2,987522901/7435800000⟩, ⟨2,1,273296729/619650000⟩, ⟨2,0,369863/159375⟩, ⟨1,4,-112291/1586304⟩, ⟨1,3,-667632419/3212265600⟩, ⟨1,2,2908075453/5353776000⟩, ⟨1,1,-27058409/49572000⟩, ⟨1,0,-342704/103275⟩, ⟨0,4,-15625/1586304⟩, ⟨0,3,-529375/15116544⟩, ⟨0,2,-4297075/42830208⟩, ⟨0,1,-1084825/3569184⟩, ⟨0,0,18325/11016⟩]
      center_bound := by norm_num }
  | .quadraticPair =>
    { center := -25/36
      terms := [⟨2,1,25/36⟩, ⟨1,0,25/18⟩]
      center_bound := by norm_num }

def sourcePower : Branch → ℕ
  | .quadraticPair => 2
  | _ => 1

def sourceCoefficient : Branch → ℝ
  | .vectorReal => -54
  | .vectorPhase => -392578125
  | .axialPhase => -100383300000000
  | .quadraticPair => 36

def sourceFactor {R : Type*} [CommRing R] (branch : Branch) (v w : R) : R :=
  match branch with
  | .vectorReal => 25*v^2 + 50*v*w - 54*v + 25*w^2 - 90*w
  | .vectorPhase => 188956800*v^5 + 944784000*v^4*w - 201752208*v^4 + 1889568000*v^3*w^2 - 1079106624*v^3*w - 1622298375*v^3 + 1889568000*v^2*w^3 - 2026806624*v^2*w^2 - 4184551125*v^2*w + 1677484375*v^2 + 944784000*v*w^4 - 1623302208*v*w^3 - 3502207125*v*w^2 + 2944906250*v*w - 392578125*v + 188956800*w^5 - 473850000*w^4 - 939954375*w^3 + 1267421875*w^2 - 322265625*w
  | .axialPhase => 103312130400*v^6 + 88042059000*v^5*w - 1326196135152*v^5 - 2812927273200*v^4*w^2 + 7146135894492*v^4*w - 10666675605312*v^4 - 348356420550*v^3*w^3 - 4054836616488*v^3*w^2 + 54877225175424*v^3*w - 29979885888000*v^3 + 8566446093750*v^2*w^4 + 14320336749875*v^2*w^3 - 13331559163500*v^2*w^2 - 44274070098000*v^2*w - 232960429728000*v^2 + 7105914843750*v*w^5 + 20863513093750*v*w^4 - 54526414743750*v*w^3 + 54793278225000*v*w^2 + 333108288000000*v*w - 100383300000000*v + 988769531250*w^6 + 3515380859375*w^5 + 10071269531250*w^4 + 30510703125000*w^3 - 166986562500000*w^2 + 77456250000000*w
  | .quadraticPair => 25*v^2 + 50*v*w + 36*v + 25*w^2

def momentumRadius : ℝ := 5234375/294988800512

theorem momentumRadius_positive : 0<momentumRadius := by norm_num [momentumRadius]

theorem momentumRadius_bound : momentumRadius≤1 := by norm_num [momentumRadius]

theorem source_radius (branch : Branch) : momentumRadius≤(sourceRoot branch).radius := by
  cases branch <;> norm_num [momentumRadius,sourceRoot,RootSource.radius,coefficientBound,differentiate]

theorem source_factorization (branch : Branch) (r w : ℝ) :
    sourceFactor branch (w^(sourcePower branch)*r) w=
      sourceCoefficient branch*w^(sourcePower branch)*(sourceRoot branch).normalized w r := by
  cases branch <;> norm_num [sourceFactor,sourcePower,sourceCoefficient,sourceRoot,RootSource.normalized,value] <;> ring

theorem source_factor_root (branch : Branch) (w : ℝ) (small : |w|≤(sourceRoot branch).radius) :
    sourceFactor branch (w^(sourcePower branch)*(sourceRoot branch).root w) w=0 := by
  rw [source_factorization,(RootSource.root_spec _ w small).2,mul_zero]

theorem source_coefficient_nonzero (branch : Branch) : sourceCoefficient branch≠0 := by
  cases branch <;> norm_num [sourceCoefficient]

theorem source_root_unique (branch : Branch) (w r : ℝ) (small : |w|≤(sourceRoot branch).radius)
    (nonzero : w≠0) (inside : r∈Set.Icc ((sourceRoot branch).center-1/20) ((sourceRoot branch).center+1/20))
    (root : sourceFactor branch (w^(sourcePower branch)*r) w=0) : r=(sourceRoot branch).root w := by
  rw [source_factorization] at root
  have normal := (mul_eq_zero.mp root).resolve_left
    (mul_ne_zero (source_coefficient_nonzero branch) (pow_ne_zero _ nonzero))
  exact (sourceRoot branch).root_unique w r small inside normal

theorem source_root_simple (branch : Branch) (w : ℝ) (small : |w|≤(sourceRoot branch).radius) (nonzero : w≠0) :
    HasDerivAt (fun r : ℝ => sourceFactor branch (w^(sourcePower branch)*r) w)
      (sourceCoefficient branch*w^(sourcePower branch)*
        (1+w*value (differentiate (sourceRoot branch).terms) ((sourceRoot branch).root w) w))
      ((sourceRoot branch).root w) ∧
    sourceCoefficient branch*w^(sourcePower branch)*
      (1+w*value (differentiate (sourceRoot branch).terms) ((sourceRoot branch).root w) w)≠0 := by
  constructor
  · have generated := ((sourceRoot branch).normalized_derivative ((sourceRoot branch).root w) w).const_mul
      (sourceCoefficient branch*w^(sourcePower branch))
    convert! generated using 1
    funext r
    exact source_factorization branch r w
  · exact mul_ne_zero (mul_ne_zero (source_coefficient_nonzero branch) (pow_ne_zero _ nonzero))
      ((sourceRoot branch).root_derivative_positive w small).ne'

theorem momentum_root_domain (branch : Branch) (q : ℝ) (small : |q|≤momentumRadius) :
    |q^2|≤(sourceRoot branch).radius := by
  have qsmall : |q|≤1 := small.trans momentumRadius_bound
  have squares : |q^2|≤|q| := by rw [abs_pow]; nlinarith [abs_nonneg q]
  exact squares.trans (small.trans (source_radius branch))

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightModes
