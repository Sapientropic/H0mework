import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualContactDualImaginaryData
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockImaginaryPoint
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.ActualContactDualImaginary
open MixedSpectatorContactExchange MixedSpectatorDual24Data MixedSpectatorPairedSourceFrame
open scoped Matrix BigOperators

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private theorem sqrt15_sq : (Real.sqrt 15 : ℂ)^2 = 15 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)
private theorem contact_point_0 :
    contactPolynomial (worldTransfer Complex.I 0) 0 = contactValue 0 := by
  change ((-5/72) * (Real.sqrt 30 : ℂ)) = ((-5/72) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_1 :
    contactPolynomial (worldTransfer Complex.I 0) 1 = contactValue 1 := by
  change ((-5/72) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 30 : ℂ)) = ((-1/60) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_2 :
    contactPolynomial (worldTransfer Complex.I 0) 2 = contactValue 2 := by
  change ((-5/72) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_3 :
    contactPolynomial (worldTransfer Complex.I 0) 3 = contactValue 3 := by
  change ((1/24) * (Real.sqrt 15 : ℂ)) = ((1/24) * (Real.sqrt 15 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_4 :
    contactPolynomial (worldTransfer Complex.I 0) 4 = contactValue 4 := by
  change ((-5/72) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_5 :
    contactPolynomial (worldTransfer Complex.I 0) 5 = contactValue 5 := by
  change ((-1/24) * (Real.sqrt 15 : ℂ)) = ((-1/24) * (Real.sqrt 15 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_6 :
    contactPolynomial (worldTransfer Complex.I 0) 6 = contactValue 6 := by
  change ((-5/72) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_7 :
    contactPolynomial (worldTransfer Complex.I 0) 7 = contactValue 7 := by
  change ((-5/48) * (Real.sqrt 30 : ℂ)) = ((-5/48) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_8 :
    contactPolynomial (worldTransfer Complex.I 0) 8 = contactValue 8 := by
  change ((-5/144) * (Real.sqrt 30 : ℂ)) = ((-5/144) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_9 :
    contactPolynomial (worldTransfer Complex.I 0) 9 = contactValue 9 := by
  change ((5/144) * (Real.sqrt 30 : ℂ)) = ((5/144) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_10 :
    contactPolynomial (worldTransfer Complex.I 0) 10 = contactValue 10 := by
  change ((-5/48) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 30 : ℂ)) = ((-1/40) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_11 :
    contactPolynomial (worldTransfer Complex.I 0) 11 = contactValue 11 := by
  change ((-5/144) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 30 : ℂ)) = ((-1/120) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_12 :
    contactPolynomial (worldTransfer Complex.I 0) 12 = contactValue 12 := by
  change ((5/144) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 30 : ℂ)) = ((1/120) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_13 :
    contactPolynomial (worldTransfer Complex.I 0) 13 = contactValue 13 := by
  change ((1/16) * (Real.sqrt 15 : ℂ)) = ((1/16) * (Real.sqrt 15 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_14 :
    contactPolynomial (worldTransfer Complex.I 0) 14 = contactValue 14 := by
  change ((-5/48) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_15 :
    contactPolynomial (worldTransfer Complex.I 0) 15 = contactValue 15 := by
  change ((-5/144) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_16 :
    contactPolynomial (worldTransfer Complex.I 0) 16 = contactValue 16 := by
  change ((5/144) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_17 :
    contactPolynomial (worldTransfer Complex.I 0) 17 = contactValue 17 := by
  change ((-1/16) * (Real.sqrt 15 : ℂ)) = ((-1/16) * (Real.sqrt 15 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_18 :
    contactPolynomial (worldTransfer Complex.I 0) 18 = contactValue 18 := by
  change ((-5/48) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_19 :
    contactPolynomial (worldTransfer Complex.I 0) 19 = contactValue 19 := by
  change ((-5/144) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_20 :
    contactPolynomial (worldTransfer Complex.I 0) 20 = contactValue 20 := by
  change ((5/144) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_21 :
    contactPolynomial (worldTransfer Complex.I 0) 21 = contactValue 21 := by
  change ((-5/48) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_22 :
    contactPolynomial (worldTransfer Complex.I 0) 22 = contactValue 22 := by
  change ((-5/144) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_23 :
    contactPolynomial (worldTransfer Complex.I 0) 23 = contactValue 23 := by
  change ((5/144) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_24 :
    contactPolynomial (worldTransfer Complex.I 0) 24 = contactValue 24 := by
  change ((1/48) * (Real.sqrt 15 : ℂ)) = ((1/48) * (Real.sqrt 15 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_25 :
    contactPolynomial (worldTransfer Complex.I 0) 25 = contactValue 25 := by
  change ((-1/48) * (Real.sqrt 15 : ℂ)) = ((-1/48) * (Real.sqrt 15 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_26 :
    contactPolynomial (worldTransfer Complex.I 0) 26 = contactValue 26 := by
  change ((5/72) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 30 : ℂ)) = ((1/60) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_27 :
    contactPolynomial (worldTransfer Complex.I 0) 27 = contactValue 27 := by
  change ((5/72) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 0 ^ 2)) = ((-3/50) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_28 :
    contactPolynomial (worldTransfer Complex.I 0) 28 = contactValue 28 := by
  change ((5/72) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 1 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_29 :
    contactPolynomial (worldTransfer Complex.I 0) 29 = contactValue 29 := by
  change ((-1/24) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 15 : ℂ)) = ((-3/20) * Complex.I)
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_30 :
    contactPolynomial (worldTransfer Complex.I 0) 30 = contactValue 30 := by
  change ((5/72) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_31 :
    contactPolynomial (worldTransfer Complex.I 0) 31 = contactValue 31 := by
  change ((1/24) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 15 : ℂ)) = ((3/20) * Complex.I)
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_32 :
    contactPolynomial (worldTransfer Complex.I 0) 32 = contactValue 32 := by
  change ((5/72) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_33 :
    contactPolynomial (worldTransfer Complex.I 0) 33 = contactValue 33 := by
  change ((5/48) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 30 : ℂ)) = ((1/40) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_34 :
    contactPolynomial (worldTransfer Complex.I 0) 34 = contactValue 34 := by
  change ((5/48) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 0 ^ 2)) = ((-9/100) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_35 :
    contactPolynomial (worldTransfer Complex.I 0) 35 = contactValue 35 := by
  change ((5/144) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 0 ^ 2)) = ((-3/100) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_36 :
    contactPolynomial (worldTransfer Complex.I 0) 36 = contactValue 36 := by
  change ((-5/144) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 0 ^ 2)) = ((3/100) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_37 :
    contactPolynomial (worldTransfer Complex.I 0) 37 = contactValue 37 := by
  change ((-1/16) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 15 : ℂ)) = ((-9/40) * Complex.I)
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_38 :
    contactPolynomial (worldTransfer Complex.I 0) 38 = contactValue 38 := by
  change ((5/48) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 1 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_39 :
    contactPolynomial (worldTransfer Complex.I 0) 39 = contactValue 39 := by
  change ((5/144) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 1 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_40 :
    contactPolynomial (worldTransfer Complex.I 0) 40 = contactValue 40 := by
  change ((-5/144) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 1 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_41 :
    contactPolynomial (worldTransfer Complex.I 0) 41 = contactValue 41 := by
  change ((1/16) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 15 : ℂ)) = ((9/40) * Complex.I)
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_42 :
    contactPolynomial (worldTransfer Complex.I 0) 42 = contactValue 42 := by
  change ((5/48) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_43 :
    contactPolynomial (worldTransfer Complex.I 0) 43 = contactValue 43 := by
  change ((5/144) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_44 :
    contactPolynomial (worldTransfer Complex.I 0) 44 = contactValue 44 := by
  change ((-5/144) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_45 :
    contactPolynomial (worldTransfer Complex.I 0) 45 = contactValue 45 := by
  change ((5/48) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_46 :
    contactPolynomial (worldTransfer Complex.I 0) 46 = contactValue 46 := by
  change ((5/144) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_47 :
    contactPolynomial (worldTransfer Complex.I 0) 47 = contactValue 47 := by
  change ((-5/144) * (worldTransfer Complex.I 0) 0 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_48 :
    contactPolynomial (worldTransfer Complex.I 0) 48 = contactValue 48 := by
  change ((-1/48) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 15 : ℂ)) = ((-3/40) * Complex.I)
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_49 :
    contactPolynomial (worldTransfer Complex.I 0) 49 = contactValue 49 := by
  change ((1/48) * (worldTransfer Complex.I 0) 0 * (Real.sqrt 15 : ℂ)) = ((3/40) * Complex.I)
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_50 :
    contactPolynomial (worldTransfer Complex.I 0) 50 = contactValue 50 := by
  change ((-3/160) * (Real.sqrt 30 : ℂ)) = ((-3/160) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_51 :
    contactPolynomial (worldTransfer Complex.I 0) 51 = contactValue 51 := by
  change ((1/16) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_52 :
    contactPolynomial (worldTransfer Complex.I 0) 52 = contactValue 52 := by
  change ((1/48) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_53 :
    contactPolynomial (worldTransfer Complex.I 0) 53 = contactValue 53 := by
  change ((-1/48) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_54 :
    contactPolynomial (worldTransfer Complex.I 0) 54 = contactValue 54 := by
  change ((3/160) * (Real.sqrt 30 : ℂ)) = ((3/160) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_55 :
    contactPolynomial (worldTransfer Complex.I 0) 55 = contactValue 55 := by
  change ((1/16) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_56 :
    contactPolynomial (worldTransfer Complex.I 0) 56 = contactValue 56 := by
  change ((1/48) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_57 :
    contactPolynomial (worldTransfer Complex.I 0) 57 = contactValue 57 := by
  change ((-1/48) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_58 :
    contactPolynomial (worldTransfer Complex.I 0) 58 = contactValue 58 := by
  change ((1/16) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_59 :
    contactPolynomial (worldTransfer Complex.I 0) 59 = contactValue 59 := by
  change ((1/48) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_60 :
    contactPolynomial (worldTransfer Complex.I 0) 60 = contactValue 60 := by
  change ((-1/48) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_61 :
    contactPolynomial (worldTransfer Complex.I 0) 61 = contactValue 61 := by
  change ((5/72) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_62 :
    contactPolynomial (worldTransfer Complex.I 0) 62 = contactValue 62 := by
  change (((-1/80) * (Real.sqrt 30 : ℂ)) + ((5/72) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 1 ^ 2))) = ((-1/80) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_63 :
    contactPolynomial (worldTransfer Complex.I 0) 63 = contactValue 63 := by
  change ((-1/12) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_64 :
    contactPolynomial (worldTransfer Complex.I 0) 64 = contactValue 64 := by
  change ((5/72) * (worldTransfer Complex.I 0) 1 * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_65 :
    contactPolynomial (worldTransfer Complex.I 0) 65 = contactValue 65 := by
  change ((1/80) * (Real.sqrt 30 : ℂ)) = ((1/80) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_66 :
    contactPolynomial (worldTransfer Complex.I 0) 66 = contactValue 66 := by
  change ((1/24) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_67 :
    contactPolynomial (worldTransfer Complex.I 0) 67 = contactValue 67 := by
  change ((-1/24) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_68 :
    contactPolynomial (worldTransfer Complex.I 0) 68 = contactValue 68 := by
  change ((5/72) * (worldTransfer Complex.I 0) 1 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_69 :
    contactPolynomial (worldTransfer Complex.I 0) 69 = contactValue 69 := by
  change ((-1/24) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_70 :
    contactPolynomial (worldTransfer Complex.I 0) 70 = contactValue 70 := by
  change ((-1/24) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_71 :
    contactPolynomial (worldTransfer Complex.I 0) 71 = contactValue 71 := by
  change ((1/12) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_72 :
    contactPolynomial (worldTransfer Complex.I 0) 72 = contactValue 72 := by
  change ((-1/80) * (Real.sqrt 30 : ℂ)) = ((-1/80) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_73 :
    contactPolynomial (worldTransfer Complex.I 0) 73 = contactValue 73 := by
  change ((1/24) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_74 :
    contactPolynomial (worldTransfer Complex.I 0) 74 = contactValue 74 := by
  change ((1/24) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_75 :
    contactPolynomial (worldTransfer Complex.I 0) 75 = contactValue 75 := by
  change ((5/48) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_76 :
    contactPolynomial (worldTransfer Complex.I 0) 76 = contactValue 76 := by
  change ((-1/16) * (worldTransfer Complex.I 0) 1 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_77 :
    contactPolynomial (worldTransfer Complex.I 0) 77 = contactValue 77 := by
  change ((5/48) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 1 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_78 :
    contactPolynomial (worldTransfer Complex.I 0) 78 = contactValue 78 := by
  change ((5/144) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 1 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_79 :
    contactPolynomial (worldTransfer Complex.I 0) 79 = contactValue 79 := by
  change ((-5/144) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 1 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_80 :
    contactPolynomial (worldTransfer Complex.I 0) 80 = contactValue 80 := by
  change ((5/48) * (worldTransfer Complex.I 0) 1 * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_81 :
    contactPolynomial (worldTransfer Complex.I 0) 81 = contactValue 81 := by
  change ((5/144) * (worldTransfer Complex.I 0) 1 * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_82 :
    contactPolynomial (worldTransfer Complex.I 0) 82 = contactValue 82 := by
  change ((-5/144) * (worldTransfer Complex.I 0) 1 * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_83 :
    contactPolynomial (worldTransfer Complex.I 0) 83 = contactValue 83 := by
  change ((5/48) * (worldTransfer Complex.I 0) 1 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_84 :
    contactPolynomial (worldTransfer Complex.I 0) 84 = contactValue 84 := by
  change ((5/144) * (worldTransfer Complex.I 0) 1 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_85 :
    contactPolynomial (worldTransfer Complex.I 0) 85 = contactValue 85 := by
  change ((-5/144) * (worldTransfer Complex.I 0) 1 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_86 :
    contactPolynomial (worldTransfer Complex.I 0) 86 = contactValue 86 := by
  change ((5/72) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 1 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_87 :
    contactPolynomial (worldTransfer Complex.I 0) 87 = contactValue 87 := by
  change ((-1/16) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_88 :
    contactPolynomial (worldTransfer Complex.I 0) 88 = contactValue 88 := by
  change ((-1/16) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_89 :
    contactPolynomial (worldTransfer Complex.I 0) 89 = contactValue 89 := by
  change ((5/72) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_90 :
    contactPolynomial (worldTransfer Complex.I 0) 90 = contactValue 90 := by
  change (((-1/80) * (Real.sqrt 30 : ℂ)) + ((5/72) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 2 ^ 2))) = ((-1/80) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_91 :
    contactPolynomial (worldTransfer Complex.I 0) 91 = contactValue 91 := by
  change ((1/12) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_92 :
    contactPolynomial (worldTransfer Complex.I 0) 92 = contactValue 92 := by
  change ((5/72) * (worldTransfer Complex.I 0) 2 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_93 :
    contactPolynomial (worldTransfer Complex.I 0) 93 = contactValue 93 := by
  change ((-1/12) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_94 :
    contactPolynomial (worldTransfer Complex.I 0) 94 = contactValue 94 := by
  change ((5/48) * (worldTransfer Complex.I 0) 2 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_95 :
    contactPolynomial (worldTransfer Complex.I 0) 95 = contactValue 95 := by
  change ((5/48) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 2 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_96 :
    contactPolynomial (worldTransfer Complex.I 0) 96 = contactValue 96 := by
  change ((5/144) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 2 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_97 :
    contactPolynomial (worldTransfer Complex.I 0) 97 = contactValue 97 := by
  change ((-5/144) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 2 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_98 :
    contactPolynomial (worldTransfer Complex.I 0) 98 = contactValue 98 := by
  change ((5/48) * (worldTransfer Complex.I 0) 2 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_99 :
    contactPolynomial (worldTransfer Complex.I 0) 99 = contactValue 99 := by
  change ((5/144) * (worldTransfer Complex.I 0) 2 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_100 :
    contactPolynomial (worldTransfer Complex.I 0) 100 = contactValue 100 := by
  change ((-5/144) * (worldTransfer Complex.I 0) 2 * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_101 :
    contactPolynomial (worldTransfer Complex.I 0) 101 = contactValue 101 := by
  change ((5/72) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 2 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_102 :
    contactPolynomial (worldTransfer Complex.I 0) 102 = contactValue 102 := by
  change ((5/72) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_103 :
    contactPolynomial (worldTransfer Complex.I 0) 103 = contactValue 103 := by
  change (((-1/80) * (Real.sqrt 30 : ℂ)) + ((5/72) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 3 ^ 2))) = ((-1/80) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_104 :
    contactPolynomial (worldTransfer Complex.I 0) 104 = contactValue 104 := by
  change ((-1/12) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_105 :
    contactPolynomial (worldTransfer Complex.I 0) 105 = contactValue 105 := by
  change ((1/12) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 15 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_106 :
    contactPolynomial (worldTransfer Complex.I 0) 106 = contactValue 106 := by
  change ((5/48) * (worldTransfer Complex.I 0) 3 * (Real.sqrt 30 : ℂ)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_107 :
    contactPolynomial (worldTransfer Complex.I 0) 107 = contactValue 107 := by
  change ((5/48) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 3 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_108 :
    contactPolynomial (worldTransfer Complex.I 0) 108 = contactValue 108 := by
  change ((5/144) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 3 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_109 :
    contactPolynomial (worldTransfer Complex.I 0) 109 = contactValue 109 := by
  change ((-5/144) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 3 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_110 :
    contactPolynomial (worldTransfer Complex.I 0) 110 = contactValue 110 := by
  change ((5/72) * (Real.sqrt 30 : ℂ) * ((worldTransfer Complex.I 0) 3 ^ 2)) = 0
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_111 :
    contactPolynomial (worldTransfer Complex.I 0) 111 = contactValue 111 := by
  change ((-3/50) * (Real.sqrt 30 : ℂ)) = ((-3/50) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_112 :
    contactPolynomial (worldTransfer Complex.I 0) 112 = contactValue 112 := by
  change (1/2) = (1/2)
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_113 :
    contactPolynomial (worldTransfer Complex.I 0) 113 = contactValue 113 := by
  change (-1/2) = (-1/2)
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_114 :
    contactPolynomial (worldTransfer Complex.I 0) 114 = contactValue 114 := by
  change ((3/50) * (Real.sqrt 30 : ℂ)) = ((3/50) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_115 :
    contactPolynomial (worldTransfer Complex.I 0) 115 = contactValue 115 := by
  change ((5/36) * (Real.sqrt 30 : ℂ)) = ((5/36) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)
private theorem contact_point_116 :
    contactPolynomial (worldTransfer Complex.I 0) 116 = contactValue 116 := by
  change ((-5/36) * (Real.sqrt 30 : ℂ)) = ((-5/36) * (Real.sqrt 30 : ℂ))
  norm_num [worldTransfer,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (ring_nf <;> norm_num [sqrt15_sq,Complex.I_sq] <;> ring)

theorem actual_contact_polynomial_point (a : Fin 117) :
    contactPolynomial (worldTransfer Complex.I 0) a = contactValue a := by
  fin_cases a
  · exact contact_point_0
  · exact contact_point_1
  · exact contact_point_2
  · exact contact_point_3
  · exact contact_point_4
  · exact contact_point_5
  · exact contact_point_6
  · exact contact_point_7
  · exact contact_point_8
  · exact contact_point_9
  · exact contact_point_10
  · exact contact_point_11
  · exact contact_point_12
  · exact contact_point_13
  · exact contact_point_14
  · exact contact_point_15
  · exact contact_point_16
  · exact contact_point_17
  · exact contact_point_18
  · exact contact_point_19
  · exact contact_point_20
  · exact contact_point_21
  · exact contact_point_22
  · exact contact_point_23
  · exact contact_point_24
  · exact contact_point_25
  · exact contact_point_26
  · exact contact_point_27
  · exact contact_point_28
  · exact contact_point_29
  · exact contact_point_30
  · exact contact_point_31
  · exact contact_point_32
  · exact contact_point_33
  · exact contact_point_34
  · exact contact_point_35
  · exact contact_point_36
  · exact contact_point_37
  · exact contact_point_38
  · exact contact_point_39
  · exact contact_point_40
  · exact contact_point_41
  · exact contact_point_42
  · exact contact_point_43
  · exact contact_point_44
  · exact contact_point_45
  · exact contact_point_46
  · exact contact_point_47
  · exact contact_point_48
  · exact contact_point_49
  · exact contact_point_50
  · exact contact_point_51
  · exact contact_point_52
  · exact contact_point_53
  · exact contact_point_54
  · exact contact_point_55
  · exact contact_point_56
  · exact contact_point_57
  · exact contact_point_58
  · exact contact_point_59
  · exact contact_point_60
  · exact contact_point_61
  · exact contact_point_62
  · exact contact_point_63
  · exact contact_point_64
  · exact contact_point_65
  · exact contact_point_66
  · exact contact_point_67
  · exact contact_point_68
  · exact contact_point_69
  · exact contact_point_70
  · exact contact_point_71
  · exact contact_point_72
  · exact contact_point_73
  · exact contact_point_74
  · exact contact_point_75
  · exact contact_point_76
  · exact contact_point_77
  · exact contact_point_78
  · exact contact_point_79
  · exact contact_point_80
  · exact contact_point_81
  · exact contact_point_82
  · exact contact_point_83
  · exact contact_point_84
  · exact contact_point_85
  · exact contact_point_86
  · exact contact_point_87
  · exact contact_point_88
  · exact contact_point_89
  · exact contact_point_90
  · exact contact_point_91
  · exact contact_point_92
  · exact contact_point_93
  · exact contact_point_94
  · exact contact_point_95
  · exact contact_point_96
  · exact contact_point_97
  · exact contact_point_98
  · exact contact_point_99
  · exact contact_point_100
  · exact contact_point_101
  · exact contact_point_102
  · exact contact_point_103
  · exact contact_point_104
  · exact contact_point_105
  · exact contact_point_106
  · exact contact_point_107
  · exact contact_point_108
  · exact contact_point_109
  · exact contact_point_110
  · exact contact_point_111
  · exact contact_point_112
  · exact contact_point_113
  · exact contact_point_114
  · exact contact_point_115
  · exact contact_point_116
private theorem numerator_point_0 :
    numeratorPolynomial Complex.I 0 0 = dualNumeratorValue 0 := by
  change numerator0 Complex.I 0 = (852489/1250000)
  norm_num [numerator0,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_1 :
    numeratorPolynomial Complex.I 0 1 = dualNumeratorValue 1 := by
  change numerator1 Complex.I 0 = (-28677/250000)
  norm_num [numerator1,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_2 :
    numeratorPolynomial Complex.I 0 2 = dualNumeratorValue 2 := by
  change numerator2 Complex.I 0 = (-159027/250000)
  norm_num [numerator2,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_3 :
    numeratorPolynomial Complex.I 0 3 = dualNumeratorValue 3 := by
  change numerator3 Complex.I 0 = ((14773/31250) * Complex.I)
  norm_num [numerator3,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_4 :
    numeratorPolynomial Complex.I 0 4 = dualNumeratorValue 4 := by
  change numerator4 Complex.I 0 = 0
  norm_num [numerator4,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_5 :
    numeratorPolynomial Complex.I 0 5 = dualNumeratorValue 5 := by
  change numerator5 Complex.I 0 = 0
  norm_num [numerator5,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_6 :
    numeratorPolynomial Complex.I 0 6 = dualNumeratorValue 6 := by
  change numerator6 Complex.I 0 = ((7821/12500) * Complex.I)
  norm_num [numerator6,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_7 :
    numeratorPolynomial Complex.I 0 7 = dualNumeratorValue 7 := by
  change numerator7 Complex.I 0 = (852489/1250000)
  norm_num [numerator7,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_8 :
    numeratorPolynomial Complex.I 0 8 = dualNumeratorValue 8 := by
  change numerator8 Complex.I 0 = (-159027/250000)
  norm_num [numerator8,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_9 :
    numeratorPolynomial Complex.I 0 9 = dualNumeratorValue 9 := by
  change numerator9 Complex.I 0 = ((14773/31250) * Complex.I)
  norm_num [numerator9,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_10 :
    numeratorPolynomial Complex.I 0 10 = dualNumeratorValue 10 := by
  change numerator10 Complex.I 0 = ((7821/12500) * Complex.I)
  norm_num [numerator10,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_11 :
    numeratorPolynomial Complex.I 0 11 = dualNumeratorValue 11 := by
  change numerator11 Complex.I 0 = ((-7821/12500) * Complex.I)
  norm_num [numerator11,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_12 :
    numeratorPolynomial Complex.I 0 12 = dualNumeratorValue 12 := by
  change numerator12 Complex.I 0 = ((-14773/31250) * Complex.I)
  norm_num [numerator12,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_13 :
    numeratorPolynomial Complex.I 0 13 = dualNumeratorValue 13 := by
  change numerator13 Complex.I 0 = ((-7821/12500) * Complex.I)
  norm_num [numerator13,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_14 :
    numeratorPolynomial Complex.I 0 14 = dualNumeratorValue 14 := by
  change numerator14 Complex.I 0 = ((-14773/31250) * Complex.I)
  norm_num [numerator14,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_15 :
    numeratorPolynomial Complex.I 0 15 = dualNumeratorValue 15 := by
  change numerator15 Complex.I 0 = (28677/250000)
  norm_num [numerator15,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_16 :
    numeratorPolynomial Complex.I 0 16 = dualNumeratorValue 16 := by
  change numerator16 Complex.I 0 = (159027/250000)
  norm_num [numerator16,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_17 :
    numeratorPolynomial Complex.I 0 17 = dualNumeratorValue 17 := by
  change numerator17 Complex.I 0 = (159027/250000)
  norm_num [numerator17,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_18 :
    numeratorPolynomial Complex.I 0 18 = dualNumeratorValue 18 := by
  change numerator18 Complex.I 0 = (-129/5000)
  norm_num [numerator18,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_19 :
    numeratorPolynomial Complex.I 0 19 = dualNumeratorValue 19 := by
  change numerator19 Complex.I 0 = (-342/625)
  norm_num [numerator19,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_20 :
    numeratorPolynomial Complex.I 0 20 = dualNumeratorValue 20 := by
  change numerator20 Complex.I 0 = (183/2500)
  norm_num [numerator20,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_21 :
    numeratorPolynomial Complex.I 0 21 = dualNumeratorValue 21 := by
  change numerator21 Complex.I 0 = (-2241/5000)
  norm_num [numerator21,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_22 :
    numeratorPolynomial Complex.I 0 22 = dualNumeratorValue 22 := by
  change numerator22 Complex.I 0 = ((19/5000) * Complex.I)
  norm_num [numerator22,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_23 :
    numeratorPolynomial Complex.I 0 23 = dualNumeratorValue 23 := by
  change numerator23 Complex.I 0 = ((-1719/5000) * Complex.I)
  norm_num [numerator23,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_24 :
    numeratorPolynomial Complex.I 0 24 = dualNumeratorValue 24 := by
  change numerator24 Complex.I 0 = ((9/40) * Complex.I)
  norm_num [numerator24,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_25 :
    numeratorPolynomial Complex.I 0 25 = dualNumeratorValue 25 := by
  change numerator25 Complex.I 0 = ((9/40) * Complex.I)
  norm_num [numerator25,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_26 :
    numeratorPolynomial Complex.I 0 26 = dualNumeratorValue 26 := by
  change numerator26 Complex.I 0 = (-129/5000)
  norm_num [numerator26,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_27 :
    numeratorPolynomial Complex.I 0 27 = dualNumeratorValue 27 := by
  change numerator27 Complex.I 0 = (-2241/5000)
  norm_num [numerator27,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_28 :
    numeratorPolynomial Complex.I 0 28 = dualNumeratorValue 28 := by
  change numerator28 Complex.I 0 = ((-1719/5000) * Complex.I)
  norm_num [numerator28,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_29 :
    numeratorPolynomial Complex.I 0 29 = dualNumeratorValue 29 := by
  change numerator29 Complex.I 0 = ((19/5000) * Complex.I)
  norm_num [numerator29,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_30 :
    numeratorPolynomial Complex.I 0 30 = dualNumeratorValue 30 := by
  change numerator30 Complex.I 0 = ((9/40) * Complex.I)
  norm_num [numerator30,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_31 :
    numeratorPolynomial Complex.I 0 31 = dualNumeratorValue 31 := by
  change numerator31 Complex.I 0 = ((9/40) * Complex.I)
  norm_num [numerator31,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_32 :
    numeratorPolynomial Complex.I 0 32 = dualNumeratorValue 32 := by
  change numerator32 Complex.I 0 = ((-9/40) * Complex.I)
  norm_num [numerator32,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_33 :
    numeratorPolynomial Complex.I 0 33 = dualNumeratorValue 33 := by
  change numerator33 Complex.I 0 = ((-9/40) * Complex.I)
  norm_num [numerator33,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_34 :
    numeratorPolynomial Complex.I 0 34 = dualNumeratorValue 34 := by
  change numerator34 Complex.I 0 = ((-19/5000) * Complex.I)
  norm_num [numerator34,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_35 :
    numeratorPolynomial Complex.I 0 35 = dualNumeratorValue 35 := by
  change numerator35 Complex.I 0 = ((1719/5000) * Complex.I)
  norm_num [numerator35,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_36 :
    numeratorPolynomial Complex.I 0 36 = dualNumeratorValue 36 := by
  change numerator36 Complex.I 0 = ((-9/40) * Complex.I)
  norm_num [numerator36,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_37 :
    numeratorPolynomial Complex.I 0 37 = dualNumeratorValue 37 := by
  change numerator37 Complex.I 0 = ((-9/40) * Complex.I)
  norm_num [numerator37,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_38 :
    numeratorPolynomial Complex.I 0 38 = dualNumeratorValue 38 := by
  change numerator38 Complex.I 0 = ((1719/5000) * Complex.I)
  norm_num [numerator38,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_39 :
    numeratorPolynomial Complex.I 0 39 = dualNumeratorValue 39 := by
  change numerator39 Complex.I 0 = ((-19/5000) * Complex.I)
  norm_num [numerator39,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_40 :
    numeratorPolynomial Complex.I 0 40 = dualNumeratorValue 40 := by
  change numerator40 Complex.I 0 = (-51/250)
  norm_num [numerator40,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_41 :
    numeratorPolynomial Complex.I 0 41 = dualNumeratorValue 41 := by
  change numerator41 Complex.I 0 = (-51/250)
  norm_num [numerator41,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_42 :
    numeratorPolynomial Complex.I 0 42 = dualNumeratorValue 42 := by
  change numerator42 Complex.I 0 = (27/100)
  norm_num [numerator42,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_43 :
    numeratorPolynomial Complex.I 0 43 = dualNumeratorValue 43 := by
  change numerator43 Complex.I 0 = (27/100)
  norm_num [numerator43,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_44 :
    numeratorPolynomial Complex.I 0 44 = dualNumeratorValue 44 := by
  change numerator44 Complex.I 0 = (-51/250)
  norm_num [numerator44,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_45 :
    numeratorPolynomial Complex.I 0 45 = dualNumeratorValue 45 := by
  change numerator45 Complex.I 0 = (27/100)
  norm_num [numerator45,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_46 :
    numeratorPolynomial Complex.I 0 46 = dualNumeratorValue 46 := by
  change numerator46 Complex.I 0 = (9/40)
  norm_num [numerator46,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_47 :
    numeratorPolynomial Complex.I 0 47 = dualNumeratorValue 47 := by
  change numerator47 Complex.I 0 = ((1/4) * Complex.I)
  norm_num [numerator47,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_48 :
    numeratorPolynomial Complex.I 0 48 = dualNumeratorValue 48 := by
  change numerator48 Complex.I 0 = ((-1/4) * Complex.I)
  norm_num [numerator48,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_49 :
    numeratorPolynomial Complex.I 0 49 = dualNumeratorValue 49 := by
  change numerator49 Complex.I 0 = ((1/4) * Complex.I)
  norm_num [numerator49,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring
private theorem numerator_point_50 :
    numeratorPolynomial Complex.I 0 50 = dualNumeratorValue 50 := by
  change numerator50 Complex.I 0 = ((-1/4) * Complex.I)
  norm_num [numerator50,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]
  all_goals ring

theorem actual_dual_numerator_point (a : Fin 51) :
    numeratorPolynomial Complex.I 0 a = dualNumeratorValue a := by
  fin_cases a
  · exact numerator_point_0
  · exact numerator_point_1
  · exact numerator_point_2
  · exact numerator_point_3
  · exact numerator_point_4
  · exact numerator_point_5
  · exact numerator_point_6
  · exact numerator_point_7
  · exact numerator_point_8
  · exact numerator_point_9
  · exact numerator_point_10
  · exact numerator_point_11
  · exact numerator_point_12
  · exact numerator_point_13
  · exact numerator_point_14
  · exact numerator_point_15
  · exact numerator_point_16
  · exact numerator_point_17
  · exact numerator_point_18
  · exact numerator_point_19
  · exact numerator_point_20
  · exact numerator_point_21
  · exact numerator_point_22
  · exact numerator_point_23
  · exact numerator_point_24
  · exact numerator_point_25
  · exact numerator_point_26
  · exact numerator_point_27
  · exact numerator_point_28
  · exact numerator_point_29
  · exact numerator_point_30
  · exact numerator_point_31
  · exact numerator_point_32
  · exact numerator_point_33
  · exact numerator_point_34
  · exact numerator_point_35
  · exact numerator_point_36
  · exact numerator_point_37
  · exact numerator_point_38
  · exact numerator_point_39
  · exact numerator_point_40
  · exact numerator_point_41
  · exact numerator_point_42
  · exact numerator_point_43
  · exact numerator_point_44
  · exact numerator_point_45
  · exact numerator_point_46
  · exact numerator_point_47
  · exact numerator_point_48
  · exact numerator_point_49
  · exact numerator_point_50

theorem actual_dual_denominator_point (a : Fin 6) :
    denominator Complex.I 0 a = dualDenominatorValue a := by
  fin_cases a <;> norm_num [denominator,dualDenominatorValue,Complex.I_pow_eq_pow_mod]
  all_goals norm_num [Complex.I_sq]

private def axialForm (numeratorFamily : Fin 51 → ℂ) (denominatorFamily : Fin 6 → ℂ) (a b : Fin 24) : ℂ :=
  let entry : ℂ := match a.val, b.val with
    | 0, 0 => numeratorFamily 0 / denominatorFamily 0
    | 0, 4 => numeratorFamily 1 / denominatorFamily 0
    | 0, 6 => numeratorFamily 1 / denominatorFamily 0
    | 0, 10 => numeratorFamily 2 / denominatorFamily 0
    | 0, 12 => numeratorFamily 3 / denominatorFamily 0
    | 0, 16 => numeratorFamily 4 / denominatorFamily 0
    | 0, 18 => numeratorFamily 5 / denominatorFamily 0
    | 0, 22 => numeratorFamily 6 / denominatorFamily 0
    | 4, 0 => numeratorFamily 1 / denominatorFamily 0
    | 4, 4 => numeratorFamily 7 / denominatorFamily 0
    | 4, 6 => numeratorFamily 8 / denominatorFamily 0
    | 4, 10 => numeratorFamily 1 / denominatorFamily 0
    | 4, 12 => numeratorFamily 5 / denominatorFamily 0
    | 4, 16 => numeratorFamily 9 / denominatorFamily 0
    | 4, 18 => numeratorFamily 10 / denominatorFamily 0
    | 4, 22 => numeratorFamily 4 / denominatorFamily 0
    | 6, 0 => numeratorFamily 1 / denominatorFamily 0
    | 6, 4 => numeratorFamily 8 / denominatorFamily 0
    | 6, 6 => numeratorFamily 7 / denominatorFamily 0
    | 6, 10 => numeratorFamily 1 / denominatorFamily 0
    | 6, 12 => numeratorFamily 5 / denominatorFamily 0
    | 6, 16 => numeratorFamily 11 / denominatorFamily 0
    | 6, 18 => numeratorFamily 12 / denominatorFamily 0
    | 6, 22 => numeratorFamily 4 / denominatorFamily 0
    | 10, 0 => numeratorFamily 2 / denominatorFamily 0
    | 10, 4 => numeratorFamily 1 / denominatorFamily 0
    | 10, 6 => numeratorFamily 1 / denominatorFamily 0
    | 10, 10 => numeratorFamily 0 / denominatorFamily 0
    | 10, 12 => numeratorFamily 13 / denominatorFamily 0
    | 10, 16 => numeratorFamily 4 / denominatorFamily 0
    | 10, 18 => numeratorFamily 5 / denominatorFamily 0
    | 10, 22 => numeratorFamily 14 / denominatorFamily 0
    | 12, 0 => numeratorFamily 14 / denominatorFamily 0
    | 12, 4 => numeratorFamily 4 / denominatorFamily 0
    | 12, 6 => numeratorFamily 4 / denominatorFamily 0
    | 12, 10 => numeratorFamily 6 / denominatorFamily 0
    | 12, 12 => numeratorFamily 0 / denominatorFamily 0
    | 12, 16 => numeratorFamily 15 / denominatorFamily 0
    | 12, 18 => numeratorFamily 1 / denominatorFamily 0
    | 12, 22 => numeratorFamily 16 / denominatorFamily 0
    | 16, 0 => numeratorFamily 5 / denominatorFamily 0
    | 16, 4 => numeratorFamily 12 / denominatorFamily 0
    | 16, 6 => numeratorFamily 10 / denominatorFamily 0
    | 16, 10 => numeratorFamily 5 / denominatorFamily 0
    | 16, 12 => numeratorFamily 15 / denominatorFamily 0
    | 16, 16 => numeratorFamily 7 / denominatorFamily 0
    | 16, 18 => numeratorFamily 17 / denominatorFamily 0
    | 16, 22 => numeratorFamily 1 / denominatorFamily 0
    | 18, 0 => numeratorFamily 4 / denominatorFamily 0
    | 18, 4 => numeratorFamily 11 / denominatorFamily 0
    | 18, 6 => numeratorFamily 9 / denominatorFamily 0
    | 18, 10 => numeratorFamily 4 / denominatorFamily 0
    | 18, 12 => numeratorFamily 1 / denominatorFamily 0
    | 18, 16 => numeratorFamily 17 / denominatorFamily 0
    | 18, 18 => numeratorFamily 7 / denominatorFamily 0
    | 18, 22 => numeratorFamily 15 / denominatorFamily 0
    | 22, 0 => numeratorFamily 13 / denominatorFamily 0
    | 22, 4 => numeratorFamily 5 / denominatorFamily 0
    | 22, 6 => numeratorFamily 5 / denominatorFamily 0
    | 22, 10 => numeratorFamily 3 / denominatorFamily 0
    | 22, 12 => numeratorFamily 16 / denominatorFamily 0
    | 22, 16 => numeratorFamily 1 / denominatorFamily 0
    | 22, 18 => numeratorFamily 15 / denominatorFamily 0
    | 22, 22 => numeratorFamily 0 / denominatorFamily 0
    | 1, 1 => numeratorFamily 18 / denominatorFamily 1
    | 1, 3 => numeratorFamily 19 / denominatorFamily 1
    | 1, 7 => numeratorFamily 20 / denominatorFamily 1
    | 1, 9 => numeratorFamily 21 / denominatorFamily 1
    | 1, 13 => numeratorFamily 22 / denominatorFamily 1
    | 1, 15 => numeratorFamily 23 / denominatorFamily 1
    | 1, 19 => numeratorFamily 24 / denominatorFamily 1
    | 1, 21 => numeratorFamily 25 / denominatorFamily 1
    | 3, 1 => numeratorFamily 19 / denominatorFamily 1
    | 3, 3 => numeratorFamily 26 / denominatorFamily 1
    | 3, 7 => numeratorFamily 27 / denominatorFamily 1
    | 3, 9 => numeratorFamily 20 / denominatorFamily 1
    | 3, 13 => numeratorFamily 28 / denominatorFamily 1
    | 3, 15 => numeratorFamily 29 / denominatorFamily 1
    | 3, 19 => numeratorFamily 30 / denominatorFamily 1
    | 3, 21 => numeratorFamily 31 / denominatorFamily 1
    | 7, 1 => numeratorFamily 20 / denominatorFamily 1
    | 7, 3 => numeratorFamily 27 / denominatorFamily 1
    | 7, 7 => numeratorFamily 26 / denominatorFamily 1
    | 7, 9 => numeratorFamily 19 / denominatorFamily 1
    | 7, 13 => numeratorFamily 32 / denominatorFamily 1
    | 7, 15 => numeratorFamily 33 / denominatorFamily 1
    | 7, 19 => numeratorFamily 34 / denominatorFamily 1
    | 7, 21 => numeratorFamily 35 / denominatorFamily 1
    | 9, 1 => numeratorFamily 21 / denominatorFamily 1
    | 9, 3 => numeratorFamily 20 / denominatorFamily 1
    | 9, 7 => numeratorFamily 19 / denominatorFamily 1
    | 9, 9 => numeratorFamily 18 / denominatorFamily 1
    | 9, 13 => numeratorFamily 36 / denominatorFamily 1
    | 9, 15 => numeratorFamily 37 / denominatorFamily 1
    | 9, 19 => numeratorFamily 38 / denominatorFamily 1
    | 9, 21 => numeratorFamily 39 / denominatorFamily 1
    | 13, 1 => numeratorFamily 39 / denominatorFamily 1
    | 13, 3 => numeratorFamily 35 / denominatorFamily 1
    | 13, 7 => numeratorFamily 31 / denominatorFamily 1
    | 13, 9 => numeratorFamily 25 / denominatorFamily 1
    | 13, 13 => numeratorFamily 40 / denominatorFamily 1
    | 13, 15 => numeratorFamily 41 / denominatorFamily 1
    | 13, 19 => numeratorFamily 42 / denominatorFamily 1
    | 13, 21 => numeratorFamily 43 / denominatorFamily 1
    | 15, 1 => numeratorFamily 38 / denominatorFamily 1
    | 15, 3 => numeratorFamily 34 / denominatorFamily 1
    | 15, 7 => numeratorFamily 30 / denominatorFamily 1
    | 15, 9 => numeratorFamily 24 / denominatorFamily 1
    | 15, 13 => numeratorFamily 41 / denominatorFamily 1
    | 15, 15 => numeratorFamily 44 / denominatorFamily 1
    | 15, 19 => numeratorFamily 45 / denominatorFamily 1
    | 15, 21 => numeratorFamily 42 / denominatorFamily 1
    | 19, 1 => numeratorFamily 37 / denominatorFamily 1
    | 19, 3 => numeratorFamily 33 / denominatorFamily 1
    | 19, 7 => numeratorFamily 29 / denominatorFamily 1
    | 19, 9 => numeratorFamily 23 / denominatorFamily 1
    | 19, 13 => numeratorFamily 42 / denominatorFamily 1
    | 19, 15 => numeratorFamily 45 / denominatorFamily 1
    | 19, 19 => numeratorFamily 44 / denominatorFamily 1
    | 19, 21 => numeratorFamily 41 / denominatorFamily 1
    | 21, 1 => numeratorFamily 36 / denominatorFamily 1
    | 21, 3 => numeratorFamily 32 / denominatorFamily 1
    | 21, 7 => numeratorFamily 28 / denominatorFamily 1
    | 21, 9 => numeratorFamily 22 / denominatorFamily 1
    | 21, 13 => numeratorFamily 43 / denominatorFamily 1
    | 21, 15 => numeratorFamily 42 / denominatorFamily 1
    | 21, 19 => numeratorFamily 41 / denominatorFamily 1
    | 21, 21 => numeratorFamily 40 / denominatorFamily 1
    | 2, 2 => numeratorFamily 46 / denominatorFamily 2
    | 2, 14 => numeratorFamily 47 / denominatorFamily 2
    | 14, 2 => numeratorFamily 48 / denominatorFamily 2
    | 14, 14 => numeratorFamily 46 / denominatorFamily 2
    | 5, 5 => numeratorFamily 46 / denominatorFamily 3
    | 5, 17 => numeratorFamily 49 / denominatorFamily 3
    | 17, 5 => numeratorFamily 50 / denominatorFamily 3
    | 17, 17 => numeratorFamily 46 / denominatorFamily 3
    | 8, 8 => numeratorFamily 46 / denominatorFamily 4
    | 8, 20 => numeratorFamily 50 / denominatorFamily 4
    | 20, 8 => numeratorFamily 49 / denominatorFamily 4
    | 20, 20 => numeratorFamily 46 / denominatorFamily 4
    | 11, 11 => numeratorFamily 46 / denominatorFamily 5
    | 11, 23 => numeratorFamily 48 / denominatorFamily 5
    | 23, 11 => numeratorFamily 47 / denominatorFamily 5
    | 23, 23 => numeratorFamily 46 / denominatorFamily 5
    | _, _ => 0
  entry / (SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse : ℂ)

theorem actual_dual_axial_point (a b : Fin 24) :
    axialInverse Complex.I 0 a b = dualAxialValue a b := by
  have hn : numeratorPolynomial Complex.I 0 = dualNumeratorValue :=
    funext actual_dual_numerator_point
  have hd : denominator Complex.I 0 = dualDenominatorValue :=
    funext actual_dual_denominator_point
  change axialForm (numeratorPolynomial Complex.I 0) (denominator Complex.I 0) a b =
    axialForm dualNumeratorValue dualDenominatorValue a b
  exact congrArg₂ (fun n d => axialForm n d a b) hn hd

theorem actual_dual_world_source_zero (a : Fin 24) (b : Fin 97) :
    MixedSpectatorDual24Exchange.worldSourceMap 0 a b = axialSourceMap a b := by
  classical
  simp [MixedSpectatorDual24Exchange.worldSourceMap,actual_zero_source_frame,Matrix.one_apply]

theorem actual_dual_coefficient_point (a b : Fin 97) :
    MixedSpectatorDual24Exchange.dualCoefficient Complex.I 0 a b =
      ∑i : Fin 24,∑j : Fin 24,axialSourceMap i a * dualAxialValue i j * axialSourceMap j b := by
  simp only [MixedSpectatorDual24Exchange.dualCoefficient,actual_dual_world_source_zero,
    ActualFourBlockElastic.zero_signed_radius,Complex.ofReal_zero,actual_dual_axial_point]

end LowEnergy.ActualContactDualImaginary
