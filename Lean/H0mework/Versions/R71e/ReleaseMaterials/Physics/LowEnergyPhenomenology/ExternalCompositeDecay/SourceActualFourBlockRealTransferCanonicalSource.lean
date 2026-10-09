import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79SourceSparseRows
import Lean.Elab.Tactic
import Mathlib.Analysis.Meromorphic.Order

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorCanonical79Data MixedSpectatorCanonical79Exchange
open scoped BigOperators

theorem actual_canonical_denominator_analytic (z : ℂ) (a : Fin 10) :
    AnalyticAt ℂ (fun x => denominator x 0 a) z := by
  fin_cases a <;> simp only [denominator, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> fun_prop

theorem actual_canonical_source_polynomial_analytic (z : ℂ) (a : Fin 16) :
    AnalyticAt ℂ (fun x => sourceMapPolynomial x 0 a) z := by
  fin_cases a <;> simp only [sourceMapPolynomial, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> fun_prop

open Lean Meta Elab Tactic
elab "analytic_paid_source_schema_row" n:num : tactic => do
  let i := n.getNat
  let file := if i = 0 then "SourceCanonical79SourceSparsePilot" else
    "SourceCanonical79SourceSparseRows" ++ toString (i / 16)
  let ns := Name.str (Name.str (Name.num (Name.str `_private file) 0) "LowEnergy")
    "ActualCanonical79Imaginary"
  let identity := mkIdent (Name.str ns ("schema" ++ toString i))
  let row := mkIdent (Name.str ns ("schemaRow" ++ toString i))
  evalTactic (← `(tactic| simp_rw [$identity:ident]))
  if i != 0 then evalTactic (← `(tactic| unfold $row:ident))
  let _h := mkIdent `_h
  evalTactic (← `(tactic| first | exact analyticAt_const | (split <;> first | exact $_h:ident _ | exact analyticAt_const)))

private theorem source_schema_row0_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 0 b) z := by
  analytic_paid_source_schema_row 0

private theorem source_schema_row1_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 1 b) z := by
  analytic_paid_source_schema_row 1

private theorem source_schema_row2_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 2 b) z := by
  analytic_paid_source_schema_row 2

private theorem source_schema_row3_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 3 b) z := by
  analytic_paid_source_schema_row 3

private theorem source_schema_row4_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 4 b) z := by
  analytic_paid_source_schema_row 4

private theorem source_schema_row5_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 5 b) z := by
  analytic_paid_source_schema_row 5

private theorem source_schema_row6_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 6 b) z := by
  analytic_paid_source_schema_row 6

private theorem source_schema_row7_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 7 b) z := by
  analytic_paid_source_schema_row 7

private theorem source_schema_row8_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 8 b) z := by
  analytic_paid_source_schema_row 8

private theorem source_schema_row9_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 9 b) z := by
  analytic_paid_source_schema_row 9

private theorem source_schema_row10_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 10 b) z := by
  analytic_paid_source_schema_row 10

private theorem source_schema_row11_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 11 b) z := by
  analytic_paid_source_schema_row 11

private theorem source_schema_row12_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 12 b) z := by
  analytic_paid_source_schema_row 12

private theorem source_schema_row13_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 13 b) z := by
  analytic_paid_source_schema_row 13

private theorem source_schema_row14_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 14 b) z := by
  analytic_paid_source_schema_row 14

private theorem source_schema_row15_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 15 b) z := by
  analytic_paid_source_schema_row 15

private theorem source_schema_row16_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 16 b) z := by
  analytic_paid_source_schema_row 16

private theorem source_schema_row17_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 17 b) z := by
  analytic_paid_source_schema_row 17

private theorem source_schema_row18_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 18 b) z := by
  analytic_paid_source_schema_row 18

private theorem source_schema_row19_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 19 b) z := by
  analytic_paid_source_schema_row 19

private theorem source_schema_row20_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 20 b) z := by
  analytic_paid_source_schema_row 20

private theorem source_schema_row21_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 21 b) z := by
  analytic_paid_source_schema_row 21

private theorem source_schema_row22_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 22 b) z := by
  analytic_paid_source_schema_row 22

private theorem source_schema_row23_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 23 b) z := by
  analytic_paid_source_schema_row 23

private theorem source_schema_row24_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 24 b) z := by
  analytic_paid_source_schema_row 24

private theorem source_schema_row25_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 25 b) z := by
  analytic_paid_source_schema_row 25

private theorem source_schema_row26_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 26 b) z := by
  analytic_paid_source_schema_row 26

private theorem source_schema_row27_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 27 b) z := by
  analytic_paid_source_schema_row 27

private theorem source_schema_row28_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 28 b) z := by
  analytic_paid_source_schema_row 28

private theorem source_schema_row29_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 29 b) z := by
  analytic_paid_source_schema_row 29

private theorem source_schema_row30_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 30 b) z := by
  analytic_paid_source_schema_row 30

private theorem source_schema_row31_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 31 b) z := by
  analytic_paid_source_schema_row 31

private theorem source_schema_row32_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 32 b) z := by
  analytic_paid_source_schema_row 32

private theorem source_schema_row33_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 33 b) z := by
  analytic_paid_source_schema_row 33

private theorem source_schema_row34_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 34 b) z := by
  analytic_paid_source_schema_row 34

private theorem source_schema_row35_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 35 b) z := by
  analytic_paid_source_schema_row 35

private theorem source_schema_row36_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 36 b) z := by
  analytic_paid_source_schema_row 36

private theorem source_schema_row37_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 37 b) z := by
  analytic_paid_source_schema_row 37

private theorem source_schema_row38_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 38 b) z := by
  analytic_paid_source_schema_row 38

private theorem source_schema_row39_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 39 b) z := by
  analytic_paid_source_schema_row 39

private theorem source_schema_row40_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 40 b) z := by
  analytic_paid_source_schema_row 40

private theorem source_schema_row41_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 41 b) z := by
  analytic_paid_source_schema_row 41

private theorem source_schema_row42_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 42 b) z := by
  analytic_paid_source_schema_row 42

private theorem source_schema_row43_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 43 b) z := by
  analytic_paid_source_schema_row 43

private theorem source_schema_row44_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 44 b) z := by
  analytic_paid_source_schema_row 44

private theorem source_schema_row45_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 45 b) z := by
  analytic_paid_source_schema_row 45

private theorem source_schema_row46_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 46 b) z := by
  analytic_paid_source_schema_row 46

private theorem source_schema_row47_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 47 b) z := by
  analytic_paid_source_schema_row 47

private theorem source_schema_row48_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 48 b) z := by
  analytic_paid_source_schema_row 48

private theorem source_schema_row49_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 49 b) z := by
  analytic_paid_source_schema_row 49

private theorem source_schema_row50_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 50 b) z := by
  analytic_paid_source_schema_row 50

private theorem source_schema_row51_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 51 b) z := by
  analytic_paid_source_schema_row 51

private theorem source_schema_row52_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 52 b) z := by
  analytic_paid_source_schema_row 52

private theorem source_schema_row53_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 53 b) z := by
  analytic_paid_source_schema_row 53

private theorem source_schema_row54_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 54 b) z := by
  analytic_paid_source_schema_row 54

private theorem source_schema_row55_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 55 b) z := by
  analytic_paid_source_schema_row 55

private theorem source_schema_row56_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 56 b) z := by
  analytic_paid_source_schema_row 56

private theorem source_schema_row57_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 57 b) z := by
  analytic_paid_source_schema_row 57

private theorem source_schema_row58_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 58 b) z := by
  analytic_paid_source_schema_row 58

private theorem source_schema_row59_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 59 b) z := by
  analytic_paid_source_schema_row 59

private theorem source_schema_row60_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 60 b) z := by
  analytic_paid_source_schema_row 60

private theorem source_schema_row61_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 61 b) z := by
  analytic_paid_source_schema_row 61

private theorem source_schema_row62_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 62 b) z := by
  analytic_paid_source_schema_row 62

private theorem source_schema_row63_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 63 b) z := by
  analytic_paid_source_schema_row 63

private theorem source_schema_row64_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 64 b) z := by
  analytic_paid_source_schema_row 64

private theorem source_schema_row65_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 65 b) z := by
  analytic_paid_source_schema_row 65

private theorem source_schema_row66_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 66 b) z := by
  analytic_paid_source_schema_row 66

private theorem source_schema_row67_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 67 b) z := by
  analytic_paid_source_schema_row 67

private theorem source_schema_row68_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 68 b) z := by
  analytic_paid_source_schema_row 68

private theorem source_schema_row69_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 69 b) z := by
  analytic_paid_source_schema_row 69

private theorem source_schema_row70_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 70 b) z := by
  analytic_paid_source_schema_row 70

private theorem source_schema_row71_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 71 b) z := by
  analytic_paid_source_schema_row 71

private theorem source_schema_row72_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 72 b) z := by
  analytic_paid_source_schema_row 72

private theorem source_schema_row73_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 73 b) z := by
  analytic_paid_source_schema_row 73

private theorem source_schema_row74_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 74 b) z := by
  analytic_paid_source_schema_row 74

private theorem source_schema_row75_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 75 b) z := by
  analytic_paid_source_schema_row 75

private theorem source_schema_row76_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 76 b) z := by
  analytic_paid_source_schema_row 76

private theorem source_schema_row77_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 77 b) z := by
  analytic_paid_source_schema_row 77

private theorem source_schema_row78_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) 78 b) z := by
  analytic_paid_source_schema_row 78

private theorem source_schema_analytic (z : ℂ) (v : ℂ → Fin 16 → ℂ)
    (_h : ∀ i, AnalyticAt ℂ (fun x => v x i) z) (a : Fin 79) (b : Fin 97) :
    AnalyticAt ℂ (fun x => ActualCanonical79Imaginary.sourceSchema (v x) a b) z := by
  fin_cases a
  · exact source_schema_row0_analytic z v _h b
  · exact source_schema_row1_analytic z v _h b
  · exact source_schema_row2_analytic z v _h b
  · exact source_schema_row3_analytic z v _h b
  · exact source_schema_row4_analytic z v _h b
  · exact source_schema_row5_analytic z v _h b
  · exact source_schema_row6_analytic z v _h b
  · exact source_schema_row7_analytic z v _h b
  · exact source_schema_row8_analytic z v _h b
  · exact source_schema_row9_analytic z v _h b
  · exact source_schema_row10_analytic z v _h b
  · exact source_schema_row11_analytic z v _h b
  · exact source_schema_row12_analytic z v _h b
  · exact source_schema_row13_analytic z v _h b
  · exact source_schema_row14_analytic z v _h b
  · exact source_schema_row15_analytic z v _h b
  · exact source_schema_row16_analytic z v _h b
  · exact source_schema_row17_analytic z v _h b
  · exact source_schema_row18_analytic z v _h b
  · exact source_schema_row19_analytic z v _h b
  · exact source_schema_row20_analytic z v _h b
  · exact source_schema_row21_analytic z v _h b
  · exact source_schema_row22_analytic z v _h b
  · exact source_schema_row23_analytic z v _h b
  · exact source_schema_row24_analytic z v _h b
  · exact source_schema_row25_analytic z v _h b
  · exact source_schema_row26_analytic z v _h b
  · exact source_schema_row27_analytic z v _h b
  · exact source_schema_row28_analytic z v _h b
  · exact source_schema_row29_analytic z v _h b
  · exact source_schema_row30_analytic z v _h b
  · exact source_schema_row31_analytic z v _h b
  · exact source_schema_row32_analytic z v _h b
  · exact source_schema_row33_analytic z v _h b
  · exact source_schema_row34_analytic z v _h b
  · exact source_schema_row35_analytic z v _h b
  · exact source_schema_row36_analytic z v _h b
  · exact source_schema_row37_analytic z v _h b
  · exact source_schema_row38_analytic z v _h b
  · exact source_schema_row39_analytic z v _h b
  · exact source_schema_row40_analytic z v _h b
  · exact source_schema_row41_analytic z v _h b
  · exact source_schema_row42_analytic z v _h b
  · exact source_schema_row43_analytic z v _h b
  · exact source_schema_row44_analytic z v _h b
  · exact source_schema_row45_analytic z v _h b
  · exact source_schema_row46_analytic z v _h b
  · exact source_schema_row47_analytic z v _h b
  · exact source_schema_row48_analytic z v _h b
  · exact source_schema_row49_analytic z v _h b
  · exact source_schema_row50_analytic z v _h b
  · exact source_schema_row51_analytic z v _h b
  · exact source_schema_row52_analytic z v _h b
  · exact source_schema_row53_analytic z v _h b
  · exact source_schema_row54_analytic z v _h b
  · exact source_schema_row55_analytic z v _h b
  · exact source_schema_row56_analytic z v _h b
  · exact source_schema_row57_analytic z v _h b
  · exact source_schema_row58_analytic z v _h b
  · exact source_schema_row59_analytic z v _h b
  · exact source_schema_row60_analytic z v _h b
  · exact source_schema_row61_analytic z v _h b
  · exact source_schema_row62_analytic z v _h b
  · exact source_schema_row63_analytic z v _h b
  · exact source_schema_row64_analytic z v _h b
  · exact source_schema_row65_analytic z v _h b
  · exact source_schema_row66_analytic z v _h b
  · exact source_schema_row67_analytic z v _h b
  · exact source_schema_row68_analytic z v _h b
  · exact source_schema_row69_analytic z v _h b
  · exact source_schema_row70_analytic z v _h b
  · exact source_schema_row71_analytic z v _h b
  · exact source_schema_row72_analytic z v _h b
  · exact source_schema_row73_analytic z v _h b
  · exact source_schema_row74_analytic z v _h b
  · exact source_schema_row75_analytic z v _h b
  · exact source_schema_row76_analytic z v _h b
  · exact source_schema_row77_analytic z v _h b
  · exact source_schema_row78_analytic z v _h b

theorem actual_canonical_axial_source_analytic (z : ℂ) (a : Fin 79) (b : Fin 97) :
    AnalyticAt ℂ (fun x => axialSourceMap x 0 a b) z := by
  change AnalyticAt ℂ
    (fun x => ActualCanonical79Imaginary.sourceSchema (sourceMapPolynomial x 0) a b) z
  exact source_schema_analytic z _ (actual_canonical_source_polynomial_analytic z) a b

theorem actual_canonical_world_source_analytic (negative : Bool) (z : ℂ)
    (a : Fin 79) (b : Fin 97) :
    AnalyticAt ℂ (fun x => worldSourceMap negative x 0 a b) z := by
  unfold worldSourceMap
  simp only [ActualFourBlockElastic.zero_signed_radius, Complex.ofReal_zero, neg_zero,
    ite_self]
  apply Finset.analyticAt_fun_sum
  intro c _
  cases negative
  · simpa only [Bool.false_eq_true, ↓reduceIte] using!
      (actual_canonical_axial_source_analytic z a c).mul analyticAt_const
  · simpa only [↓reduceIte] using!
      ((actual_canonical_axial_source_analytic (-z) a c).comp
        (analyticAt_id.neg)).mul analyticAt_const

end LowEnergy.ActualFourBlockRealTransfer
