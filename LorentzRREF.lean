import Mathlib.Data.Matrix.Basic
import Mathlib
/-!
# RREF of Matrix

This file defines a function which puts a matrix in row reduced
echelon form

## Tags
matrix, rref, reduce

A matrix is in RREF iff:
1) Matrix is in REF.
2) The leading entry in each row is 1
3) Each coloumn containg containing leading 1 has 0s everyhwere else

REF:
1) look at first coloumn; find first non-zero term. Perform a row swap.
2) eliminate down that coloumn to all 0s.
3) repeat at next coloumn
-/

/-- Return the first `pvt >= r` with `A pvt ≠ 0`, or `none` if everything below `r` is `0`  -/
def findPivot {R : ℕ} {K : Type _} [Field K] [DecidableEq K]
    (A : Fin R → K) (r : Fin (R + 1)) :
    Option (Fin R) :=
  Fin.find (fun i ↦ i ≥ r ∧ A i ≠ 0)

def Matrix.RREFTransformation {R C : ℕ} {K : Type _} [Field K] [DecidableEq K]
    (A : Matrix (Fin R) (Fin C) K) (r : Fin (R + 1) := 0) :
    Matrix (Fin R) (Fin R) K :=
  match C with
  | 0 => 1
  | C'+1 => match findPivot (fun i => A i 0) r with
    | .none => Matrix.RREFTransformation (fun i k => A i (Fin.succ k)) r
    | .some pvt =>
     let (A', T₁) := matrixRowSwap A pvt r
     let (A'', T₂) := matrixRowDilation A' r
     let (A''', T₃) := matrixRowTransvections A' r
    Matrix.RREFTransformation (fun i k => A i (Fin.succ k)) (r + 1) * T₃ * T₂ * T₁

#eval findPivot (![0, 1, 2, 0, 3, 0] : Fin _ → ℚ)

def
#eval Matrix.RREFTransformation (!![;] : Matrix (Fin 1) (Fin 0) ℚ)
