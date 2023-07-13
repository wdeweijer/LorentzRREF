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

section RREF

variable {K : Type _}
variable [Field K] [DecidableEq K]

-- Shouldn't need Decidable
def IsUnitVectorAt (c : Fin R → K) (r : Fin R) : Prop :=
  ∀ (i : Fin R), i ≠ r ∧ c i = 0 ∨
                 i = r ∧ c i = 1

def IsZeroOnwards (c : Fin R → K) (r : Fin (R + 1)) : Prop :=
  ∀ i : Fin R, i ≥ r → c i = 0

instance (c : Fin R → K) (r : Fin R) : Decidable (IsUnitVectorAt c r) := by
  unfold IsUnitVectorAt; infer_instance

instance (c : Fin R → K) (r : Fin (R + 1)) : Decidable (IsZeroOnwards c r) := by
  unfold IsZeroOnwards; infer_instance

theorem notBoth (c : Fin R → K) (r : Fin R) : ¬ (IsUnitVectorAt c r ∧ IsZeroOnwards c r) := by
  rintro ⟨h1, h0⟩
  have h0 : c r = 0
  · simpa using h0 r
  have h1 : c r = 1
  · simpa using h1 r
  exact zero_ne_one (h0.symm.trans h1)

def IsRREF (A : Matrix (Fin R) (Fin C) K) (r : Fin (R + 1) := 0) : Prop :=
  match C with
  | 0 => True
  | C + 1 => Fin.lastCases
    True
    (fun r =>
      IsUnitVectorAt (fun i => A i 0) r ∧ IsRREF (fun i k => A i (Fin.succ k)) (Fin.succ r) ∨
      IsZeroOnwards  (fun i => A i 0) r ∧ IsRREF (fun i k => A i (Fin.succ k)) r)
    r

--                        Why? vvvvvv
theorem empty_IsRREF : IsRREF (K := K) !![] := by unfold IsRREF ; trivial

/-- Return the first `pvt >= r` with `A pvt ≠ 0`, or `none` if everything below `r` is `0`  -/
def findPivot (A : Fin R → K) (r : Fin (R + 1)) :
    Option (Fin R) :=
  Fin.find (fun i ↦ i ≥ r ∧ A i ≠ 0)

def swapRows {M N: ℕ} (Q: Matrix (Fin M) (Fin N) K) (r₁ r₂: (Fin M)): 
  Matrix (Fin M) (Fin N) K := by
  let f := (Equiv.swap r₁ r₂)
  exact fun i j => Q (f i) j

-- theorem IsZeroOnwards_swapRows_inv (c : Fin R → K) : IsZeroOnwards c r → IsZeroOnwards (swapRows)

def matrixRowSwap (A : Matrix (Fin R) (Fin C) K) (pvt r : Fin R) :
  Matrix (Fin R) (Fin C) K × Matrix (Fin R) (Fin R) K :=
  ⟨swapRows A pvt r, swapRows 1 pvt r⟩


def matrixRowDilation (A : Matrix (Fin R) (Fin (C + 1)) K) (r : Fin R) :
  Matrix (Fin R) (Fin (C + 1)) K × Matrix (Fin R) (Fin R) K := by
  let a := A r 0
  let v := fun (i: Fin R) => ite (i = r) (1/a) 1
  let A' := (Matrix.diagonal v).mul A
  exact ⟨ A' , (Matrix.diagonal v)⟩
  
open BigOperators Matrix

def matrixRowTransvections (A : Matrix (Fin R) (Fin (C + 1)) K) (r : Fin R) :
  Matrix (Fin R) (Fin (C + 1)) K × Matrix (Fin R) (Fin R) K := by
  -- Note that A r 0 must be equal to 1
  let T := ((List.finRange R).map fun i => 
    (ite (i = r) 1 (Matrix.transvection i r (-A i 0)))).prod
  exact ⟨T ⬝ A, T⟩

def Matrix.RREFTransformation {R C : ℕ} (A : Matrix (Fin R) (Fin C) K)
    (r : Fin (R + 1) := 0) :
    Matrix (Fin R) (Fin R) K :=
  match C with
  | 0 => 1
  | C'+1 => Fin.lastCases
    1 -- Done with all the rows, nothing to transform.
    (fun r => match findPivot (fun i => A i 0) r with
      | .none => Matrix.RREFTransformation (fun i k => A i (Fin.succ k)) r
      | .some pvt =>
       let (A', T₁) := matrixRowSwap A pvt r
       let (A'', T₂) := matrixRowDilation A' r
       let (A''', T₃) := matrixRowTransvections A'' r
      Matrix.RREFTransformation (fun i k => A''' i (Fin.succ k)) (r + 1) * T₃ * T₂ * T₁)
    r

theorem RREF_CorrectForm (A : Matrix (Fin R) (Fin C) K) (r : Fin (R + 1)):
    IsRREF ((RREFTransformation A r).mul A) r := by
  
  induction' C with C' ih generalizing r; triv
  unfold IsRREF
  induction' hyp_equal : r using Fin.lastCases with r' <;> simp
  set opvt := findPivot (fun i => A i 0) r with h
  rcases opvt with why | pvt
  · right; constructor
    · unfold RREFTransformation IsZeroOnwards
      simp
      intros i hr'i
      rw [←hyp_equal, ←h]
      dsimp
      rw [mul_apply]
      sorry
    · skip
      -- apply ih
      sorry
  · sorry

end RREF
