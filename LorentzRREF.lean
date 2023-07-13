import Mathlib.Data.Matrix.Basic
import Mathlib

import LorentzRREF.ArrayMatrix
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
def isUnitVectorAt (c : Fin R → K) (r : Fin R) : Prop :=
  ∀ (i : Fin R), i ≠ r ∧ c i = 0 ∨
                 i = r ∧ c i = 1

def isZeroOnwards (c : Fin R → K) (r : Fin (R + 1)) : Prop :=
  ∀ i : Fin R, i ≥ r → c i = 0

theorem notBoth (c : Fin R → K) (r : Fin R) : ¬ (isUnitVectorAt c r ∧ isZeroOnwards c r) := by
  rintro ⟨h1, h0⟩
  specialize h1 r
  specialize h0 r
  suffices ding : (1 = (0 : K))
  admit
  rcases h1 with ⟨bang, _⟩ | ⟨_, h1⟩
  admit
  rw [← h0 ?_, ← h1]
  simp


