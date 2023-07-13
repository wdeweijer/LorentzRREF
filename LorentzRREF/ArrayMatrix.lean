import Mathlib

def ArrayVec (n : ℕ) (α : Type) := { x: Array α // x.size = n}

def ArrayMat (m n : ℕ)(α : Type) := ArrayVec (m*n) α


@[simp]
lemma ArrayMat.size {m n : ℕ} {α : Type} (A: ArrayMat m n α) : 
  A.1.size = m*n := A.2

/-
i : row index, j: column index
m: number of rows, n : number of columns
-/

def ArrayMat.get_elem {m n : ℕ} {α : Type} (A: ArrayMat m n α) (i: Fin m) (j: Fin n) := 
  A.1.get ⟨i*n + j, by 
    cases' m with m; fin_cases i
    cases' n with n; fin_cases j
    simp only [ArrayMat.size]
    dsimp only [Nat.succ_eq_add_one]
    refine (add_le_add ((mul_le_mul_right ?_).mpr i.is_le) j.is_le).trans_lt ?_
    simp only [add_pos_iff, or_true]
    linarith ⟩ -- Row Major Order

def Matrix.toArrayMat {m n: ℕ}{α: Type} (A: Matrix (Fin m) (Fin n) α): ArrayMat m n α := 
  ⟨Array.ofFn (fun k: (Fin (m*n)) => A k.divNat k.modNat), Array.size_ofFn _ ⟩




def ArrayMat.dropFirstColumns {m n: ℕ} (z: ℕ) (A: ArrayMat (m) (n + z) α) : 
  (ArrayMat m n α) :=
  ⟨Array.ofFn (fun k: (Fin (m*n)) => A.get_elem k.divNat (Fin.addNat z k.modNat)), 
  Array.size_ofFn _ ⟩

open Matrix BigOperators

variable {α: Type}[Semiring α]

def ArrayMat.toMatrix {m n: ℕ} (A: ArrayMat m n α) : Matrix (Fin m) (Fin n) α := 
  (Matrix.of fun i j => A.get_elem i j)

def ArrayMat.mul {m n p: ℕ} (A: ArrayMat m n α) (B: ArrayMat n p α) : 
  (ArrayMat m p α) := (A.toMatrix ⬝ B.toMatrix).toArrayMat

instance ArrayMat.instOne {m: ℕ} : One (ArrayMat m m α) where
  one := (1: Matrix (Fin m) (Fin m) α).toArrayMat
-- Array.ofFn (fun k: (Fin (m*p)) => ite (k.divNat = k.modNat) 1 0

instance ArrayMat.instMul {m: ℕ} : Mul (ArrayMat m m α) where
  mul := ArrayMat.mul

def ArrayMat.mul'_elem {m n p: ℕ} (A: ArrayMat m n α) (B: ArrayMat n p α) 
  (k: Fin (m*p)): α := by
  let i := k.divNat 
  let j := k.modNat
  exact ∑ k, A.get_elem i k * B.get_elem k j

def ArrayMat.mul' {m n p: ℕ} (A: ArrayMat m n α) (B: ArrayMat n p α) : 
  (ArrayMat m p α) :=
  ⟨ Array.ofFn (fun k: (Fin (m*p)) => ArrayMat.mul'_elem A B k), Array.size_ofFn _ ⟩

variable {K: Type}[Field K]
def swapRows {M N: ℕ} (Q: ArrayMat M N K) (r₁ r₂: (Fin M)): ArrayMat M N K := by
  let f := (Equiv.swap r₁ r₂)
  exact (Matrix.of (fun i j => Q.get_elem (f i) j)).toArrayMat

def matrixRowSwap (A : ArrayMat R C K) (pvt r : Fin R) :
  ArrayMat R C K × ArrayMat R R K :=
  ⟨swapRows A pvt r, swapRows 1 pvt r⟩

def matrixRowDilation (A : ArrayMat R (C + 1) K) (r : Fin R) :
  (ArrayMat R (C + 1) K) ×  (ArrayMat R R K) := by
  let a := A.get_elem r 0
  let v := fun (i: Fin R) => ite (i = r) ((1:K) / a) (1:K)
  let D := (Matrix.diagonal v).toArrayMat
  let A' := D.mul A
  exact ⟨ A' , D⟩

def matrixRowTransvections (A : ArrayMat R (C + 1) K) (r : Fin R) :
  (ArrayMat R (C + 1) K) × ArrayMat R R K := by
  -- Note that A r 0 must be equal to 1
  let T := ((List.finRange R).map fun i => 
    (ite (i = r) 1 (Matrix.transvection i r (-A.get_elem i 0)).toArrayMat )).prod
  exact ⟨T.mul A, T⟩

def exMat := 
!![(1:ℚ), 2, 3; 
  4, 5, 7; 
  -2, 0, 3;]
#eval swapRows exMat.toArrayMat 0 2
#eval matrixRowSwap exMat.toArrayMat 0 2
#eval matrixRowDilation exMat.toArrayMat 1
#eval matrixRowTransvections exMat.toArrayMat 0

def step1 := !![(1:ℚ), 2, 3; 0, -3, -5; 0, 4, 9] 
def t1 := !![1, 0, 0, -4, 1, 0, 2, 0, 1]

def step1_c := ArrayMat.dropFirstColumns 1 step1.toArrayMat

#eval matrixRowDilation step1_c 1
