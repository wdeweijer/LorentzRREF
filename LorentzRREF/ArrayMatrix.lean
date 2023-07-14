import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic

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

@[ext] theorem ArrayMat.ext {m n : ℕ} {α : Type} (A B: ArrayMat m n α) :
  (∀ (i: Fin m)(j: Fin n), A.get_elem i j = B.get_elem i j) → A = B := by
  intros h
  apply Subtype.ext
  apply Array.ext
  simp only [size]
  intros k hka hkb
  let k' : Fin (m*n) := ⟨k, by simpa only [size] using hka⟩
  unfold get_elem at h
  simp only [Array.get_eq_getElem, Array.getElem_ofFn] at h
  convert h k'.divNat k'.modNat 
  <;> simp only [Fin.coe_divNat, Fin.coe_modNat, mul_comm, Nat.div_add_mod]


def Matrix.toArrayMat {m n: ℕ}{α: Type} (A: Matrix (Fin m) (Fin n) α): ArrayMat m n α := 
  ⟨Array.ofFn (fun k: (Fin (m*n)) => A k.divNat k.modNat), Array.size_ofFn _ ⟩

@[simp]
theorem ar_get_el_corr {m n: ℕ}{α: Type} (A : Matrix (Fin m) (Fin n) α) (i : Fin m) (j : Fin n ):
    ArrayMat.get_elem (Matrix.toArrayMat A) i j = A i j := by
    cases' m with m; fin_cases i
    cases' n with n; fin_cases j

    unfold Matrix.toArrayMat ArrayMat.get_elem
    simp only [Array.get_eq_getElem, Array.getElem_ofFn]
    congr <;> ext <;> dsimp
    · rw [Nat.add_div, if_neg]
      simp only [add_zero]
      rw [Nat.mul_div_cancel, Nat.div_eq_of_lt, add_zero]
      exact Fin.prop j
      simp only [Nat.succ_pos']
      simp only [Nat.mul_mod_left, zero_add, not_le]
      apply Nat.mod_lt
      simp only [gt_iff_lt, Nat.succ_pos']
      simp only [Nat.succ_pos']
    · rw [Nat.add_mod]
      simp only [Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_succ_eq_iff_lt, Fin.is_lt]
        

def ArrayMat.dropFirstColumns {m n: ℕ} (z: ℕ) (A: ArrayMat (m) (n + z) α) : 
  (ArrayMat m n α) :=
  ⟨Array.ofFn (fun k: (Fin (m*n)) => A.get_elem k.divNat (Fin.addNat z k.modNat)), 
  Array.size_ofFn _ ⟩

open Matrix BigOperators

variable {α: Type}[Semiring α]

def ArrayMat.toMatrix {m n: ℕ} (A: ArrayMat m n α) : Matrix (Fin m) (Fin n) α := 
  (Matrix.of fun i j => A.get_elem i j)

-- These should move to ArrayMatrix.lean
@[simp]
theorem tomat_toarray (A : Matrix (Fin m) (Fin n) α) : A.toArrayMat.toMatrix = A := by
  ext i j
  apply ar_get_el_corr

#check tomat_toarray

@[simp]
lemma toarray_tomat {m n: ℕ} (A : ArrayMat m n α) : A.toMatrix.toArrayMat = A := by
  ext
  simp only [ar_get_el_corr, ArrayMat.toMatrix, of_apply]

def ArrayMat.mul {m n p: ℕ} (A: ArrayMat m n α) (B: ArrayMat n p α) : 
  (ArrayMat m p α) := (A.toMatrix ⬝ B.toMatrix).toArrayMat

@[simp]
theorem am_mul_corr (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin n) (Fin p) α) :
    (A.toArrayMat.mul B.toArrayMat).toMatrix = A.mul B := by
  unfold ArrayMat.mul
  simp only [tomat_toarray]

theorem m_mul_ar_mat (A : ArrayMat m n α) (B : Matrix (Fin n) (Fin p) α) :
    (A.mul B.toArrayMat).toMatrix = A.toMatrix.mul B := by
  unfold ArrayMat.mul
  simp only [tomat_toarray]

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
variable (m n)
#check Fin n → Fin m → ℕ

#check (Fin n × Fin m) → ℕ

#check (Fin n → Fin m) → ℕ


instance : GetElem (ArrayMat m n α) (Fin m × Fin n) α (fun _ _ => True) :=
⟨fun m i _ => Function.uncurry m.get_elem i⟩

instance [Repr α] : Repr (ArrayMat m n α) where
  reprPrec f _p :=
    (Std.Format.bracket "@[" · "]") <|
      (Std.Format.joinSep · (";\n")) <|
        (List.finRange m).map fun i =>
          Std.Format.fill <|  -- wrap line in a single place rather than all at once
            (Std.Format.joinSep · ("," ++ Std.Format.line)) <|
            (List.finRange n).map fun j => _root_.repr f[(i,j)]


            
#eval repr (matrixRowDilation step1_c 1)
