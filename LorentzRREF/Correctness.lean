import LorentzRREF.RREF

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

#check Matrix.RREF
variable {K : Type _}
variable [Field K] [DecidableEq K]

def IsUnitVectorAt (c : Fin R → K) (r : Fin R) : Prop :=
  -- ∀ (i : Fin R), i ≠ r ∧ c i = 0 ∨
  --                i = r ∧ c i = 1
  ∀ (i : Fin R), if i = r then c i = 1 else c i = 0

def IsZeroOnwards (c : Fin R → K) (r : Fin (R + 1)) : Prop :=
  ∀ i : Fin R, i ≥ r → c i = 0

instance (c : Fin R → K) (r : Fin R) : Decidable (IsUnitVectorAt c r) := by
  unfold IsUnitVectorAt; infer_instance

instance (c : Fin R → K) (r : Fin (R + 1)) : Decidable (IsZeroOnwards c r) := by
  unfold IsZeroOnwards; infer_instance

theorem IsZeroOnwards_monotone (c : Fin R → K) (r : Fin R) :
    IsZeroOnwards c r → IsZeroOnwards c r.succ := by
  simp only [IsZeroOnwards, Fin.coe_eq_castSuccEmb]
  intros h i hgt
  apply h
  exact le_of_lt hgt

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
  | C + 1 => if h : r = Fin.last R
    then True
    else (let r : Fin R := ⟨r.val, by exact Fin.val_lt_last h⟩
      IsUnitVectorAt (fun i => A i 0) r ∧ IsRREF (fun i k => A i (Fin.succ k)) (Fin.succ r) ∨
      IsZeroOnwards  (fun i => A i 0) r ∧ IsRREF (fun i k => A i (Fin.succ k)) r)

instance (A : Matrix (Fin R) (Fin C) K) (r : Fin (R + 1)) : Decidable (IsRREF A r) := by
  induction' C generalizing r <;> dsimp [IsRREF]
  infer_instance
  by_cases r = Fin.last R <;> infer_instance  

--                        Why? vvvvvv
theorem empty_IsRREF : IsRREF (K := K) !![] := by unfold IsRREF ; trivial

def isRowPreserve {R: ℕ}(B: ArrayMat R R K) (r: Fin R) := 
  ∀ {C: ℕ}(A: ArrayMat R C K) (j: Fin C), (B.mul A).get_elem r j = A.get_elem r j

open BigOperators
theorem mul_left_apply_of_ne' {m n K: Type}[Ring K]
  [Fintype m][Fintype n][DecidableEq m][DecidableEq n](c: K)
  (i: m)(j : m)(a : m)(b: n) (h : a ≠ i) (M : Matrix m n K) :
    ((Matrix.stdBasisMatrix i j c).mul M) a b = 0 := by
  rw [Matrix.mul_apply]
  unfold Matrix.stdBasisMatrix
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_eq_zero]
  simp [h.symm]

lemma one_tv_invariant (r i : Fin R)(c : K) (hir : i ≠ r):
    isRowPreserve (Matrix.transvection i r c).toArrayMat r := by
  intros C A j 
  unfold ArrayMat.mul
  simp only [tomat_toarray, ar_get_el_corr]
  unfold Matrix.transvection
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  rw [mul_left_apply_of_ne', add_zero]
  unfold ArrayMat.toMatrix
  simp only [Matrix.of_apply]
  exact hir.symm

lemma tv_mul_apply (A: ArrayMat R C K)(r i : Fin R) (c: K)(j: Fin C):
  ((Matrix.transvection i r c).toArrayMat.mul A).get_elem i j = 
  (A.get_elem i j) + c * (A.get_elem r j) := by
  unfold ArrayMat.mul
  simp only [tomat_toarray, ar_get_el_corr]
  unfold Matrix.transvection
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
  unfold Matrix.stdBasisMatrix
  simp only [true_and, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr

lemma isRowPreserve_one {R: ℕ}(r: Fin R) : isRowPreserve (1: ArrayMat R R K) r := sorry 

lemma isRowPreserve_mul {R: ℕ}(r: Fin R) (A B: ArrayMat R R K) : 
  isRowPreserve A r → isRowPreserve B r → isRowPreserve (A.mul B) r := sorry

theorem matrixRowTransvections_ind_nonmodify 
  (Tv: List (ArrayMat R R K)) (pvt: Fin R)
  (hL: ∀ tv ∈ Tv, isRowPreserve tv pvt): 
  isRowPreserve Tv.prod pvt
  := by 
  induction' Tv with H T ih
  simp only [List.prod_nil, isRowPreserve_one]
  simp only [List.prod_cons]
  apply isRowPreserve_mul
  apply hL
  simp only [List.find?, List.mem_cons, true_or]
  apply ih
  intros x hx
  apply hL
  simp only [List.find?, List.mem_cons]
  right; exact hx

lemma ArrayMat.mul_mul_assoc_left {R C: ℕ}(A B: ArrayMat R R K)(M: ArrayMat R C K):
  (A*B).mul M = A.mul (B.mul M) := sorry

lemma Matrix.doColumnRREFTransform_Correct {R C : ℕ} (A : ArrayMat R (C + 1) K) (r pvt: Fin R) 
  (hnz: A.get_elem pvt 0 ≠ 0):
    -- let TA := Matrix.doColumnRREFTransform A r pvt
    IsUnitVectorAt (fun i : (Fin R) => (Matrix.doColumnRREFTransform A r pvt).1.get_elem i 0) r := by
  intros i
  -- unfold IsUnitVectorAt
  have s1 : (matrixRowSwap A pvt r).1.get_elem r 0 ≠ 0 := by
    sorry
  have s2 : (matrixRowDilation (matrixRowSwap A pvt r).1 r).1.get_elem r 0 = 1 := by
    sorry
  
  split_ifs with h
  · subst h
    unfold doColumnRREFTransform
    dsimp
    unfold matrixRowTransvections
    dsimp
    rw [matrixRowTransvections_ind_nonmodify, s2]
    simp_rw [List.mem_map ]
    rintro tv ⟨ a, ha₁, ha₂⟩
    split_ifs at ha₂ with h
    rw [← ha₂]
    apply isRowPreserve_one
    rw [← ha₂]
    apply one_tv_invariant
    exact h
  · unfold doColumnRREFTransform matrixRowTransvections
    dsimp
    have : i ∈ List.finRange R := by exact List.mem_finRange i
    rw [List.mem_iff_append ] at this
    rcases this with ⟨s, t, hst⟩
    rw [hst]
    simp only [List.map_append, List.map, h, ite_false, 
      List.prod_append, List.prod_cons]
    rw [ArrayMat.mul_mul_assoc_left]
    rw [matrixRowTransvections_ind_nonmodify]
    rw [ArrayMat.mul_mul_assoc_left]
    rw [tv_mul_apply]
    rw [neg_mul,← sub_eq_add_neg]
    rw [matrixRowTransvections_ind_nonmodify]
    rw [matrixRowTransvections_ind_nonmodify]
    rw [s2, mul_one, sub_self]
    intros tv htv
    intros C A j
    
    sorry
    sorry
    sorry

theorem IsRREF_monotone (A : Matrix (Fin R) (Fin C) K) (r : Fin R) :
    IsRREF A ↑(Fin.castSuccEmb r') → IsRREF A r.succ := by
  sorry

theorem RREF_CorrectForm (A : Matrix (Fin R) (Fin C) K):
    IsRREF (A.RREF) := by
  unfold Matrix.RREF
  rw [m_mul_ar_mat]
  generalize (0 : Fin (R + 1)) = r -- r will grow in the pivot case
  induction' C with C' ih generalizing r; triv
  dsimp [IsRREF]
  induction' r using Fin.lastCases with r' <;> simp
  have hr_notLast : (↑(Fin.castSuccEmb r') ≠ Fin.last R) :=
    ne_of_lt (Fin.castSuccEmb_lt_last _)
  rw [dif_neg hr_notLast]
  have cutmul : -- Yikes!
    (fun i k =>
      Matrix.mul
        (ArrayMat.toMatrix (ArrayMat.RREFTransformation' (Matrix.toArrayMat A) ↑(Fin.castSuccEmb r')))
        A
          i (Fin.succ k))
    = Matrix.mul
      (ArrayMat.toMatrix (ArrayMat.RREFTransformation' (Matrix.toArrayMat (fun i k => A i k.succ)) ↑(Fin.castSuccEmb r')))
      (fun i k => A i (Fin.succ k)) := by sorry
  set opvt := findPivot (fun i => A i 0) (↑(Fin.castSuccEmb r')) with h
  rcases opvt with why | pvt --ugly
  · right; constructor
    · simp [ArrayMat.RREFTransformation', IsZeroOnwards]
      intros i hr'i
      rw [if_neg hr_notLast]
      rw [←h]; dsimp
      sorry -- show that applying RREF from r leaves an IsZeroOnwards r column invariant?
    · rw [cutmul]
      apply ih
  · left; constructor
    · simp [ArrayMat.RREFTransformation', IsUnitVectorAt]
      intros i
      rw [if_neg hr_notLast]
      rw [←h]; dsimp
      split_ifs with hir'
      · sorry
      · sorry
    · rw [cutmul]
      generalize (fun i k => A i (Fin.succ k)) = A'
      apply IsRREF_monotone
      apply ih
  done


end RREF
