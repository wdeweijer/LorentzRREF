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

lemma tv_mul_apply (A: ArrayMat R C K)(r i : Fin R) (c: K):
  Matrix.transvection r i c

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
    

theorem RREF_CorrectForm (A : Matrix (Fin R) (Fin C) K):
    IsRREF (A.RREF) := by
  unfold Matrix.RREF
  rw [m_mul_ar_mat]
  generalize (0 : Fin (R + 1)) = r -- r will grow in the pivot case
  induction' C with C' ih generalizing r; triv
  unfold IsRREF
  induction' hyp_equal : r using Fin.lastCases with r' <;> simp
  set opvt := findPivot (fun i => ArrayMat.get_elem (Matrix.toArrayMat A) i 0) r with h --ugly
  rcases opvt with why | pvt
  · right; constructor
    · unfold ArrayMat.RREFTransformation' IsZeroOnwards; simp
      intros i hr'i
      rw [if_neg (ne_of_lt (Fin.castSuccEmb_lt_last _))]
      rw [←hyp_equal] -- needed?
      -- rw [←h]; dsimp
      -- rw [mul_apply]
      -- show that applying RREF from r leaves an IsZeroOnwards r column invariant?
      sorry
    · -- use induction hyp ih
      sorry
  · left; constructor
    · unfold ArrayMat.RREFTransformation' IsUnitVectorAt; simp
      intros i
      rw [if_neg (ne_of_lt (Fin.castSuccEmb_lt_last _))] -- same as before, reuse
      rw [←hyp_equal] -- needed?
      -- rw [←h]; dsimp
      have : i = r' ∨ ¬ i = r' := by sorry
      cases this -- make terser
      · -- right; constructor; assumption
        sorry
      · -- left; constructor; assumption
        sorry
    · -- use induction
      sorry
  done


end RREF
