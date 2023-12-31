import LorentzRREF.ArrayMatrix

variable {K: Type}[Field K][DecidableEq K]

/-- Return the first `pvt >= r` with `A pvt ≠ 0`, or `none` if everything below `r` is `0`  -/
def findPivot (A : Fin R → K) (r : Fin (R + 1)) :
    Option (Fin R) :=
  Fin.find (fun i ↦ i ≥ r ∧ A i ≠ 0)

def Matrix.doColumnRREFTransform {R C : ℕ}(A : ArrayMat R (C + 1) K) (r pvt: Fin R):
    ArrayMat R (C + 1) K × ArrayMat R R K :=
  let (A', T₁) := matrixRowSwap A pvt r
  let (A'', T₂) := matrixRowDilation A' r
  let (A''', T₃) := matrixRowTransvections A'' r
  ⟨A''', T₃  * T₂ *  T₁⟩

def ArrayMat.RREFTransformation' {R C : ℕ}(A : ArrayMat R C K)
    (r : Fin (R + 1) := 0) :
    ArrayMat R R K :=
  match C with
  | 0 => 1
  | C'+ 1 => if h : r = Fin.last R
    then 1 -- Done with all the rows, nothing to transform. 
    else ( let r : Fin R := ⟨r.val, by exact Fin.val_lt_last h⟩
      match findPivot (fun i => A.get_elem i 0) r with
      | .none => ArrayMat.RREFTransformation' (ArrayMat.dropFirstColumns 1 A) r
      | .some pvt =>
       let ⟨A''', Tx⟩ := Matrix.doColumnRREFTransform A r pvt
      (ArrayMat.RREFTransformation' (ArrayMat.dropFirstColumns 1 A''') (r + 1)) * Tx)

def Matrix.RREFTransformation {R C : ℕ} (A: Matrix (Fin R) (Fin C) K) :
  Matrix (Fin R) (Fin R) K := (ArrayMat.RREFTransformation' A.toArrayMat).toMatrix

def Matrix.RREF {R C : ℕ} (A: Matrix (Fin R) (Fin C) K) :
    Matrix (Fin R) (Fin C) K := 
  (A.toArrayMat.RREFTransformation'.mul A.toArrayMat).toMatrix
