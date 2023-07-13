import Mathlib
import LorentzRREF.ArrayMatrix

variable {K: Type}[Field K][DecidableEq K]

/-- Return the first `pvt >= r` with `A pvt ≠ 0`, or `none` if everything below `r` is `0`  -/
def findPivot (A : Fin R → K) (r : Fin (R + 1)) :
    Option (Fin R) :=
  Fin.find (fun i ↦ i ≥ r ∧ A i ≠ 0)

def Matrix.RREFTransformation' {R C : ℕ}[ToString K] (A : ArrayMat R C K)
    (r : Fin (R + 1) := 0) :
    ArrayMat R R K :=
  match C with
  | 0 => 1
  | C'+ 1 => dbgTrace ("Z: " ++ toString C' ++ toString A.1) fun _ => if h : r = Fin.last R
    then 1 -- Done with all the rows, nothing to transform. 
    else ( let r : Fin R := ⟨r.val, by exact Fin.val_lt_last h⟩
      match findPivot (fun i => A.get_elem i 0) r with
      | .none => Matrix.RREFTransformation' (ArrayMat.dropFirstColumns 1 A) r
      | .some pvt => dbgTrace ("C': " ++ toString C' ++ " / PVT: " ++ toString pvt) fun _ =>
       let (A', T₁) := matrixRowSwap A pvt r
       let (A'', T₂) := matrixRowDilation A' r
       let (A''', T₃) := matrixRowTransvections A'' r
      (Matrix.RREFTransformation' (ArrayMat.dropFirstColumns 1 A''') (r + 1)) * T₃ * T₂ * T₁)