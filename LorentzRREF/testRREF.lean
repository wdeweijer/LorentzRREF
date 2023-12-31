import LorentzRREF.RREF
import LorentzRREF.Correctness

def wierdMat1 := (!![(1:ℚ), 3, 1, 9; 1, 1, -1, 1; 3, 11, 5, 35])

def wikiRREF_example := 
!![ (1:ℚ), 0, -2, -3;
    0, 1, 1, 4;
    0, 0, 0, 0]

def wierdMat2 := (1: Matrix (Fin 3) (Fin 3) ℚ)
def wierdMat3 := (0: Matrix (Fin 3) (Fin 4) ℚ)
def wierdMat4 := (!![(0:ℚ), 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0;])

-- set_option trace.compiler true
#eval wierdMat1.toArrayMat      -- Original Matrix
#eval wierdMat1.RREFTransformation.toArrayMat       -- Transformation Matrix
#eval wierdMat1.RREF        -- Reduced Row Echelon Form
#eval IsRREF (wierdMat1.RREF)
#eval wierdMat1.toArrayMat.RREFTransformation'

def bigMat1 := fun (i : Fin 12) (j : Fin 12) => (1 : ℚ) + 3*i + 2*j + 5*i*j
#eval Matrix.toArrayMat bigMat1
-- #eval Matrix.RREF bigMat1
