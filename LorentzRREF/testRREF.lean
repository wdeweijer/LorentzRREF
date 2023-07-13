import LorentzRREF.RREF

def wierdMat1 := (!![(1:ℚ), 3, 1, 9; 1, 1, -1, 1; 3, 11, 5, 37000000000000000000]).toArrayMat
def wierdMat2 := (1: Matrix (Fin 3) (Fin 3) ℚ).toArrayMat
def wierdMat3 := (0: Matrix (Fin 3) (Fin 4) ℚ).toArrayMat
def wierdMat4 := (!![(0:ℚ), 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0;]).toArrayMat

set_option trace.compiler true
#eval wierdMat1
#eval Matrix.RREFTransformation' wierdMat1
#eval (Matrix.RREFTransformation' wierdMat1).mul wierdMat1
#eval (Matrix.RREFTransformation' wierdMat4).mul wierdMat4