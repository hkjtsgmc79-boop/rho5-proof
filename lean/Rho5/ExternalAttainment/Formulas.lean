import Rho5.Shared.Pivot
import Rho5.Shared.Conventions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic

noncomputable section
namespace Rho5.ExternalAttainment

/-! Literal reconstruction first, then compact expressions for exactly the same
matrix and its successive leading Schur tails.  The equalities between these
forms are proved in SchurIdentities; no CP property is built into a definition. -/
def denomT (x y z : ℝ) : ℝ :=
  (((((((2:ℝ) * (x ^ 2)) * z) + (x * (z ^ 2))) + (x * z)) - ((2:ℝ) * x)) - (2:ℝ))

def denomR (x y z : ℝ) : ℝ :=
  ((denomT x y z) + ((z * ((((2:ℝ) * x) + z) + (1:ℝ))) * (y + (1:ℝ))))

def corePivot (x y z : ℝ) : ℝ :=
  (((2:ℝ) - (x * z)) - (z ^ 2))

def pivotTwo (x y z : ℝ) : ℝ :=
  ((1:ℝ) + z)

def headEntry (x y z : ℝ) : ℝ :=
  ((((((x * z) + (z ^ 2)) + z) - (1:ℝ)) * (denomT x y z)) / (denomR x y z))

def ratioRD (x y z : ℝ) : ℝ :=
  ((denomR x y z) / (denomT x y z))

def topRight (x y z : ℝ) : ℝ :=
  ((z * (x + z)) / (x + (1:ℝ)))

def halfHeight (x y z : ℝ) : ℝ :=
  ((2:ℝ) + (((z * (z - (1:ℝ))) * (y + (1:ℝ))) / (denomT x y z)))

def coreArm (x y z : ℝ) : ℝ :=
  ((-z) * (x + (1:ℝ)))

def coreBottom (x y z : ℝ) : ℝ :=
  (((1:ℝ) + ((z ^ 2) / y)) + (headEntry x y z))

def coreCorner (x y z : ℝ) : ℝ :=
  ((2:ℝ) - ((z * ((x + z) ^ 2)) / (x + (1:ℝ))))

def reducedT (x y z : ℝ) : ℝ :=
  (y + ((pivotTwo x y z) * (ratioRD x y z)))

def reducedB23 (x y z : ℝ) : ℝ :=
  ((headEntry x y z) - ((x * z) / y))

def reducedB33 (x y z : ℝ) : ℝ :=
  (((corePivot x y z) + (headEntry x y z)) + (z / y))

def yMinusT (x y z : ℝ) : ℝ :=
  (y - (reducedT x y z))

def xPlusOne (x y z : ℝ) : ℝ :=
  (x + (1:ℝ))

/-- The unabridged numerator prescribed by the input reconstruction. -/
def numerT (x y z : ℝ) : ℝ :=
  2*x^2*y*z + 2*x^2*z^2 + 2*x^2*z + 3*x*y*z^2 + 3*x*y*z - 2*x*y
  + x*z^3 + 4*x*z^2 + x*z - 2*x + y*z^3 + 2*y*z^2 + y*z - 2*y
  + z^3 + 2*z^2 - z - 2

def paperT (x y z : ℝ) : ℝ := numerT x y z / denomT x y z

def paperB23 (x y z : ℝ) : ℝ :=
  -(-paperT x y z*x*z + x*y*z^2 + 2*x*y*z + y*z^3 + 2*y*z^2 - y)
    / (y*(y-paperT x y z))

def paperB33 (x y z : ℝ) : ℝ :=
  -(-paperT x y z*x*y*z - paperT x y z*y*z^2 + 2*paperT x y z*y
    + paperT x y z*z + x*y^2*z + x*y*z^2 + x*y*z + y^2*z^2 - 2*y^2
    + y*z^3 + 2*y*z^2 - y*z - y) / (y*(y-paperT x y z))

/-- The actual matrix in the task.  It is independent of g, but its tail
identification will use the equations containing g. -/
def candidateMatrix (x y z g : ℝ) : Rho5.Matrix5 :=
  !![1, 1, -z/y, -z, z*(x+z)/(x+1);
     x, x+z+1, paperB23 x y z, -1, 1;
     -1, z, paperB33 x y z, -1, -1;
     y, paperT x y z, 1, 1, 1;
     z, -1, 1, -1, 1]

def matrixA (x y z : ℝ) : Rho5.Matrix5 :=
  !![(1:ℝ), (1:ℝ), ((-z) / y), (-z), (topRight x y z);
     x, ((x + z) + (1:ℝ)), (reducedB23 x y z), (-1:ℝ), (1:ℝ);
     (-1:ℝ), z, (reducedB33 x y z), (-1:ℝ), (-1:ℝ);
     y, (reducedT x y z), (1:ℝ), (1:ℝ), (1:ℝ);
     z, (-1:ℝ), (1:ℝ), (-1:ℝ), (1:ℝ)]

def matrixF (x y z : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(pivotTwo x y z), (headEntry x y z), ((x * z) - (1:ℝ)), ((1:ℝ) - (x * (topRight x y z)));
     (pivotTwo x y z), ((corePivot x y z) + (headEntry x y z)), (-(pivotTwo x y z)), ((topRight x y z) - (1:ℝ));
     ((pivotTwo x y z) * (ratioRD x y z)), (pivotTwo x y z), ((1:ℝ) + (y * z)), ((1:ℝ) - (y * (topRight x y z)));
     (-(pivotTwo x y z)), ((1:ℝ) + ((z ^ 2) / y)), ((z ^ 2) - (1:ℝ)), ((1:ℝ) - (z * (topRight x y z)))]

def matrixG (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(corePivot x y z), (coreArm x y z), (-(corePivot x y z));
     (corePivot x y z), ((halfHeight x y z) + (coreArm x y z)), ((halfHeight x y z) - (corePivot x y z));
     (coreBottom x y z), (-(corePivot x y z)), (coreCorner x y z)]

def matrixH (x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(halfHeight x y z), (halfHeight x y z);
     ((-(corePivot x y z)) - (((coreBottom x y z) * (coreArm x y z)) / (corePivot x y z))), ((coreCorner x y z) + (coreBottom x y z))]

/-- Every stage below is a Schur tail of the same actual matrix. -/
def stageF (x y z g : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Rho5.Pivot.fixedSchur (candidateMatrix x y z g)
def stageG (x y z g : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Rho5.Pivot.fixedSchur (stageF x y z g)
def stageH (x y z g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Rho5.Pivot.fixedSchur (stageG x y z g)
def stageL (x y z g : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  Rho5.Pivot.fixedSchur (stageH x y z g)

/-- This is the actual third pivot, not an independently chosen parameter. -/
def p3 (x y z g : ℝ) : ℝ := stageG x y z g 0 0

def candidateValues (x y z g : ℝ) : List ℝ :=
  [1, 1+z, p3 x y z g, g/2, g]

end Rho5.ExternalAttainment
