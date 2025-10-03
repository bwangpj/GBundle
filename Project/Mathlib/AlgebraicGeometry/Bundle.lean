import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Mod_

universe u

open AlgebraicGeometry CategoryTheory

variable {X M G : Scheme.{u}} [M.Over X]
variable [G.Over X] [GrpObj (G.asOver X)]

open MonoidalCategory MonoidalOpposite

#check ModObj ((G.asOver X)ᵐᵒᵖ) (M.asOver X)
