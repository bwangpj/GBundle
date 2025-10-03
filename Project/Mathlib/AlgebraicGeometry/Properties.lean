import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Basic properties of schemes

We provide some basic properties of schemes

## Main definition
* `AlgebraicGeometry.IsGeometricallyIntegral`: A scheme over a field `k` is geometrically integral
  if it remains integral after base change to any field extension `k'` of `k`.
-/

universe u
open AlgebraicGeometry CategoryTheory Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u}) {k : Type u} [Field k] [X.Over Spec(k)]

/-- A scheme `X` is geometrically integral if
it remains integral after base change to any field extension `k'` of `k`. -/
class IsGeometricallyIntegral : Prop where
  base_change :
    ∀ (k' : Type u) [Field k'] [Algebra k k'],
    IsIntegral (pullback (X ↘ Spec(k))
      (Spec.map (CommRingCat.ofHom <| algebraMap k k')))

end AlgebraicGeometry
