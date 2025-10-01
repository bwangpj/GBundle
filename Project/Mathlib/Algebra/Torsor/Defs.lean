import Mathlib.Algebra.Group.Action.Pretransitive

class AddTorsor
    (G : Type*) [AddGroup G] (F : Type*) [AddAction G F]
    extends AddAction.IsPretransitive G F where
  nonempty : Nonempty F
  free : ∀ (f : F) (g : G), g +ᵥ f = f → g = 0

@[to_additive (attr := mk_iff)]
class MulTorsor
    (G : Type*) [Group G] (F : Type*) [MulAction G F]
    extends MulAction.IsPretransitive G F where
  nonempty : Nonempty F
  free : ∀ (f : F) (g : G), g • f = f → g = 1
