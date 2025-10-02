import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Algebra.AddTorsor.Defs
import Mathlib.GroupTheory.GroupAction.Hom

class IsAddTorsor
    (G : Type*) [AddGroup G] (F : Type*) [AddAction G F]
    extends AddAction.IsPretransitive G F where
  nonempty : Nonempty F
  free : ∀ (f : F) (g : G), g +ᵥ f = f → g = 0

@[to_additive (attr := mk_iff)]
class IsMulTorsor
    (G : Type*) [Group G] (F : Type*) [MulAction G F]
    extends MulAction.IsPretransitive G F where
  nonempty : Nonempty F
  free : ∀ (f : F) (g : G), g • f = f → g = 1

instance AddTorsor.isAddTorsor {G : Type*} [AddGroup G] {F : Type*} [AddTorsor G F] :
    IsAddTorsor G F where
  exists_vadd_eq x y := ⟨y -ᵥ x, vsub_vadd' _ _⟩
  nonempty := nonempty
  free f g h := (vsub_self f) ▸ (h ▸ (vadd_vsub' g f)).symm

@[to_additive]
noncomputable def IsMulTorsor.equiv_group (G : Type*) [Group G] (F : Type*)
    [MulAction G F] [IsMulTorsor G F]
    (b : F) :
    F ≃ G where
  toFun f := (toIsPretransitive.exists_smul_eq b f).choose
  invFun g := g • b
  left_inv := by
    refine Function.leftInverse_iff_comp.mpr ?_
    ext f; simpa using (toIsPretransitive.exists_smul_eq b f).choose_spec
  right_inv := by
    refine Function.rightInverse_iff_comp.mpr ?_
    ext g; simp only [Function.comp_apply, id_eq]
    apply inv_mul_eq_one.mp
    apply free b _
    rw [mul_smul]
    exact inv_smul_eq_iff.mpr
      (toIsPretransitive.exists_smul_eq b (g • b)).choose_spec.symm
