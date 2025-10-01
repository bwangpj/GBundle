import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Topology.Algebra.MulAction

open Bundle

structure GBundleCore
    (ι : Type*) (B : Type*) [TopologicalSpace B]
    (F : Type*) [TopologicalSpace F]
    (G : Type*) [Group G]
    [MulAction G F] [MulAction.IsPretransitive G F]
    extends FiberBundleCore ι B F where
  coordChange_structure_group :
    ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∃ g : G, ∀ v : F, coordChange i j x v = g • v
  /- respects_fibres : ∀ (p : TotalSpace F (core.Fiber)) (g : G), core.proj (p <• g) = core.proj p
  (is_free : ∀ (p : TotalSpace F (core.Fiber)) (g : G), p <• g = p → g = 1)
  (is_transitive : ∀ (p q : TotalSpace F (core.Fiber)),
    core.proj p = core.proj q → ∃ g : G, p <• g = q) -/
