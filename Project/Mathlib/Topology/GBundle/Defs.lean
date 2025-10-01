import Mathlib.Topology.FiberBundle.Basic
import Project.Mathlib.Algebra.Torsor.Defs

structure GBundleCore
    (ι : Type*) (B : Type*) [TopologicalSpace B]
    (F : Type*) [TopologicalSpace F]
    (G : Type*) [Group G]
    [MulAction G F] [IsMulTorsor G F]
    extends FiberBundleCore ι B F where
  coordChange_structure_group :
    ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∃ g : G, ∀ v : F, coordChange i j x v = g • v
