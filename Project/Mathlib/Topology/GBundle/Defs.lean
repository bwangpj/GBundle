import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Group.Defs
import Project.Mathlib.Algebra.Torsor.Defs

/- structure GBundleCore
    (ι : Type*) (B : Type*) [TopologicalSpace B]
    (F : Type*) [TopologicalSpace F]
    (G : Type*) [Group G]
    [MulAction Gᵐᵒᵖ F] [IsMulTorsor G F]
    extends FiberBundleCore ι B F where
  coordChange_structure_group :
    ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∃ g : G, ∀ v : F, coordChange i j x v = g • v -/

class PrincipalGBundle {B : Type*} (F : Type*) [TopologicalSpace B] [TopologicalSpace F]
    (E : B → Type*) [TopologicalSpace (Bundle.TotalSpace F E)] [(b : B) → TopologicalSpace (E b)]
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MulAction Gᵐᵒᵖ (Bundle.TotalSpace F E)] [ContinuousSMul Gᵐᵒᵖ (Bundle.TotalSpace F E)] extends FiberBundle F E where

  torsor := ∀ b : B, IsMulTorsor Gᵐᵒᵖ (E b)


