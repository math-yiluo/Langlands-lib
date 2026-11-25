/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf

/-!
# The condensed ring of a finite discrete ring is constant

Let `T` be a finite ring with the discrete topology. A continuous map `S → T` on a profinite set
`S` is locally constant, constant on each of the finitely many clopen fibres. Hence the
morphism of presheaves of rings from the constant presheaf `T` to `C(-, T)` given by the
constant maps is locally bijective for the coherent topology, and induces an isomorphism of
ring objects from the constant ring sheaf `T` to the condensed ring `T̲ = C(-, T)`
(`Profinite.constRingSheafToContinuousMapRingObj`).

Local injectivity uses that the empty profinite set is covered by the empty family.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite
open scoped CategoryTheory.Obj

namespace Profinite

variable (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- The constant maps, as a morphism of abelian presheaves from the constant presheaf `T` to the
presheaf `C(-, T)` of continuous maps. -/
noncomputable def constToContinuousMap :
    Presheaf.constRingObj (C := Profinite.{u}) (ULift.{u + 1} T) ⟶
      continuousMapRingPresheaf.{u} T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} where
  app _ := AddCommGrpCat.ofHom
    { toFun r := ULift.up (ContinuousMap.const _ r.down)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

instance isMonHom_constToContinuousMap : IsMonHom (constToContinuousMap.{u} T) where
  one_hom := NatTrans.ext (funext fun _ ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ ↦
    ULift.ext (ContinuousMap.ext fun _ ↦ rfl)))
  mul_hom := NatTrans.ext (funext fun _ ↦ AddCommGrpCat.hom_ext_toIntLinearMap
    (TensorProduct.ext' fun _ _ ↦ ULift.ext (ContinuousMap.ext fun _ ↦ rfl)))

/-- The empty profinite set is covered by the empty family. -/
lemma mem_coherentTopology_of_isEmpty {S : Profinite.{u}} (hS : IsEmpty S) (R : Sieve S) :
    R ∈ coherentTopology Profinite.{u} S :=
  (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily R).mpr
    ⟨PEmpty, inferInstance, PEmpty.elim, fun a ↦ a.elim,
      effectiveEpiFamily_of_jointly_surjective _ _ fun b ↦ hS.elim b, fun a ↦ a.elim⟩

/-- The constant maps are locally injective: they are injective on nonempty profinite sets, and
the empty profinite set is covered by the empty family. -/
instance isLocallyInjective_constToContinuousMap :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u}) (constToContinuousMap.{u} T) where
  equalizerSieve_mem {S} x y h := by
    cases isEmpty_or_nonempty S.unop with
    | inl hS => exact mem_coherentTopology_of_isEmpty hS _
    | inr hS =>
      obtain rfl : x = y := ULift.ext (congrArg (fun f ↦ f.down hS.some) h)
      rw [Presheaf.equalizerSieve_self_eq_top]
      exact (coherentTopology Profinite.{u}).top_mem _

variable [DiscreteTopology T]

/-- A fibre of a continuous map to a discrete space is closed, hence compact. -/
instance compactSpace_preimage_singleton {S : Profinite.{u}} (f : C(S, T)) (t : T) :
    CompactSpace (f ⁻¹' {t}) :=
  isCompact_iff_compactSpace.mp (isClosed_singleton.preimage f.continuous).isCompact

/-- The fibre `f ⁻¹' {t}` of a continuous map `f : S → T` to a discrete space, a clopen subset of
`S`, as a profinite set. -/
noncomputable def fibre {S : Profinite.{u}} (f : C(S, T)) (t : T) : Profinite.{u} :=
  Profinite.of (f ⁻¹' {t})

/-- The inclusion of a fibre. -/
noncomputable def fibreι {S : Profinite.{u}} (f : C(S, T)) (t : T) : fibre T f t ⟶ S :=
  CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩

variable [Finite T]

/-- The constant maps are locally surjective: a continuous map to the finite discrete `T` is
constant on each of its finitely many fibres, which cover. -/
instance isLocallySurjective_constToContinuousMap :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u}) (constToContinuousMap.{u} T) where
  imageSieve_mem g :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mpr
      ⟨T, inferInstance, fibre T g.down, fibreι T g.down,
        effectiveEpiFamily_of_jointly_surjective _ _ fun b ↦ ⟨g.down b, ⟨b, rfl⟩, rfl⟩,
        fun t ↦ ⟨ULift.up t, ULift.ext (ContinuousMap.ext fun x ↦ x.2.symm)⟩⟩

/-- The constant maps induce a morphism of ring objects from the constant ring sheaf `T` to the
condensed ring `T̲ = C(-, T)`. -/
noncomputable def constRingSheafToContinuousMapRingObj :
    Sheaf.constRingSheaf (coherentTopology Profinite.{u}) (ULift.{u + 1} T) ⟶
      continuousMapRingObj.{u} T :=
  (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map (constToContinuousMap T) ≫
    (Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
      (continuousMapRingSheaf.{u} T)).hom

instance isMonHom_constRingSheafToContinuousMapRingObj :
    IsMonHom (constRingSheafToContinuousMapRingObj.{u} T) := by
  dsimp only [constRingSheafToContinuousMapRingObj]
  infer_instance

/-- For a finite discrete ring `T`, the condensed ring `T̲ = C(-, T)` is the constant ring
sheaf `T`. -/
instance isIso_constRingSheafToContinuousMapRingObj :
    IsIso (constRingSheafToContinuousMapRingObj.{u} T) := by
  have : IsIso ((presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      (constToContinuousMap T)) := by
    rw [← GrothendieckTopology.W_iff]
    exact GrothendieckTopology.W_of_isLocallyBijective _ _
  dsimp only [constRingSheafToContinuousMapRingObj]
  infer_instance

end Profinite
