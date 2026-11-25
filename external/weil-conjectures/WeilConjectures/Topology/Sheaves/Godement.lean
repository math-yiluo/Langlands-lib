/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Topology.Sheaves.Cech

/-!
# The Godement sheaf

For a family `S` of abelian groups indexed by the points of a topological space `X`, the presheaf
`TopCat.Presheaf.godement S` of all (not necessarily continuous) sections of `S` is a flasque
sheaf. Applied to the stalks of an abelian sheaf `F`, this gives a functorial embedding
`F ⟶ godementFunctor.obj F` of `F` into a flasque sheaf.

## Main definitions

- `TopCat.Sheaf.godementFunctor`: the functor `F ↦ ∏_x F_x` (all sections of the stalks).
- `TopCat.Sheaf.toGodementFunctor`: the natural monomorphism `F ⟶ godementFunctor.obj F`
  sending a section to its germs.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- The presheaf of all sections of a family of abelian groups is a sheaf. -/
theorem isSheaf_godement (S : X → Type u) [∀ x, AddCommGroup (S x)] :
    TopCat.Presheaf.IsSheaf (godement S) := by
  rw [isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hmem (x : ↥(iSup U)) : ∃ i, x.1 ∈ U i := Opens.mem_iSup.1 x.2
  let s : ∀ x : ↥(iSup U), S x.1 := fun x ↦ sf (hmem x).choose ⟨x.1, (hmem x).choose_spec⟩
  have hcompat (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
      sf i ⟨x, hi⟩ = sf j ⟨x, hj⟩ :=
    congrFun (hsf i j) ⟨x, hi, hj⟩
  refine ⟨s, fun i ↦ funext fun x ↦ hcompat _ _ _ _ _, fun t ht ↦ funext fun x ↦ ?_⟩
  have := congrFun (ht (hmem x).choose) ⟨x.1, (hmem x).choose_spec⟩
  exact this

/-- The presheaf of all sections of a family of abelian groups is flasque: a section over `V`
extends by zero to any `U ≥ V`. -/
instance isFlasque_godement (S : X → Type u) [∀ x, AddCommGroup (S x)] :
    IsFlasque (godement S) where
  epi {U V} i := by
    classical
    refine (AddCommGrpCat.epi_iff_surjective _).2 fun t ↦ ?_
    refine ⟨fun x ↦ if h : x.1 ∈ V.unop then t ⟨x.1, h⟩ else 0, funext fun x ↦ ?_⟩
    change (if h : x.1 ∈ V.unop then t ⟨x.1, h⟩ else 0) = t x
    rw [dite_eq_left x.2]

/-- The morphism of Godement presheaves induced by a family of additive maps. -/
@[simps]
noncomputable def godementMap {S T : X → Type u} [∀ x, AddCommGroup (S x)]
    [∀ x, AddCommGroup (T x)] (f : ∀ x, S x →+ T x) : godement S ⟶ godement T where
  app _ := AddCommGrpCat.ofHom
    { toFun := fun s x ↦ f x.1 (s x)
      map_zero' := funext fun x ↦ (f x.1).map_zero
      map_add' := fun _ _ ↦ funext fun x ↦ (f x.1).map_add _ _ }
  naturality _ _ _ := rfl

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

open Presheaf

/-- The presheaf functor `F ↦ godement (stalks of F)` on abelian sheaves. -/
@[simps]
noncomputable def godementPresheafFunctor :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj F := godement fun x : X ↦
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.obj x : Type u)
  map φ := godementMap fun x ↦ ((stalkFunctor AddCommGrpCat.{u} x).map φ.hom).hom
  map_id F := by
    refine NatTrans.ext (funext fun W ↦ AddCommGrpCat.ext fun s ↦ funext fun x ↦ ?_)
    change (stalkFunctor AddCommGrpCat.{u} x.1).map (𝟙 F.obj) (s x) = s x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp φ ψ := by
    refine NatTrans.ext (funext fun W ↦ AddCommGrpCat.ext fun s ↦ funext fun x ↦ ?_)
    change (stalkFunctor AddCommGrpCat.{u} x.1).map (φ.hom ≫ ψ.hom) (s x) = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- The Godement functor `F ↦ ∏_x F_x` on abelian sheaves on `X`: the sheaf of all, not
necessarily continuous, sections of the stalks of `F`. -/
noncomputable def godementFunctor :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  ObjectProperty.lift _ godementPresheafFunctor fun F ↦ isSheaf_godement
    fun x : X ↦ (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.obj x : Type u)

instance (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Presheaf.IsFlasque (godementFunctor.obj F).obj :=
  isFlasque_godement fun x : X ↦ (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.obj x : Type u)

/-- The natural map `F ⟶ godementFunctor.obj F` sending a section to its germs. -/
noncomputable def toGodementFunctor : 𝟭 (TopCat.Sheaf AddCommGrpCat.{u} X) ⟶ godementFunctor where
  app F := ObjectProperty.homMk (toGodement F)
  naturality F G φ := by
    refine (sheafToPresheaf _ _).map_injective
      (NatTrans.ext (funext fun W ↦ AddCommGrpCat.ext fun s ↦ funext fun x ↦ ?_))
    change TopCat.Presheaf.germ G.obj W.unop x.1 x.2 (φ.hom.app W s) =
      (stalkFunctor AddCommGrpCat.{u} x.1).map φ.hom
        (TopCat.Presheaf.germ F.obj W.unop x.1 x.2 s)
    rw [stalkFunctor_map_germ_apply]

instance (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Mono (toGodementFunctor.app F) := by
  have : Mono (toGodement F) := inferInstance
  exact (sheafToPresheaf _ _).mono_of_mono_map this

end TopCat.Sheaf
