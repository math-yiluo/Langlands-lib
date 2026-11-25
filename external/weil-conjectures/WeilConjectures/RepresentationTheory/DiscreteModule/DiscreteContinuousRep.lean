/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedHom
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import WeilConjectures.RepresentationTheory.DiscreteModule.Basic

/-!
# Discrete modules as continuous `ℤ`-representations

The category `DiscreteModule G` of discrete `G`-modules (a full subcategory of
`Action AddCommGrpCat G`) is equivalent to the category `Rep.DiscreteContinuousRep ℤ G` of
`ℤ`-linear representations of `G` with open stabilizers (a full subcategory of `Rep ℤ G`).

## Main definitions

- `DiscreteModule.toDiscreteContinuousRep`, `DiscreteModule.ofDiscreteContinuousRep`: the two
  functors, which do not change the underlying abelian groups.
- `DiscreteModule.discreteContinuousRepEquivalence`: the equivalence of categories.
- `DiscreteModule.toDiscreteContinuousRepCompForgetIso`,
  `DiscreteModule.toDiscreteContinuousRepCompInvariantsIso`: compatibility with the forgetful
  functors and the invariants functors.
- `DiscreteModule.hAddEquivRightDerivedInvariants`: `Hⁿ(G, M)` is the `n`-th right derived functor
  of the invariants functor.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace DiscreteModule

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The `ℤ`-linear representation underlying a discrete `G`-module. -/
@[simps]
def representation (M : DiscreteModule.{w} G) : Representation ℤ G M.obj.V where
  toFun g := (M.obj.ρ g).asHom.hom.toIntLinearMap
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- A discrete `G`-module as a continuous `ℤ`-representation of `G`. -/
def toDiscreteContinuousRep :
    DiscreteModule.{w} G ⥤ Rep.DiscreteContinuousRep.{0, u, max u w} ℤ G where
  obj M := ⟨Rep.of (representation G M), fun x ↦ M.property x⟩
  map {M N} f := ObjectProperty.homMk (Rep.ofHom
    { toLinearMap := f.hom.hom.hom.toIntLinearMap
      isIntertwining' g := by
        ext x
        exact Action.hom_comm_apply f.hom g x })

variable {G}

@[simp]
lemma toDiscreteContinuousRep_obj_V (M : DiscreteModule.{w} G) :
    ((toDiscreteContinuousRep G).obj M).obj.V = M.obj.V :=
  rfl

@[simp]
lemma toDiscreteContinuousRep_obj_ρ_apply (M : DiscreteModule.{w} G) (g : G) (x : M.obj.V) :
    ((toDiscreteContinuousRep G).obj M).obj.ρ g x = (M.obj.ρ g).asHom.hom x :=
  rfl

@[simp]
lemma toDiscreteContinuousRep_map_hom_hom_apply {M N : DiscreteModule.{w} G} (f : M ⟶ N)
    (x : M.obj.V) :
    ((toDiscreteContinuousRep G).map f).hom.hom x = f.hom.hom.hom x :=
  rfl

variable (G)

/-- A continuous `ℤ`-representation of `G` as a discrete `G`-module. -/
def ofDiscreteContinuousRep :
    Rep.DiscreteContinuousRep.{0, u, max u w} ℤ G ⥤ DiscreteModule.{w} G where
  obj X := ⟨{ V := AddCommGrpCat.of X.obj.V
              ρ :=
                { toFun g := End.of (AddCommGrpCat.ofHom (X.obj.ρ g : X.obj.V →+ X.obj.V))
                  map_one' := End.ext (AddCommGrpCat.ext fun x ↦ by simp [End.one_asHom])
                  map_mul' _ _ :=
                    End.ext (AddCommGrpCat.ext fun x ↦ by simp [End.mul_asHom]) } },
    fun x ↦ X.property x⟩
  map {X Y} f := ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom (f.hom.hom : X.obj.V →+ Y.obj.V)
      comm g := AddCommGrpCat.ext fun x ↦ Rep.hom_comm_apply f.hom g x }

variable {G}

@[simp]
lemma ofDiscreteContinuousRep_obj_V (X : Rep.DiscreteContinuousRep.{0, u, max u w} ℤ G) :
    ((ofDiscreteContinuousRep G).obj X).obj.V = AddCommGrpCat.of X.obj.V :=
  rfl

@[simp]
lemma ofDiscreteContinuousRep_obj_ρ_apply (X : Rep.DiscreteContinuousRep.{0, u, max u w} ℤ G)
    (g : G) (x : X.obj.V) :
    (((ofDiscreteContinuousRep G).obj X).obj.ρ g).asHom.hom x = X.obj.ρ g x :=
  rfl

@[simp]
lemma ofDiscreteContinuousRep_map_hom_hom_apply
    {X Y : Rep.DiscreteContinuousRep.{0, u, max u w} ℤ G} (f : X ⟶ Y) (x : X.obj.V) :
    ((ofDiscreteContinuousRep G).map f).hom.hom.hom x = f.hom.hom x :=
  rfl

/-- The identity of the underlying group, as an isomorphism in `Rep ℤ G` from
`toDiscreteContinuousRep (ofDiscreteContinuousRep X)` to `X`. The two `ℤ`-module structures on
the underlying group are only propositionally equal, so the instances are given explicitly. -/
def discreteContinuousRepCounitIso (X : Rep.DiscreteContinuousRep.{0, u, max u w} ℤ G) :
    ((toDiscreteContinuousRep G).obj ((ofDiscreteContinuousRep G).obj X)).obj ≅ X.obj where
  hom := ConcreteCategory.ofHom (C := Rep ℤ G)
    (@Representation.IntertwiningMap.mk ℤ G X.obj.V X.obj.V _ _ _ _
      ((toDiscreteContinuousRep G).obj ((ofDiscreteContinuousRep G).obj X)).obj.hV2 X.obj.hV2
      ((toDiscreteContinuousRep G).obj ((ofDiscreteContinuousRep G).obj X)).obj.ρ X.obj.ρ
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) X.obj.V X.obj.V _ _
        ((toDiscreteContinuousRep G).obj ((ofDiscreteContinuousRep G).obj X)).obj.hV2 X.obj.hV2
        ⟨fun x ↦ x, fun _ _ ↦ rfl⟩ fun n x ↦ (int_smul_eq_zsmul X.obj.hV2 n x).symm)
      fun _ ↦ rfl)
  inv := ConcreteCategory.ofHom (C := Rep ℤ G)
    (@Representation.IntertwiningMap.mk ℤ G X.obj.V X.obj.V _ _ _ _ X.obj.hV2
      ((toDiscreteContinuousRep G).obj ((ofDiscreteContinuousRep G).obj X)).obj.hV2
      X.obj.ρ ((toDiscreteContinuousRep G).obj ((ofDiscreteContinuousRep G).obj X)).obj.ρ
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) X.obj.V X.obj.V _ _ X.obj.hV2
        ((toDiscreteContinuousRep G).obj ((ofDiscreteContinuousRep G).obj X)).obj.hV2
        ⟨fun x ↦ x, fun _ _ ↦ rfl⟩ fun n x ↦ int_smul_eq_zsmul X.obj.hV2 n x)
      fun _ ↦ rfl)
@[simp]
lemma discreteContinuousRepCounitIso_hom_hom_apply
    (X : Rep.DiscreteContinuousRep.{0, u, max u w} ℤ G) (x : X.obj.V) :
    (discreteContinuousRepCounitIso X).hom.hom x = x :=
  rfl

@[simp]
lemma discreteContinuousRepCounitIso_inv_hom_apply
    (X : Rep.DiscreteContinuousRep.{0, u, max u w} ℤ G) (x : X.obj.V) :
    (discreteContinuousRepCounitIso X).inv.hom x = x :=
  rfl

variable (G)

/-- The equivalence between discrete `G`-modules and continuous `ℤ`-representations of `G`. -/
def discreteContinuousRepEquivalence :
    DiscreteModule.{w} G ≌ Rep.DiscreteContinuousRep.{0, u, max u w} ℤ G where
  functor := toDiscreteContinuousRep G
  inverse := ofDiscreteContinuousRep G
  unitIso := NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (Action.mkIso (AddEquiv.refl M.obj.V).toAddCommGrpIso fun _ ↦ rfl)) fun _ ↦ rfl
  counitIso := NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _
    (discreteContinuousRepCounitIso X)) fun _ ↦ rfl
  functor_unitIso_comp _ := by ext; rfl

/-- Forgetting to abelian groups after `toDiscreteContinuousRep` is the forgetful functor. -/
def toDiscreteContinuousRepCompForgetIso :
    toDiscreteContinuousRep G ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ G ⋙
        Action.forget (ModuleCat.{max u w} ℤ) G ⋙
        forget₂ (ModuleCat.{max u w} ℤ) AddCommGrpCat.{max u w} ≅
      ObjectProperty.ι _ ⋙ Action.forget AddCommGrpCat.{max u w} G :=
  NatIso.ofComponents (fun M ↦ (AddEquiv.refl M.obj.V).toAddCommGrpIso) fun _ ↦ rfl

@[simp]
lemma toDiscreteContinuousRepCompForgetIso_hom_app_apply (M : DiscreteModule.{w} G)
    (x : M.obj.V) : ((toDiscreteContinuousRepCompForgetIso G).hom.app M).hom x = x :=
  rfl

@[simp]
lemma toDiscreteContinuousRepCompForgetIso_inv_app_apply (M : DiscreteModule.{w} G)
    (x : M.obj.V) : ((toDiscreteContinuousRepCompForgetIso G).inv.app M).hom x = x :=
  rfl

/-- The invariants of the representation attached to a discrete `G`-module are its invariants. -/
noncomputable def toDiscreteContinuousRepCompInvariantsIso :
    toDiscreteContinuousRep G ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
        forget₂ (ModuleCat.{max u w} ℤ) AddCommGrpCat.{max u w} ≅
      invariants G :=
  NatIso.ofComponents (fun M ↦ AddEquiv.toAddCommGrpIso
    { toFun x := ⟨x.1, x.2⟩
      invFun x := ⟨x.1, x.2⟩
      map_add' _ _ := rfl }) fun _ ↦ rfl

@[simp]
lemma toDiscreteContinuousRepCompInvariantsIso_hom_app_apply_coe (M : DiscreteModule.{w} G)
    (x : ((toDiscreteContinuousRep G).obj M).obj.ρ.invariants) :
    (((toDiscreteContinuousRepCompInvariantsIso G).hom.app M).hom x).1 = x.1 :=
  rfl

@[simp]
lemma toDiscreteContinuousRepCompInvariantsIso_inv_app_apply_coe (M : DiscreteModule.{w} G)
    (x : invariantsSubgroup M) :
    (((toDiscreteContinuousRepCompInvariantsIso G).inv.app M).hom x).1 = x.1 :=
  rfl

/-- Morphisms out of the trivial module `ℤ` are naturally the invariants. -/
def homIntTrivialIso :
    preadditiveCoyoneda.obj (op (intTrivial.{w} G)) ≅ invariants G :=
  NatIso.ofComponents (fun M ↦ (homIntTrivialEquiv M).toAddCommGrpIso) fun _ ↦ rfl

instance : (invariants.{w} G).Additive :=
  Functor.additive_of_iso (homIntTrivialIso G)

/-- `Hⁿ(G, M)` is the `n`-th right derived functor of the invariants functor, evaluated at `M`.
This uses the (non-canonically chosen, via `Nonempty.some`) comparison
`nonempty_extFunctor_iso_rightDerivedHom` between `Ext` and the right derived functors of `Hom`. -/
noncomputable def hAddEquivRightDerivedInvariants (M : DiscreteModule.{w} G) (n : ℕ) :
    H G M n ≃+ ((invariants G).rightDerived n).obj M :=
  (((nonempty_extFunctor_iso_rightDerivedHom (intTrivial.{w} G) n).some ≪≫
    { hom := NatTrans.rightDerived (homIntTrivialIso G).hom n
      inv := NatTrans.rightDerived (homIntTrivialIso G).inv n
      hom_inv_id := by
        rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by
        rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id] }).app
    M).addCommGroupIsoToAddEquiv

end DiscreteModule
