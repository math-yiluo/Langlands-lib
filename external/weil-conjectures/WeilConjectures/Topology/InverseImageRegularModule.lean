/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.InverseImageModule
import WeilConjectures.Topology.InverseImageOperationExt
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-! # Inverse image of the regular module

Source: Stacks Project, Tags 008X and 008A.
(blueprint: stage3-inverse-image-regular-module).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace TopCat.Sheaf
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (R : Y.Sheaf CommRingCat.{u})
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S

private abbrev forgetAb : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}

private instance : PreservesFilteredColimits (forgetAb.{u}) :=
  comp_preservesFilteredColimits (forget₂ CommRingCat.{u} RingCat.{u})
    (forget₂ RingCat.{u} AddCommGrpCat.{u})

private instance : (Opens.grothendieckTopology X).PreservesSheafification (forgetAb.{u}) :=
  GrothendieckTopology.instPreservesSheafification _ _

private instance (W : (Opens X)ᵒᵖ) : IsFiltered (CostructuredArrow (Opens.map f).op W) :=
  IsFiltered.of_equivalence (structuredArrowOpEquivalence (Opens.map f) (unop W))

private def inverseRegularAbIso :
    (inverseImageAb f R (SheafOfModules.unit (𝓡 R))).obj ≅
      (inverseImageRing f R).obj ⋙ forgetAb.{u} := by
  let L := (Opens.map f).op
  let J := Opens.grothendieckTopology X
  let i := forgetAb.leftKanExtensionCompIsoOfPreserves R.obj L
  exact (presheafToSheaf J AddCommGrpCat.{u} ⋙ sheafToPresheaf J AddCommGrpCat.{u}).mapIso
    i.symm ≪≫ sheafifyComposeIso J forgetAb (L.lan.obj R.obj)

private instance (D : Type (u + 1)) [Category.{u} D] [HasColimits.{u} D] :
    ∀ (A : (Opens Y)ᵒᵖ ⥤ D), (Opens.map f).op.HasLeftKanExtension A :=
  fun A ↦ Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (Opens.map f).op A)

private theorem inverseImageUnit_hom (D : Type (u + 1)) [Category.{u} D]
    [HasColimits.{u} D] [HasWeakSheafify (Opens.grothendieckTopology X) D]
    (A : Y.Sheaf D) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) D (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).unit.app A).hom =
      (Opens.map f).op.lanUnit.app A.obj ≫
        Functor.whiskerLeft (Opens.map f).op
          (toSheafify (Opens.grothendieckTopology X) ((Opens.map f).op.lan.obj A.obj)) := by
  change (sheafToPresheaf _ _).map ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) D (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X)).unit.app A) = _
  simp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
    sheafificationAdjunction_unit_app, Functor.comp_map, Iso.refl_hom, NatTrans.id_app]
  simp only [Functor.lanAdjunction_unit]
  ext V
  dsimp
  simp only [Category.comp_id]

private theorem inverseRegularAbIso_unit (V : (Opens Y)ᵒᵖ) (d : R.obj.obj V) :
    (inverseRegularAbIso f R).hom.app ((Opens.map f).op.obj V)
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app
          ((SheafOfModules.toSheaf (𝓡 R)).obj
            (SheafOfModules.unit (𝓡 R)))).hom.app V d) =
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) CommRingCat.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app R).hom.app V d := by
  let L := (Opens.map f).op
  let J := Opens.grothendieckTopology X
  let i := forgetAb.leftKanExtensionCompIsoOfPreserves R.obj L
  rw [inverseImageUnit_hom, inverseImageUnit_hom]
  change ((sheafifyMap J i.inv) ≫
    (sheafifyComposeIso J forgetAb (L.lan.obj R.obj)).hom).app (L.obj V)
      (((toSheafify J (L.lan.obj (R.obj ⋙ forgetAb))).app (L.obj V))
        ((L.lanUnit.app (R.obj ⋙ forgetAb)).app V d)) =
    (toSheafify J (L.lan.obj R.obj)).app (L.obj V)
      ((L.lanUnit.app R.obj).app V d)
  have hn := NatTrans.congr_app (toSheafify_naturality J i.inv) (L.obj V)
  have hs := NatTrans.congr_app
    (sheafComposeIso_hom_fac J forgetAb (L.lan.obj R.obj)) (L.obj V)
  have hl := forgetAb.leftKanExtensionCompIsoOfPreserves_inv_fac_app R.obj L V
  let x := (L.lanUnit.app (R.obj ⋙ forgetAb)).app V d
  have hn' := ConcreteCategory.congr_hom hn x
  have hs' := ConcreteCategory.congr_hom hs (i.inv.app (L.obj V) x)
  have hl' := ConcreteCategory.congr_hom hl d
  exact (congrArg ((sheafifyComposeIso J forgetAb (L.lan.obj R.obj)).hom.app (L.obj V))
    hn'.symm).trans (hs'.trans
      (congrArg ((toSheafify J (L.lan.obj R.obj)).app (L.obj V)) hl'))

private theorem inverseRegularAbIso_smul (W : (Opens X)ᵒᵖ)
    (r : (inverseImageRing f R).obj.obj W)
    (m : (inverseImageModule f R (SheafOfModules.unit (𝓡 R))).val.obj W) :
    (inverseRegularAbIso f R).hom.app W (r • m) =
      r * (show (inverseImageRing f R).obj.obj W from
        (inverseRegularAbIso f R).hom.app W m) := by
  let M := SheafOfModules.unit (𝓡 R)
  let q := inverseRegularAbIso f R
  let hd := Classical.choose_spec (exists_inverseImageModuleInstances f R M)
  apply inverseImageOperation_ext f R ((SheafOfModules.toSheaf (𝓡 R)).obj M)
    ((sheafCompose (Opens.grothendieckTopology X) forgetAb).obj (inverseImageRing f R))
    (fun W r m ↦ q.hom.app W
      (@SMul.smul _ _ (inverseImageModuleInstances f R M W).toSMul r m))
    (fun W r m ↦ (show (inverseImageRing f R).obj.obj W from r) *
      (show (inverseImageRing f R).obj.obj W from q.hom.app W m))
    (by
      intro V W i r m
      exact (ConcreteCategory.congr_hom (q.hom.naturality i).symm
        (@SMul.smul _ _ (inverseImageModuleInstances f R M V).toSMul r m)).trans
          (congrArg (q.hom.app W) (hd.1 i r m)))
    (by
      intro V W i r m
      change (inverseImageRing f R).obj.map i
        ((show (inverseImageRing f R).obj.obj V from r) *
          (show (inverseImageRing f R).obj.obj V from q.hom.app V m)) = _
      rw [map_mul]
      exact congrArg (fun (x : (inverseImageRing f R).obj.obj W) ↦
        (inverseImageRing f R).obj.map i r * x)
        (ConcreteCategory.congr_hom (q.hom.naturality i).symm m))
    (by
      intro V r m
      have h := congrArg (q.hom.app ((Opens.map f).op.obj V)) (hd.2 V r m)
      have hmul := inverseRegularAbIso_unit f R V (r * (show R.obj.obj V from m))
      have hr := inverseRegularAbIso_unit f R V m
      let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) CommRingCat.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app R).hom.app V
      have hmult : η (r * (show R.obj.obj V from m)) = η r * η m :=
        η.hom.map_mul r m
      exact h.symm.trans (hmul.trans (hmult.trans
        (congrArg (fun (x : (inverseImageRing f R).obj.obj ((Opens.map f).op.obj V)) ↦
          (show (inverseImageRing f R).obj.obj ((Opens.map f).op.obj V) from η r) * x)
          hr.symm))))
    W r m

/-- The inverse image of a regular module is the regular inverse-image ring module,
with the comparison carrying the additive inverse-image unit to the ring unit.
Source: Stacks Project, Tags 008X and 008A.
(blueprint: stage3-inverse-image-regular-module).

Proof: On each source open, the regular module's additive group is the additive group
of the section ring. The filtered colimit defining presheaf inverse image commutes
with forgetting commutative rings to additive groups: both colimits identify local
representatives after passage to a common neighbourhood. The comparison sends a
representative to the same representative, and thus preserves the colimit units.
Sheafify this comparison. The associated additive sheaf of the inverse-image ring
is the sheafification of the underlying additive presheaf, since gluing and equality
are checked on the same locally represented sections. These two identifications
produce an additive sheaf isomorphism q preserving the inverse-image units.
Its linearity is checked on pairs of unit images: the inverse-image module unit is
semilinear, the ring unit preserves multiplication, and the original regular action
is multiplication. Both operations commute with restriction, so
inverseImageOperation_ext extends that identity to every pair of local sections.
The additive inverse is linear by applying q's injectivity. These maps give the
asserted module isomorphism and its unit formula. Empty opens and the zero ring
use the same colimit and sheafification comparisons. -/
theorem exists_inverseImage_regularModule_iso :
    ∃ e : inverseImageModule f R (SheafOfModules.unit (𝓡 R)) ≅
      SheafOfModules.unit (𝓡 (inverseImageRing f R)),
      ∀ (V : (Opens Y)ᵒᵖ) (d : R.obj.obj V),
        e.hom.val.app ((Opens.map f).op.obj V)
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map f) AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology X)).unit.app
              ((SheafOfModules.toSheaf (𝓡 R)).obj
                (SheafOfModules.unit (𝓡 R)))).hom.app V d) =
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map f) CommRingCat.{u} (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology X)).unit.app R).hom.app V d := by
  let q := inverseRegularAbIso f R
  let e : inverseImageModule f R (SheafOfModules.unit (𝓡 R)) ≅
      SheafOfModules.unit (𝓡 (inverseImageRing f R)) :=
    { hom := ⟨PresheafOfModules.homMk q.hom (inverseRegularAbIso_smul f R)⟩
      inv := ⟨PresheafOfModules.homMk q.inv (fun W r m ↦ by
        apply (ConcreteCategory.bijective_of_isIso (q.hom.app W)).1
        have hi (x : (inverseImageRing f R).obj.obj W) :
            q.hom.app W (q.inv.app W x) = x :=
          ConcreteCategory.congr_hom (NatTrans.congr_app q.inv_hom_id W) x
        let r' : (inverseImageRing f R).obj.obj W := r
        let m' : (inverseImageRing f R).obj.obj W := m
        let n : (inverseImageModule f R (SheafOfModules.unit (𝓡 R))).val.obj W :=
          q.inv.app W m
        exact (hi (r' * m')).trans ((congrArg (fun x ↦ r' * x) (hi m')).symm.trans
          (inverseRegularAbIso_smul f R W r' n).symm))⟩
      hom_inv_id := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact ConcreteCategory.congr_hom (NatTrans.congr_app q.hom_inv_id W) m
      inv_hom_id := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact ConcreteCategory.congr_hom (NatTrans.congr_app q.inv_hom_id W) m }
  exact ⟨e, inverseRegularAbIso_unit f R⟩

end
end TopCat.Sheaf
