/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Skyscraper modules on a ringed space

Source: Stacks Project, Sheaves, Tag 009A, case (4)
(blueprint: def-pc-ringed-module-skyscraper).

## Main definitions

* `SheafOfModules.ringedModuleSkyscraperFunctor`: skyscraper modules, also applied termwise.
-/

@[expose] public section

universe u_sky

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace SheafOfModules

variable (X : RingedSpace.{u_sky, u_sky}) (x : X)

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
The section type shared by ringed-space and scheme skyscraper modules. -/
abbrev ringedSkyscraperSectionsType (I : Type u_sky) (V : Opens X) : Type u_sky :=
  PLift (x ∈ V) → I

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
Sections are functions from the proposition that the open contains the chosen point:
a copy of the module when inhabited, and the zero group when empty. -/
abbrev RingedSkyscraperSections (M : ModuleCat.{u_sky} (X.presheaf.stalk x))
    (V : Opens X) : Type u_sky := ringedSkyscraperSectionsType X x M V

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
Scalars act through the germ at the point, componentwise on sections. -/
noncomputable instance ringedSkyscraperSectionsModule
    (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) (V : Opens X) :
    Module (((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf).obj.obj (op V))
      (RingedSkyscraperSections X x M V) :=
  letI (h : PLift (x ∈ V)) : Module (((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf).obj.obj (op V)) M :=
    Module.compHom M (X.presheaf.germ V x h.down).hom
  inferInstanceAs (Module (((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf).obj.obj (op V))
      (∀ _ : PLift (x ∈ V), M))

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
The underlying abelian presheaf has restriction given by precomposition of membership proofs. -/
abbrev ringedSkyscraperPresheafAbOfType (I : Type u_sky) [AddCommGroup I] :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u_sky} where
  obj V := AddCommGrpCat.of (ringedSkyscraperSectionsType X x I V.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := fun s h ↦ s ⟨f.unop.le h.down⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
The common abelian skyscraper construction on a bundled stalk module. -/
abbrev ringedSkyscraperPresheafAb (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u_sky} := ringedSkyscraperPresheafAbOfType X x M

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
The module structure on the bundled abelian presheaf values is the germ scalar action. -/
noncomputable instance ringedSkyscraperPresheafAb_module
    (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) (V : (Opens X)ᵒᵖ) :
    Module (((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf).obj.obj V)
      ((ringedSkyscraperPresheafAb X x M).obj V) :=
  ringedSkyscraperSectionsModule X x M V.unop

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
Restrictions are semilinear. Proof: evaluate at membership in the smaller open; the germ of
a restricted ring section equals the germ of the original section, so the scalar actions agree. -/
theorem ringedSkyscraperPresheafAb_smul
    (M : ModuleCat.{u_sky} (X.presheaf.stalk x))
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) (a : ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf).obj.obj V)
    (s : (ringedSkyscraperPresheafAb X x M).obj V) :
    (ringedSkyscraperPresheafAb X x M).map f (a • s) =
      ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf).obj.map f a •
        (ringedSkyscraperPresheafAb X x M).map f s := by
  funext h
  change (X.presheaf.germ V.unop x (f.unop.le h.down) a) • s ⟨f.unop.le h.down⟩ =
    (X.presheaf.germ W.unop x h.down (X.presheaf.map f a)) • s ⟨f.unop.le h.down⟩
  rw [X.presheaf.germ_res_apply' f x h.down a]

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
The skyscraper presheaf is a sheaf. Proof: on a cover, all components whose opens contain x
have the same value by compatibility on intersections. This common value glues the family;
when the open excludes x there is a unique section. Uniqueness follows on a cover member
containing x, or from the empty domain of the section function. -/
theorem ringedSkyscraperPresheafAbOfType_isSheaf (I : Type u_sky) [AddCommGroup I] :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (ringedSkyscraperPresheafAbOfType X x I) := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X.carrier)
    (ringedSkyscraperPresheafAbOfType X x I)).mpr
  intro ι U sf hsf
  choose index index_spec using fun h : PLift (x ∈ iSup U) ↦ Opens.mem_iSup.mp h.down
  let s : ringedSkyscraperSectionsType X x I (iSup U) :=
    fun h ↦ sf (index h) ⟨index_spec h⟩
  refine ⟨s, ?_, ?_⟩
  · intro i
    funext h
    exact congrFun (hsf (index ⟨(Opens.leSupr U i).le h.down⟩) i)
      ⟨⟨index_spec ⟨(Opens.leSupr U i).le h.down⟩, h.down⟩⟩
  · intro t ht
    funext h
    exact congrFun (ht (index h)) ⟨index_spec h⟩

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
Sheafness is inherited from the shared abelian skyscraper construction. -/
theorem ringedSkyscraperPresheafAb_isSheaf
    (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (ringedSkyscraperPresheafAb X x M) :=
  ringedSkyscraperPresheafAbOfType_isSheaf X x M

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
The skyscraper module, with its concrete section data and germ scalar action. -/
noncomputable abbrev ringedModuleSkyscraper
    (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) : SheafOfModules.{u_sky}
      ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf) where
  val := PresheafOfModules.ofPresheaf (ringedSkyscraperPresheafAb X x M)
    (fun {_ _} f a s ↦ ringedSkyscraperPresheafAb_smul X x M f a s)
  isSheaf := ringedSkyscraperPresheafAb_isSheaf X x M

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
A linear map acts pointwise on skyscraper sections; its scalar law is the original scalar law. -/
noncomputable def ringedModuleSkyscraperMap
    {M N : ModuleCat.{u_sky} (X.presheaf.stalk x)} (f : M ⟶ N) :
    ringedModuleSkyscraper X x M ⟶ ringedModuleSkyscraper X x N where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        { toFun := fun s h ↦ f (s h)
          map_add' := fun s t ↦ funext fun h ↦ f.hom.map_add (s h) (t h)
          map_smul' := fun a s ↦ funext fun h ↦
            f.hom.map_smul
              ((X.presheaf.germ V.unop x h.down) a)
              (s h) }
      naturality := fun _ ↦ rfl }

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
Skyscraper maps preserve identities. Proof: on each open and membership proof the induced
map is the identity on the value module; extensionality gives the equality. -/
theorem ringedModuleSkyscraperMap_id (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) :
    ringedModuleSkyscraperMap X x (𝟙 M) =
      (𝟙 (ringedModuleSkyscraper X x M) :
        ringedModuleSkyscraper X x M ⟶ ringedModuleSkyscraper X x M) := by
  rfl

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
Skyscraper maps preserve composition. Proof: evaluate the two sides on a section and a
membership proof; both are the composite of the original module maps. -/
theorem ringedModuleSkyscraperMap_comp
    {M N P : ModuleCat.{u_sky} (X.presheaf.stalk x)} (f : M ⟶ N) (g : N ⟶ P) :
    ringedModuleSkyscraperMap X x (f ≫ g) =
      ringedModuleSkyscraperMap X x f ≫ ringedModuleSkyscraperMap X x g := by
  rfl

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
The skyscraper functor from stalk modules to sheaves of modules on the ringed space.
Its extension by `Functor.mapHomologicalComplex` is the termwise skyscraper complex. -/
noncomputable def ringedModuleSkyscraperFunctor :
    ModuleCat.{u_sky} (X.presheaf.stalk x) ⥤ SheafOfModules.{u_sky}
      ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf) where
  obj M := ringedModuleSkyscraper X x M
  map f := ringedModuleSkyscraperMap X x f
  map_id := ringedModuleSkyscraperMap_id X x
  map_comp f g := ringedModuleSkyscraperMap_comp X x f g

/-- Stacks, Tag 009A (4) (blueprint: def-pc-ringed-module-skyscraper).
The skyscraper functor is additive. Proof: each map on sections is pointwise the input map,
so the image of a sum of module maps is the sum of the images, on every open. -/
theorem ringedModuleSkyscraperFunctor_additive :
    (ringedModuleSkyscraperFunctor X x).Additive := by
  constructor
  intro M N f g
  rfl

attribute [instance] ringedModuleSkyscraperFunctor_additive

end SheafOfModules
