/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.ModuleLift
public import WeilConjectures.CategoryTheory.Sites.SheafSmul
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-!
# Lifting morphisms of underlying abelian sheaves to sheaves of modules

A morphism of the underlying abelian sheaves of two sheaves of modules over a commutative ring `Λ`
commuting with the multiplications by the scalars is a morphism of sheaves of `Λ`-modules
(`CategoryTheory.Sheaf.homOfSheafComposeForget₂`); similarly for natural isomorphisms
(`CategoryTheory.Sheaf.isoOfSheafComposeForget₂`).

We also record how the action of global sections on module objects
(`CategoryTheory.Mod.sectionAct`) behaves under restriction of scalars
(`CategoryTheory.Mod.sectionAct_comap`) and under lax monoidal functors
(`CategoryTheory.Mod.sectionAct_mapMod`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory MonObj Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {Λ : Type w} [CommRing Λ]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- A morphism of the underlying abelian sheaves of two sheaves of `Λ`-modules commuting with the
multiplications by the scalars is a morphism of sheaves of `Λ`-modules. -/
noncomputable def homOfSheafComposeForget₂ {F G : Sheaf J (ModuleCat.{w} Λ)}
    (f : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G)
    (hf : ∀ c : Λ, (sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map (smulEnd F c) ≫ f =
      f ≫ (sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map (smulEnd G c)) :
    F ⟶ G where
  hom :=
    { app U := ModuleCat.ofHom
        { toFun := f.hom.app U
          map_add' := (f.hom.app U).hom.map_add
          map_smul' := fun c x ↦
            (ConcreteCategory.congr_hom
              (NatTrans.congr_app (Sheaf.hom_ext_iff.1 (hf c)) U) x) }
      naturality _ _ g := ModuleCat.hom_ext (LinearMap.ext fun x ↦
        ConcreteCategory.congr_hom (f.hom.naturality g) x) }

@[simp]
lemma sheafCompose_map_homOfSheafComposeForget₂ {F G : Sheaf J (ModuleCat.{w} Λ)}
    (f : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G) (hf) :
    (sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map (homOfSheafComposeForget₂ f hf) = f := by
  ext U x
  simp only [homOfSheafComposeForget₂]
  rfl

instance isIso_homOfSheafComposeForget₂ {F G : Sheaf J (ModuleCat.{w} Λ)}
    (f : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G) [IsIso f] (hf) :
    IsIso (homOfSheafComposeForget₂ f hf) := by
  have : IsIso ((sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map
      (homOfSheafComposeForget₂ f hf)) := by
    rw [sheafCompose_map_homOfSheafComposeForget₂]
    infer_instance
  exact isIso_of_reflects_iso _ (sheafCompose J (forget₂ _ AddCommGrpCat.{w}))

/-- A natural isomorphism of the underlying abelian sheaves of two functors to sheaves of
`Λ`-modules commuting with the multiplications by the scalars lifts to a natural isomorphism. -/
noncomputable def isoOfSheafComposeForget₂ {𝒜 : Type*} [Category* 𝒜]
    {P Q : 𝒜 ⥤ Sheaf J (ModuleCat.{w} Λ)}
    (e : P ⋙ sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≅
      Q ⋙ sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))
    (he : ∀ (a : 𝒜) (c : Λ),
      (sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map (smulEnd (P.obj a) c) ≫ e.hom.app a =
        e.hom.app a ≫ (sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map (smulEnd (Q.obj a) c)) :
    P ≅ Q :=
  NatIso.ofComponents (fun a ↦ asIso (homOfSheafComposeForget₂ (e.hom.app a) (he a)))
    fun {a b} f ↦ by
      ext U x
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (Sheaf.hom_ext_iff.1 (e.hom.naturality f)) U) x

@[simp]
lemma sheafCompose_map_isoOfSheafComposeForget₂_hom_app {𝒜 : Type*} [Category* 𝒜]
    {P Q : 𝒜 ⥤ Sheaf J (ModuleCat.{w} Λ)}
    (e : P ⋙ sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≅
      Q ⋙ sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})) (he) (a : 𝒜) :
    (sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map ((isoOfSheafComposeForget₂ e he).hom.app a) =
      e.hom.app a :=
  sheafCompose_map_homOfSheafComposeForget₂ _ (he a)

/-- On the lift `moduleLift P ρ hρ`, multiplication by `c` is the action `ρ a c`. -/
lemma sheafCompose_map_smulEnd_moduleLift_obj {𝒜 : Type*} [Category* 𝒜]
    (P : 𝒜 ⥤ Sheaf J AddCommGrpCat.{w}) (ρ : ∀ a, Λ →+* End (P.obj a))
    (hρ : ∀ {a b : 𝒜} (f : a ⟶ b) (c : Λ),
      (ρ a c).asHom ≫ P.map f = P.map f ≫ (ρ b c).asHom) (a : 𝒜) (c : Λ) :
    (sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map (smulEnd ((moduleLift P ρ hρ).obj a) c) =
      (ρ a c).asHom := by
  ext U x
  rfl

/-- The identification `moduleLiftCompIso` intertwines multiplication by `c` with `ρ a c`. -/
@[reassoc]
lemma sheafCompose_map_smulEnd_moduleLift_obj_comp_moduleLiftCompIso_hom_app {𝒜 : Type*}
    [Category* 𝒜] (P : 𝒜 ⥤ Sheaf J AddCommGrpCat.{w}) (ρ : ∀ a, Λ →+* End (P.obj a))
    (hρ : ∀ {a b : 𝒜} (f : a ⟶ b) (c : Λ),
      (ρ a c).asHom ≫ P.map f = P.map f ≫ (ρ b c).asHom) (a : 𝒜) (c : Λ) :
    (sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map (smulEnd ((moduleLift P ρ hρ).obj a) c) ≫
        (moduleLiftCompIso P ρ hρ).hom.app a =
      (moduleLiftCompIso P ρ hρ).hom.app a ≫ (ρ a c).asHom := by
  rw [moduleLiftCompIso_hom_app, sheafCompose_map_smulEnd_moduleLift_obj]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The identification `moduleLiftCompIso` intertwines `ρ a c` with multiplication by `c`. -/
@[reassoc]
lemma moduleLiftCompIso_inv_app_comp_sheafCompose_map_smulEnd {𝒜 : Type*}
    [Category* 𝒜] (P : 𝒜 ⥤ Sheaf J AddCommGrpCat.{w}) (ρ : ∀ a, Λ →+* End (P.obj a))
    (hρ : ∀ {a b : 𝒜} (f : a ⟶ b) (c : Λ),
      (ρ a c).asHom ≫ P.map f = P.map f ≫ (ρ b c).asHom) (a : 𝒜) (c : Λ) :
    (ρ a c).asHom ≫ (moduleLiftCompIso P ρ hρ).inv.app a =
      (moduleLiftCompIso P ρ hρ).inv.app a ≫
        (sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map
          (smulEnd ((moduleLift P ρ hρ).obj a) c) := by
  rw [moduleLiftCompIso_inv_app, sheafCompose_map_smulEnd_moduleLift_obj]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end CategoryTheory.Sheaf

/-! ### The action of global sections under change of rings -/

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- The action of a global section `t` of `R` on the restriction of scalars of `N` along
`φ : R ⟶ S` is the action of `t ≫ φ`. -/
lemma sectionAct_comap {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] (N : Mod C S)
    (t : 𝟙_ C ⟶ R) : sectionAct ((comap φ).obj N).X t = sectionAct N.X (t ≫ φ) := by
  change (λ_ N.X).inv ≫ t ▷ N.X ≫ φ ▷ N.X ≫ γ[S,N.X] =
    (λ_ N.X).inv ≫ (t ≫ φ) ▷ N.X ≫ γ[S,N.X]
  rw [comp_whiskerRight, Category.assoc]

/-- For a lax monoidal functor `F`, the action of the global section `ε ≫ F s` on `F M` is the
image under `F` of the action of `s` on `M`. -/
lemma sectionAct_mapMod {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D)
    [F.LaxMonoidal] {R : C} [MonObj R] (M : Mod C R) (s : 𝟙_ C ⟶ R) :
    sectionAct ((F.mapMod R).obj M).X (ε F ≫ F.map s) = F.map (sectionAct M.X s) := by
  change (λ_ (F.obj M.X)).inv ≫ (ε F ≫ F.map s) ▷ F.obj M.X ≫
      Functor.LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X] = F.map ((λ_ M.X).inv ≫ s ▷ M.X ≫ γ[R,M.X])
  have h := left_unitality_inv (F := F) M.X
  rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc, reassoc_of% h, Functor.map_comp,
    Functor.map_comp]

end CategoryTheory.Mod
