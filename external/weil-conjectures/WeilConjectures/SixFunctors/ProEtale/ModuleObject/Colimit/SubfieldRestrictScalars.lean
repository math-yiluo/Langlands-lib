/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIso
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComapFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStarDeligne

/-!
# Extension and restriction of scalars along `E_X ⟶ F_X` on bounded constructible complexes

Let `E ≤ F` be finite subextensions of `ℚ̄_ℓ / ℚ_ℓ` and `X` a scheme.

* Since `F_X` is finite free over `E_X`
  (`ProEtale.CondensedRing.exists_comap_regular_iso_finiteFree`), the restriction of scalars
  `D(Res)` along `E_X ⟶ F_X` preserves bounded constructible complexes
  (`ProEtale.CondensedRing.boundedConstructible_restrictScalarsSubfield_obj`): it is exact, so it
  commutes with the cohomology sheaves, it commutes with the pullbacks to the strata and to the
  members of pro-étale covers, and it sends finitely presented `F`-modules to finitely presented
  `E`-modules.
* Hence restriction of scalars restricts to a functor
  `ProEtale.CondensedRing.boundedConstructibleRestrictScalarsSubfield X ℓ h` on the categories
  `Dᵇc(X)⟦Λ⟧`, which reflects isomorphisms, and right adjoint to the extension of scalars
  `ProEtale.CondensedRing.boundedConstructibleExtendScalarsSubfield X ℓ h` (the functor
  `ProEtale.constructibleExtendScalars`, typed on the categories `Dᵇc(X)⟦Λ⟧`)
  (`ProEtale.CondensedRing.boundedConstructibleExtendRestrictScalarsSubfieldAdjunction`).
* **(Push)** for a morphism `g : Z ⟶ Y` of separated `k`-schemes of finite type: restriction of
  scalars commutes with `Rg_*` on bounded constructible complexes
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarRestrictScalarsSubfieldIso`), and its mate
  `Rg_*^E ⋙ T_Y ⟶ T_Z ⋙ Rg_*^F`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarExtendScalarsSubfield`) is, on the
  underlying complexes, the (Push) comparison `ProEtale.CondensedRing.derivedPushHom` of the
  unbounded derived categories
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarExtendScalarsSubfield_app_hom`); in
  particular it is an isomorphism.
-/

@[expose] public section


universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {PA : ObjectProperty A} {PB : ObjectProperty B} {PA' : ObjectProperty A'}
  {PB' : ObjectProperty B'}
  {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁)
  {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'} (adj₂ : E₂ ⊣ Res₂)
  {L₁ : A ⥤ A'} {L₂ : B ⥤ B'} (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁)
  (hE₁ : ∀ K : PA.FullSubcategory, PB ((PA.ι ⋙ E₁).obj K))
  (hRes₁ : ∀ K : PB.FullSubcategory, PA ((PB.ι ⋙ Res₁).obj K))
  (hE₂ : ∀ K : PA'.FullSubcategory, PB' ((PA'.ι ⋙ E₂).obj K))
  (hRes₂ : ∀ K : PB'.FullSubcategory, PA' ((PB'.ι ⋙ Res₂).obj K))
  (hL₁ : ∀ K : PA.FullSubcategory, PA' ((PA.ι ⋙ L₁).obj K))
  (hL₂ : ∀ K : PB.FullSubcategory, PB' ((PB.ι ⋙ L₂).obj K))

/-- **Mates of restrictions to full subcategories.** Consider adjunctions `E₁ ⊣ Res₁ : A ⇄ B` and
`E₂ ⊣ Res₂ : A' ⇄ B'`, functors `L₁ : A ⥤ A'`, `L₂ : B ⥤ B'` and an isomorphism
`e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁`, all of which preserve full subcategories `PA`, `PB`, `PA'`, `PB'`,
so that the adjunctions restrict to the full subcategories (`Adjunction.restrictFullyFaithful`).
If `e'` is an isomorphism of the restricted functors which is `e` on the underlying objects, then
the mate `L₁ ⋙ E₂ ⟶ E₁ ⋙ L₂` of `e'` (`Adjunction.pushHomOfComapIso`) is, on the underlying
objects, the mate of `e`. -/
lemma pushHomOfComapIso_restrictFullyFaithful_app_hom
    (e' : PB'.lift (PB.ι ⋙ L₂) hL₂ ⋙ PA'.lift (PB'.ι ⋙ Res₂) hRes₂ ≅
      PA.lift (PB.ι ⋙ Res₁) hRes₁ ⋙ PA'.lift (PA.ι ⋙ L₁) hL₁)
    (he' : ∀ K, (e'.hom.app K).hom = e.hom.app K.obj) (K : PA.FullSubcategory) :
    ((pushHomOfComapIso
        (adj₁.restrictFullyFaithful PA.fullyFaithfulι PB.fullyFaithfulι
          (PB.liftCompιIso (PA.ι ⋙ E₁) hE₁).symm (PA.liftCompιIso (PB.ι ⋙ Res₁) hRes₁).symm)
        (adj₂.restrictFullyFaithful PA'.fullyFaithfulι PB'.fullyFaithfulι
          (PB'.liftCompιIso (PA'.ι ⋙ E₂) hE₂).symm (PA'.liftCompιIso (PB'.ι ⋙ Res₂) hRes₂).symm)
        e').app K).hom =
      (pushHomOfComapIso adj₁ adj₂ e).app K.obj := by
  have he'' (K : PB.FullSubcategory) : (e'.inv.app K).hom = e.inv.app K.obj := by
    rw [← cancel_mono (e.hom.app K.obj), ← he', ← ObjectProperty.FullSubcategory.comp_hom,
      Iso.inv_hom_id_app, he', Iso.inv_hom_id_app]
    rfl
  have hu : ((adj₁.restrictFullyFaithful PA.fullyFaithfulι PB.fullyFaithfulι
      (PB.liftCompιIso (PA.ι ⋙ E₁) hE₁).symm (PA.liftCompιIso (PB.ι ⋙ Res₁) hRes₁).symm).unit.app
        K).hom = adj₁.unit.app K.obj := by
    simpa [ObjectProperty.liftCompιIso] using map_restrictFullyFaithful_unit_app adj₁
      PA.fullyFaithfulι PB.fullyFaithfulι
      (PB.liftCompιIso (PA.ι ⋙ E₁) hE₁).symm (PA.liftCompιIso (PB.ι ⋙ Res₁) hRes₁).symm K
  have hc (K' : PB'.FullSubcategory) : ((adj₂.restrictFullyFaithful PA'.fullyFaithfulι
      PB'.fullyFaithfulι (PB'.liftCompιIso (PA'.ι ⋙ E₂) hE₂).symm
      (PA'.liftCompιIso (PB'.ι ⋙ Res₂) hRes₂).symm).counit.app K').hom =
        adj₂.counit.app K'.obj := by
    simpa [ObjectProperty.liftCompιIso] using map_restrictFullyFaithful_counit_app adj₂
      PA'.fullyFaithfulι PB'.fullyFaithfulι
      (PB'.liftCompιIso (PA'.ι ⋙ E₂) hE₂).symm (PA'.liftCompιIso (PB'.ι ⋙ Res₂) hRes₂).symm K'
  simp [pushHomOfComapIso, mateEquiv, hu, hc, he'']
end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-! ### Restriction of scalars preserves constructibility -/

section Constructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)

/-- Restriction of scalars along `E_X ⟶ F_X` preserves finitely presented module objects, `F_X`
being finite free over `E_X`. -/
lemma isFinitelyPresented_comap_padicSubfieldRingObjMap {X : Scheme.{u}}
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)}
    (hN : Mod.IsFinitelyPresented (padicSubfieldRingObj X ℓ F) N) :
    Mod.IsFinitelyPresented (padicSubfieldRingObj X ℓ E)
      ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj N) := by
  obtain ⟨d, hd⟩ := exists_comap_regular_iso_finiteFree ℓ h
  exact hN.comap_of_finiteFree _ (hd X).some

/-- Restriction of scalars along `E_X ⟶ F_X` preserves pro-étale locally finitely presented
module objects: it commutes with the pullbacks to the members of a pro-étale cover. -/
lemma isLocallyFinitelyPresented_comap_padicSubfieldRingObjMap {X : Scheme.{u}}
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)}
    (hN : IsLocallyFinitelyPresented (padicSubfieldRingObj X ℓ F) N) :
    IsLocallyFinitelyPresented (padicSubfieldRingObj X ℓ E)
      ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj N) := by
  obtain ⟨𝒰, h𝒰⟩ := hN
  refine ⟨𝒰, fun i ↦ (isFinitelyPresented_mapMod_iff (Profinite.continuousMapRingObj E) _ _).2 ?_⟩
  have e := (comapUpperStarIso (Profinite.padicSubfieldRingObjMap ℓ h) (𝒰.f i)).app N
  dsimp only [Functor.comp_obj] at e
  have h₁ := (isFinitelyPresented_mapMod_iff (Profinite.continuousMapRingObj F) _ _).1 (h𝒰 i)
  have h₂ := isFinitelyPresented_comap_padicSubfieldRingObjMap ℓ h h₁
  exact h₂.of_iso e

/-- Restriction of scalars along `E_X ⟶ F_X` preserves constructible module objects: it
commutes with the pullbacks to the strata of a stratification. -/
lemma isConstructibleModuleObject_comap_padicSubfieldRingObjMap {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)}
    (hM : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ F) M) :
    IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E)
      ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦
    (isLocallyFinitelyPresented_mapMod_iff (Profinite.continuousMapRingObj E) _ _).2 ?_⟩
  exact IsLocallyFinitelyPresented.of_iso
    ((comapUpperStarIso (Profinite.padicSubfieldRingObjMap ℓ h) (S.immersion a)).app M)
    (isLocallyFinitelyPresented_comap_padicSubfieldRingObjMap ℓ h
      ((isLocallyFinitelyPresented_mapMod_iff (Profinite.continuousMapRingObj F) _ _).1 (hS a)))

end Constructible

/-! ### Restriction and extension of scalars on bounded constructible complexes -/

section BoundedConstructible

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)

/-- Restriction of scalars `D(Res)` along `E_X ⟶ F_X` preserves bounded constructible complexes:
it is exact, hence preserves boundedness and commutes with the cohomology sheaves, and it
preserves constructible module objects. -/
lemma boundedConstructible_restrictScalarsSubfield_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ F) K) :
    boundedConstructible (padicSubfieldRingObj X ℓ E)
      ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory.obj K) :=
  ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦
    IsConstructibleModuleObject.of_iso
      (((Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategoryHomologyFunctorIso n).app K)
      (isConstructibleModuleObject_comap_padicSubfieldRingObjMap ℓ h (hK.2 n))⟩

/-- The restriction of scalars `D(Res) : Dᵇc(X)⟦F⟧ ⥤ Dᵇc(X)⟦E⟧` along `E_X ⟶ F_X` on bounded
constructible complexes. -/
noncomputable def boundedConstructibleRestrictScalarsSubfield :
    Dᵇc(X)⟦Profinite.continuousMapRingObj F⟧ ⥤ Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory)
    fun K ↦ boundedConstructible_restrictScalarsSubfield_obj X ℓ h K.obj K.property

/-- The restriction of scalars on bounded constructible complexes is compatible with the
inclusions. -/
noncomputable def boundedConstructibleRestrictScalarsSubfieldCompatibility :
    boundedConstructibleRestrictScalarsSubfield X ℓ h ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

/-- The restriction of scalars along `E_X ⟶ F_X` on the derived categories reflects
isomorphisms. -/
instance reflectsIsomorphisms_mapDerivedCategory_comap_padicSubfieldRingObjMap :
    (Mod.comap (padicSubfieldRingObjMap X ℓ h) :
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F) ⥤
        Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)
      ).mapDerivedCategory.ReflectsIsomorphisms :=
  Functor.reflectsIsomorphisms_mapDerivedCategory_of_faithful _

/-- The restriction of scalars on bounded constructible complexes reflects isomorphisms, as the
restriction of scalars on the derived categories does. -/
instance reflectsIsomorphisms_boundedConstructibleRestrictScalarsSubfield :
    (boundedConstructibleRestrictScalarsSubfield X ℓ h).ReflectsIsomorphisms where
  reflects {K L} f _ := by
    have : IsIso ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory.map f.hom) :=
      inferInstanceAs (IsIso ((boundedConstructible _).ι.map
        ((boundedConstructibleRestrictScalarsSubfield X ℓ h).map f)))
    have : IsIso ((boundedConstructible _).ι.map f) :=
      isIso_of_reflects_iso f.hom (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory
    exact isIso_of_reflects_iso f (boundedConstructible _).ι

/-- The extension of scalars `T_{E,F} : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦F⟧` on bounded constructible
complexes: the functor `ProEtale.constructibleExtendScalars`, typed on the categories `Dᵇc(X)⟦Λ⟧`
of the six operations rather than on `ProEtale.PadicSubfieldConstructible`. -/
noncomputable def boundedConstructibleExtendScalarsSubfield :
    Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(X)⟦Profinite.continuousMapRingObj F⟧ :=
  constructibleExtendScalars X ℓ h

lemma boundedConstructibleExtendScalarsSubfield_eq :
    boundedConstructibleExtendScalarsSubfield X ℓ h = constructibleExtendScalars X ℓ h :=
  rfl

/-- The extension of scalars on bounded constructible complexes is compatible with the
inclusions. -/
noncomputable def boundedConstructibleExtendScalarsSubfieldCompatibility :
    boundedConstructibleExtendScalarsSubfield X ℓ h ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ derivedExtendScalarsSubfield X ℓ h :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `T_{E,F} ⊣ D(Res)` on bounded constructible complexes: the restriction of
`Mod.derivedExtendMapDerivedCategoryAdjunction` along the fully faithful inclusions. -/
noncomputable def boundedConstructibleExtendRestrictScalarsSubfieldAdjunction :
    boundedConstructibleExtendScalarsSubfield X ℓ h ⊣
      boundedConstructibleRestrictScalarsSubfield X ℓ h :=
  Adjunction.restrictFullyFaithful
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap X ℓ h))
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleExtendScalarsSubfieldCompatibility X ℓ h).symm
    (boundedConstructibleRestrictScalarsSubfieldCompatibility X ℓ h).symm

end BoundedConstructible

/-! ### (Push) on bounded constructible complexes -/

section LowerStar

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y)

/-- Restriction of scalars along `E ≤ F` commutes with the derived pushforward on bounded
constructible complexes: `Rg_*^F ⋙ D(Res_Y) ≅ D(Res_Z) ⋙ Rg_*^E`, the restriction of
`ProEtale.CondensedRing.derivedComapLowerStarIso` along the fully faithful inclusions. -/
noncomputable def boundedConstructibleLowerStarRestrictScalarsSubfieldIso :
    ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g ⋙
        boundedConstructibleRestrictScalarsSubfield Y.left ℓ h ≅
      boundedConstructibleRestrictScalarsSubfield Z.left ℓ h ⋙
        ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((derivedComapLowerStarIso (Profinite.padicSubfieldRingObjMap ℓ h) g.left).app K.obj))
    (fun f ↦ (ObjectProperty.fullyFaithfulι _).map_injective
      ((derivedComapLowerStarIso (Profinite.padicSubfieldRingObjMap ℓ h) g.left).hom.naturality
        f.hom))

/-- The isomorphism `boundedConstructibleLowerStarRestrictScalarsSubfieldIso` is, on the
underlying complexes, `ProEtale.CondensedRing.derivedComapLowerStarIso`. -/
lemma boundedConstructibleLowerStarRestrictScalarsSubfieldIso_hom_app_hom
    (K : Dᵇc(Z.left)⟦Profinite.continuousMapRingObj F⟧) :
    ((boundedConstructibleLowerStarRestrictScalarsSubfieldIso ℓ h g).hom.app K).hom =
      (derivedComapLowerStarIso (Profinite.padicSubfieldRingObjMap ℓ h) g.left).hom.app K.obj :=
  rfl

/-- **(Push)** on bounded constructible complexes, for finite subextensions `E ≤ F`: the
canonical comparison `Rg_*^E ⋙ T_Y ⟶ T_Z ⋙ Rg_*^F`, the mate of
`boundedConstructibleLowerStarRestrictScalarsSubfieldIso` along the adjunctions
`T ⊣ D(Res)`. -/
noncomputable def boundedConstructibleLowerStarExtendScalarsSubfield :
    ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g ⋙
        boundedConstructibleExtendScalarsSubfield Y.left ℓ h ⟶
      boundedConstructibleExtendScalarsSubfield Z.left ℓ h ⋙
        ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g :=
  Adjunction.pushHomOfComapIso
    (boundedConstructibleExtendRestrictScalarsSubfieldAdjunction Z.left ℓ h)
    (boundedConstructibleExtendRestrictScalarsSubfieldAdjunction Y.left ℓ h)
    (boundedConstructibleLowerStarRestrictScalarsSubfieldIso ℓ h g)

/-- **(Push)** on bounded constructible complexes is, on the underlying complexes, the (Push)
comparison `ProEtale.CondensedRing.derivedPushHom` of the unbounded derived categories. -/
lemma boundedConstructibleLowerStarExtendScalarsSubfield_app_hom
    (K : Dᵇc(Z.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleLowerStarExtendScalarsSubfield ℓ h g).app K).hom =
      (derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ h) g.left).app K.obj := by
  have H := Adjunction.pushHomOfComapIso_restrictFullyFaithful_app_hom
    (PA := boundedConstructible (padicSubfieldRingObj Z.left ℓ E))
    (PB := boundedConstructible (padicSubfieldRingObj Z.left ℓ F))
    (PA' := boundedConstructible (padicSubfieldRingObj Y.left ℓ E))
    (PB' := boundedConstructible (padicSubfieldRingObj Y.left ℓ F))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap Z.left ℓ h))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap Y.left ℓ h))
    (derivedComapLowerStarIso (Profinite.padicSubfieldRingObjMap ℓ h) g.left)
    (fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj Z.left ℓ h K)
    (fun K ↦ boundedConstructible_restrictScalarsSubfield_obj Z.left ℓ h K.obj K.property)
    (fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj Y.left ℓ h K)
    (fun K ↦ boundedConstructible_restrictScalarsSubfield_obj Y.left ℓ h K.obj K.property)
    (fun K ↦ ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E g K)
    (fun K ↦ ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ F g K)
    (boundedConstructibleLowerStarRestrictScalarsSubfieldIso ℓ h g)
    (boundedConstructibleLowerStarRestrictScalarsSubfieldIso_hom_app_hom ℓ h g) K
  unfold boundedConstructibleLowerStarExtendScalarsSubfield
    boundedConstructibleExtendRestrictScalarsSubfieldAdjunction
    boundedConstructibleExtendScalarsSubfieldCompatibility
    boundedConstructibleRestrictScalarsSubfieldCompatibility
    boundedConstructibleExtendScalarsSubfield constructibleExtendScalars
    boundedConstructibleRestrictScalarsSubfield ContinuousMapRingObj.boundedConstructibleLowerStar
    derivedPushHom
  with_reducible_and_instances exact H

/-- **(Push)** on bounded constructible complexes is an isomorphism, as the (Push) comparison
of the unbounded derived categories is one for a finite extension `F/E`
(`ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjMap`). -/
instance isIso_boundedConstructibleLowerStarExtendScalarsSubfield :
    IsIso (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h g) := by
  have (K : Dᵇc(Z.left)⟦Profinite.continuousMapRingObj E⟧) :
      IsIso ((boundedConstructibleLowerStarExtendScalarsSubfield ℓ h g).app K) := by
    rw [← ObjectProperty.isIso_hom_iff,
      boundedConstructibleLowerStarExtendScalarsSubfield_app_hom]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end LowerStar

end AlgebraicGeometry.ProEtale.CondensedRing
