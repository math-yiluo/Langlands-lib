/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal

/-!
# The tensor comparison of module objects along a lax braided functor

Let `G : D ⥤ C` be a lax braided functor between braided monoidal categories with
coequalizers preserved by tensoring, and `R : D` a commutative algebra object. Transport of
module objects `G.mapMod R : Mod D R ⥤ Mod C (G R)` receives the comparison map
```
G M ⊗_{G R} G N ⟶ G (M ⊗_R N)
```
(`CategoryTheory.Functor.mapModLaxTensorHom`), induced on the coequalizers presenting the
relative tensor products by the tensorator `μ G M N : G M ⊗ G N ⟶ G (M ⊗ N)`
(`CategoryTheory.Functor.tensorObjπ_mapModLaxTensorHom_hom`).

If `G` is the right adjoint of a braided strong monoidal functor `F` by a monoidal adjunction,
and `G.mapMod R` is an equivalence, then this comparison is an isomorphism
(`CategoryTheory.Functor.isIso_mapModLaxTensorHom`). The proof uses the left adjoint
`M ↦ R ⊗_{F (G R)} F M` of `G.mapMod R`, which is strong monoidal: the comparison map is the
mate of its comonoidal structure, and mates along an adjoint equivalence of isomorphisms are
isomorphisms.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory BraidedCategory MonObj Limits Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  [HasCoequalizers D] [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

section Lax

variable [BraidedCategory D] (G : D ⥤ C) [G.LaxBraided] {R : D} [MonObj R] [IsCommMonObj R]

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The composite `G M ⊗ G N ⟶ G (M ⊗ N) ⟶ G (M ⊗_R N)` is balanced for the two actions of
`G R`, for a lax braided functor `G`. -/
lemma mapMod_laxμ_balanced (M N : Mod D R) :
    ((β_ ((G.mapMod R).obj M).X (G.obj R)).hom ≫ γ[G.obj R, ((G.mapMod R).obj M).X]) ▷
        ((G.mapMod R).obj N).X ≫ LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorObjπ M N) =
      ((α_ ((G.mapMod R).obj M).X (G.obj R) ((G.mapMod R).obj N).X).hom ≫
        ((G.mapMod R).obj M).X ◁ γ[G.obj R, ((G.mapMod R).obj N).X]) ≫
          LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorObjπ M N) := by
  dsimp only [Functor.mapMod]
  simp only [G.modObjObj_smul]
  simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [μ_natural_left_assoc, μ_natural_right_assoc]
  slice_lhs 1 2 => rw [← comp_whiskerRight, ← Functor.LaxBraided.braided]
  simp only [comp_whiskerRight, Category.assoc]
  rw [μ_natural_left_assoc, ← associativity_assoc]
  simp only [← G.map_comp]
  have h := Mod.tensorObjπ_condition M N
  simp only [comp_whiskerRight, Category.assoc] at h
  rw [h]

/-- The comparison `G M ⊗_{G R} G N ⟶ G (M ⊗_R N)` on underlying objects, induced by the
tensorator `μ G M N`. -/
noncomputable def mapModLaxTensorHomX (M N : Mod D R) :
    ((G.mapMod R).obj M ⊗ (G.mapMod R).obj N).X ⟶ ((G.mapMod R).obj (M ⊗ N)).X :=
  Mod.tensorObjDesc _ _ (LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorObjπ M N))
    (G.mapMod_laxμ_balanced M N)

@[reassoc]
lemma tensorObjπ_mapModLaxTensorHomX (M N : Mod D R) :
    Mod.tensorObjπ ((G.mapMod R).obj M) ((G.mapMod R).obj N) ≫ G.mapModLaxTensorHomX M N =
      LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorObjπ M N) :=
  Mod.tensorObjπ_tensorObjDesc _ _ _ _

/-- The comparison `G M ⊗_{G R} G N ⟶ G (M ⊗_R N)` is `G R`-linear. -/
lemma mapModLaxTensorHomX_linear (M N : Mod D R) :
    γ[G.obj R, ((G.mapMod R).obj M ⊗ (G.mapMod R).obj N).X] ≫ G.mapModLaxTensorHomX M N =
      G.obj R ◁ G.mapModLaxTensorHomX M N ≫ γ[G.obj R, ((G.mapMod R).obj (M ⊗ N)).X] := by
  rw [← cancel_epi (G.obj R ◁ Mod.tensorObjπ ((G.mapMod R).obj M) ((G.mapMod R).obj N)),
    Mod.whiskerLeft_tensorπ_smul_assoc, tensorObjπ_mapModLaxTensorHomX,
    ← MonoidalCategory.whiskerLeft_comp_assoc, tensorObjπ_mapModLaxTensorHomX]
  change (α_ (G.obj R) (G.obj M.X) (G.obj N.X)).inv ≫
      (LaxMonoidal.μ G R M.X ≫ G.map γ[R,M.X]) ▷ G.obj N.X ≫
        LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorObjπ M N) =
    G.obj R ◁ (LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorObjπ M N)) ≫
      LaxMonoidal.μ G R (M ⊗ N).X ≫ G.map γ[R,(M ⊗ N).X]
  simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [μ_natural_left_assoc, μ_natural_right_assoc]
  simp only [← G.map_comp]
  rw [Mod.whiskerLeft_tensorπ_smul]
  simp only [G.map_comp]
  rw [associativity_inv_assoc]

/-- The `G R`-linear comparison `G M ⊗_{G R} G N ⟶ G (M ⊗_R N)` of module objects along a lax
braided functor `G`, induced by the tensorator `μ G M N`. -/
noncomputable def mapModLaxTensorHom (M N : Mod D R) :
    (G.mapMod R).obj M ⊗ (G.mapMod R).obj N ⟶ (G.mapMod R).obj (M ⊗ N) :=
  Mod.homMk (G.mapModLaxTensorHomX M N) (G.mapModLaxTensorHomX_linear M N)

/-- On the projection `G M ⊗ G N ⟶ G M ⊗_{G R} G N`, the comparison
`G.mapModLaxTensorHom M N` is the tensorator of `G` followed by `G` of the projection
`M ⊗ N ⟶ M ⊗_R N`. -/
@[reassoc (attr := simp)]
lemma tensorObjπ_mapModLaxTensorHom_hom (M N : Mod D R) :
    Mod.tensorObjπ ((G.mapMod R).obj M) ((G.mapMod R).obj N) ≫ (G.mapModLaxTensorHom M N).hom =
      LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorObjπ M N) :=
  G.tensorObjπ_mapModLaxTensorHomX M N

/-- The comparison `G M ⊗_{G R} G N ⟶ G (M ⊗_R N)` is natural in both module objects. -/
@[reassoc]
lemma mapModLaxTensorHom_natural {M M' N N' : Mod D R} (f : M ⟶ M') (g : N ⟶ N') :
    ((G.mapMod R).map f ⊗ₘ (G.mapMod R).map g) ≫ G.mapModLaxTensorHom M' N' =
      G.mapModLaxTensorHom M N ≫ (G.mapMod R).map (f ⊗ₘ g) := by
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.tensorObjπ ((G.mapMod R).obj M) ((G.mapMod R).obj N)),
    Mod.comp_hom', Mod.comp_hom', MonoidalCategory.tensorHom_def ((G.mapMod R).map f),
    MonoidalCategory.tensorHom_def f, Functor.map_comp]
  simp only [Mod.comp_hom', Category.assoc]
  rw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft_assoc,
    tensorObjπ_mapModLaxTensorHom_hom, tensorObjπ_mapModLaxTensorHom_hom_assoc]
  change G.map f.hom ▷ G.obj N.X ≫ G.obj M'.X ◁ G.map g.hom ≫ LaxMonoidal.μ G M'.X N'.X ≫
      G.map (Mod.tensorObjπ M' N') = LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorObjπ M N) ≫
        G.map (f ▷ N).hom ≫ G.map (M' ◁ g).hom
  rw [μ_natural_right_assoc, μ_natural_left_assoc]
  simp only [← G.map_comp, Mod.tensorObjπ_whiskerRight_assoc,
    Mod.tensorObjπ_whiskerLeft]

section Comap

variable {S : C} [MonObj S] [IsCommMonObj S] (ψ : S ⟶ G.obj R) [IsMonHom ψ] [IsIso ψ]
  [∀ M N : Mod D R, IsIso (G.mapModLaxTensorHom M N)]

/-- The tensor comparison `ψ^* G M ⊗_S ψ^* G N ≅ ψ^* G (M ⊗_R N)` of transport of module objects
along a lax braided functor `G` followed by restriction of scalars along an isomorphism
`ψ : S ⟶ G R`, when the comparison `G.mapModLaxTensorHom` is invertible. -/
noncomputable def mapModComapTensorIso (M N : Mod D R) :
    (G.mapMod R ⋙ Mod.comap ψ).obj M ⊗ (G.mapMod R ⋙ Mod.comap ψ).obj N ≅
      (G.mapMod R ⋙ Mod.comap ψ).obj (M ⊗ N) :=
  Mod.comapTensorIso ψ _ _ ≪≫ (Mod.comap ψ).mapIso (asIso (G.mapModLaxTensorHom M N))

/-- On the projection onto the relative tensor product, `G.mapModComapTensorIso ψ M N` is the
tensorator of `G` followed by `G` of the projection `M ⊗ N ⟶ M ⊗_R N`. -/
@[reassoc (attr := simp)]
lemma tensorObjπ_mapModComapTensorIso_hom_hom (M N : Mod D R) :
    Mod.tensorObjπ ((G.mapMod R ⋙ Mod.comap ψ).obj M) ((G.mapMod R ⋙ Mod.comap ψ).obj N) ≫
        (G.mapModComapTensorIso ψ M N).hom.hom =
      LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorObjπ M N) := by
  rw [mapModComapTensorIso, Iso.trans_hom, Mod.comp_hom']
  erw [Mod.tensorπ_comapTensorIso_hom_hom_assoc]
  exact G.tensorObjπ_mapModLaxTensorHom_hom M N

/-- The comparison `G.mapModComapTensorIso ψ M N` is natural in both module objects. -/
@[reassoc]
lemma mapModComapTensorIso_hom_natural {M M' N N' : Mod D R} (f : M ⟶ M') (g : N ⟶ N') :
    ((G.mapMod R ⋙ Mod.comap ψ).map f ⊗ₘ (G.mapMod R ⋙ Mod.comap ψ).map g) ≫
        (G.mapModComapTensorIso ψ M' N').hom =
      (G.mapModComapTensorIso ψ M N).hom ≫ (G.mapMod R ⋙ Mod.comap ψ).map (f ⊗ₘ g) := by
  have h := LaxMonoidal.μ_natural (Mod.comap ψ) ((G.mapMod R).map f) ((G.mapMod R).map g)
  dsimp only [mapModComapTensorIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.comp_map]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← mapModLaxTensorHom_natural, Functor.map_comp]
  exact (reassoc_of% h) _

end Comap

end Lax
section Adjunction

variable [SymmetricCategory D] {F : C ⥤ D} {G : D ⥤ C} [F.Braided] [G.LaxBraided]
  [PreservesColimitsOfShape WalkingParallelPair F] (R : D) [MonObj R] [IsCommMonObj R]

/-- The comparison `G M ⊗_{G R} G N ⟶ G (M ⊗_R N)` is an isomorphism when `G` is the right
adjoint of a braided monoidal functor by a monoidal adjunction and `G.mapMod R` is an
equivalence. -/
theorem isIso_mapModLaxTensorHom (a : F ⊣ G) [a.IsMonoidal] [(G.mapMod R).IsEquivalence]
    (M N : Mod D R) :
    IsIso (G.mapModLaxTensorHom M N) := by
  let A := G.obj R
  let φ := a.counitAlgHom R
  obtain ⟨m, hm⟩ := Mod.exists_extendScalarsMonoidal φ
  let : (Mod.extendScalars φ).Monoidal := m
  let L := F.mapMod A ⋙ Mod.extendScalars φ
  let : L.Monoidal := inferInstanceAs (F.mapMod A ⋙ Mod.extendScalars φ).Monoidal
  let r : Mod.comap φ ⋙ (G.mapMod (F.obj A) ⋙ Mod.comap (a.unitAlgHom A)) ≅ G.mapMod R :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapModComapIso φ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Mod.comapComp _ _).symm ≪≫
        Mod.comapCongr (a.right_triangle_components R) ≪≫ Mod.comapId _)
  let b : L ⊣ G.mapMod R :=
    ((a.mapModAdjunction A).comp (Mod.extendRestrictAdjunction φ)).ofNatIsoRight r
  have : L.IsEquivalence := b.isEquivalence_left_of_isEquivalence_right
  have hunit (P : Mod C A) : (b.unit.app P).hom =
      a.unit.app P.X ≫ G.map (Mod.extendUnitHom φ ((F.mapMod A).obj P)) := by
    simp only [id_obj, comp_obj, isoWhiskerLeft_trans, Adjunction.ofNatIsoRight_unit,
      Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerLeft_comp,
      whiskerLeft_twice, Category.assoc, Iso.hom_inv_id_assoc, NatTrans.comp_app,
      Adjunction.comp_unit_app, comp_map, mapMod_map, Mod.extendRestrictAdjunction_unit_app_hom,
      whiskerLeft_app, associator_inv_app, whiskerRight_app, associator_hom_app, Category.comp_id,
      Category.id_comp, Mod.comp_hom', Adjunction.mapModAdjunction_unit_app_hom, Mod.comap_map_hom,
      Mod.homMk_hom, mapModComapIso_hom_app_hom, Mod.id_hom', Mod.comapComp_inv_app_hom,
      Mod.comapCongr_hom_app_hom, Mod.comapId_hom_app_hom, b, r]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id]
  have hcounit (M : Mod D R) : Mod.extendUnitHom φ ((F.mapMod A).obj ((G.mapMod R).obj M)) ≫
      (b.counit.app M).hom = a.counit.app M.X := by
    rw [← b.homEquiv_symm_id]
    dsimp only [b]
    rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, Adjunction.comp_homEquiv,
      Equiv.symm_trans_apply]
    dsimp only [Mod.extendRestrictAdjunction, Adjunction.mapModAdjunction]
    rw [Adjunction.mkOfHomEquiv_homEquiv, Adjunction.mkOfHomEquiv_homEquiv]
    simp only [id_obj, comp_obj, Adjunction.homEquiv_counit, Equiv.symm_mk, isoWhiskerLeft_trans,
      Iso.trans_inv, isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc, isoWhiskerRight_inv,
      NatTrans.comp_app, whiskerLeft_app, associator_inv_app, whiskerRight_app, associator_hom_app,
      Category.comp_id, Category.id_comp, Equiv.coe_fn_mk, Mod.comp_hom', Mod.comapId_inv_app_hom,
      Mod.comapCongr_inv_app_hom, Mod.comapComp_hom_app_hom, Mod.comap_map_hom,
      mapModComapIso_inv_app_hom, map_comp, map_id, r]
    erw [Mod.extendHomEquiv_symm_apply, Mod.extendUnitHom_extendHom]
    exact (by simp : F.map (𝟙 (G.obj M.X)) ≫ F.map (𝟙 (G.obj M.X)) ≫ a.counit.app M.X =
      a.counit.app M.X)
  have he {X Y : Mod D (F.obj A)} (g : X ⟶ Y) :
      Mod.extendUnitHom φ X ≫ ((Mod.extendScalars φ).map g).hom =
        g.hom ≫ Mod.extendUnitHom φ Y := by
    have h := congrArg Mod.Hom.hom ((Mod.extendRestrictAdjunction φ).unit.naturality g)
    simpa only [Mod.extendScalars_map, id_obj, comp_obj, comp_map, Mod.comp_hom',
      Mod.extendRestrictAdjunction_unit_app_hom, Mod.comap_map_hom, id_map] using h.symm
  have hδ (P Q : Mod C A) : F.map (Mod.tensorObjπ P Q) ≫ (OplaxMonoidal.δ (F.mapMod A) P Q).hom =
      OplaxMonoidal.δ F P.X Q.X ≫ Mod.tensorObjπ ((F.mapMod A).obj P) ((F.mapMod A).obj Q) := by
    have h := F.tensorπ_mapModTensorIso_hom_hom P Q
    rw [mapModTensorIso_hom_hom, ← mapMod_μ_hom] at h
    rw [← cancel_epi (LaxMonoidal.μ F P.X Q.X), ← Category.assoc, ← h, Category.assoc,
      ← Mod.comp_hom', Monoidal.μ_δ, Mod.id_hom', Category.comp_id, Monoidal.μ_δ_assoc]
  have key : G.mapModLaxTensorHom M N = b.unit.app _ ≫ (G.mapMod R).map
      (OplaxMonoidal.δ L _ _ ≫ (b.counit.app M ⊗ₘ b.counit.app N)) := by
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ ((G.mapMod R).obj M) ((G.mapMod R).obj N)),
      tensorObjπ_mapModLaxTensorHom_hom, Mod.comp_hom', hunit, Category.assoc,
      ← a.unit_naturality_assoc, Adjunction.IsMonoidal.leftAdjoint_μ (adj := a)]
    simp only [Category.assoc, ← G.map_comp, Functor.mapMod_map_hom]
    congr 2
    symm
    erw [Mod.comp_hom', OplaxMonoidal.comp_δ, Mod.comp_hom']
    simp only [Category.assoc]
    rw [reassoc_of% he, reassoc_of% hδ]
    simp only [Mod.extendUnit_hom] at hm
    rw [reassoc_of% hm, MonoidalCategory.tensorHom_def (b.counit.app M), Mod.comp_hom']
    erw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft]
    rw [
      ← MonoidalCategory.tensorHom_def_assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      hcounit, hcounit]
    rfl
  rw [key]
  infer_instance

end Adjunction

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- A natural family of isomorphisms `F M ⊗ F N ≅ F (M ⊗ N)` as an isomorphism of functors
`C × C ⥤ D`, between the uncurried tensor product followed by `F` and `F × F` followed by the
uncurried tensor product. -/
@[simps!]
def uncurryTensorIsoOfTensorIso (F : C ⥤ D) (e : ∀ M N : C, F.obj M ⊗ F.obj N ≅ F.obj (M ⊗ N))
    (he : ∀ {M M' N N' : C} (f : M ⟶ M') (g : N ⟶ N'),
      (F.map f ⊗ₘ F.map g) ≫ (e M' N').hom = (e M N).hom ≫ F.map (f ⊗ₘ g)) :
    uncurry.obj (curriedTensor C) ⋙ F ≅ F.prod F ⋙ uncurry.obj (curriedTensor D) :=
  NatIso.ofComponents (fun MN ↦ (e MN.1 MN.2).symm) (fun {MN MN'} fg ↦ by
    have h := he fg.1 fg.2
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def] at h
    dsimp only [Functor.comp_map, Functor.prod_map, uncurry_obj_map, curriedTensor_map_app,
      curriedTensor_obj_map, Iso.symm_hom]
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact h.symm)

end CategoryTheory.Functor
