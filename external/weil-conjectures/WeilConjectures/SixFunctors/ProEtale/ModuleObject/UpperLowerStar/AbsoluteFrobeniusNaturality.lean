/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
public import WeilConjectures.SixFunctors.ProEtale.AbsoluteFrobeniusNaturality

/-!
# Naturality of the Frobenius trivialization of module objects

Let `g : T ⟶ X` be a morphism of schemes in which the prime `p` vanishes, and `F_X`, `F_T` the
`p ^ n`-power absolute Frobenii, so that `g ≫ F_X = F_T ≫ g`. The trivializations
`F_X^* ≅ 𝟭` and `F_T^* ≅ 𝟭` of the pullbacks of module objects
(`ProEtale.CondensedRing.upperStarIterateFrobeniusIso`) are compatible with the pullback `g^*`:
```
(g ≫ F_X)^* M ≅ g^* F_X^* M --g^* κ_X--> g^* M
     ‖                                     ‖
(F_T ≫ g)^* M ≅ F_T^* g^* M --κ_T------> g^* M
```

## Main results

- `ProEtale.CondensedRing.upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app`,
  with the equality of natural transformations
  `ProEtale.CondensedRing.upperStarComp_hom_comp_whiskerRight_upperStarIterateFrobeniusIso_hom`.
  Both sides are conjugate to morphisms `g_* ⟶ (g ≫ F_X)_*` of pushforwards, which are
  compared on underlying sheaves
  (`ProEtale.lowerStarIterateFrobeniusIso_inv_app_comp_lowerStarComp_hom_app`), using that the
  conjugate of `F_X^* ≅ 𝟭` on module objects is `F_{X*} ≅ 𝟭` on underlying sheaves
  (`ProEtale.CondensedRing.conjugateEquiv_upperStarIterateFrobeniusIso_hom_app_hom`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {T X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (hT : (p : Γ(T, ⊤)) = 0)
  (n : ℕ) (g : T ⟶ X)

section IsoId

variable {Y : Scheme.{u}}

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- The conjugate `𝟭 ⟶ R` of a transformation `L ⟶ 𝟭` of left adjoints, `𝟭 ⊣ 𝟭` and `L ⊣ R`, has
as components the adjoints of the components. -/
lemma _root_.CategoryTheory.conjugateEquiv_id_app {C : Type*} [Category C] {L R : C ⥤ C}
    (adj : L ⊣ R) (α : L ⟶ 𝟭 C) (c : C) :
    (conjugateEquiv Adjunction.id adj α).app c = adj.homEquiv c c (α.app c) := by
  rw [conjugateEquiv_apply_app, Adjunction.homEquiv_unit]
  simp [Adjunction.id]

/-- The unit `M ⟶ Λ_X ⊗_{f^* Λ_Y} M` of the extension of scalars along `α_f` is natural. -/
@[reassoc]
lemma extendUnitHom_extendScalars_map_hom {Z : Scheme.{u}} (f : Z ⟶ Y)
    {M N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y))} (φ : M ⟶ N) :
    Mod.extendUnitHom (condensedPullbackHom Λ f) M ≫
        ((Mod.extendScalars (condensedPullbackHom Λ f)).map φ).hom =
      φ.hom ≫ Mod.extendUnitHom (condensedPullbackHom Λ f) N := by
  have hn := congrArg Mod.Hom.hom
    ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ f)).unit.naturality φ)
  simp only [Functor.id_map, Functor.comp_map, Mod.comp_hom', Mod.comap_map_hom,
    extendRestrictAdjunction_condensedPullbackHom_unit_app_hom] at hn
  exact hn.symm

/-- The conjugate `𝟭 ⟶ f_*` of a trivialization of `f^*` on `Λ`-modules induced by a
trivialization `κ` of the pullback of abelian sheaves is, on the underlying sheaves, the
conjugate of `κ`. -/
lemma conjugateEquiv_upperStarIsoIdOfIsoId_hom_app_hom (f : Y ⟶ Y) (κ : (f)^*[Ab.{u + 1}] ≅ 𝟭 _)
    [NatTrans.IsMonoidal κ.hom]
    (hκ : κ.hom.app (condensedRingObj Λ Y) = condensedPullbackHom Λ f)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ((conjugateEquiv Adjunction.id (upperStarLowerStarAdjunction Λ f)
        (upperStarIsoIdOfIsoId Λ f κ hκ).hom).app M).hom =
      (conjugateEquiv Adjunction.id (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
        κ.hom).app M.X := by
  rw [conjugateEquiv_id_app, conjugateEquiv_id_app, upperStarLowerStarAdjunction_homEquiv_hom,
    Adjunction.homEquiv_unit]
  congr 2
  simp only [upperStarIsoIdOfIsoId, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Mod.comp_hom']
  rw [extendUnitHom_extendScalars_map_hom_assoc,
    reassoc_of% (extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f),
    Functor.mapModIsoComapOfIsoId_hom_app_hom]
  exact Category.comp_id _

end IsoId

omit [IsCommMonObj Λ] in
/-- On underlying sheaves, the inverse of the transport of the pushforward of module objects
along `f = f'` is that of the pushforward of sheaves. -/
@[simp]
lemma lowerStarCongr_inv_app_hom {f f' : T ⟶ X} (h : f = f')
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    ((lowerStarCongr Λ h).inv.app M).hom =
      (ProEtale.lowerStarCongr Ab.{u + 1} h).inv.app M.X := by
  subst h
  rfl

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- The components of `α ≫ κ ▷ G ≫ λ_G`, for `κ : F ⟶ 𝟭`. -/
lemma _root_.CategoryTheory.NatTrans.comp_whiskerRight_leftUnitor_hom_app {C D : Type*}
    [Category C] [Category D] {F : C ⥤ C} {G H : C ⥤ D} (α : H ⟶ F ⋙ G) (κ : F ⟶ 𝟭 C)
    (c : C) :
    (α ≫ Functor.whiskerRight κ G ≫ (Functor.leftUnitor G).hom).app c =
      α.app c ≫ G.map (κ.app c) := by
  simp

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- The components of `α ≫ β ≫ G ◁ κ ≫ ρ_G`, for `κ : F ⟶ 𝟭`. -/
lemma _root_.CategoryTheory.NatTrans.comp_comp_whiskerLeft_rightUnitor_hom_app {C D : Type*}
    [Category C] [Category D] {F : D ⥤ D} {G H K : C ⥤ D} (α : H ⟶ K) (β : K ⟶ G ⋙ F)
    (κ : F ⟶ 𝟭 D) (c : C) :
    (α ≫ β ≫ Functor.whiskerLeft G κ ≫ (Functor.rightUnitor G).hom).app c =
      α.app c ≫ β.app c ≫ κ.app (G.obj c) := by
  simp

/-- The components of the transport of the pullback of module objects along `f = f'`. -/
lemma upperStarCongr_hom_app {f f' : T ⟶ X} (h : f = f')
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarCongr Λ h).hom.app M = eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj M) h) := by
  subst h
  rfl

/-- The conjugate `𝟭 ⟶ F_{X*}` of the Frobenius trivialization of `F_X^*` on module objects is,
on the underlying sheaves, the inverse of the trivialization `F_{X*} ≅ 𝟭` of abelian sheaves. -/
lemma conjugateEquiv_upperStarIterateFrobeniusIso_hom_app_hom
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((conjugateEquiv Adjunction.id (upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX n))
        (upperStarIterateFrobeniusIso Λ hp hX n).hom).app M).hom =
      (ProEtale.lowerStarIterateFrobeniusIso Ab.{u + 1} hp hX n).inv.app M.X := by
  rw [upperStarIterateFrobeniusIso, conjugateEquiv_upperStarIsoIdOfIsoId_hom_app_hom,
    ← conjugateIsoEquiv_apply_hom, ProEtale.conjugateIsoEquiv_upperStarIterateFrobeniusIso]
  rfl

/-- The pushforward form of
`ProEtale.CondensedRing.upperStarComp_hom_comp_whiskerRight_upperStarIterateFrobeniusIso_hom`:
the conjugates of the two morphisms `(g ≫ F_X)^* ⟶ g^*` agree. -/
lemma rightUnitor_inv_comp_whiskerLeft_conjugateEquiv_upperStarIterateFrobeniusIso_hom :
    ((g)_*⟦Λ⟧.rightUnitor.inv ≫ (g)_*⟦Λ⟧.whiskerLeft
        (conjugateEquiv Adjunction.id (upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX n))
          (upperStarIterateFrobeniusIso Λ hp hX n).hom)) ≫
        (lowerStarComp Λ g (X.iterateFrobenius hp hX n)).hom =
      (((g)_*⟦Λ⟧.leftUnitor.inv ≫ Functor.whiskerRight
          (conjugateEquiv Adjunction.id
            (upperStarLowerStarAdjunction Λ (T.iterateFrobenius hp hT n))
            (upperStarIterateFrobeniusIso Λ hp hT n).hom) (g)_*⟦Λ⟧) ≫
        (lowerStarComp Λ (T.iterateFrobenius hp hT n) g).hom) ≫
        (lowerStarCongr Λ (comp_iterateFrobenius hp g hX hT n)).symm.hom := by
  refine NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_)
  simp only [NatTrans.comp_app, Mod.comp_hom', Functor.rightUnitor_inv_app,
    Functor.leftUnitor_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    lowerStar_map_hom, conjugateEquiv_upperStarIterateFrobeniusIso_hom_app_hom,
    lowerStarComp_hom_app_hom, Iso.symm_hom, lowerStarCongr_inv_app_hom, Category.id_comp,
    Category.assoc]
  exact ProEtale.lowerStarIterateFrobeniusIso_inv_app_comp_lowerStarComp_hom_app hp hX hT n g
    Ab.{u + 1} M.X

/-- **Naturality of the Frobenius trivialization**, as an equality of natural transformations
`(g ≫ F_X)^* ⟶ g^*`. -/
lemma upperStarComp_hom_comp_whiskerRight_upperStarIterateFrobeniusIso_hom :
    (upperStarComp Λ g (X.iterateFrobenius hp hX n)).hom ≫
        Functor.whiskerRight (upperStarIterateFrobeniusIso Λ hp hX n).hom (g)^*⟦Λ⟧ ≫
        (Functor.leftUnitor _).hom =
      (upperStarCongr Λ (comp_iterateFrobenius hp g hX hT n)).hom ≫
        (upperStarComp Λ (T.iterateFrobenius hp hT n) g).hom ≫
        Functor.whiskerLeft (g)^*⟦Λ⟧ (upperStarIterateFrobeniusIso Λ hp hT n).hom ≫
        (Functor.rightUnitor _).hom := by
  apply (conjugateEquiv (upperStarLowerStarAdjunction Λ g)
    (upperStarLowerStarAdjunction Λ (g ≫ X.iterateFrobenius hp hX n))).injective
  have h₁ := congrArg Iso.hom (conjugateIsoEquiv_upperStarComp Λ g (X.iterateFrobenius hp hX n))
  have h₂ := congrArg Iso.hom (conjugateIsoEquiv_upperStarComp Λ (T.iterateFrobenius hp hT n) g)
  have h₃ := congrArg Iso.hom
    (conjugateIsoEquiv_upperStarCongr Λ (comp_iterateFrobenius hp g hX hT n))
  simp only [conjugateIsoEquiv_apply_hom] at h₁ h₂ h₃
  rw [← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX n)).comp
      (upperStarLowerStarAdjunction Λ g)),
    ← conjugateEquiv_comp _ (Adjunction.id.comp (upperStarLowerStarAdjunction Λ g)),
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction Λ (T.iterateFrobenius hp hT n ≫ g)),
    ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction Λ g).comp
      (upperStarLowerStarAdjunction Λ (T.iterateFrobenius hp hT n))),
    ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction Λ g).comp Adjunction.id),
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerRight,
    conjugateEquiv_whiskerLeft, h₁, h₂, h₃]
  exact rightUnitor_inv_comp_whiskerLeft_conjugateEquiv_upperStarIterateFrobeniusIso_hom Λ hp hX hT
    n g

/-- **Naturality of the Frobenius trivialization**: for `g : T ⟶ X` with `g ≫ F_X = F_T ≫ g`,
the two identifications `(g ≫ F_X)^* M ≅ g^* M` through `κ_X` and through `κ_T` agree. -/
theorem upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ g (X.iterateFrobenius hp hX n)).hom.app M ≫
        (g)^*⟦Λ⟧.map ((upperStarIterateFrobeniusIso Λ hp hX n).hom.app M) =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj M) (comp_iterateFrobenius hp g hX hT n)) ≫
        (upperStarComp Λ (T.iterateFrobenius hp hT n) g).hom.app M ≫
        (upperStarIterateFrobeniusIso Λ hp hT n).hom.app ((g)^*⟦Λ⟧.obj M) := by
  have h := NatTrans.congr_app
    (upperStarComp_hom_comp_whiskerRight_upperStarIterateFrobeniusIso_hom Λ hp hX hT n g) M
  rw [NatTrans.comp_whiskerRight_leftUnitor_hom_app,
    NatTrans.comp_comp_whiskerLeft_rightUnitor_hom_app,
    upperStarCongr_hom_app] at h
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
