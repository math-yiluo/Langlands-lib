/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-!

# Coherence of the composition isomorphisms of `g^*` and `g_*` on pro-étale sheaves

The composition isomorphisms `ProEtale.lowerStarComp : f_* ⋙ g_* ≅ (f ≫ g)_*` and
`ProEtale.upperStarComp : (f ≫ g)^* ≅ g^* ⋙ f^*` of pushforwards and pullbacks on pro-étale
sheaves with values in a Grothendieck abelian category `A`, and the identity isomorphisms
`ProEtale.lowerStarId` and `ProEtale.upperStarId`, satisfy the coherences of a pseudofunctor.
This file proves those that compare pullbacks along morphisms over a fixed base.

## The morphisms `η`

Let `k_X : X ⟶ W` and `k_Y : Y ⟶ W` be morphisms of schemes and `f : X ⟶ Y` with
`f ≫ k_Y = k_X`. For a sheaf `F` on `W_proét`, the composition isomorphism of the pullbacks gives
`f^* k_Y^* F ≅ (f ≫ k_Y)^* F = k_X^* F`, and its mate under `f^* ⊣ f_*` is a morphism
```
η_f(F) : k_Y^* F ⟶ f_* k_X^* F,
```
the unit of `f^* ⊣ f_*` followed by `f_*` of that isomorphism. For the coefficient rings pulled
back from the pro-étale site of a point, `k_X` is the structure morphism `X ⟶ Spec ℤ`, and
`η_f(F)` is the canonical coefficient morphism `Λ_Y ⟶ f_* Λ_X` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

The morphisms `η` are compatible with identities and compositions
(`ProEtale.unitCompUpperStarComp_id` and `ProEtale.unitCompUpperStarComp_comp`):
```
η_{𝟙 X}(F) = (𝟙 X)_* ≅ 𝟭 at k_X^* F,
η_{f ≫ g}(F) = η_g(F) ≫ g_* η_f(F) ≫ (g_* f_* ≅ (f ≫ g)_*) at k_X^* F.
```

## Proof

Under the adjunction `k^* ⊣ k_*`, the morphism `η_f(F)` corresponds to the unit of
`k_X^* ⊣ k_X_*` followed by the composition isomorphism `k_X_* ≅ k_Y_* ∘ f_*` of the
pushforwards (`ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp`), the composition
isomorphism of the pullbacks being by definition conjugate to that of the pushforwards. The two
compatibilities are thus reduced to the associativity and the left unit law of the composition
isomorphisms of the pushforwards (`ProEtale.lowerStarComp_assoc` and
`ProEtale.lowerStarComp_id_left`). These hold on sections, the pushforwards being restrictions
along the base change functors of the pro-étale sites: both sides are the restriction maps along
the canonical isomorphisms between iterated fibre products, which agree, maps into a fibre
product being determined by their projections.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-! ### Base change along the identity -/

section Site

/-- The structure morphism of the base change of `V` along `k` is the second projection. -/
lemma ProEt.overPullback_obj_hom {X Y : Scheme.{u}} (k : X ⟶ Y) (V : Y.ProEt) :
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ k).obj V).hom = pullback.snd V.hom k :=
  rfl

/-- The identification of base change along the identity with the identity is the first
projection. -/
lemma ProEt.overPullbackId_hom_app_left (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).hom.app W).left = pullback.fst W.hom (𝟙 X) := by
  simp [ProEt.overPullbackId, conjugateEquiv_apply_app]

/-- The inverse of `ProEt.overPullbackId` is a section of the first projection. -/
@[reassoc (attr := simp)]
lemma ProEt.overPullbackId_inv_app_left_fst (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).inv.app W).left ≫ pullback.fst W.hom (𝟙 X) = 𝟙 _ := by
  rw [← ProEt.overPullbackId_hom_app_left, ← MorphismProperty.Comma.comp_left,
    Iso.inv_hom_id_app]
  rfl

/-- The inverse of `ProEt.overPullbackId` is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma ProEt.overPullbackId_inv_app_left_snd (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).inv.app W).left ≫ pullback.snd W.hom (𝟙 X) = W.hom :=
  MorphismProperty.Over.w ((ProEt.overPullbackId X).inv.app W)

/-- The inverse of `ProEt.overPullbackId`, explicitly. -/
lemma ProEt.overPullbackId_inv_app_left (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).inv.app W).left =
      pullback.lift (𝟙 W.left) W.hom (by simp) := by
  apply pullback.hom_ext
  · rw [ProEt.overPullbackId_inv_app_left_fst, pullback.lift_fst]
    rfl
  · rw [ProEt.overPullbackId_inv_app_left_snd, pullback.lift_snd]

end Site

/-! ### The composition isomorphisms of the pushforwards -/

section LowerStar

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of `eqToHom` between pushforwards along equal morphisms are the restriction
maps along the base change isomorphisms `MorphismProperty.Over.pullbackCongr`. -/
lemma ProEtale.eqToHom_lowerStar_app_hom_app {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (e : g = g')
    (p : (g)_*[A] = (g')_*[A]) (G : Sheaf (Scheme.ProEt.topology Z) A) (V : Y.ProEt) :
    ((eqToHom p).app G).hom.app (op V) =
      G.obj.map ((MorphismProperty.Over.pullbackCongr e.symm).hom.app V).op := by
  subst e
  rw [eqToHom_refl, NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  erw [← G.obj.map_id]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;>
    simp only [Functor.op_obj, Functor.id_obj, Functor.const_obj_obj, unop_id,
      MorphismProperty.Comma.id_hom, Comma.id_left, Category.id_comp, Quiver.Hom.unop_op,
      MorphismProperty.Over.pullbackCongr_hom_app_left_fst,
      MorphismProperty.Over.pullbackCongr_hom_app_left_snd]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` are the restriction
maps along the base change isomorphisms `MorphismProperty.Over.pullbackComp`. -/
lemma ProEtale.coefficient_lowerStarComp_hom_app_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R)
    (G : Sheaf (Scheme.ProEt.topology T) A) (V : R.ProEt) :
    ((lowerStarComp A h₁ h₂).hom.app G).hom.app (op V) =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V).op := by
  simp [lowerStarComp]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphisms of pushforwards are associative, up to `eqToHom` along
`(h₁ ≫ h₂) ≫ h₃ = h₁ ≫ h₂ ≫ h₃`: on sections, both sides are the restriction maps along the
canonical isomorphisms of iterated fibre products. -/
lemma ProEtale.lowerStarComp_assoc {X₀ X₁ X₂ X₃ : Scheme.{u}} (h₁ : X₀ ⟶ X₁) (h₂ : X₁ ⟶ X₂)
    (h₃ : X₂ ⟶ X₃) :
    Functor.whiskerLeft (h₁)_*[A] (lowerStarComp A h₂ h₃).hom ≫
        (lowerStarComp A h₁ (h₂ ≫ h₃)).hom =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (lowerStarComp A h₁ h₂).hom (h₃)_*[A] ≫
        (lowerStarComp A (h₁ ≫ h₂) h₃).hom ≫ eqToHom (by rw [Category.assoc]) := by
  ext G : 2
  apply Sheaf.hom_ext
  ext ⟨V⟩
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    eqToHom_lowerStar_app_hom_app A (Category.assoc h₁ h₂ h₃), lowerStar_map_hom_app,
    coefficient_lowerStarComp_hom_app_hom_app]
  erw [show ∀ x, ((h₁)_*[A].obj G).obj.map x =
    G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h₁).map x.unop).op from fun _ ↦ rfl]
  simp only [← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  dsimp only [MorphismProperty.Over.pullback, MorphismProperty.Over.mk, MorphismProperty.Comma.mk]
  apply pullback.hom_ext <;> (try apply pullback.hom_ext) <;> (try apply pullback.hom_ext) <;>
    simp [pullback.condition, MorphismProperty.Over.pullbackCongr]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism `(𝟙 X)_* ⋙ k_* ≅ (𝟙 X ≫ k)_*` is induced by the identity
isomorphism `(𝟙 X)_* ≅ 𝟭`, up to `eqToHom` along `𝟙 X ≫ k = k`. -/
lemma ProEtale.lowerStarComp_id_left {X Y : Scheme.{u}} (k : X ⟶ Y) :
    (lowerStarComp A (𝟙 X) k).hom =
      Functor.whiskerRight (lowerStarId A X).hom (k)_*[A] ≫ (Functor.leftUnitor _).hom ≫
        eqToHom (by rw [Category.id_comp]) := by
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    lowerStarCongr, eqToIso.hom, Iso.symm_hom,
    eqToIso.inv] using congrArg Iso.hom (ProEtale.legacy_lowerStarComp_id_left A k)

end LowerStar

/-! ### The morphisms `η` -/

section Eta

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Composition with the identity transformation of a functor between sheaf categories, stated
with the instances as they occur after `eqToHom_refl`. -/
lemma ProEtale.id_app_comp {Y₁ Y₂ : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology Y₁) A ⥤
    Sheaf (Scheme.ProEt.topology Y₂) A) (G : Sheaf (Scheme.ProEt.topology Y₁) A)
    {M : Sheaf (Scheme.ProEt.topology Y₂) A} (h : F.obj G ⟶ M) : NatTrans.app (𝟙 F) G ≫ h = h :=
  Category.id_comp h

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Composition with the identity transformation of a functor between sheaf categories, stated
with the instances as they occur after `eqToHom_refl`. -/
lemma ProEtale.comp_id_app {Y₁ Y₂ : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology Y₁) A ⥤
    Sheaf (Scheme.ProEt.topology Y₂) A) (G : Sheaf (Scheme.ProEt.topology Y₁) A)
    {M : Sheaf (Scheme.ProEt.topology Y₂) A} (h : M ⟶ F.obj G) : h ≫ NatTrans.app (𝟙 F) G = h :=
  Category.comp_id h

/-- For a functor `G` with values in sheaves on `W_proét`, the components of the isomorphism
`(G ⋙ k_Y^*) ⋙ f^* ≅ G ⋙ k_X^*` induced by the composition isomorphism of the pullbacks and
`f ≫ k_Y = k_X` are those of the composition isomorphism followed by `eqToHom`. -/
lemma ProEtale.associator_isoWhiskerLeft_upperStarComp_hom_app {W X Y : Scheme.{u}}
    {D : Type*} [Category* D] (G : D ⥤ Sheaf (Scheme.ProEt.topology W) A) (f : X ⟶ Y)
    (kX : X ⟶ W) (kY : Y ⟶ W) (h : f ≫ kY = kX) (c : D) :
    (Functor.associator G (kY)^*[A] (f)^*[A] ≪≫ Functor.isoWhiskerLeft G
        ((upperStarComp A f kY).symm ≪≫ eqToIso (congrArg (upperStar A) h))).hom.app c =
      (upperStarComp A f kY).inv.app (G.obj c) ≫
        (eqToHom (congrArg (upperStar A) h)).app (G.obj c) := by
  simp

/-- The composition isomorphism of the pullbacks is conjugate to that of the pushforwards. -/
lemma ProEtale.coefficient_conjugateEquiv_upperStarComp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    conjugateEquiv (upperStarLowerStarAdjunction A (f ≫ g))
        ((upperStarLowerStarAdjunction A g).comp (upperStarLowerStarAdjunction A f))
        (upperStarComp A f g).inv = (lowerStarComp A f g).inv := by
  simp [upperStarComp]

/-- Let `f : X ⟶ Y`, `k_X : X ⟶ W`, `k_Y : Y ⟶ W` with `f ≫ k_Y = k_X`. The morphism
`η_f(F) : k_Y^* F ⟶ f_* k_X^* F` adjoint to the composition isomorphism `f^* k_Y^* F ≅ k_X^* F`
corresponds, under the adjunction `k_Y^* ⊣ k_Y_*`, to the unit of `k_X^* ⊣ k_X_*` followed by the
composition isomorphism `k_X_* ≅ k_Y_* ∘ f_*` of the pushforwards. -/
@[reassoc]
lemma ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp {W X Y : Scheme.{u}}
    (f : X ⟶ Y) (kX : X ⟶ W) (kY : Y ⟶ W) (hf : f ≫ kY = kX)
    (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A kY).unit.app F ≫
        (kY)_*[A].map ((upperStarLowerStarAdjunction A f).unit.app ((kY)^*[A].obj F) ≫
          (f)_*[A].map ((upperStarComp A f kY).inv.app F ≫
            (eqToHom (congrArg (upperStar A) hf)).app F)) =
      (upperStarLowerStarAdjunction A kX).unit.app F ≫
        (eqToHom (congrArg (lowerStar A) hf.symm)).app _ ≫
          (lowerStarComp A f kY).inv.app ((kX)^*[A].obj F) := by
  subst hf
  have := unit_conjugateEquiv (upperStarLowerStarAdjunction A (f ≫ kY))
    ((upperStarLowerStarAdjunction A kY).comp (upperStarLowerStarAdjunction A f))
    (upperStarComp A f kY).inv F
  rw [coefficient_conjugateEquiv_upperStarComp_inv, Adjunction.comp_unit_app] at this
  simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id, Functor.map_comp]
  erw [Category.id_comp, this]
  simp only [Functor.comp_map, Category.assoc]

/-- The special case `k_X = f ≫ k_Y` of
`ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp`. -/
@[reassoc]
lemma ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp' {W X Y : Scheme.{u}}
    (f : X ⟶ Y) (kY : Y ⟶ W) (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A kY).unit.app F ≫
        (kY)_*[A].map ((upperStarLowerStarAdjunction A f).unit.app ((kY)^*[A].obj F) ≫
          (f)_*[A].map ((upperStarComp A f kY).inv.app F)) =
      (upperStarLowerStarAdjunction A (f ≫ kY)).unit.app F ≫
        (lowerStarComp A f kY).inv.app ((f ≫ kY)^*[A].obj F) := by
  simpa only [eqToHom_refl, id_app_comp, comp_id_app] using
    unit_comp_lowerStar_map_unit_comp_upperStarComp A f (f ≫ kY) kY rfl F

/-- **Compatibility of `η` with composition.** For `f : X ⟶ Y` and `g : Y ⟶ Z` over `W`, with
structure morphisms `k_X`, `k_Y`, `k_Z`, the morphism `η_{f ≫ g}(F) : k_Z^* F ⟶ (f ≫ g)_* k_X^* F`
adjoint to the composition isomorphism of the pullbacks is `η_g(F)`, followed by `g_* η_f(F)`,
followed by the composition isomorphism `g_* f_* ≅ (f ≫ g)_*`. -/
lemma ProEtale.unitCompUpperStarComp_comp {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (kX : X ⟶ W) (kY : Y ⟶ W) (kZ : Z ⟶ W) (hf : f ≫ kY = kX) (hg : g ≫ kZ = kY)
    (hfg : (f ≫ g) ≫ kZ = kX) (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A (f ≫ g)).unit.app ((kZ)^*[A].obj F) ≫
        (f ≫ g)_*[A].map ((upperStarComp A (f ≫ g) kZ).inv.app F ≫
          (eqToHom (congrArg (upperStar A) hfg)).app F) =
      ((upperStarLowerStarAdjunction A g).unit.app ((kZ)^*[A].obj F) ≫
        (g)_*[A].map ((upperStarComp A g kZ).inv.app F ≫
          (eqToHom (congrArg (upperStar A) hg)).app F)) ≫
      (g)_*[A].map ((upperStarLowerStarAdjunction A f).unit.app ((kY)^*[A].obj F) ≫
        (f)_*[A].map ((upperStarComp A f kY).inv.app F ≫
          (eqToHom (congrArg (upperStar A) hf)).app F)) ≫
      (lowerStarComp A f g).hom.app ((kX)^*[A].obj F) := by
  subst hf hg
  apply ((upperStarLowerStarAdjunction A kZ).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [unit_comp_lowerStar_map_unit_comp_upperStarComp A (f ≫ g) _ kZ hfg]
  rw [Functor.map_comp (kZ)_*[A],
    unit_comp_lowerStar_map_unit_comp_upperStarComp_assoc A g _ kZ rfl]
  simp only [eqToHom_refl, id_app_comp, comp_id_app]
  rw [Functor.map_comp (kZ)_*[A]]
  erw [← (lowerStarComp A g kZ).inv.naturality_assoc]
  rw [unit_comp_lowerStar_map_unit_comp_upperStarComp'_assoc]
  congr 1
  have h := congr_app (lowerStarComp_assoc A f g kZ) ((f ≫ g ≫ kZ)^*[A].obj F)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, eqToHom_refl, comp_id_app] at h
  erw [Category.id_comp] at h
  rw [← cancel_mono ((lowerStarComp A (f ≫ g) kZ).hom.app _)]
  simp only [Category.assoc, ← h, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  rfl

/-- **Compatibility of `η` with identities.** The morphism
`η_{𝟙 X}(F) : k_X^* F ⟶ (𝟙 X)_* k_X^* F` adjoint to the composition isomorphism of the pullbacks
along `𝟙 X` and `k_X` is the identification `k_X^* F ≅ (𝟙 X)_* k_X^* F`. -/
lemma ProEtale.unitCompUpperStarComp_id {W X : Scheme.{u}} (kX : X ⟶ W) (h : 𝟙 X ≫ kX = kX)
    (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A (𝟙 X)).unit.app ((kX)^*[A].obj F) ≫
        (𝟙 X)_*[A].map ((upperStarComp A (𝟙 X) kX).inv.app F ≫
          (eqToHom (congrArg (upperStar A) h)).app F) =
      (lowerStarId A X).inv.app ((kX)^*[A].obj F) := by
  apply ((upperStarLowerStarAdjunction A kX).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [unit_comp_lowerStar_map_unit_comp_upperStarComp A (𝟙 X) kX kX h]
  congr 1
  have h' := congr_app (lowerStarComp_id_left A kX) ((kX)^*[A].obj F)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h'
  rw [← cancel_mono ((lowerStarComp A (𝟙 X) kX).hom.app _)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [h']
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp

end Eta

end AlgebraicGeometry
