/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.ExtPlus
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

/-!
# Stalks of higher direct images at geometric points

Let `f : X ⟶ S` be quasi-compact and quasi-separated, `F` an étale sheaf of `Λ`-modules on `X`
and `s : Spec Ω ⟶ S` a geometric point. Then the geometric stalk of `R^q f_* F` at `s` is the
étale cohomology `H^q(S_(s) ×_S X, F|)` of the base change of `X` to the strict localization
`S_(s)` of `S` at `s` ([Stacks, Tag 03Q9], blueprint
`prop-weil-pbc-strict-henselization-stalk-formula`).

The proof follows the blueprint: `R^q f_* F` is the sheafification of the presheaf
`V ↦ H^q(V ×_S X, F|)`, so its stalk is the colimit of `H^q(V ×_S X, F|)` over the pointed étale
neighbourhoods `V` of `s`. The affine neighbourhoods are cofinal, `S_(s) ×_S X` is the limit of
the `V ×_S X` (`AlgebraicGeometry.Scheme.isLimitStrictLocalizationConePullback`) and the
continuity of étale cohomology
(`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit`)
identifies the colimit of the cohomology groups with the cohomology of the limit.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_geometricStalk_higherDirectImage_addEquiv`: the stalk
  formula `(R^q f_* F)_s ≅ H^q(S_(s) ×_S X, F|)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]


section GlobalSections

variable {T : Scheme.{u}}

/-- Maps out of the constant sheaf `Λ` on `T_ét` are global sections. -/
noncomputable def constSheafHomEquiv (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶ G) ≃
      G.obj.obj (op (Etale.finalObject T)) :=
  ((constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv
    _ _).trans (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf Λ Λ _).toEquiv)

lemma constSheafHomEquiv_comp {G G' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶ G) (ψ : G ⟶ G') :
    constSheafHomEquiv Λ G' (φ ≫ ψ) = ψ.hom.app _ (constSheafHomEquiv Λ G φ) := by
  simp only [constSheafHomEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl


lemma constSheafHomEquiv_apply {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶ G) :
    constSheafHomEquiv Λ G φ = φ.hom.app _ (Etale.constSheafOne Λ (Etale.finalObject T)) := by
  simp only [constSheafHomEquiv, Equiv.trans_apply, Adjunction.homEquiv_unit]
  rfl
end GlobalSections

section EtalePullback

variable {X T : Scheme.{u}} (t : T ⟶ X) (h : AlgebraicGeometry.Etale t)
  (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

set_option backward.isDefEq.respectTransparency false in
/-- For an étale `t`, the identification `t^* G ≅ j_t^* G` of the pullback with the restriction
along `T_ét ⥤ X_ét` sends the pullback `φ^* g` of a section `g` of `G` over `U` along
`φ : V ⟶ U` to the restriction of `g` along `φ`, viewed as a morphism of étale `X`-schemes. -/
lemma upperStarIsoLocalizationRestriction_hom_app_pullSection_moduleCat {V : T.Etale} {U : X.Etale}
    (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ t) (g : G.obj.obj (op U)) :
    ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) t h).hom.app G).hom.app
        (op V) (ModuleSheaf.pullSection t G φ hφ g) =
      G.obj.map (MorphismProperty.Over.homMk φ hφ :
        (MorphismProperty.Over.map ⊤ h).obj V ⟶ U).op g := by
  set e := Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) t h
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t)
    (Etale.localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) t h) G
  have h₂ := congrArg (fun α ↦ α.hom.app (op U) g) h₁
  have h₃ : (e.hom.app G).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ t).obj U))
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit.app G).hom.app (op U) g) =
      G.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ t h trivial).counit.app U).op g :=
    h₂
  rw [ModuleSheaf.pullSection, NatTrans.naturality_apply, h₃]
  change G.obj.map _ (G.obj.map _ g) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 3
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp [homToPullback]

include h in
/-- **Sections of the pullback along an étale morphism.** For an étale `t : T ⟶ X`, an étale
`T`-scheme `V`, an étale `X`-scheme `U` and an isomorphism `φ : V ⟶ U` over `X`, the pullback
of sections `F(U) ⟶ (t^* F)(V)` is bijective. -/
lemma bijective_pullSection_of_etale_moduleCat {V : T.Etale} {U : X.Etale} (φ : V.left ⟶ U.left)
    [IsIso φ] (hφ : φ ≫ U.hom = V.hom ≫ t) :
    Function.Bijective (ModuleSheaf.pullSection t G φ hφ) := by
  let ψ : (MorphismProperty.Over.map ⊤ h).obj V ⟶ U := MorphismProperty.Over.homMk φ hφ
  have : IsIso ψ := ⟨MorphismProperty.Over.homMk (inv φ)
      (by rw [IsIso.inv_comp_eq, hφ]; rfl),
    MorphismProperty.Over.Hom.ext (by simp [ψ]), MorphismProperty.Over.Hom.ext (by simp [ψ])⟩
  have h₁ : Function.Bijective (G.obj.map ψ.op) :=
    ConcreteCategory.bijective_of_isIso (G.obj.map ψ.op)
  have h₂ : Function.Bijective
      (((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) t h).hom.app G).hom.app
        (op V)) :=
    ConcreteCategory.bijective_of_isIso (((sheafSections _ _).obj (op V)).map
      ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) t h).hom.app G))
  have h₃ : (((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) t h).hom.app
      G).hom.app (op V)) ∘ ModuleSheaf.pullSection t G φ hφ = G.obj.map ψ.op :=
    funext fun g ↦ upperStarIsoLocalizationRestriction_hom_app_pullSection_moduleCat Λ t h G φ hφ g
  rw [← h₂.of_comp_iff', h₃]
  exact h₁

end EtalePullback

section Restrict

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The canonical global section of `t^* f^* Λ[V]` attached to a `T`-point `b` of `V` over `f`
(with `t : T ⟶ X`): the generator of `Λ[V]`, pulled back along `f`, and then pulled back along
the morphism `T ⟶ X ×_S V` given by `b` and `t`. -/
noncomputable def freeSheafPullbackSection {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    ((t)^*[ModuleCat.{u + 1} Λ].obj ((f)^*[ModuleCat.{u + 1} Λ].obj
      ((Etale.freeSheaf Λ S).obj V))).obj.obj (op (Etale.finalObject T)) :=
  ModuleSheaf.pullSection t ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V))
    (V := Etale.finalObject T) (U := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
    (pullback.lift b t hb) ((pullback.lift_snd _ _ _).trans (Category.id_comp t).symm)
    (Etale.modulePullbackSection Λ f _ V (freeSheafGenerator Λ V))

/-- The morphism `Λ ⟶ t^* f^* Λ[V]` corresponding to `freeSheafPullbackSection`. -/
noncomputable def freeSheafPullbackMap {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶
      (t)^*[ModuleCat.{u + 1} Λ].obj ((f)^*[ModuleCat.{u + 1} Λ].obj
        ((Etale.freeSheaf Λ S).obj V)) :=
  (constSheafHomEquiv Λ _).symm (freeSheafPullbackSection Λ f t V b hb)

variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)

/-- The restriction of a section `Hᵠ(V ×_S X, F|)` of the cohomology presheaf to a `T`-point
`b` of `V` over `f`: a class `f^* Λ[V] ⟶ F[q]` is pulled back along `t : T ⟶ X` and evaluated
at the canonical section of `t^* f^* Λ[V]`. -/
noncomputable def cohomologyPresheafRestrict {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    (Etale.higherDirectImagePresheaf Λ f q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V) →+
      Ext (SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ)
        ((t)^*[ModuleCat.{u + 1} Λ].obj F) q :=
  ((t)^*[ModuleCat.{u + 1} Λ].mapExtPrecomp (freeSheafPullbackMap Λ f t V b hb) F q).comp
    (DerivedCategory.Plus.shiftedHomAddEquivExt _ _ q).toAddMonoidHom

/-- **Naturality in `V`** of `cohomologyPresheafRestrict`. -/
lemma cohomologyPresheafRestrict_map {T : Scheme.{u}} (t : T ⟶ X) {V V' : S.Etale} (a : V' ⟶ V)
    (b : T ⟶ V'.left) (hb : b ≫ V'.hom = t ≫ f)
    (p : (Etale.higherDirectImagePresheaf Λ f q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V)) :
    cohomologyPresheafRestrict Λ f F q t V' b hb
        ((Etale.higherDirectImagePresheaf Λ f q
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).map a.op p) =
      cohomologyPresheafRestrict Λ f F q t V (b ≫ a.left)
        (by rw [Category.assoc, MorphismProperty.Over.w a, hb]) p := by
  have hsec : ((t)^*[ModuleCat.{u + 1} Λ].map ((f)^*[ModuleCat.{u + 1} Λ].map
      ((Etale.freeSheaf Λ S).map a))).hom.app _ (freeSheafPullbackSection Λ f t V' b hb) =
      freeSheafPullbackSection Λ f t V (b ≫ a.left)
        (by rw [Category.assoc, MorphismProperty.Over.w a, hb]) := by
    simp only [freeSheafPullbackSection]
    rw [ModuleSheaf.pullSection_naturality, Etale.modulePullbackSection_naturality,
      freeSheaf_map_freeSheafGenerator, ← Etale.modulePullbackSection_map,
      ← ModuleSheaf.pullSection_comp]
    exact ModuleSheaf.pullSection_congr _ _ _ (by apply pullback.hom_ext <;> simp) _
  have hσ : freeSheafPullbackMap Λ f t V' b hb ≫ (t)^*[ModuleCat.{u + 1} Λ].map
      ((f)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheaf Λ S).map a)) =
      freeSheafPullbackMap Λ f t V (b ≫ a.left)
        (by rw [Category.assoc, MorphismProperty.Over.w a, hb]) := by
    apply (constSheafHomEquiv Λ _).injective
    rw [constSheafHomEquiv_comp, freeSheafPullbackMap, freeSheafPullbackMap,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, hsec]
  simp only [cohomologyPresheafRestrict, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, Functor.mapExtPrecomp_apply]
  erw [DerivedCategory.Plus.shiftedHomAddEquivExt_precomp]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  exact congrArg (fun φ ↦ (Ext.mk₀ φ).comp _ (zero_add q)) hσ


/-- **Composition**: restricting along `h : T' ⟶ T` the restriction of a section of the
cohomology presheaf to a `T`-point `b` is its restriction to the `T'`-point `h ≫ b`. -/
lemma cohomologyPresheafRestrict_comp {T T' : Scheme.{u}} (t : T ⟶ X) (h : T' ⟶ T) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f)
    (p : (Etale.higherDirectImagePresheaf Λ f q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V)) :
    cohomologyPresheafRestrict Λ f F q (h ≫ t) V (h ≫ b)
        (by rw [Category.assoc, hb, Category.assoc]) p =
      cohomologyRestrictOver Λ (h ≫ t) t h rfl F q
        (cohomologyPresheafRestrict Λ f F q t V b hb p) := by
  let A := (f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V)
  let τ := Etale.upperStarComp (ModuleCat.{u + 1} Λ) h t (h ≫ t) rfl
  let c := (Etale.constantSheafCompUpperStarIso Λ h).app (ModuleCat.of Λ Λ)
  have hι : h ≫ (Etale.finalObject T).hom = (Etale.finalObject T').hom ≫ h :=
    (Category.comp_id h).trans (Category.id_comp h).symm
  let ι : Etale.finalObject T' ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ h).obj (Etale.finalObject T) :=
    homToPullback h h hι
  have KE : freeSheafPullbackMap Λ f (h ≫ t) V (h ≫ b)
      (by rw [Category.assoc, hb, Category.assoc]) ≫ τ.hom.app A =
      c.inv ≫ (h)^*[ModuleCat.{u + 1} Λ].map (freeSheafPullbackMap Λ f t V b hb) := by
    apply (constSheafHomEquiv Λ _).injective
    rw [constSheafHomEquiv_comp, constSheafHomEquiv_comp, constSheafHomEquiv_apply Λ c.inv]
    have hσ₁ : constSheafHomEquiv Λ _ (freeSheafPullbackMap Λ f (h ≫ t) V (h ≫ b)
        (by rw [Category.assoc, hb, Category.assoc])) = freeSheafPullbackSection Λ f (h ≫ t) V
          (h ≫ b) (by rw [Category.assoc, hb, Category.assoc]) :=
      Equiv.apply_symm_apply _ _
    have hσ₂ : (freeSheafPullbackMap Λ f t V b hb).hom.app _
        (Etale.constSheafOne Λ (Etale.finalObject T)) = freeSheafPullbackSection Λ f t V b hb := by
      rw [← constSheafHomEquiv_apply, freeSheafPullbackMap, Equiv.apply_symm_apply]
    have e1 : c.inv.hom.app (op (Etale.finalObject T'))
        (Etale.constSheafOne Λ (Etale.finalObject T')) =
        ((h)^*[ModuleCat.{u + 1} Λ].obj
          (SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ)).obj.map ι.op
          (Etale.modulePullbackSection Λ h _ (Etale.finalObject T)
            (Etale.constSheafOne Λ (Etale.finalObject T))) := by
      rw [← Etale.constSheafOne_map Λ ι, ← Etale.constantSheafCompUpperStarIso_inv_one]
      exact NatTrans.naturality_apply c.inv.hom ι.op _
    have R1 : ((h)^*[ModuleCat.{u + 1} Λ].map (freeSheafPullbackMap Λ f t V b hb)).hom.app
        (op (Etale.finalObject T')) (c.inv.hom.app (op (Etale.finalObject T'))
          (Etale.constSheafOne Λ (Etale.finalObject T'))) =
        ((h)^*[ModuleCat.{u + 1} Λ].obj ((t)^*[ModuleCat.{u + 1} Λ].obj A)).obj.map ι.op
          (Etale.modulePullbackSection Λ h _ (Etale.finalObject T)
            (freeSheafPullbackSection Λ f t V b hb)) := by
      rw [e1]
      refine (NatTrans.naturality_apply
        ((h)^*[ModuleCat.{u + 1} Λ].map (freeSheafPullbackMap Λ f t V b hb)).hom ι.op _).trans ?_
      rw [Etale.modulePullbackSection_naturality, hσ₂]
    have e2 : freeSheafPullbackSection Λ f (h ≫ t) V (h ≫ b)
        (by rw [Category.assoc, hb, Category.assoc]) =
        ModuleSheaf.restrictAlong t A h (h ≫ t) rfl (V := Etale.finalObject T)
          (V' := Etale.finalObject T') h hι (freeSheafPullbackSection Λ f t V b hb) := by
      simp only [freeSheafPullbackSection]
      rw [ModuleSheaf.restrictAlong_pullSection]
      exact ModuleSheaf.pullSection_congr _ _ _ (by apply pullback.hom_ext <;> simp) _
    have R2 : ModuleSheaf.restrictAlong t A h (h ≫ t) rfl (V := Etale.finalObject T)
        (V' := Etale.finalObject T') h hι (freeSheafPullbackSection Λ f t V b hb) =
        (τ.inv.app A).hom.app (op (Etale.finalObject T'))
          (((h)^*[ModuleCat.{u + 1} Λ].obj ((t)^*[ModuleCat.{u + 1} Λ].obj A)).obj.map ι.op
            (Etale.modulePullbackSection Λ h _ (Etale.finalObject T)
              (freeSheafPullbackSection Λ f t V b hb))) :=
      (NatTrans.naturality_apply (τ.inv.app A).hom ι.op _).symm
    rw [hσ₁]
    refine Eq.trans ?_ R1.symm
    rw [e2, R2]
    exact ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app (op (Etale.finalObject T'))) (τ.inv_hom_id_app A)) _
  simp only [cohomologyPresheafRestrict, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, Functor.mapExtPrecomp_apply]
  suffices key : ∀ x : Ext A F q,
      (Ext.mk₀ (freeSheafPullbackMap Λ f (h ≫ t) V (h ≫ b)
        (by rw [Category.assoc, hb, Category.assoc]))).comp
        (x.mapExactFunctor ((h ≫ t)^*[ModuleCat.{u + 1} Λ])) (zero_add q) =
      cohomologyRestrictOver Λ (h ≫ t) t h rfl F q
        ((Ext.mk₀ (freeSheafPullbackMap Λ f t V b hb)).comp
          (x.mapExactFunctor (t)^*[ModuleCat.{u + 1} Λ]) (zero_add q)) from key _
  intro x
  have M := Ext.mapExactFunctor_comp_mk₀_eq (t)^*[ModuleCat.{u + 1} Λ]
    (h)^*[ModuleCat.{u + 1} Λ] ((h ≫ t)^*[ModuleCat.{u + 1} Λ]) τ q x
  have M' : x.mapExactFunctor ((h ≫ t)^*[ModuleCat.{u + 1} Λ]) =
      ((Ext.mk₀ (τ.hom.app A)).comp ((x.mapExactFunctor (t)^*[ModuleCat.{u + 1} Λ]).mapExactFunctor
        (h)^*[ModuleCat.{u + 1} Λ]) (zero_add q)).comp (Ext.mk₀ (τ.inv.app F)) (add_zero q) := by
    rw [← M, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id_app,
      Ext.comp_mk₀_id]
  have hR (y : Ext (SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ)
      ((t)^*[ModuleCat.{u + 1} Λ].obj F) q) :
      cohomologyRestrictOver Λ (h ≫ t) t h rfl F q y =
        ((Ext.mk₀ c.inv).comp (y.mapExactFunctor (h)^*[ModuleCat.{u + 1} Λ]) (zero_add q)).comp
          (Ext.mk₀ (τ.inv.app F)) (add_zero q) := rfl
  rw [hR, M', Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_assoc_of_third_deg_zero]
  simp only [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, KE]


/-- **The cohomology presheaf computes the cohomology of `X ×_S V`**: for an étale `S`-scheme
`V`, restricting to the tautological point of `V` over `X ×_S V` is a bijection
`Hᵠ(V ×_S X, F|) ≃ Hᵠ(X ×_S V, F|)` from the value of the cohomology presheaf at `V` to the
étale cohomology of `X ×_S V` (blueprint `def-weil-pbc-direct-image`). -/
lemma bijective_cohomologyPresheafRestrict (V : S.Etale) :
    Function.Bijective (cohomologyPresheafRestrict Λ f F q (pullback.snd V.hom f) V
      (pullback.fst V.hom f) pullback.condition) := by
  have : AlgebraicGeometry.Etale V.hom := V.prop
  let t := pullback.snd V.hom f
  let A := (f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V)
  let W := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
  have hψ : pullback.lift (pullback.fst V.hom f) t pullback.condition ≫ W.hom =
      (Etale.finalObject (pullback V.hom f)).hom ≫ t :=
    (pullback.lift_snd _ _ _).trans (Category.id_comp t).symm
  have : IsIso (pullback.lift (pullback.fst V.hom f) t pullback.condition) := by
    rw [show pullback.lift (pullback.fst V.hom f) t pullback.condition = 𝟙 _ from
      pullback.lift_fst_snd _ _]
    infer_instance
  -- the degree-zero bijection
  have hu (B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      Function.Bijective (fun φ : A ⟶ B ↦ freeSheafPullbackMap Λ f t V (pullback.fst V.hom f)
        pullback.condition ≫ (t)^*[ModuleCat.{u + 1} Λ].map φ) := by
    have e : (constSheafHomEquiv Λ _) ∘ (fun φ : A ⟶ B ↦ freeSheafPullbackMap Λ f t V
        (pullback.fst V.hom f) pullback.condition ≫ (t)^*[ModuleCat.{u + 1} Λ].map φ) =
        (ModuleSheaf.pullSection t B (V := Etale.finalObject (pullback V.hom f)) (U := W)
          (pullback.lift (pullback.fst V.hom f) t pullback.condition) hψ) ∘
          (Etale.freeSheafHomEquiv Λ V _) ∘
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _) := by
      funext φ
      simp only [Function.comp_apply]
      rw [constSheafHomEquiv_comp, freeSheafPullbackMap, Equiv.apply_symm_apply,
        freeSheafPullbackSection, ModuleSheaf.pullSection_naturality, Adjunction.homEquiv_unit,
        Etale.freeSheafHomEquiv_comp]
      have hg : Etale.freeSheafHomEquiv Λ V _
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
            ((Etale.freeSheaf Λ S).obj V)) =
          Etale.modulePullbackSection Λ f _ V (freeSheafGenerator Λ V) := by
        rw [← Category.id_comp ((Etale.upperStarLowerStarAdjunction _ f).unit.app _),
          Etale.freeSheafHomEquiv_comp]
        rfl
      rw [hg]
      rfl
    rw [← (constSheafHomEquiv Λ _).bijective.of_comp_iff', e]
    exact (bijective_pullSection_of_etale_moduleCat Λ t inferInstance B _ hψ).comp
      ((Etale.freeSheafHomEquiv Λ V _).bijective.comp (Equiv.bijective _))
  exact (Functor.mapExtPrecomp_bijective _ _
    (fun I _ ↦ Etale.injective_upperStar_obj_of_etale Λ t I) hu F q).comp
    (DerivedCategory.Plus.shiftedHomAddEquivExt _ _ q).bijective

lemma cohomologyPresheafRestrict_congr {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    {b b' : T ⟶ V.left} (hb : b ≫ V.hom = t ≫ f) (h : b = b') :
    cohomologyPresheafRestrict Λ f F q t V b hb =
      cohomologyPresheafRestrict Λ f F q t V b' (h ▸ hb) := by
  subst h
  rfl

/-- `cohomologyPresheafRestrict_comp` with the composite morphisms given up to equality. -/
lemma cohomologyPresheafRestrict_comp' {T T' : Scheme.{u}} (t : T ⟶ X) (h : T' ⟶ T)
    (V : S.Etale) (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) (t' : T' ⟶ X) (ht' : h ≫ t = t')
    (b' : T' ⟶ V.left) (hb' : h ≫ b = b')
    (p : (Etale.higherDirectImagePresheaf Λ f q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V)) :
    cohomologyPresheafRestrict Λ f F q t' V b' (by rw [← ht', ← hb', Category.assoc, hb,
        Category.assoc]) p =
      cohomologyRestrictOver Λ t' t h ht' F q (cohomologyPresheafRestrict Λ f F q t V b hb p) := by
  subst ht' hb'
  exact cohomologyPresheafRestrict_comp Λ f F q t h V b hb p
end Restrict

section Stalk

variable {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The geometric stalk of `Hᵠ(Rf_* K)` at `s` is the fibre at `s` of the hypercohomology presheaf
`V ↦ Hᵠ(V ×_S X, K|)`, of which it is the sheafification. -/
noncomputable def presheafFiberHigherDirectImagePresheafAddEquiv (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((Scheme.pointSmallEtale s).presheafFiber (A := AddCommGrpCat.{u + 1})).obj
      (Etale.higherDirectImagePresheaf Λ f q K) ≃+
      (Scheme.geometricStalkFunctor s (ModuleCat.{u + 1} Λ)).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj
          (R+((f)_*[ModuleCat.{u + 1} Λ]).obj K)) :=
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : LocallySmall.{u} S.Etale := locallySmall_self _
  have h := Etale.isLocallyBijective_higherDirectImagePresheafToSheaf Λ f q K
  have := h.1
  have := h.2
  (AddEquiv.ofBijective ((Scheme.pointSmallEtale s).presheafFiber.map
      (Etale.higherDirectImagePresheafToSheaf Λ f q K)).hom
    ((Scheme.pointSmallEtale s).toPresheafFiber_map_bijective _)).trans
    (((Scheme.pointSmallEtale s).sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app _).addCommGroupIsoToAddEquiv


/-- The point `S_(s) ×_S X ⟶ V` of a pointed étale neighbourhood `(V, v)` of `s`, through the
strict localization. -/
noncomputable def stalkPoint (x : Scheme.PointedEtaleNeighborhood s) :
    pullback (Scheme.strictLocalizationToBase s) f ⟶ x.1.left :=
  pullback.fst _ _ ≫ (Scheme.strictLocalizationConeAll s).π.app x

lemma stalkPoint_w (x : Scheme.PointedEtaleNeighborhood s) :
    stalkPoint f s x ≫ x.1.hom = pullback.snd _ _ ≫ f := by
  rw [stalkPoint, Category.assoc, ← pullback.condition]
  congr 1
  exact (Scheme.strictLocalizationConeAll s).w (Scheme.PointedEtaleNeighborhood.toBase s x)

lemma stalkPoint_map {x y : Scheme.PointedEtaleNeighborhood s} (g : x ⟶ y) :
    stalkPoint f s x ≫ g.1.left = stalkPoint f s y := by
  rw [stalkPoint, stalkPoint, Category.assoc]
  congr 1
  exact (Scheme.strictLocalizationConeAll s).w g


lemma stalkPoint_ι (x : Scheme.AffinePointedEtaleNeighborhood s) :
    stalkPoint f s ((Scheme.AffinePointedEtaleNeighborhood.ι s).obj x) =
      pullback.fst _ _ ≫ (Scheme.strictLocalizationCone s).π.app x := by
  rw [stalkPoint]
  erw [Functor.Initial.extendCone_obj_π_app' (F := Scheme.AffinePointedEtaleNeighborhood.ι s) _
      (𝟙 _), CategoryTheory.Functor.map_id, Category.comp_id]
variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)

lemma cohomologyPresheafRestrict_stalkPoint_map {V V' : S.Etale} (a : V ⟶ V')
    (v : (Scheme.pointSmallEtale s).fiber.obj V)
    (p : (Etale.higherDirectImagePresheaf Λ f q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V')) :
    cohomologyPresheafRestrict Λ f F q _ V (stalkPoint f s (Functor.elementsMk _ V v))
      (stalkPoint_w f s (Functor.elementsMk _ V v))
        ((Etale.higherDirectImagePresheaf Λ f q
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).map a.op p) =
      cohomologyPresheafRestrict Λ f F q _ V' (stalkPoint f s (Functor.elementsMk _ V' _))
        (stalkPoint_w f s
          (Functor.elementsMk _ V' ((Scheme.pointSmallEtale s).fiber.map a v))) p := by
  have e : stalkPoint f s (Functor.elementsMk _ V v) ≫ a.left =
      stalkPoint f s (Functor.elementsMk _ V' ((Scheme.pointSmallEtale s).fiber.map a v)) :=
    stalkPoint_map f s (Functor.Elements.homMk (x := Functor.elementsMk _ V v)
      (y := Functor.elementsMk _ V' _) a rfl)
  rw [cohomologyPresheafRestrict_map, cohomologyPresheafRestrict_congr Λ f F q _ V' _ e]

/-- The comparison map from the fibre at `s` of the cohomology presheaf `V ↦ Hᵠ(V ×_S X, F|)`
to the cohomology `Hᵠ(S_(s) ×_S X, F|)`: restriction along the points `S_(s) ×_S X ⟶ V`. -/
noncomputable def higherDirectImageStalkComparison :
    ((Scheme.pointSmallEtale s).presheafFiber (A := AddCommGrpCat.{u + 1})).obj
      (Etale.higherDirectImagePresheaf Λ f q ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
      AddCommGrpCat.of (Ext (SemiSimplicialObject.constSheaf
          (pullback (Scheme.strictLocalizationToBase s) f).smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.snd (Scheme.strictLocalizationToBase s) f)).obj F) q) :=
  (Scheme.pointSmallEtale s).presheafFiberDesc
    (fun V v ↦ AddCommGrpCat.ofHom (cohomologyPresheafRestrict Λ f F q _ V
      (stalkPoint f s (Functor.elementsMk _ V v)) (stalkPoint_w f s (Functor.elementsMk _ V v))))
    (fun _ _ a v ↦ AddCommGrpCat.ext fun p ↦
      cohomologyPresheafRestrict_stalkPoint_map Λ f s F q a v p)

lemma toPresheafFiber_higherDirectImageStalkComparison (V : S.Etale)
    (v : (Scheme.pointSmallEtale s).fiber.obj V)
    (p : (Etale.higherDirectImagePresheaf Λ f q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V)) :
    higherDirectImageStalkComparison Λ f s F q ((Scheme.pointSmallEtale s).toPresheafFiber V v
      (Etale.higherDirectImagePresheaf Λ f q ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) p) =
      cohomologyPresheafRestrict Λ f F q _ V (stalkPoint f s (Functor.elementsMk _ V v))
        (stalkPoint_w f s (Functor.elementsMk _ V v)) p :=
  ConcreteCategory.congr_hom
    ((Scheme.pointSmallEtale s).toPresheafFiber_presheafFiberDesc _ _ V v) p
end Stalk

/-- **Strict-henselization stalk formula** (blueprint
`prop-weil-pbc-strict-henselization-stalk-formula`): for a quasi-compact quasi-separated
`f : X ⟶ S`, a sheaf `F` of `Λ`-modules on `X_ét` and a geometric point `s : Spec Ω ⟶ S`, the
geometric stalk of `R^q f_* F` at `s` is the étale cohomology `H^q(S_(s) ×_S X, F|)` of the base
change of `X` to the strict localization `S_(s)`. -/
@[stacks 03Q9]
theorem nonempty_geometricStalk_higherDirectImage_addEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Nonempty ((Scheme.geometricStalkFunctor s (ModuleCat.{u + 1} Λ)).obj
        (Etale.higherDirectImage Λ f q F) ≃+
      Ext (SemiSimplicialObject.constSheaf
          (pullback (Scheme.strictLocalizationToBase s) f).smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.snd (Scheme.strictLocalizationToBase s) f)).obj F) q) := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : LocallySmall.{u} S.Etale := locallySmall_self _
  let P := Etale.higherDirectImagePresheaf Λ f q ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  let Θ := higherDirectImageStalkComparison Λ f s F q
  suffices hΘ : Function.Bijective Θ from
    ⟨(presheafFiberHigherDirectImagePresheafAddEquiv Λ f s (q : ℤ)
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).symm.trans
        (AddEquiv.ofBijective Θ.hom hΘ)⟩
  -- a small cofiltered model of the affine pointed étale neighbourhoods of `s`
  obtain ⟨J, _, _, G₀, _⟩ :=
    InitiallySmall.exists_of_isCofiltered.{u} (Scheme.AffinePointedEtaleNeighborhood s)
  let D : J ⥤ Over X := G₀ ⋙ Scheme.affineNeighborhoodDiagramOver s ⋙ Over.pullback f
  let c : Cone D := (Over.pullback f).mapCone ((Scheme.strictLocalizationConeOver s).whisker G₀)
  have hc : IsLimit ((Over.forget X).mapCone c) :=
    (Functor.Initial.isLimitWhiskerEquiv G₀ _).symm
      (Scheme.isLimitStrictLocalizationConePullback s f)
  -- the neighbourhood `V_j` of `s` and its point
  let V (j : J) : S.Etale := (G₀.obj j).obj.1
  let v (j : J) : (Scheme.pointSmallEtale s).fiber.obj (V j) := (G₀.obj j).obj.2
  have : ∀ j, CompactSpace (D.obj j).left := fun j ↦ by
    have : CompactSpace ((𝟭 Scheme).obj (V j).left) :=
      inferInstanceAs (CompactSpace (G₀.obj j).obj.1.left)
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (V j).hom f)
  have : ∀ j, QuasiSeparatedSpace (D.obj j).left := fun j ↦ by
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj (V j).left) :=
      inferInstanceAs (QuasiSeparatedSpace (G₀.obj j).obj.1.left)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (V j).hom f)
  have : ∀ {i j : J} (φ : i ⟶ j), IsAffineHom (D.map φ).left := fun {i j} φ ↦ by
    let a : (V i).left ⟶ (V j).left := (G₀.map φ).hom.1.left
    have : IsAffineHom a := inferInstance
    have H : IsPullback (D.map φ).left (pullback.fst (V i).hom f) (pullback.fst (V j).hom f) a := by
      refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
        (IsPullback.of_hasPullback (V j).hom f).flip
      have e1 : (D.map φ).left ≫ pullback.snd (V j).hom f = pullback.snd (V i).hom f :=
        Over.w (D.map φ)
      have e2 : a ≫ (V j).hom = (V i).hom := MorphismProperty.Over.w (G₀.map φ).hom.1
      rw [e1, e2]
      exact (IsPullback.of_hasPullback (V i).hom f).flip
    exact MorphismProperty.of_isPullback H.flip this
  -- the comparison maps at the stages
  have KI (j : J) : (c.π.app j).left ≫ pullback.fst (V j).hom f =
      stalkPoint f s (Functor.elementsMk _ (V j) (v j)) := by
    refine Eq.trans ?_ (stalkPoint_ι f s (G₀.obj j)).symm
    simp only [c, Scheme.strictLocalizationConeOver]
    exact pullback.lift_fst _ _ _
  have hΘj (j : J) (p : P.obj (op (V j))) :
      Θ ((Scheme.pointSmallEtale s).toPresheafFiber (V j) (v j) P p) =
        cohomologyRestrictOver Λ c.pt.hom (D.obj j).hom (c.π.app j).left (Over.w _) F q
          (cohomologyPresheafRestrict Λ f F q (pullback.snd (V j).hom f) (V j)
            (pullback.fst (V j).hom f) pullback.condition p) :=
    (toPresheafFiber_higherDirectImageStalkComparison Λ f s F q (V j) (v j) p).trans
      (cohomologyPresheafRestrict_comp' Λ f F q (pullback.snd (V j).hom f) (c.π.app j).left (V j)
        (pullback.fst (V j).hom f) pullback.condition _ (Over.w _) _ (KI j) p)
  refine ⟨(injective_iff_map_eq_zero Θ.hom).2 fun ξ hξ ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨W, w, p, rfl⟩ := (Scheme.pointSmallEtale s).toPresheafFiber_jointly_surjective ξ
    obtain ⟨y, ⟨g₁⟩⟩ :=
      Scheme.AffinePointedEtaleNeighborhood.exists_hom s (Functor.elementsMk _ W w)
    obtain ⟨⟨j, ⟨⟩, g₂⟩⟩ : Nonempty (CostructuredArrow G₀ y) := IsConnected.is_nonempty
    let g : (Scheme.AffinePointedEtaleNeighborhood.ι s).obj (G₀.obj j) ⟶
        (Scheme.pointSmallEtale s).fiber.elementsMk W w :=
      (Scheme.AffinePointedEtaleNeighborhood.ι s).map g₂ ≫ g₁
    have hp : (Scheme.pointSmallEtale s).toPresheafFiber W w P p =
        (Scheme.pointSmallEtale s).toPresheafFiber (V j) (v j) P (P.map g.1.op p) := by
      have h2 : (Scheme.pointSmallEtale s).fiber.map g.1 (v j) = w := g.2
      exact (congrArg (fun z ↦ (Scheme.pointSmallEtale s).toPresheafFiber W z P p) h2).symm.trans
        ((Scheme.pointSmallEtale s).toPresheafFiber_w_apply g.1 (v j) P p).symm
    rw [hp] at hξ ⊢
    rw [hΘj] at hξ
    obtain ⟨j', φ, hφ⟩ := Etale.exists_cohomologyRestrictOver_eq_zero_of_isLimit Λ D c hc F q j _
      hξ
    let a : V j' ⟶ V j := (G₀.map φ).hom.1
    have hφ' := (cohomologyPresheafRestrict_comp' Λ f F q (pullback.snd (V j).hom f)
      (D.map φ).left (V j) (pullback.fst (V j).hom f) pullback.condition
      (pullback.snd (V j').hom f) (Over.w (D.map φ)) (pullback.fst (V j').hom f ≫ a.left)
      (pullback.lift_fst _ _ _) _).trans hφ
    have h3 := cohomologyPresheafRestrict_map Λ f F q (pullback.snd (V j').hom f) a
      (pullback.fst (V j').hom f) pullback.condition (P.map g.1.op p)
    have h0 := (bijective_cohomologyPresheafRestrict Λ f F q (V j')).1
      ((h3.trans hφ').trans (map_zero _).symm)
    have hv : (Scheme.pointSmallEtale s).fiber.map a (v j') = v j := (G₀.map φ).hom.2
    rw [← hv, ← (Scheme.pointSmallEtale s).toPresheafFiber_w_apply, h0, map_zero]
  · obtain ⟨j, y, hy⟩ := Etale.exists_cohomologyRestrictOver_eq_of_isLimit Λ D c hc F q x
    obtain ⟨p, rfl⟩ := (bijective_cohomologyPresheafRestrict Λ f F q (V j)).2 y
    exact ⟨_, (hΘj j p).trans hy⟩

end AlgebraicGeometry.Etale
