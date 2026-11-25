/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SupportCohomologyTrianglePullback

/-!

# Restriction maps of derived sections over étale objects

Let `e : X' ⟶ X` be a morphism of schemes, `V` an étale `X`-scheme, `W` an étale `X'`-scheme and
`φ : W ⟶ V` a morphism over `e`. The pullback of sections `F(V) ⟶ (e^* F)(W)`
(`AlgebraicGeometry.Etale.sectionsPullback`) induces, on right derived functors, the *restriction*
```
RΓ(V, K) ⟶ RΓ(W, e^* K)
```
(`AlgebraicGeometry.Etale.sectionsRestriction`). All the restriction maps of the local calculation
on curves (blueprint `lemma-vanishing-local-term-zero-stalk`) are of this form: the restriction of
`RΓ(T ∖ G, P)` to the punctured diagonal, its factorization through `RΓ(T ∖ (G ∪ V), P)`, and the
pullbacks along the finite covers. They compose
(`AlgebraicGeometry.Etale.sectionsRestriction_comp`), and the third component of the morphism of
localization triangles `sectionsWithSupportTrianglePullback` is one of them
(`AlgebraicGeometry.Etale.sectionsWithSupportTrianglePullback_app_hom₃`).

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite Pretriangulated DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C C' D : Type*} [Category C] [Category C'] [Category D] [Abelian C] [Abelian C']
  [Abelian D] [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
  (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {F : C ⥤ D} {F' : C' ⥤ D} [F.Additive] [F'.Additive]

/-- If `α : F ⟶ P ⋙ F'` is an isomorphism and `P` preserves K-injective complexes, the pullback
map `RF ⟶ P ⋙ RF'` of right derived functors is an isomorphism: on a K-injective complex `I` it
is `F(I) ≅ F'(P I)`, `P I` being K-injective. -/
lemma isIso_rightDerivedPullback_app [P.PreservesKInjectiveComplexes] (α : F ⟶ P ⋙ F')
    [IsIso α] (K : DerivedCategory C) : IsIso ((rightDerivedPullback P α).app K) := by
  obtain ⟨L, ⟨e⟩⟩ : ∃ L, Nonempty (DerivedCategory.Q.obj L ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  obtain ⟨I, _, i, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective L
  refine (NatTrans.isIso_app_iff_of_iso _ (e.symm ≪≫ asIso (DerivedCategory.Q.map i))).2 ?_
  have h := rightDerivedPullback_app_Q_obj P α I ((P.mapHomologicalComplex _).obj I) (𝟙 _)
  have : IsIso ((rightDerivedPullback P α).app (Q.obj I) ≫
      F'.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app I ≫ Q.map (𝟙 _))) := by
    have : IsIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I) :=
      inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex (asIso α) _).app I).hom)
    have : IsIso ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (𝟙 ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := by
      rw [CategoryTheory.Functor.map_id]
      infer_instance
    rw [h]
    refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' ?_ inferInstance)
    have := IsIso.comp_isIso' (f := (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I)
      inferInstance (inferInstance : IsIso ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (𝟙 ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))))
    exact Functor.map_isIso _ _
  exact IsIso.of_isIso_comp_right _ (F'.rightDerivedFunctor.map
    (P.mapDerivedCategoryFactors.hom.app I ≫ Q.map (𝟙 _)))

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Restriction

variable {X X' : Scheme.{u}} (e : X' ⟶ X)

/-- The **restriction of derived sections** `RΓ(V, K) ⟶ RΓ(W, e^* K)` along a morphism
`φ : W ⟶ V` over `e : X' ⟶ X` from an étale `X'`-scheme `W` to an étale `X`-scheme `V`: the
pullback map of right derived functors induced by the pullback of sections. -/
noncomputable def sectionsRestriction {V : X.Etale} {W : X'.Etale} (φ : W.left ⟶ V.left)
    (hφ : φ ≫ V.hom = W.hom ≫ e) :
    ((sheafSections X.smallEtaleTopology A).obj (op V)).rightDerivedFunctor ⟶
      (e)^*[A].mapDerivedCategory ⋙
        ((sheafSections X'.smallEtaleTopology A).obj (op W)).rightDerivedFunctor :=
  Functor.rightDerivedPullback (e)^*[A] (sectionsPullback A e φ hφ)

lemma sectionsRestriction_congr {V : X.Etale} {W : X'.Etale} {φ φ' : W.left ⟶ V.left}
    (hφ : φ ≫ V.hom = W.hom ≫ e) (h : φ = φ') :
    sectionsRestriction A e φ hφ = sectionsRestriction A e φ' (h ▸ hφ) := by
  subst h
  rfl

/-- The third component of the morphism of localization triangles along a morphism of pairs is
the restriction of derived sections over the open complements. -/
lemma sectionsWithSupportTrianglePullback_app_hom₃ {Z Z' : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (i' : Z' ⟶ X') [IsClosedImmersion i']
    (h : i'.openComplement ≤ e ⁻¹ᵁ i.openComplement)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ((sectionsWithSupportTrianglePullback A e i i' h).app K).hom₃ =
      (sectionsRestriction A e (V := Scheme.Etale.mk i.openComplement.ι)
        (W := Scheme.Etale.mk i'.openComplement.ι) (e.resLE _ _ h)
        (Scheme.Hom.resLE_comp_ι _ _)).app K.obj :=
  rfl

variable {X'' : Scheme.{u}} (e' : X'' ⟶ X')

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

/-- **Restrictions compose**: the restriction along `φ' ≫ φ` over `e' ≫ e` is the composite of
the restrictions along `φ` and `φ'`, up to the comparison `(e' ≫ e)^* ≅ e'^* e^*`. -/
lemma sectionsRestriction_comp {V : X.Etale} {W : X'.Etale} {W'' : X''.Etale}
    (φ : W.left ⟶ V.left) (hφ : φ ≫ V.hom = W.hom ≫ e) (φ' : W''.left ⟶ W.left)
    (hφ' : φ' ≫ W.hom = W''.hom ≫ e') (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (sectionsRestriction A (e' ≫ e) (φ' ≫ φ) (by rw [assoc, hφ, ← assoc, hφ', assoc])).app K ≫
        ((sheafSections X''.smallEtaleTopology A).obj (op W'')).rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryNatIso (upperStarComp A e' e) ≪≫
            (Functor.mapDerivedCategoryCompIso (e)^*[A] (e')^*[A]).symm).hom.app K) =
      (sectionsRestriction A e φ hφ).app K ≫
        (sectionsRestriction A e' φ' hφ').app ((e)^*[A].mapDerivedCategory.obj K) :=
  Functor.rightDerivedPullback_comp _ _ _ _ _ _ _ (by
    ext F
    exact sectionsPullback_comp A e e' φ hφ φ' hφ' F) K

end Restriction

end AlgebraicGeometry.Etale
