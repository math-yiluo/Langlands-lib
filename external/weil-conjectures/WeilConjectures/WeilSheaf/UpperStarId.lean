/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.WeilSheaf.UpperStarComp
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFullyFaithful

/-!
# Identity, congruence and composition isomorphisms for pullbacks of Weil sheaves

`(𝟙 X)^* ≅ 𝟭`, `φ^* ≅ φ'^*` for `φ = φ'` and `(f ≫ g)^* ≅ g^* ⋙ f^*`, for pullbacks of pro-étale
Weil sheaves, Weil sheaves and Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory.ObjectProperty

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] (P : ObjectProperty C)
  (Q : ObjectProperty D) (R : ObjectProperty E)

/-- An isomorphism `H ≅ F ⋙ G` induces an isomorphism between the induced functors between
full subcategories. -/
@[simps!]
def liftFullSubcategoryCompIso {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : H ≅ F ⋙ G)
    (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ X, Q X → R (G.obj X))
    (hH : ∀ X, P X → R (H.obj X)) :
    P.liftFullSubcategory R H hH ≅
      P.liftFullSubcategory Q F hF ⋙ Q.liftFullSubcategory R G hG :=
  NatIso.ofComponents (fun X ↦ R.isoMk (e.app X.obj)) fun f ↦ R.hom_ext (e.hom.naturality f.hom)

/-- An isomorphism `H ≅ 𝟭 C` induces an isomorphism between the induced endofunctor of a full
subcategory and the identity. -/
@[simps!]
def liftFullSubcategoryIdIso {H : C ⥤ C} (e : H ≅ 𝟭 C) (hH : ∀ X, P X → P (H.obj X)) :
    P.liftFullSubcategory P H hH ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X ↦ P.isoMk (e.app X.obj)) fun f ↦ P.hom_ext (e.hom.naturality f.hom)

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

section ProEtaleWeilSheaf

variable (k₀ l)

/-- The pullbacks of pro-étale Weil sheaves along equal morphisms are isomorphic. -/
noncomputable def ProEtaleWeilSheaf.upperStarCongrIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {φ φ' : X ⟶ Y}
    [φ.IsOver (Spec (CommRingCat.of k₀))] [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') :
    ProEtaleWeilSheaf.upperStar k₀ l φ ≅ ProEtaleWeilSheaf.upperStar k₀ l φ' := by
  subst h
  exact Iso.refl _

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The pullback of pro-étale Weil sheaves along the identity is fully faithful: it is the
transport of Weil structures along the pullback along the identity of the geometric fiber,
an equivalence. -/
noncomputable def ProEtaleWeilSheaf.fullyFaithfulUpperStarId :
    (ProEtaleWeilSheaf.upperStar k₀ l (𝟙 X)).FullyFaithful := by
  have : IsIso (Scheme.Hom.geometricFiberMap (𝟙 X)
      (comp_over (𝟙 X) (Spec (CommRingCat.of k₀)))) := by
    rw [Scheme.Hom.geometricFiberMap_id]
    infer_instance
  exact IsoAlgebra.fullyFaithfulMapOfNatIso _ (Functor.FullyFaithful.ofFullyFaithful _)

/-- The pullback of pro-étale Weil sheaves along the identity is isomorphic to the identity
functor: it is fully faithful and satisfies `(𝟙 X)^* ⋙ (𝟙 X)^* ≅ (𝟙 X ≫ 𝟙 X)^* = (𝟙 X)^*`. -/
noncomputable def ProEtaleWeilSheaf.upperStarIdIso :
    ProEtaleWeilSheaf.upperStar k₀ l (𝟙 X) ≅ 𝟭 _ :=
  (ProEtaleWeilSheaf.fullyFaithfulUpperStarId k₀ l X).isoIdOfCompSelfIso
    ((ProEtaleWeilSheaf.upperStarCompIso k₀ l (𝟙 X) (𝟙 X)).symm ≪≫
      ProEtaleWeilSheaf.upperStarCongrIso k₀ l (Category.comp_id (𝟙 X)))

end ProEtaleWeilSheaf

variable [Fact (ringChar k₀ ≠ l)]

section WeilSheaf

/-- Pullbacks of Weil sheaves along equal morphisms are isomorphic. Stating this for an equation
of morphisms keeps the kernel from unfolding `WeilSheaf.upperStar` when two instances of
`Scheme.Hom.IsOver` differ; the instances are implicit arguments, so that they are found by
unification. -/
noncomputable def WeilSheaf.upperStarCongr {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {φ ψ : X ⟶ Y}
    {_ : φ.IsOver (Spec (CommRingCat.of k₀))} {_ : ψ.IsOver (Spec (CommRingCat.of k₀))}
    (h : φ = ψ) : WeilSheaf.upperStar (k₀ := k₀) (l := l) φ ≅ WeilSheaf.upperStar ψ :=
  eqToIso (by subst h; rfl)

/-- Pullback of Weil sheaves is compatible with composition: `(f ≫ g)^* ≅ g^* ⋙ f^*`. -/
noncomputable def WeilSheaf.upperStarCompIso {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf.upperStar (k₀ := k₀) (l := l) (f ≫ g) ≅
      WeilSheaf.upperStar g ⋙ WeilSheaf.upperStar f :=
  ObjectProperty.liftFullSubcategoryCompIso _ _ _
    (ProEtaleWeilSheaf.upperStarCompIso k₀ l f g) _ _ _

/-- `φ^* g^* F ≅ g'^* F` for `φ ≫ g = g'`, from the composition and congruence isomorphisms. -/
theorem WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (φ : Y ⟶ X) (g : X ⟶ Z) (g' : Y ⟶ Z)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    [g'.IsOver (Spec (CommRingCat.of k₀))] (h : φ ≫ g = g') (F : WeilSheaf k₀ l Z) :
    Nonempty ((WeilSheaf.upperStar φ).obj ((WeilSheaf.upperStar g).obj F) ≅
      (WeilSheaf.upperStar g').obj F) := by
  rw [← Functor.comp_obj]
  exact ⟨((WeilSheaf.upperStarCompIso φ g).app F).symm ≪≫
    (WeilSheaf.upperStarCongr h).app F⟩

/-- Pullback of Weil sheaves along the identity is the identity. -/
noncomputable def WeilSheaf.upperStarIdIso (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    WeilSheaf.upperStar (k₀ := k₀) (l := l) (𝟙 X) ≅ 𝟭 _ :=
  ObjectProperty.liftFullSubcategoryIdIso _ (ProEtaleWeilSheaf.upperStarIdIso k₀ l X) _

end WeilSheaf

section WeilComplex

/-- The pullbacks of Weil complexes along equal morphisms are isomorphic. -/
noncomputable def WeilComplex.upperStarCongrIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {φ φ' : X ⟶ Y}
    [φ.IsOver (Spec (CommRingCat.of k₀))] [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') :
    WeilComplex.upperStar (k₀ := k₀) (l := l) φ ≅ WeilComplex.upperStar φ' := by
  subst h
  exact Iso.refl _

/-- Pullback of Weil complexes is compatible with composition: `(f ≫ g)^* ≅ g^* ⋙ f^*`. -/
noncomputable def WeilComplex.upperStarCompIso {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))] :
    WeilComplex.upperStar (k₀ := k₀) (l := l) (f ≫ g) ≅
      WeilComplex.upperStar g ⋙ WeilComplex.upperStar f :=
  ObjectProperty.liftFullSubcategoryCompIso _ _ _
    (Functor.mapDerivedCategoryNatIso (ProEtaleWeilSheaf.upperStarCompIso k₀ l f g) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm) _ _ _

/-- Pullback of Weil complexes along the identity is the identity. -/
noncomputable def WeilComplex.upperStarIdIso (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] :
    WeilComplex.upperStar (k₀ := k₀) (l := l) (𝟙 X) ≅ 𝟭 _ :=
  ObjectProperty.liftFullSubcategoryIdIso _
    (Functor.mapDerivedCategoryNatIso (ProEtaleWeilSheaf.upperStarIdIso k₀ l X) ≪≫
      Functor.mapDerivedCategoryIdIso _) _

end WeilComplex

end AlgebraicGeometry
