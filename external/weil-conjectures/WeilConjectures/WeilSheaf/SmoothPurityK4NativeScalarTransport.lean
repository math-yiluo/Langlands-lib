/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarCoefficientTransport
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Scalar transport with normalized component sources -/

@[expose] public section

namespace CategoryTheory.K4Native

/-- A descent component whose source is explicitly the iterated object map. -/
def scalarComponent
    {C₀ C : Type*} [Category C₀] [Category C]
    (P : C₀ ⥤ C) (Q : C ⥤ C) (b : P ⋙ Q ≅ P) (M : C₀) :
    Q.obj (P.obj M) ≅ P.obj M := b.app M

/-- Functor-indexed coefficient transport retains the canonical comparison
components instead of unfolding their concrete source categories. -/
lemma scalarFunctor_coefficient
    {C₀ C D₀ D : Type*} [Category C₀] [Category C] [Preadditive C]
    [Category D₀] [Category D] [Preadditive D]
    (P : C₀ ⥤ C) (F₀ : C₀ ⥤ D₀) (F : C ⥤ D) [F.Additive]
    (P' : D₀ ⥤ D) (Q : C ⥤ C) (R : D ⥤ D)
    (τ : Q ⋙ F ≅ F ⋙ R) (α : P ⋙ F ≅ F₀ ⋙ P')
    (b : P ⋙ Q ≅ P) (b' : P' ⋙ R ≅ P') (M N : C₀)
    (hc : ∀ K, F.map (b.hom.app K) ≫ α.hom.app K =
      τ.hom.app (P.obj K) ≫ R.map (α.hom.app K) ≫ b'.hom.app (F₀.obj K))
    (e : P.obj M ≅ P.obj N) (c : ℤ)
    (he : c • (b.hom.app M ≫ e.hom) = Q.map e.hom ≫ b.hom.app N) :
    c • ((scalarComponent P' R b' (F₀.obj M)).hom ≫
        ((α.app M).symm ≪≫ F.mapIso e ≪≫ α.app N).hom) =
      R.map ((α.app M).symm ≪≫ F.mapIso e ≪≫ α.app N).hom ≫
        (scalarComponent P' R b' (F₀.obj N)).hom := by
  exact purity_scalarFunctor_coefficient P F₀ F P' Q R τ α b b' M N hc e c he

/-- The isomorphism version retains both the datum's component and the named
composite isomorphism in its conclusion. -/
lemma scalarDatum_postcomposeIso
    {C₀ C : Type*} [Category C₀] [Category C] [Preadditive C]
    (P : C₀ ⥤ C) (Q : C ⥤ C) (b : P ⋙ Q ≅ P)
    {K M N : C₀} (e : P.obj K ≅ P.obj M) (v : M ≅ N) (t : P.obj K ≅ P.obj N)
    (ht : t = e ≪≫ P.mapIso v) (c : ℤ)
    (he : c • ((scalarComponent P Q b K).hom ≫ e.hom) =
      Q.map e.hom ≫ (scalarComponent P Q b M).hom) :
    c • ((scalarComponent P Q b K).hom ≫ t.hom) = Q.map t.hom ≫ (scalarComponent P Q b N).hom := by
  exact purity_scalarDatum_postcomposeIso P Q b e v t ht c he

end CategoryTheory.K4Native
