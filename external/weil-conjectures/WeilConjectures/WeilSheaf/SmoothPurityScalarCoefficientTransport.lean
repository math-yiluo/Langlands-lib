/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarDatumConjugation
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Scalar equations under coefficient extension -/

@[expose] public section

namespace CategoryTheory

/-- An additive functor preserves a scalar equation when its endofunctor
comparison is used to transport the two data. -/
lemma purity_scalarDatum_map
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (Q : C ⥤ C) (R : D ⥤ D)
    (τ : Q ⋙ F ≅ F ⋙ R) {M N : C}
    (a : Q.obj M ⟶ M) (b : Q.obj N ⟶ N) (e : M ≅ N) (c : ℤ)
    (he : c • (a ≫ e.hom) = Q.map e.hom ≫ b) :
    c • ((τ.inv.app M ≫ F.map a) ≫ (F.mapIso e).hom) =
      R.map (F.mapIso e).hom ≫ (τ.inv.app N ≫ F.map b) := by
  have hn := τ.inv.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.mapIso_hom, Category.assoc]
  rw [← F.map_comp, ← Preadditive.comp_zsmul, ← F.map_zsmul, he,
    F.map_comp, ← Category.assoc, ← hn, Category.assoc]

/-- Functor-indexed coefficient transport retains the canonical comparison
components instead of unfolding their concrete source categories. -/
lemma purity_scalarFunctor_coefficient
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
    c • (b'.hom.app (F₀.obj M) ≫
        ((α.app M).symm ≪≫ F.mapIso e ≪≫ α.app N).hom) =
      R.map ((α.app M).symm ≪≫ F.mapIso e ≪≫ α.app N).hom ≫
        b'.hom.app (F₀.obj N) := by
  apply purity_scalarDatum_conjugate R (α.app M) (α.app N)
    (τ.inv.app (P.obj M) ≫ F.map (b.hom.app M))
    (τ.inv.app (P.obj N) ≫ F.map (b.hom.app N))
    (b'.hom.app (F₀.obj M)) (b'.hom.app (F₀.obj N))
  · simp only [Iso.app_hom, Category.assoc, hc, Iso.inv_hom_id_app_assoc]
  · simp only [Iso.app_hom, Category.assoc, hc, Iso.inv_hom_id_app_assoc]
  · exact purity_scalarDatum_map F Q R τ (b.hom.app M) (b.hom.app N) e c he

/-- Postcomposition with a morphism pulled back from the base preserves a scalar law. -/
lemma purity_scalarDatum_postcompose
    {C₀ C : Type*} [Category C₀] [Category C] [Preadditive C]
    (P : C₀ ⥤ C) (Q : C ⥤ C) (b : P ⋙ Q ≅ P)
    {A : C} {M N : C₀} (a : Q.obj A ⟶ A) (e : A ⟶ P.obj M)
    (v : M ⟶ N) (c : ℤ)
    (he : c • (a ≫ e) = Q.map e ≫ b.hom.app M) :
    c • (a ≫ (e ≫ P.map v)) = Q.map (e ≫ P.map v) ≫ b.hom.app N := by
  have hn := b.hom.naturality v
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [Preadditive.zsmul_comp, Category.assoc] using
    congrArg (fun w ↦ w ≫ P.map v) he

/-- The isomorphism version retains both the datum's component and the named
composite isomorphism in its conclusion. -/
lemma purity_scalarDatum_postcomposeIso
    {C₀ C : Type*} [Category C₀] [Category C] [Preadditive C]
    (P : C₀ ⥤ C) (Q : C ⥤ C) (b : P ⋙ Q ≅ P)
    {K M N : C₀} (e : P.obj K ≅ P.obj M) (v : M ≅ N) (t : P.obj K ≅ P.obj N)
    (ht : t = e ≪≫ P.mapIso v) (c : ℤ)
    (he : c • (b.hom.app K ≫ e.hom) = Q.map e.hom ≫ b.hom.app M) :
    c • (b.hom.app K ≫ t.hom) = Q.map t.hom ≫ b.hom.app N := by
  subst t
  exact purity_scalarDatum_postcompose P Q b (b.hom.app K) e.hom v.hom c he

end CategoryTheory
