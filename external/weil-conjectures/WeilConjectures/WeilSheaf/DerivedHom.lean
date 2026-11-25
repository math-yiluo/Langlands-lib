/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom
public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# The derived internal hom of pro-étale Weil sheaves

The internal hom `𝓗om(A, B)` of pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.ihom`)
is contravariant in `A` (`AlgebraicGeometry.ProEtaleWeilSheaf.ihomMapLeft`), which makes it a
bifunctor `AlgebraicGeometry.ProEtaleWeilSheaf.ihomBifunctor`. Its derived functor in the sense
of `WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom`, computed by the hom complex
`∏_p 𝓗om(K^p, I^{p + n})` between K-injective complexes representing the two variables, is the
derived internal hom

`RHom(-, L) : D(X̄_proét, Weil)ᵒᵖ ⥤ D(X̄_proét, Weil)`

(`AlgebraicGeometry.ProEtaleWeilSheaf.derivedHom`), the internal hom `R𝓗om_{ℚ̄_ℓ}(-, L)` of
`prose-03-02` with its Weil structure (`prose-10-20`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor Opposite

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtaleWeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- A morphism `φ : A ⟶ A'` of pro-étale Weil sheaves induces `𝓗om(A', B) ⟶ 𝓗om(A, B)`. -/
noncomputable def ihomMapLeft {A A' : ProEtaleWeilSheaf k₀ l X} (φ : A ⟶ A')
    (B : ProEtaleWeilSheaf k₀ l X) : ihom k₀ l X A' B ⟶ ihom k₀ l X A B :=
  ObjectProperty.homMk ⟨(Mod.ihomMap φ.hom.f).app B.carrier, by
    have h := adicLowerStarCompIhomIso_inv_app_comp_ihomMap l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv φ.hom.f B.carrier
    have hφ : A.str.inv ≫ (WeilSheaf.frobeniusPullback k₀ l X).map φ.hom.f =
        φ.hom.f ≫ A'.str.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
      exact φ.hom.h
    rw [ihom_obj_str, ihom_obj_str]
    change (WeilSheaf.frobeniusPullback k₀ l X).map ((Mod.ihomMap φ.hom.f).app B.carrier) ≫ _ =
      _ ≫ (Mod.ihomMap φ.hom.f).app B.carrier
    rw [← reassoc_of% h]
    simp only [Category.assoc]
    erw [(Mod.ihomMap φ.hom.f).naturality B.obj.str]
    rw [← NatTrans.comp_app_assoc, ← NatTrans.comp_app_assoc, ← Mod.ihomMap_comp,
      ← Mod.ihomMap_comp, hφ]⟩

@[simp]
lemma ihomMapLeft_hom_f {A A' : ProEtaleWeilSheaf k₀ l X} (φ : A ⟶ A')
    (B : ProEtaleWeilSheaf k₀ l X) :
    (ihomMapLeft φ B).hom.f = (Mod.ihomMap φ.hom.f).app B.carrier :=
  rfl

variable (k₀ l X) in
/-- The internal hom of pro-étale Weil sheaves as a bifunctor, contravariant in the first
variable. -/
noncomputable def ihomBifunctor :
    (ProEtaleWeilSheaf k₀ l X)ᵒᵖ ⥤ ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X where
  obj A := ihomFunctor k₀ l X A.unop
  map φ :=
    { app B := ihomMapLeft φ.unop B
      naturality _ _ f := IsoAlgebra.hom_ext (by
        change (AdicSheaf.ihom _).map f.hom.f ≫ (Mod.ihomMap φ.unop.hom.f).app _ =
          (Mod.ihomMap φ.unop.hom.f).app _ ≫ (AdicSheaf.ihom _).map f.hom.f
        exact (Mod.ihomMap φ.unop.hom.f).naturality f.hom.f) }
  map_id A := by
    refine NatTrans.ext (funext fun B ↦ IsoAlgebra.hom_ext ?_)
    change (Mod.ihomMap (𝟙 A.unop.carrier)).app B.carrier = 𝟙 _
    rw [Mod.ihomMap_id]
    rfl
  map_comp φ ψ := by
    refine NatTrans.ext (funext fun B ↦ IsoAlgebra.hom_ext ?_)
    change (Mod.ihomMap (ψ.unop.hom.f ≫ φ.unop.hom.f)).app B.carrier =
      (Mod.ihomMap φ.unop.hom.f).app B.carrier ≫ (Mod.ihomMap ψ.unop.hom.f).app B.carrier
    rw [Mod.ihomMap_comp]
    rfl

instance (A : (ProEtaleWeilSheaf k₀ l X)ᵒᵖ) : ((ihomBifunctor k₀ l X).obj A).Additive :=
  ⟨ObjectProperty.hom_ext _ (Algebra.Hom.ext (ProEtale.AdicSheaf.ihom A.unop.carrier).map_add)⟩

instance : (ihomBifunctor k₀ l X).Additive where
  map_add {A A'} {φ ψ} := by
    refine NatTrans.ext (funext fun B ↦ ?_)
    rw [NatTrans.app_add]
    apply (IsoAlgebra.forget _).map_injective
    rw [(IsoAlgebra.forget _).map_add]
    change (Mod.ihomMap (φ + ψ).unop.hom.f).app B.carrier =
      (Mod.ihomMap φ.unop.hom.f).app B.carrier + (Mod.ihomMap ψ.unop.hom.f).app B.carrier
    rw [unop_add, ← IsoAlgebra.forget_map, (IsoAlgebra.forget _).map_add, IsoAlgebra.forget_map,
      IsoAlgebra.forget_map, Mod.ihomMap_add, NatTrans.app_add]

variable (k₀ l X) in
/-- The derived internal hom `RHom(-, L) = R𝓗om_{ℚ̄_ℓ,X̄}(-, L)` of pro-étale Weil sheaves into an
object `L` of the derived category (blueprint: `prose-03-02`, with the
Weil structure of `prose-10-20`): the hom complex `∏_p 𝓗om(K^p, I^{p + n})` between
K-injective complexes `K` and `I` representing the two variables. -/
noncomputable def derivedHom (L : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    (DerivedCategory (ProEtaleWeilSheaf k₀ l X))ᵒᵖ ⥤ DerivedCategory (ProEtaleWeilSheaf k₀ l X) :=
  DerivedCategory.bifunctorRHom (ihomBifunctor k₀ l X) L

end ProEtaleWeilSheaf

end AlgebraicGeometry
