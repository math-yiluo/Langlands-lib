/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.DirectImageStalk
public import WeilConjectures.WeilSheaf.StalkTransportGeneral

/-!
# The counit of `j^* ⊣ j_*` and the Weil structures

Let `j : U₀ ⟶ C₀` be a quasi-compact open immersion of `k₀`-schemes and `F` a Weil sheaf on `U₀`.
The underlying morphism of sheaves `j̄^* L(F) ⟶ F` of a morphism of Weil sheaves `j^* L(F) ⟶ F`
is compatible with the Weil structures
(`AlgebraicGeometry.WeilSheaf.upperStarHom_frobeniusStr_compatible`). For the counit of
`j^* ⊣ j_*` this morphism is the counit of `j̄^* ⊣ j̄_*` on the underlying sheaves
(`AlgebraicGeometry.WeilSheaf.upperStarHom_counit`), so that the latter is compatible with the
Weil structures of `F` and `j_* F` (`AlgebraicGeometry.WeilSheaf.counit_frobeniusStr_compatible`).

This is used for the Frobenius equivariance of the generic specialization of sections of `j_* F`
over a strictly henselian neighbourhood of a boundary point, in blueprint
`lemma-boundary-stalk--1`. The statements are made for `WeilSheaf.lowerStar` and an
arbitrary functor `L` rather than for `WeilSheaf.directImage`: the kernel checks the unfolding of
`directImage` and of the Weil structures of `j^* j_* F` very slowly.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

set_option hygiene false in
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))


/-- Category algebra for the compatibility of the counit: a morphism `i ≫ θ` built from a
morphism `i` compatible with structure maps and a morphism `θ` compatible with structure maps. -/
lemma comp_map_comp_eq_of_compatible {𝒞 : Type*} [Category 𝒞] (T : 𝒞 ⥤ 𝒞) {W Z Z' M N F' : 𝒞}
    (u : W ⟶ T.obj M) (v : W ⟶ Z') (w : Z' ⟶ Z) (ψ' : Z ⟶ M) (i : M ⟶ N) (θ : N ⟶ F')
    (ψN : T.obj N ⟶ N) (ψF : T.obj F' ⟶ F') (hc : u ≫ T.map i ≫ ψN = v ≫ w ≫ ψ' ≫ i)
    (hn : T.map θ ≫ ψF = ψN ≫ θ) :
    u ≫ T.map (i ≫ θ) ≫ ψF = v ≫ w ≫ ψ' ≫ i ≫ θ := by
  rw [T.map_comp, Category.assoc, hn, reassoc_of% hc]

section UpperStarHom

variable {F} (L : WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X)

/-- The underlying morphism `j̄^* L(F) ⟶ F` of sheaves of a morphism of Weil sheaves
`θ : j^* L(F) ⟶ F`, for a functor `L` (stated for the composite `L ⋙ j^*`, as for the counit of
`j^* ⊣ j_*`). -/
noncomputable def upperStarHom (θ : (L ⋙ upperStar j).obj F ⟶ (𝟭 _).obj F) :
    (j̄)^*[WeilCoefficients.{u} l].obj (L.obj F).obj.carrier.X ⟶ F.obj.carrier.X :=
  (𝟙 _ : (j̄)^*[_].obj (L.obj F).obj.carrier.X ⟶ ((L ⋙ upperStar j).obj F).obj.carrier.X) ≫
    θ.hom.hom.f.hom

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [IsOpenImmersion j] [QuasiCompact j] in
/-- The underlying morphism `j̄^* L(F) ⟶ F` of a morphism of Weil sheaves `j^* L(F) ⟶ F` is
compatible with the Weil structures. -/
lemma upperStarHom_frobeniusStr_compatible (θ : (L ⋙ upperStar j).obj F ⟶ (𝟭 _).obj F) :
    (ProEtale.upperStarComp _ (U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      (j̄)).hom.app (L.obj F).obj.carrier.X ≫
        ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map
          (upperStarHom j L θ) ≫ F.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          j (comp_over j (Spec (CommRingCat.of k₀)))).symm).hom.app (L.obj F).obj.carrier.X ≫
        (ProEtale.upperStarComp _ (j̄)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
          (L.obj F).obj.carrier.X ≫
        (j̄)^*[_].map (L.obj F).frobeniusStr ≫ upperStarHom j L θ :=
  comp_map_comp_eq_of_compatible
    (((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[WeilCoefficients.{u} l])
    _ _ _ _ _ θ.hom.hom.f.hom ((upperStar j).obj (L.obj F)).frobeniusStr F.frobeniusStr
    (upperStar_frobeniusStr_compatible (φ := j) (L.obj F)) (frobeniusStr_naturality θ)

end UpperStarHom

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- The underlying morphism of the counit `j^* j_* F ⟶ F` of Weil sheaves is the counit of
`j̄^* ⊣ j̄_*` on the underlying sheaves. -/
lemma upperStarHom_counit :
    upperStarHom j (lowerStar j) ((upperStarLowerStarAdjunction j).counit.app F) =
      (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) (j̄)).counit.app
        F.obj.carrier.X := by
  rw [upperStarHom, upperStarLowerStarAdjunction_counit_app_hom_hom_f,
    ProEtale.adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_counit_app_hom]
  exact Category.id_comp _

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- **The counit `j̄^* j̄_* F ⟶ F` is compatible with the Weil structures** of `F` and of
`j_* F`. -/
lemma counit_frobeniusStr_compatible :
    (ProEtale.upperStarComp _ (U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      (j̄)).hom.app ((lowerStar j).obj F).obj.carrier.X ≫
        ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map
          ((ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) (j̄)).counit.app
            F.obj.carrier.X) ≫ F.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          j (comp_over j (Spec (CommRingCat.of k₀)))).symm).hom.app
          ((lowerStar j).obj F).obj.carrier.X ≫
        (ProEtale.upperStarComp _ (j̄)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
          ((lowerStar j).obj F).obj.carrier.X ≫
        (j̄)^*[_].map ((lowerStar j).obj F).frobeniusStr ≫
          (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) (j̄)).counit.app
            F.obj.carrier.X := by
  have h := upperStarHom_frobeniusStr_compatible j (lowerStar j)
    ((upperStarLowerStarAdjunction j).counit.app F)
  rw [upperStarHom_counit] at h
  exact h

end AlgebraicGeometry.WeilSheaf
