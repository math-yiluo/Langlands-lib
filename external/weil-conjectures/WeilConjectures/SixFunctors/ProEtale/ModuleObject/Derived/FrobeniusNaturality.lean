/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobeniusNaturality

/-!
# Naturality of the derived Frobenius trivialization of module objects

Let `g : T ⟶ X` be a morphism of schemes and `F_X : X ⟶ X`, `F_T : T ⟶ T` endomorphisms with
`g ≫ F_X = F_T ≫ g`, and let `κ_X : F_X^* ≅ 𝟭`, `κ_T : F_T^* ≅ 𝟭` be trivializations of the
pullbacks of module objects which are compatible with `g^*`:
```
(g ≫ F_X)^* M ≅ g^* F_X^* M --g^* κ_X--> g^* M
     ‖                                     ‖
(F_T ≫ g)^* M ≅ F_T^* g^* M --κ_T------> g^* M
```
Then the derived trivializations `Lκ_X : L(F_X^*) ≅ 𝟭`, `Lκ_T : L(F_T^*) ≅ 𝟭` are compatible
with `Lg^*` in the same way. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence`, this is first
proved for abstract exact functors between abelian categories with functorial flat resolutions
(`CategoryTheory.Functor.leftDerivedFunctorFactorIso_comp_map_leftDerivedFunctorIdIso_app`),
using that the derived isomorphisms are determined by their compatibility with the counits of
the left derived functors.

## Main results

- `ProEtale.CondensedRing.leftDerivedUpperStarComp_hom_app_comp_map_leftDerivedFunctorIdIso`:
  the derived compatibility, for any trivializations satisfying the underived one.
- `ProEtale.CondensedRing.leftDerivedUpperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso`:
  the specialization to the Frobenius trivializations
  `ProEtale.CondensedRing.upperStarIterateFrobeniusIso`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Functor

/-! ### Additive functors on homotopy categories -/

section Homotopy

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Preadditive C₁] [Preadditive C₂]

/-- The compatibility of trivializations `κA : A ≅ 𝟭`, `κB : B ≅ 𝟭` of additive functors with a
functor `G` (through isomorphisms `P ≅ A ⋙ G`, `P' ≅ G ⋙ B`, `P ≅ P'`) holds on the homotopy
categories if it holds on objects. -/
lemma mapHomotopyCategory_comp_map_idIso_of_app {G : C₁ ⥤ C₂} {A : C₁ ⥤ C₁} {B : C₂ ⥤ C₂}
    {P P' : C₁ ⥤ C₂} [G.Additive] [A.Additive] [B.Additive] [P.Additive] [P'.Additive]
    (e₁ : P ≅ A ⋙ G) (e₂ : P' ≅ G ⋙ B) (κA : A ≅ 𝟭 C₁) (κB : B ≅ 𝟭 C₂) (c : P ≅ P')
    (h : ∀ M, e₁.hom.app M ≫ G.map (κA.hom.app M) =
      c.hom.app M ≫ e₂.hom.app M ≫ κB.hom.app (G.obj M))
    (Q : HomotopyCategory C₁ (.up ℤ)) :
    (NatTrans.mapHomotopyCategory e₁.hom (.up ℤ)).app Q ≫
        (G.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory κA.hom (.up ℤ)).app Q ≫
            (mapHomotopyCategoryIdIso C₁ (.up ℤ)).hom.app Q) =
      (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app Q ≫
        (NatTrans.mapHomotopyCategory e₂.hom (.up ℤ)).app Q ≫
          (NatTrans.mapHomotopyCategory κB.hom (.up ℤ)).app
              ((G.mapHomotopyCategory (.up ℤ)).obj Q) ≫
            (mapHomotopyCategoryIdIso C₂ (.up ℤ)).hom.app
              ((G.mapHomotopyCategory (.up ℤ)).obj Q) := by
  rw [mapHomotopyCategoryIdIso_hom_app_eq_id, mapHomotopyCategoryIdIso_hom_app_eq_id]
  erw [Category.comp_id, Category.comp_id]
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Q
  change (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex e₁.hom _).app K) ≫
      (HomotopyCategory.quotient _ _).map ((G.mapHomologicalComplex _).map
        ((NatTrans.mapHomologicalComplex κA.hom _).app K)) =
    (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex c.hom _).app K) ≫
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex e₂.hom _).app K) ≫
        (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex κB.hom _).app
          ((G.mapHomologicalComplex _).obj K))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact h (K.X n)

end Homotopy

/-! ### Exact functors -/

section Generic

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [MonoidalCategory C₁] [MonoidalPreadditive C₁] [HasCountableCoproducts C₁]
  [HasColimitsOfShape ℤ C₁] [HasExactColimitsOfShape ℤ C₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).obj X)]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁]
  [MonoidalCategory C₂] [MonoidalPreadditive C₂] [HasCountableCoproducts C₂]
  [HasColimitsOfShape ℤ C₂] [HasExactColimitsOfShape ℤ C₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₂), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).obj X)]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₂]
  {G : C₁ ⥤ C₂} {A : C₁ ⥤ C₁} {B : C₂ ⥤ C₂} {P P' : C₁ ⥤ C₂}
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [P'.Additive] [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
  (e₁ : P ≅ A ⋙ G) (e₂ : P' ≅ G ⋙ B) (κA : A ≅ 𝟭 C₁) (κB : B ≅ 𝟭 C₂) (c : P ≅ P')

/-- The compatibility of the derived trivializations `L(A) ≅ 𝟭`, `L(B) ≅ 𝟭` with `L(G)`, on the
image `Qh Q` of a complex. -/
lemma leftDerivedFunctorFactorIso_comp_map_leftDerivedFunctorIdIso_app_Qh_obj
    (h : ∀ M, e₁.hom.app M ≫ G.map (κA.hom.app M) =
      c.hom.app M ≫ e₂.hom.app M ≫ κB.hom.app (G.obj M))
    (Q : HomotopyCategory C₁ (.up ℤ)) :
    (leftDerivedFunctorFactorIso e₁).hom.app (Qh.obj Q) ≫
        G.leftDerivedFunctor.map ((leftDerivedFunctorIdIso κA).hom.app (Qh.obj Q)) =
      (P.leftDerivedFunctorNatIso c).hom.app (Qh.obj Q) ≫
        (leftDerivedFunctorFactorIso e₂).hom.app (Qh.obj Q) ≫
          (leftDerivedFunctorIdIso κB).hom.app (G.leftDerivedFunctor.obj (Qh.obj Q)) := by
  rw [← cancel_mono (G.leftDerivedFunctorCounit.app Q)]
  have u₁ := leftDerivedFunctorFactorIso_hom_app_comp_counit e₁ Q
  have u₂ := leftDerivedFunctorFactorIso_hom_app_comp_counit e₂ Q
  have u₃ := leftDerivedFunctorNatIso_hom_app_comp_counit P c Q
  have n₁ : G.leftDerivedFunctor.map
      (Qh.map ((NatTrans.mapHomotopyCategory κA.hom (.up ℤ)).app Q ≫
        (mapHomotopyCategoryIdIso C₁ (.up ℤ)).hom.app Q)) ≫ G.leftDerivedFunctorCounit.app Q =
      G.leftDerivedFunctorCounit.app ((A.mapHomotopyCategory (.up ℤ)).obj Q) ≫
        Qh.map ((G.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory κA.hom (.up ℤ)).app Q ≫
            (mapHomotopyCategoryIdIso C₁ (.up ℤ)).hom.app Q)) :=
    leftDerivedFunctorCounit_naturality _
  have n₂ : (leftDerivedFunctorIdIso κB).hom.app (G.leftDerivedFunctor.obj (Qh.obj Q)) ≫
      G.leftDerivedFunctorCounit.app Q =
      B.leftDerivedFunctor.map (G.leftDerivedFunctorCounit.app Q) ≫
        (leftDerivedFunctorIdIso κB).hom.app (Qh.obj ((G.mapHomotopyCategory (.up ℤ)).obj Q)) :=
    ((leftDerivedFunctorIdIso κB).hom.naturality (G.leftDerivedFunctorCounit.app Q)).symm
  rw [Category.assoc, leftDerivedFunctorIdIso_hom_app_Qh_obj, Functor.map_comp, Category.assoc,
    n₁, reassoc_of% u₁, Category.assoc, Category.assoc, n₂,
    leftDerivedFunctorIdIso_hom_app_Qh_obj, reassoc_of% u₂, reassoc_of% u₃,
    ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    mapHomotopyCategory_comp_map_idIso_of_app e₁ e₂ κA κB c h Q]

/-- **Compatibility of derived trivializations with a derived functor**: let `κA : A ≅ 𝟭`,
`κB : B ≅ 𝟭` be trivializations of exact functors, compatible with an exact functor `G` through
isomorphisms `e₁ : P ≅ A ⋙ G`, `e₂ : P' ≅ G ⋙ B` and `c : P ≅ P'`. Then the derived
trivializations `L(A) ≅ 𝟭`, `L(B) ≅ 𝟭` are compatible with `L(G)` in the same way. -/
lemma leftDerivedFunctorFactorIso_comp_map_leftDerivedFunctorIdIso_app
    (h : ∀ M, e₁.hom.app M ≫ G.map (κA.hom.app M) =
      c.hom.app M ≫ e₂.hom.app M ≫ κB.hom.app (G.obj M))
    (K : DerivedCategory C₁) :
    (leftDerivedFunctorFactorIso e₁).hom.app K ≫
        G.leftDerivedFunctor.map ((leftDerivedFunctorIdIso κA).hom.app K) =
      (P.leftDerivedFunctorNatIso c).hom.app K ≫
        (leftDerivedFunctorFactorIso e₂).hom.app K ≫
          (leftDerivedFunctorIdIso κB).hom.app (G.leftDerivedFunctor.obj K) := by
  have := Localization.natTrans_ext (L := Qh) (W := HomotopyCategory.quasiIso C₁ (.up ℤ))
    (τ := (leftDerivedFunctorFactorIso e₁).hom ≫
      Functor.whiskerRight (leftDerivedFunctorIdIso κA).hom G.leftDerivedFunctor)
    (τ' := (P.leftDerivedFunctorNatIso c).hom ≫ (leftDerivedFunctorFactorIso e₂).hom ≫
      Functor.whiskerLeft G.leftDerivedFunctor (leftDerivedFunctorIdIso κB).hom)
    fun Q ↦ by
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      exact leftDerivedFunctorFactorIso_comp_map_leftDerivedFunctorIdIso_app_Qh_obj e₁ e₂ κA κB
        c h Q
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using NatTrans.congr_app this K

end Generic

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {T X : Scheme.{u}}

-- the instances of the general lemma are found for each of the categories of module objects
/-- **Naturality of derived trivializations of pullbacks**: let `g : T ⟶ X`, `F_X : X ⟶ X`,
`F_T : T ⟶ T` with `g ≫ F_X = F_T ≫ g`, and trivializations `κ_X : F_X^* ≅ 𝟭`,
`κ_T : F_T^* ≅ 𝟭` of the pullbacks of module objects compatible with `g^*`. Then the derived
trivializations `Lκ_X`, `Lκ_T` are compatible with `Lg^*`: the two identifications
`L(g ≫ F_X)^* M ≅ Lg^* M` through `Lκ_X` and through `Lκ_T` agree. -/
theorem leftDerivedUpperStarComp_hom_app_comp_map_leftDerivedFunctorIdIso (g : T ⟶ X)
    {FX : X ⟶ X} {FT : T ⟶ T} (h : g ≫ FX = FT ≫ g) (κX : (FX)^*⟦Λ⟧ ≅ 𝟭 _)
    (κT : (FT)^*⟦Λ⟧ ≅ 𝟭 _)
    (hκ : ∀ M, (upperStarComp Λ g FX).hom.app M ≫ (g)^*⟦Λ⟧.map (κX.hom.app M) =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj M) h) ≫ (upperStarComp Λ FT g).hom.app M ≫
        κT.hom.app ((g)^*⟦Λ⟧.obj M))
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (leftDerivedUpperStarComp Λ g FX).hom.app M ≫
        L((g)^*⟦Λ⟧).map ((Functor.leftDerivedFunctorIdIso κX).hom.app M) =
      eqToHom (congrArg (fun s ↦ L((s)^*⟦Λ⟧).obj M) h) ≫
        (leftDerivedUpperStarComp Λ FT g).hom.app M ≫
          (Functor.leftDerivedFunctorIdIso κT).hom.app (L((g)^*⟦Λ⟧).obj M) := by
  -- Synthesize the tensor conditions pointwise, and reuse them for both module categories.
  have (Y : Scheme.{u}) (K₁ K₂ K₃ K₄ : GradedObject ℤ
      (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
      GradedObject.HasTensor₄ObjExt K₁ K₂ K₃ K₄ := inferInstance
  have (Y : Scheme.{u}) (K₁ K₂ K₃ : GradedObject ℤ
      (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
      GradedObject.HasGoodTensor₁₂Tensor K₁ K₂ K₃ := inferInstance
  have (Y : Scheme.{u}) (K₁ K₂ K₃ : GradedObject ℤ
      (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
      GradedObject.HasGoodTensorTensor₂₃ K₁ K₂ K₃ := inferInstance
  have hc := Functor.leftDerivedFunctorFactorIso_comp_map_leftDerivedFunctorIdIso_app
    (upperStarComp Λ g FX) (upperStarComp Λ FT g) κX κT (upperStarCongr Λ h)
    (fun N ↦ by rw [upperStarCongr_hom_app]; exact hκ N) M
  simpa only [← leftDerivedUpperStarComp_eq_leftDerivedFunctorFactorIso, upperStarCongr,
    Functor.leftDerivedFunctorNatIso_eqToIso_hom_app] using hc

-- the instances of the general lemma are found for each of the categories of module objects
/-- **Naturality of the derived Frobenius trivialization**: for `g : T ⟶ X` between schemes in
which the prime `p` vanishes, the derived trivializations `L(F_X)^* ≅ 𝟭`, `L(F_T)^* ≅ 𝟭` of
the `p ^ n`-power absolute Frobenii are compatible with `Lg^*`. -/
theorem leftDerivedUpperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso
    {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (hT : (p : Γ(T, ⊤)) = 0) (n : ℕ)
    (g : T ⟶ X)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (leftDerivedUpperStarComp Λ g (X.iterateFrobenius hp hX n)).hom.app M ≫
        L((g)^*⟦Λ⟧).map
          ((Functor.leftDerivedFunctorIdIso (upperStarIterateFrobeniusIso Λ hp hX n)).hom.app M) =
      eqToHom (congrArg (fun s ↦ L((s)^*⟦Λ⟧).obj M) (comp_iterateFrobenius hp g hX hT n)) ≫
        (leftDerivedUpperStarComp Λ (T.iterateFrobenius hp hT n) g).hom.app M ≫
          (Functor.leftDerivedFunctorIdIso (upperStarIterateFrobeniusIso Λ hp hT n)).hom.app
            (L((g)^*⟦Λ⟧).obj M) :=
  leftDerivedUpperStarComp_hom_app_comp_map_leftDerivedFunctorIdIso Λ g
    (comp_iterateFrobenius hp g hX hT n) _ _
    (upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app Λ hp hX hT n g) M

end AlgebraicGeometry.ProEtale.CondensedRing
