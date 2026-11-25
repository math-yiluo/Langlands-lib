/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# Reduction modulo `ℓⁿ` preserves bounded constructible complexes

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and
`X` a topologically noetherian scheme. This file proves that the reduction modulo `ℓⁿ`
```
K ↦ K ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{(𝒪_E ⧸ ℓⁿ)_X})
```
sends bounded constructible complexes to bounded constructible complexes
(`ProEtale.boundedConstructible_derivedExtendScalars_integersModPowReduction`), hence restricts to
a functor `D_cons(X_proét, 𝒪_E) ⥤ D_cons(X_proét, 𝒪_E ⧸ ℓⁿ)`
(`ProEtale.boundedConstructibleIntegersModPowReduction`), which commutes with the derived pullback
along morphisms of separated schemes of finite type over a field
(`ProEtale.CondensedRing.boundedConstructibleUpperStarIntegersModPowReductionIso`).

The proof uses the reduction triangle `K --ℓⁿ--> K ⟶ K ⊗ᴸ 𝒪_E ⧸ ℓⁿ ⟶ K[1]` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction`: the bounded
constructible `𝒪_{E,X}`-complexes form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible`), so the restriction of scalars of
`K ⊗ᴸ 𝒪_E ⧸ ℓⁿ` is a bounded constructible `𝒪_{E,X}`-complex. It remains to see that an
`(𝒪_E ⧸ ℓⁿ)_X`-module whose restriction of scalars to `𝒪_{E,X}` is constructible is constructible
(`ProEtale.IsConstructibleModuleObject.of_comap_of_shortExact`): an `𝒪_E ⧸ ℓⁿ`-module `N` is
`(𝒪_E ⧸ ℓⁿ) ⊗_{𝒪_E} N` (`Mod.isIso_extendRestrictAdjunction_counit_app`), and extension of scalars
preserves finite presentations; both statements are compatible with the pullbacks to the strata
and to the pro-étale covers, which are exact.

-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

/-! ### Finite presentation and reduction modulo a nonzerodivisor -/

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]

/-- An additive functor sends the multiplication by an integer `k` on `R` to the multiplication by
`k` on `F R`. -/
lemma Functor.zsmul_id_comp_map_eq_zero (F : C ⥤ D) [F.Additive] {R S : C} {φ : R ⟶ S} {k : ℤ}
    (w : (k • 𝟙 R) ≫ φ = 0) : (k • 𝟙 (F.obj R)) ≫ F.map φ = 0 := by
  rw [← F.map_id, ← F.map_zsmul, ← F.map_comp, w, F.map_zero]

/-- An exact functor preserves the short exactness of `0 ⟶ R --k--> R --φ--> S ⟶ 0`. -/
lemma Functor.shortExact_zsmul_id_map {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {R S : C} {φ : R ⟶ S} {k : ℤ} (w : (k • 𝟙 R) ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) :
    (ShortComplex.mk _ _ (F.zsmul_id_comp_map_eq_zero w)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (hφ.map_of_exact F)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact ((F.map_zsmul (f := 𝟙 R) (r := k)).trans (by rw [F.map_id])).symm) (by simp)

namespace Mod

variable {C : Type*} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]

/-- If `0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, an `S`-module whose restriction of scalars
is a finitely presented `R`-module is finitely presented: it is the extension of scalars of its
restriction of scalars, and extension of scalars preserves finite presentations. -/
lemma IsFinitelyPresented.of_comap_of_shortExact (k : ℤ) (w : (k • 𝟙 R) ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) {N : Mod C S}
    (h : IsFinitelyPresented R ((CategoryTheory.Mod.comap φ).obj N)) : IsFinitelyPresented S N :=
  have := isIso_extendRestrictAdjunction_counit_app k w hφ N
  (IsFinitelyPresented.map (extendScalars φ) (extendScalarsObjRegularIso φ) h).of_iso
    (asIso ((extendRestrictAdjunction φ).counit.app N))

end Mod

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### Constructibility and reduction modulo a nonzerodivisor -/

section Constructible

variable {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
  [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ] (k : ℤ)
  (w : (k • 𝟙 R) ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact)

include hφ in
/-- If `0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, an `S`-module whose restriction of scalars
is a pro-étale locally finitely presented `R`-module is pro-étale locally finitely presented. -/
lemma IsLocallyFinitelyPresented.of_comap_of_shortExact
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFinitelyPresented R ((Mod.comap φ).obj N)) :
    IsLocallyFinitelyPresented S N := by
  obtain ⟨𝒰, h⟩ := h
  refine ⟨𝒰, fun i ↦ ?_⟩
  exact Mod.IsFinitelyPresented.of_comap_of_shortExact k _
    ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).shortExact_zsmul_id_map w hφ)
    ((h i).of_iso (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapModComapIso φ).app N))

include hφ in
/-- If `0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, an `S`-module whose restriction of scalars
is a constructible `R`-module is constructible. -/
lemma IsConstructibleModuleObject.of_comap_of_shortExact
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsConstructibleModuleObject R ((Mod.comap φ).obj N)) :
    IsConstructibleModuleObject S N := by
  obtain ⟨𝒮, h⟩ := h
  refine ⟨𝒮, fun a ↦ ?_⟩
  exact IsLocallyFinitelyPresented.of_comap_of_shortExact k _
    ((ProEtale.upperStar Ab.{u + 1} (𝒮.immersion a)).shortExact_zsmul_id_map w hφ)
    ((h a).of_iso (((ProEtale.upperStar Ab.{u + 1} (𝒮.immersion a)).mapModComapIso φ).app N))

omit [IsCommMonObj R] [IsCommMonObj S] in
/-- A module object whose restriction of scalars is zero is zero. -/
lemma _root_.CategoryTheory.Mod.isZero_of_isZero_comap {C : Type*} [Category C]
    [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C] {R S : C} [MonObj R] [MonObj S]
    (φ : R ⟶ S) [IsMonHom φ] {N : Mod C S} (h : IsZero ((Mod.comap φ).obj N)) : IsZero N := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  have h' := congrArg Mod.Hom.hom h
  exact Mod.hom_ext _ _ h'

end Constructible

/-! ### Reduction modulo `ℓⁿ` on bounded constructible complexes -/

section Reduction

variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] (ℓ : ℕ) [Fact ℓ.Prime] (E : Type)
  [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- **Reduction modulo `ℓⁿ` preserves bounded constructible complexes**: on a topologically
noetherian scheme `X`, if `K ∈ D(Mod_{𝒪_{E,X}})` is bounded constructible, so is
`K ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ ∈ D(Mod_{(𝒪_E ⧸ ℓⁿ)_X})`. By the reduction triangle, its restriction of
scalars is a bounded constructible `𝒪_{E,X}`-complex, and constructibility descends along the
reduction `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X`. -/
theorem boundedConstructible_derivedExtendScalars_integersModPowReduction
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) K) :
    boundedConstructible (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)
      (L(Mod.extendScalars (integersModPowReduction X ℓ E n)).obj K) := by
  have hT := exists_distinguished_integersModPowReduction X ℓ E n K
  have h₃ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      (D(Mod.comap (integersModPowReduction X ℓ E n)).obj
        (L(Mod.extendScalars (integersModPowReduction X ℓ E n)).obj K)) :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₃ _ hT.choose_spec.choose_spec hK hK
  have hiso (i : ℤ) :=
    ((Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategoryHomologyFunctorIso
    i).app (L(Mod.extendScalars (integersModPowReduction X ℓ E n)).obj K)
  rw [mem_boundedConstructible_iff] at h₃ ⊢
  obtain ⟨⟨a, b, hab⟩, hc⟩ := h₃
  refine ⟨⟨a, b, fun i hi ↦ Mod.isZero_of_isZero_comap _ ((hab i hi).of_iso (hiso i))⟩,
    fun i ↦ IsConstructibleModuleObject.of_comap_of_shortExact _ _
      (shortExact_integersModPowReduction X ℓ E n) ((hc i).of_iso (hiso i).symm)⟩

/-- The reduction modulo `ℓⁿ`, `D_cons(X_proét, 𝒪_E) ⥤ D_cons(X_proét, 𝒪_E ⧸ ℓⁿ)`, on bounded
constructible complexes: the restriction of the derived extension of scalars along the reduction
`𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X`. -/
noncomputable def boundedConstructibleIntegersModPowReduction :
    BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) ⥤
      BoundedConstructible (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X) :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ L(Mod.extendScalars (integersModPowReduction X ℓ E n)))
    fun K ↦ boundedConstructible_derivedExtendScalars_integersModPowReduction X ℓ E n K.obj
      K.property

/-- The restricted reduction modulo `ℓⁿ` is compatible with the inclusions. -/
noncomputable def boundedConstructibleIntegersModPowReductionCompatibility :
    boundedConstructibleIntegersModPowReduction X ℓ E n ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L(Mod.extendScalars (integersModPowReduction X ℓ E n)) :=
  ObjectProperty.liftCompιIso _ _ _

end Reduction

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [TopologicalSpace.NoetherianSpace X.left]
  [TopologicalSpace.NoetherianSpace Y.left] (f : X ⟶ Y)

/-- **The reduction modulo `ℓⁿ` commutes with the pullback on bounded constructible
complexes**: `Lf^*_{𝒪_E} ⋙ (- ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ) ≅ (- ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ) ⋙ Lf^*_{𝒪_E ⧸ ℓⁿ}`, the
restriction of `ProEtale.integersModPowReductionUpperStarIso` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarIntegersModPowReductionIso :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f ⋙
        boundedConstructibleIntegersModPowReduction X.left ℓ E n ≅
      boundedConstructibleIntegersModPowReduction Y.left ℓ E n ⋙
        boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility _ ℓ f) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (integersModPowReductionUpperStarIso ℓ E n f.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (boundedConstructibleIntegersModPowReductionCompatibility Y.left ℓ E n).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility _ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

end AlgebraicGeometry.ProEtale.CondensedRing
