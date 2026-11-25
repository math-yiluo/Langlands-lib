/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion
public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar

/-!
# Finiteness of direct images for complexes killed by an ideal of finite index

Let `Λ` be a noetherian ring and `J` an ideal of `Λ` with `Λ ⧸ J` finite, whose exponent is
invertible on the base. For a morphism `f : X ⟶ Y` of finite-type `k`-schemes, `Rf_*` carries a
bounded constructible complex of étale sheaves of `Λ`-modules killed by `J` to a bounded
constructible complex
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_smul_eq_zero`).
This is the form of the finiteness theorem (blueprint `sk-prop-sf-finiteness`) used at the
integral coefficient stage `Λ = 𝒪_E`, for the reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹`.

The proof reduces to the finite ring `Λ ⧸ J`:

- a constructible sheaf `F` of `Λ`-modules killed by `J` is the restriction of scalars of the
  constructible sheaf `Hom_Λ(Λ ⧸ J, F)` of `Λ ⧸ J`-modules, and restriction of scalars commutes
  with `Rf_*` (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`), so the
  case of `F` placed in degree `0` is the finite-coefficient theorem
  `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`;
- a complex is handled by dévissage along its truncation triangles. Constructible sheaves of
  `Λ`-modules are only known to be closed under extensions killed by an ideal of finite index
  (`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_obj₂_of_smul_eq_zero`), so the
  dévissage keeps track of the power of `J` killing each truncation: a complex whose `m` nonzero
  homology sheaves are killed by `J` is killed by `Jᵐ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section RestrictScalars

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') {X Y : Scheme.{u}}
  (f : X ⟶ Y)

/-- Restriction of scalars along `φ : Λ →+* Λ'` commutes with the derived direct image of a sheaf
placed in degree `0`: `Res (Rf_* M) ≅ Rf_* (Res M)`. This is the bounded below comparison
`AlgebraicGeometry.Etale.rightDerivedLowerStarRestrictScalars`, transported to the unbounded
derived categories. -/
noncomputable def restrictScalarsRightDerivedLowerStarSingleIso
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategory.obj
        ((R((f)_*[ModuleCat.{u + 1} Λ'])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj M)) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M)) :=
  (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategory.mapIso
      ((((f)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlusCompatibility.app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M)).symm) ≪≫
    ((Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlusCompatibility.app
      _).symm ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso
      (asIso ((rightDerivedLowerStarRestrictScalars φ f).app _) ≪≫
        ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.mapIso
          (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusSingleFunctor
            0).app M)) ≪≫
    ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _

end RestrictScalars

variable {Λ : Type (u + 1)} [CommRing Λ] (J : Ideal Λ) {X Y : Scheme.{u}}

/-- Restriction of scalars along `Λ ⟶ Λ ⧸ J`, for `Λ ⧸ J` finite, carries bounded constructible
complexes of sheaves of `Λ ⧸ J`-modules to bounded constructible complexes of sheaves of
`Λ`-modules: it is exact and commutes with the homology sheaves, and it preserves constructible
sheaves (`AlgebraicGeometry.Scheme.isConstructibleSheaf_restrictScalars_iff`). -/
lemma boundedConstructible_mapDerivedCategory_restrictScalars [Finite (Λ ⧸ J)]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ J)))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (Λ ⧸ J)) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      ((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).mapDerivedCategory.obj
        K) := by
  let res := Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)
  refine ⟨res.bounded_mapDerivedCategory_obj hK.1, fun q ↦ ?_⟩
  have := hK.2 q
  have : IsConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q ⋙ res).obj K) :=
    (isConstructibleSheaf_restrictScalars_iff J _).2 this
  exact IsConstructibleSheaf.of_iso ((res.mapDerivedCategoryHomologyFunctorIso q).app K)

variable {k : Type u} [Field k]

/-- **Finiteness for a constructible sheaf killed by an ideal of finite index.** Let `F` be a
constructible sheaf of `Λ`-modules on `X` killed by an ideal `J` with `Λ ⧸ J` finite, whose
exponent is invertible on `X`. Then `Rf_* F` is bounded constructible: `F` is the restriction of
scalars of the constructible sheaf `Hom_Λ(Λ ⧸ J, F)` of `Λ ⧸ J`-modules, restriction of scalars
commutes with `Rf_*`, and the finite-coefficient case is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`. -/
lemma boundedConstructible_rightDerivedLowerStar_singleFunctor_of_smul_eq_zero [Finite (Λ ⧸ J)]
    [HasInvertibleExponent (Λ ⧸ J) X] (f : X ⟶ Y) [QuasiCompact f] (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hf : f ≫ aY = aX) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] (hF : ∀ r ∈ J, r • 𝟙 F = 0) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  let F' := (Sheaf.coextendScalars X.smallEtaleTopology J).obj F
  let e : (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj F' ≅ F :=
    Sheaf.restrictScalarsCoextendScalarsIso F hF
  have : IsConstructibleSheaf F' :=
    (isConstructibleSheaf_restrictScalars_iff J F').1 (IsConstructibleSheaf.of_iso e.symm)
  have h := boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent (Λ ⧸ J) f aX aY
    hf _ (DerivedCategory.boundedConstructible_singleFunctor_obj F' 0)
  exact (DerivedCategory.boundedConstructible _ Y).prop_of_iso
    (restrictScalarsRightDerivedLowerStarSingleIso (Ideal.Quotient.mk J) f F' ≪≫
      (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso e))
    (boundedConstructible_mapDerivedCategory_restrictScalars J h)

/-- An element of `R` killing an object kills every isomorphic object. -/
lemma _root_.CategoryTheory.smul_id_eq_zero_of_iso {C : Type*} [Category C] [Preadditive C]
    {R : Type*} [Semiring R] [Linear R C] {A B : C} (e : A ≅ B) {r : R} (h : r • 𝟙 A = 0) :
    r • 𝟙 B = 0 := by
  have : r • 𝟙 B = e.inv ≫ (r • 𝟙 A) ≫ e.hom := by simp
  rw [this, h, zero_comp, comp_zero]

/-- The elements of an ideal `J` kill the homology sheaves of every complex killed by `J`, the
homology functors being linear. -/
lemma smul_id_homologyFunctor_obj_eq_zero
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : ∀ r ∈ J, r • 𝟙 K = 0) (q : ℤ) :
    ∀ r ∈ J, r • 𝟙 ((_root_.DerivedCategory.homologyFunctor _ q).obj K) = 0 := fun r hr ↦ by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, hK r hr, Functor.map_zero]

open _root_.DerivedCategory in
/-- The dévissage of `boundedConstructible_rightDerivedLowerStar_of_smul_eq_zero`, by induction
on the number `m` of degrees in which `K` may have nonzero homology: if the homology sheaves of
`K` are constructible and killed by `J`, then `Rf_* K` is bounded constructible and `K` is killed
by `Jᵐ`. Along the truncation triangle `τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶`, the third term is a sheaf
placed in degree `b`, killed by `J`, so `K` is killed by `Jᵐ⁺¹` and so is `Rf_* K`; as
`Λ ⧸ Jᵐ⁺¹` is finite, `Rf_* K` is then bounded constructible as an extension of bounded
constructible complexes (`DerivedCategory.boundedConstructible_obj₂_of_smul_eq_zero`). -/
lemma boundedConstructible_rightDerivedLowerStar_of_isGE_of_isLE [IsNoetherianRing Λ]
    [Finite (Λ ⧸ J)] [HasInvertibleExponent (Λ ⧸ J) X] (f : X ⟶ Y) [QuasiCompact f]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX) (m : ℕ) :
    ∀ (a : ℤ) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      K.IsGE a → K.IsLE (a + m - 1) →
      (∀ q, IsConstructibleSheaf ((homologyFunctor _ q).obj K)) →
      (∀ q, ∀ r ∈ J, r • 𝟙 ((homologyFunctor _ q).obj K) = 0) →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) ∧ ∀ r ∈ J ^ m, r • 𝟙 K = 0 := by
  let Φ := R((f)_*[ModuleCat.{u + 1} Λ])
  let P := DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
  induction m with
  | zero =>
    intro a K _ _ _ _
    have : K.IsLE (a - 1) := by simpa using ‹K.IsLE (a + ↑(0 : ℕ) - 1)›
    have hK := TStructure.t.isZero K (a - 1) a (by lia)
    exact ⟨boundedConstructible_of_isZero Λ (Φ.map_isZero hK), fun r _ ↦ hK.eq_of_src _ _⟩
  | succ m ih =>
    intro a K _ _ hK hKJ
    set b : ℤ := a + m
    let T := (TStructure.t.triangleLTGE b).obj K
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K
    -- the third term is `Hᵇ K` placed in degree `b`
    have : T.obj₃.IsLE b := by
      have : K.IsLE b := TStructure.t.isLE_of_le K (a + ↑(m + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b)
    have : T.obj₃.IsGE b := inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE b).obj K) b)
    obtain ⟨G, ⟨eG⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ b
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl (isZero_of_isLE _ (b - 1) _ (by lia))
      (isZero_of_isLE _ (b - 1) _ (by lia))
    let eb : (homologyFunctor _ b).obj T.obj₂ ≅ G := asIso ((homologyFunctor _ b).map T.mor₂) ≪≫
      (homologyFunctor _ b).mapIso eG ≪≫ (singleFunctorCompHomologyFunctorIso _ b).app G
    have hG : IsConstructibleSheaf G := by
      have : IsConstructibleSheaf ((homologyFunctor _ b).obj T.obj₂) := hK b
      exact IsConstructibleSheaf.of_iso eb
    have hGJ : ∀ r ∈ J, r • 𝟙 G = 0 := fun r hr ↦ smul_id_eq_zero_of_iso eb (hKJ b r hr)
    have h₃ : P (Φ.obj T.obj₃) :=
      P.prop_of_iso (((Φ.commShiftIso (-b)).app _).symm ≪≫
        Φ.mapIso ((((singleFunctors _).shiftIso (-b) b 0 (by lia)).app G) ≪≫ eG.symm))
        (P.le_shift (-b) _
          (boundedConstructible_rightDerivedLowerStar_singleFunctor_of_smul_eq_zero J f aX aY hf
            G hGJ))
    have h₃J : ∀ r ∈ J, r • 𝟙 T.obj₃ = 0 := fun r hr ↦ smul_id_eq_zero_of_iso eG.symm (by
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, hGJ r hr, Functor.map_zero])
    -- the first term is handled by induction
    have h₁ := ih a T.obj₁
      (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a))
      (TStructure.t.isLE_truncLT_obj _ _ _ (by lia)) (fun q ↦ ?_) (fun q ↦ ?_)
    · -- `K` is killed by `Jᵐ⁺¹`, hence so is `Rf_* K`
      have hJK : ∀ r ∈ J ^ (m + 1), r • 𝟙 K = 0 := by
        intro r hr
        rw [pow_succ] at hr
        refine Submodule.mul_induction_on hr (fun x hx y hy ↦ ?_) (fun x y hx hy ↦ ?_)
        · exact Rationalization.smul_id_obj₂_eq_zero hT (h₁.2 x hx) (h₃J y hy)
        · rw [add_smul, hx, hy, add_zero]
      have : Finite (Λ ⧸ J ^ (m + 1)) := Ideal.finite_quotient_pow (IsNoetherian.noetherian J) _
      refine ⟨DerivedCategory.boundedConstructible_obj₂_of_smul_eq_zero (J := J ^ (m + 1))
        (Φ.map_distinguished _ hT) h₁.1 h₃ fun r hr ↦ ?_, hJK⟩
      change r • 𝟙 (Φ.obj K) = 0
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, hJK r hr, Functor.map_zero]
    all_goals by_cases hq : q < b
    · have : IsIso ((homologyFunctor _ q).map T.mor₁) :=
        isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
          (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
      have : IsConstructibleSheaf ((homologyFunctor _ q).obj T.obj₂) := hK q
      exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ q).map T.mor₁)).symm
    · have : T.obj₁.IsLE (b - 1) := TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      exact IsConstructibleSheaf.of_isZero (isZero_of_isLE _ (b - 1) _ (by lia))
    · have : IsIso ((homologyFunctor _ q).map T.mor₁) :=
        isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
          (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
      exact fun r hr ↦ smul_id_eq_zero_of_iso (asIso ((homologyFunctor _ q).map T.mor₁)).symm
        (hKJ q r hr)
    · have : T.obj₁.IsLE (b - 1) := TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      exact fun r _ ↦ (isZero_of_isLE _ (b - 1) _ (by lia)).eq_of_src _ _

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility, for coefficients killed
by an ideal of finite index.

Let `Λ` be a noetherian ring and `J` an ideal of `Λ` with `Λ ⧸ J` finite, whose exponent is
invertible on `X`, and let `f : X ⟶ Y` be a quasi-compact morphism of `k`-schemes locally of
finite type, with `Y` quasi-compact. If `K` is a bounded constructible complex of étale sheaves of
`Λ`-modules on `X` killed by `J`, then `Rf_* K` is bounded constructible. For `J = 0` this is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`; in
general the homology sheaves of `K` are sheaves of `Λ ⧸ J`-modules, to which the
finite-coefficient case applies, and `K` is reassembled by dévissage
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isGE_of_isLE`). -/
theorem boundedConstructible_rightDerivedLowerStar_of_smul_eq_zero [IsNoetherianRing Λ]
    [Finite (Λ ⧸ J)] [HasInvertibleExponent (Λ ⧸ J) X] (f : X ⟶ Y) [QuasiCompact f]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hJ : ∀ r ∈ J, r • 𝟙 K = 0) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  exact (boundedConstructible_rightDerivedLowerStar_of_isGE_of_isLE J f aX aY hf
    (b - a + 1).toNat a K ha (_root_.DerivedCategory.TStructure.t.isLE_of_le K b _ (by lia)) hc
    (smul_id_homologyFunctor_obj_eq_zero J hJ)).1

end Etale

end AlgebraicGeometry
