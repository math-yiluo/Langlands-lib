/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Reduction modulo a uniformizer is conservative on derived complete objects

Let `Λ` be a commutative ring and `ϖ ∈ Λ` a nonzerodivisor. On `D(X_ét, Λ)` the reduction
`K ↦ K ⊗ᴸ (Λ/ϖ)_X` (`AlgebraicGeometry.Etale.reductionModIdeal`) detects the invertibility
of `ϖ`: tensoring the triangle `Λ ⟶ Λ ⟶ Λ/ϖ ⟶ Λ⟦1⟧` with `K` shows that `ϖ` acts invertibly
on `K` as soon as `K ⊗ᴸ (Λ/ϖ)_X = 0`. Since a derived complete object on which `ϖ` acts
invertibly is zero, a morphism between objects which are derived complete for `(ϖ)` is an
isomorphism as soon as its reduction modulo `ϖ` is.

This is the passage to the limit in the proof of the projection formula at the integral stage
`𝒪_E` (blueprint `lemma-projection-formula-integral-coefficients`, Step 3, and `thm-sf-pf-adic`:
"the reduction functors are conservative on derived-complete complexes").

## Main statements

- `AlgebraicGeometry.Etale.isIso_smul_id_of_isZero_reductionModIdeal`: if `K ⊗ᴸ (Λ/ϖ)_X = 0`
  then `ϖ` acts invertibly on `K`.
- `AlgebraicGeometry.Etale.isIso_of_derivedComplete_of_isIso_reductionModIdeal`: reduction
  modulo `ϖ` is conservative on objects that are derived complete for `(ϖ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance localInstance_ReductionConservative_1 (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The reduction `K ↦ K ⊗ᴸ (Λ/J)_X` commutes with shifts. -/
noncomputable instance (J : Ideal Λ) : (reductionModIdeal Λ X J).CommShift ℤ :=
  inferInstanceAs (((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj _).CommShift ℤ)

/-- The reduction `K ↦ K ⊗ᴸ (Λ/J)_X` is triangulated. -/
instance (J : Ideal Λ) : (reductionModIdeal Λ X J).IsTriangulated :=
  inferInstanceAs (((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj _).IsTriangulated)

/-- The unit `Λ` of the coefficients, as a constant sheaf placed in degree `0`, is a right unit
for the derived tensor product: `K ⊗ᴸ Λ_X ≅ K`. -/
noncomputable def derivedTensorSingleUnitIso
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (𝟙_ (ModuleCat.{u + 1} Λ)))) ≅ K :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X) ≪≫
    derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X K

/-- **Reduction modulo `ϖ` detects invertibility of `ϖ`.** For a nonzerodivisor `ϖ` of `Λ` and
`K ∈ D(X_ét, Λ)`, if the reduction `K ⊗ᴸ (Λ/ϖ)_X` vanishes then `ϖ` acts invertibly on `K`:
tensoring the distinguished triangle `Λ ⟶ Λ ⟶ Λ/ϖ ⟶ Λ⟦1⟧` (the first map being the
multiplication by `ϖ`) with `K` gives a distinguished triangle `K ⟶ K ⟶ 0 ⟶ K⟦1⟧` whose first
map is the multiplication by `ϖ`. -/
theorem isIso_smul_id_of_isZero_reductionModIdeal {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ})).obj K)) :
    IsIso (ϖ • 𝟙 K) := by
  let F := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K
  let T := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ rfl 1
  have hT : F.mapTriangle.obj T ∈ distTriang _ :=
    F.map_distinguished _ (_root_.DerivedCategory.quotPowTriangle_distinguished _ hϖ rfl 1)
  -- the third vertex of the tensored triangle is the reduction of `K` modulo `ϖ`
  let e : (Ideal.quotPowFunctor (Ideal.span {ϖ})).obj (op 1) ≅
      ModuleCat.of Λ (Λ ⧸ Ideal.span {ϖ}) :=
    (Submodule.quotEquivOfEq _ _ (pow_one _)).toModuleIso
  have h₃ : IsZero (F.mapTriangle.obj T).obj₃ :=
    hK.of_iso (F.mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso e)))
  have h₁ : IsIso (F.mapTriangle.obj T).mor₁ := (Triangle.isZero₃_iff_isIso₁ _ hT).1 h₃
  have hmor : (F.mapTriangle.obj T).mor₁ = ϖ • 𝟙 (F.obj T.obj₁) := by
    change F.map T.mor₁ = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, pow_one, Functor.map_smul,
      CategoryTheory.Functor.map_id]
  rw [hmor] at h₁
  let u : F.obj T.obj₁ ≅ K := derivedTensorSingleUnitIso K
  have : ϖ • 𝟙 K = u.inv ≫ (ϖ • 𝟙 (F.obj T.obj₁)) ≫ u.hom := by
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.inv_hom_id]
  rw [this]
  infer_instance

/-- **Reduction modulo `ϖ` is conservative on derived complete objects.** Let `ϖ` be a
nonzerodivisor of `Λ` and `φ : M ⟶ N` a morphism of `D(X_ét, Λ)` between objects that are
derived complete for `(ϖ)`. If the reduction `φ ⊗ᴸ (Λ/ϖ)_X` is an isomorphism, so is `φ`.

The cone `C` of `φ` is derived complete, and its reduction vanishes, so `ϖ` acts invertibly on
`C` (`AlgebraicGeometry.Etale.isIso_smul_id_of_isZero_reductionModIdeal`); a derived complete
object on which `ϖ` acts invertibly is zero. This is the conservativity of the reduction functors
on derived-complete complexes used in blueprint `thm-sf-pf-adic`. -/
theorem isIso_of_derivedComplete_of_isIso_reductionModIdeal {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ)
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N)
    (hM : _root_.DerivedCategory.derivedComplete X.smallEtaleTopology (Ideal.span {ϖ}) M)
    (hN : _root_.DerivedCategory.derivedComplete X.smallEtaleTopology (Ideal.span {ϖ}) N)
    (hφ : IsIso ((reductionModIdeal Λ X (Ideal.span {ϖ})).map φ)) :
    IsIso φ := by
  have := _root_.DerivedCategory.isTriangulated_derivedComplete (J := X.smallEtaleTopology)
    hϖ rfl
  obtain ⟨C, hC, g, h, hT⟩ :=
    (_root_.DerivedCategory.derivedComplete X.smallEtaleTopology
      (Ideal.span {ϖ})).distinguished_cocone_triangle φ hM hN
  let F := reductionModIdeal Λ X (Ideal.span {ϖ})
  have hFT : F.mapTriangle.obj (Triangle.mk φ g h) ∈ distTriang _ := F.map_distinguished _ hT
  have hFC : IsZero (F.obj C) := (Triangle.isZero₃_iff_isIso₁ _ hFT).2 hφ
  have hϖC : IsIso (ϖ • 𝟙 C) := isIso_smul_id_of_isZero_reductionModIdeal hϖ C hFC
  have hCz : IsZero C := by
    rw [IsZero.iff_id_eq_zero]
    exact _root_.DerivedCategory.rightOrthogonal_of_derivedComplete
      (Ideal.mem_span_singleton_self ϖ) hC (𝟙 C) hϖC
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hCz

end Etale

end AlgebraicGeometry
