/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalDual
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralVerdier
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# The integral exceptional adjoint

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on an algebraically closed field `k` (the integral stage `Λ = 𝒪_E`), and
`f : X ⟶ Y` a separated morphism of separated `k`-schemes of finite type. This file proves the
integral exceptional adjoint
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint`): the derived limit
`G_f L` of the exceptional inverse images of the reductions of `L ∈ Dᵇc(Y, Λ)` lies in
`Dᵇc(X, Λ)`, is `Rf^! L`, satisfies the dual formula `G_f L ≅ 𝔻_X f^*_comp 𝔻_Y L` and has the
expected reduction Tor interval.

## Proof

* The dual formula is the Yoneda argument of `CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedHom`): biduality
  `L ≅ 𝔻_Y 𝔻_Y L` (`theorem-verdier-biduality--2`), the projection formula modulo `ϖ`
  (`proposition-six-operations-change-coefficients`), which suffices for morphisms into the derived
  complete dualizing complex, and the identification `Rf^! ω_Y ≅ ω_X` of the dualizing complexes
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_dualizing`).
* Constructibility and the Tor interval then follow, as in the blueprint, from integral
  Verdier duality applied on `Y` and on `X`, the completed pullback being a derived completion
  of `Lf^* 𝔻_Y L` and the dualizing complexes those of `proposition-sp-integral-adjunction`.

## Implementation notes

Statements at `Λ` are phrased with `AlgebraicGeometry.Etale.derivedTensor` and
`AlgebraicGeometry.Etale.derivedHom`, never with `⊗` or `ihom` found by instance search: the
kernel does not compare these in reasonable time at `ModuleCat Λ` (see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`). The formal Yoneda argument is
therefore specialised first to a general coefficient category
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedHom`).

The identification `Rf^! ω_Y ≅ ω_X` rests on the composition law of the exceptional inverse
images on the torsion tower `n ↦ Λ ⧸ Iⁿ`
(`AlgebraicGeometry.Etale.nonempty_iso_quotPowFunctor_comp_rightDerivedUpperShriek_comp`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))


/-- At integral coefficients the exceptional inverse image is a right adjoint `G` of `Rf_!`,
assumed to exist; it is `Λ`-linear, `Rf_!` being `Λ`-linear. -/
instance linear_rightAdjoint_rightDerivedLowerShriek {Λ : Type (u + 1)} [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.Linear Λ :=
  (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])).right_adjoint_linear

/-! ### The formal dual formula -/

section General

attribute [local instance] _root_.DerivedCategory.braidedCategory'

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]

/-- **The dual formula `Rf^! L ≅ RHom(N, ω_X)`.** Let `L, M, ω_Y ∈ D(Y_ét)` with an isomorphism
`L ≅ RHom(M, ω_Y)`, and assume that the projection maps
`PF_{f, K, M} : Rf_! K ⊗ᴸ M ⟶ Rf_!(K ⊗ᴸ Lf^* M)` induce bijections on morphisms into `ω_Y`.
Given `γ : Rf^! ω_Y ≅ ω_X` and `φ : Lf^* M ⟶ N` inducing bijections
`Hom(K ⊗ᴸ N, ω_X) ≃ Hom(K ⊗ᴸ Lf^* M, ω_X)`, there is an isomorphism `Rf^! L ≅ RHom(N, ω_X)`
(`CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`). -/
theorem nonempty_iso_rightDerivedUpperShriek_obj_derivedHom
    {L M ωY : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (e : L ≅ ((derivedHom A Y).obj (op M)).obj ωY)
    (hπ : ∀ K, Function.Bijective (fun a : (R(f)_![A]).obj (((derivedTensor A X).obj K).obj
        ((L((f)^*[A])).obj M)) ⟶ ωY ↦ ((projectionMap A f).app K).app M ≫ a))
    {ωX N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (γ : (R(f)_![A]).rightAdjoint.obj ωY ≅ ωX) (φ : (L((f)^*[A])).obj M ⟶ N)
    (hφ : ∀ K, Function.Bijective
      (fun a : ((derivedTensor A X).obj K).obj N ⟶ ωX ↦ ((derivedTensor A X).obj K).map φ ≫ a)) :
    Nonempty ((R(f)_![A]).rightAdjoint.obj L ≅ ((derivedHom A X).obj (op N)).obj ωX) :=
  Verdier.nonempty_iso_obj_of_adjunction (Adjunction.ofIsLeftAdjoint (R(f)_![A]))
    (derivedTensorHomAdjunction A M) e (fun K ↦ ((projectionMap A f).app K).app _)
    (fun g ↦ NatTrans.congr_app ((projectionMap A f).naturality g) _) hπ
    (derivedTensorHomAdjunction A N) γ φ hφ

end General

/-! ### Morphisms into objects orthogonal to `ϖ`-invertible objects -/

section Orthogonal

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
include hϖ

/-- The reductions modulo `ϖⁿ` of an object on which `ϖ` acts invertibly vanish: the reduction is
the cone of the multiplication by `ϖⁿ`. -/
lemma isZero_reductionModIdeal_of_smulInvertible (n : ℕ) (K : 𝐃(X, Λ))
    (hK : _root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ K) :
    IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) := by
  let F := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K
  let T := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ rfl n
  have hT : F.mapTriangle.obj T ∈ distTriang _ :=
    F.map_distinguished _ (_root_.DerivedCategory.quotPowTriangle_distinguished _ hϖ rfl n)
  have hmor : (F.mapTriangle.obj T).mor₁ = ϖ ^ n • 𝟙 (F.obj T.obj₁) := by
    change F.map T.mor₁ = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul,
      CategoryTheory.Functor.map_id]
  let u : F.obj T.obj₁ ≅ K := derivedTensorSingleUnitIso K
  have h₁ : IsIso (F.mapTriangle.obj T).mor₁ := by
    rw [hmor]
    have : ϖ ^ n • 𝟙 (F.obj T.obj₁) = u.hom ≫ (ϖ ^ n • 𝟙 K) ≫ u.inv := by
      rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.hom_inv_id]
    rw [this]
    have := hK.pow n
    infer_instance
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).2 h₁

/-- A morphism whose reduction modulo a nonzerodivisor `ϖ` is an isomorphism induces bijections
on morphisms into every object receiving no nonzero map from an object on which `ϖ` acts
invertibly (for instance a derived complete object). -/
lemma bijective_comp_of_isIso_reductionModIdeal {S T W : 𝐃(X, Λ)} (u : S ⟶ T)
    (hu : IsIso ((reductionModIdeal Λ X (Ideal.span {ϖ})).map u))
    (hW : (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal W) :
    Function.Bijective (fun a : T ⟶ W ↦ u ≫ a) := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle u
  have hC : IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ})).obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((reductionModIdeal Λ X (Ideal.span {ϖ})).map_distinguished _ hT)).2 hu
  exact ObjectProperty.bijective_comp_of_distinguished hT
    (isIso_smul_id_of_isZero_reductionModIdeal hϖ C hC) hW

/-- Tensoring a morphism whose reduction modulo `ϖ` is an isomorphism with any object gives a
morphism inducing bijections on morphisms into every object receiving no nonzero map from an
object on which `ϖ` acts invertibly. -/
lemma bijective_derivedTensor_map_comp_of_isIso_reductionModIdeal {S T W : 𝐃(X, Λ)}
    (u : S ⟶ T) (hu : IsIso ((reductionModIdeal Λ X (Ideal.span {ϖ})).map u))
    (hW : (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal W)
    (K : 𝐃(X, Λ)) :
    Function.Bijective (fun a : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj T ⟶ W ↦
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map u ≫ a) := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle u
  have hC : IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ})).obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((reductionModIdeal Λ X (Ideal.span {ϖ})).map_distinguished _ hT)).2 hu
  have hϖC : IsIso (ϖ • 𝟙 C) := isIso_smul_id_of_isZero_reductionModIdeal hϖ C hC
  let F := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K
  have hFC : _root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ (F.obj C) := by
    change IsIso (ϖ • 𝟙 _)
    rw [← F.map_id, ← Functor.map_smul]
    infer_instance
  exact ObjectProperty.bijective_comp_of_distinguished (F.map_distinguished _ hT) hFC hW

omit hϖ in
/-- The point of a homotopy limit of a tower of objects killed by powers of `ϖ` receives no
nonzero map from an object on which `ϖ` acts invertibly. -/
lemma rightOrthogonal_smulInvertible_of_isHomotopyLimit {F : ℕᵒᵖ ⥤ 𝐃(X, Λ)}
    (hF : ∀ n : ℕ, ∃ m : ℕ, ϖ ^ m • 𝟙 (F.obj (op n)) = 0) {c : Cone F}
    (hc : IsHomotopyLimit c) :
    (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal c.pt :=
  fun Z f hZ ↦ hc.hom_ext_zero
    (fun n g ↦ (hF n).elim fun _ hm ↦ hZ.hom_eq_zero hm g)
    (fun n g ↦ (hF n).elim fun _ hm ↦ (ObjectProperty.le_shift _ 1 Z hZ).hom_eq_zero hm g) f

omit hϖ in
/-- The point of a homotopy limit of the image of the tower `n ↦ Λ ⧸ Iⁿ` under a `Λ`-linear
functor receives no nonzero map from an object on which `ϖ ∈ I` acts invertibly. -/
lemma rightOrthogonal_smulInvertible_of_isHomotopyLimit_quotPowFunctor {S : Scheme.{u}}
    {I : Ideal Λ} (hϖI : ϖ ∈ I) (G : 𝐃(S, Λ) ⥤ 𝐃(X, Λ)) [G.Additive] [G.Linear Λ]
    {c : Cone (_root_.DerivedCategory.quotPowFunctor S.smallEtaleTopology I ⋙ G)}
    (hc : IsHomotopyLimit c) :
    (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal c.pt :=
  rightOrthogonal_smulInvertible_of_isHomotopyLimit (fun n ↦ ⟨n, by
    change ϖ ^ n • 𝟙 (G.obj _) = 0
    rw [← G.map_id, ← Functor.map_smul,
      _root_.DerivedCategory.smul_id_quotPowFunctor_obj _ hϖI n, G.map_zero]⟩) hc

end Orthogonal

/-! ### Closure properties of `Dᵇc(X, Λ)` -/

section Closure

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ} {X Y : Scheme.{u}}

/-- Derived completeness for `I = (ϖ)` is closed under isomorphisms. -/
lemma _root_.DerivedCategory.isClosedUnderIsomorphisms_derivedComplete
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) :
    (_root_.DerivedCategory.derivedComplete X.smallEtaleTopology I).IsClosedUnderIsomorphisms := by
  rw [_root_.DerivedCategory.derivedComplete_eq_rightOrthogonal hϖ hI]
  infer_instance

/-- `Dᵇc(X, Λ)` is closed under isomorphisms. -/
lemma DerivedCategory.isClosedUnderIsomorphisms_boundedConstructibleIntegral
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) :
    (DerivedCategory.boundedConstructibleIntegral I X).IsClosedUnderIsomorphisms where
  of_iso e := by
    have := _root_.DerivedCategory.isClosedUnderIsomorphisms_derivedComplete (X := X) hϖ hI
    rintro ⟨hc, a, b, h⟩
    exact ⟨(_root_.DerivedCategory.derivedComplete _ I).prop_of_iso e hc, a, b, fun n ↦
      ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso
          ((reductionModIdeal Λ X _).mapIso e) (h n).1,
        (DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso
          ((reductionModIdeal Λ X _).mapIso e) (h n).2⟩⟩

/-- The reductions of `Lf^* K` are the pullbacks of the reductions of `K`, so they are bounded
constructible with the same Tor amplitude as those of `K`. -/
lemma boundedConstructible_and_torAmplitudeIn_reductionModIdeal_leftDerivedUpperStar
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
    (f : X ⟶ Y) {K : 𝐃(Y, Λ)} {a b : ℤ} (n : ℕ)
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((reductionModIdeal Λ Y (I ^ (n + 1))).obj K) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
        ((reductionModIdeal Λ Y (I ^ (n + 1))).obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  subst hI
  obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal (L((f)^*[ModuleCat.{u + 1} Λ])) hϖ (n + 1) K
  exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e
      (boundedConstructible_leftDerivedUpperStar _ f hK.1),
    (DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e
      (torAmplitudeIn_leftDerivedUpperStar _ f a b hK.2)⟩

end Closure

/-! ### The dual formula at the integral stage -/

section DualFormula

variable {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

/-- **The integral dual formula, given the dualizing comparison.** Let `ϖ` be a nonzerodivisor
with `Λ ⧸ (ϖ)` finite, `ω_Y ∈ D(Y_ét, Λ)` and `ω_X ∈ D(X_ét, Λ)` objects receiving no nonzero map
from objects on which `ϖ` acts invertibly, `γ : Rf^! ω_Y ≅ ω_X`, and `L` with invertible
double-dual map `L ⟶ RHom(RHom(L, ω_Y), ω_Y)`. If `φ : Lf^* RHom(L, ω_Y) ⟶ N` is an isomorphism
modulo `ϖ`, then `Rf^! L ≅ RHom(N, ω_X)`. -/
theorem nonempty_iso_rightDerivedUpperShriek_obj_derivedHom_of_isIso_reductionModIdeal
    {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) [Finite (Λ ⧸ Ideal.span {ϖ} ^ 1)] {L ωY : 𝐃(Y, Λ)}
    (hωY : (_root_.DerivedCategory.smulInvertible Y.smallEtaleTopology ϖ).rightOrthogonal ωY)
    (hL : IsIso (derivedHomDoubleDual (ModuleCat.{u + 1} Λ) Y ωY L)) {ωX N : 𝐃(X, Λ)}
    (hωX : (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal ωX)
    (γ : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj ωY ≅ ωX)
    (φ : (L((f)^*[ModuleCat.{u + 1} Λ])).obj
      (((derivedHom (ModuleCat.{u + 1} Λ) Y).obj (op L)).obj ωY) ⟶ N)
    (hφ : IsIso ((reductionModIdeal Λ X (Ideal.span {ϖ})).map φ)) :
    Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L ≅
      ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op N)).obj ωX) :=
  nonempty_iso_rightDerivedUpperShriek_obj_derivedHom (ModuleCat.{u + 1} Λ) f
    (asIso (derivedHomDoubleDual (ModuleCat.{u + 1} Λ) Y ωY L))
    (fun K ↦ bijective_comp_of_isIso_reductionModIdeal hϖ (projectionMapApp Λ f K _) (by
      have := isIso_reductionModIdeal_map_projectionMap_of_finite hϖ 1 f K
        (((derivedHom (ModuleCat.{u + 1} Λ) Y).obj (op L)).obj ωY)
      rwa [pow_one] at this) hωY)
    γ φ (bijective_derivedTensor_map_comp_of_isIso_reductionModIdeal hϖ φ hφ hωX)

end DualFormula

/-! ### The dualizing complexes -/

section Dualizing

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ})

omit [IsDomain Λ] [IsNoetherianRing Λ] in
include hϖ hI in
/-- **The composition law of the exceptional inverse images on the torsion tower.** For
composable morphisms `f : X ⟶ Y` and `g : Y ⟶ S` admitting compactifications, the exceptional
inverse images `R(f ≫ g)^!` and `Rf^! ∘ Rg^!` of `D(-_ét, Λ)` agree on the tower
`n ↦ Λ ⧸ Iⁿ`, compatibly with the transition maps.

The composition law of the compactly supported direct images fails on `D(-_ét, 𝒪_E)`, but it
holds up to cones on which `ϖ` acts invertibly, and the objects `Λ ⧸ Iⁿ`, killed by `ϖⁿ`, see no
such cones (`AlgebraicGeometry.Etale.nonempty_iso_comp_rightDerivedUpperShriek_comp`). -/
theorem nonempty_iso_quotPowFunctor_comp_rightDerivedUpperShriek_comp {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(g)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(f ≫ g)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    Nonempty (_root_.DerivedCategory.quotPowFunctor S.smallEtaleTopology I ⋙
        (R(f ≫ g)_![ModuleCat.{u + 1} Λ]).rightAdjoint ≅
      _root_.DerivedCategory.quotPowFunctor S.smallEtaleTopology I ⋙
        (R(g)_![ModuleCat.{u + 1} Λ]).rightAdjoint ⋙
          (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint) := by
  subst hI
  have hϖI : ϖ ∈ Ideal.span {ϖ} := Ideal.subset_span rfl
  exact nonempty_iso_comp_rightDerivedUpperShriek_comp hϖ (fun n _ a hZ ↦ hZ.hom_eq_zero
    (_root_.DerivedCategory.smul_id_quotPowFunctor_obj _ hϖI n.unop) a) f g

omit [IsDomain Λ] [IsNoetherianRing Λ] in
include hϖ hI in
/-- **The dualizing complexes correspond under `Rf^!`.** For `a_X = f ≫ a_Y` and integral
dualizing complexes `ω_X`, `ω_Y` (points of homotopy limit cones of the towers
`n ↦ Ra^!(Λ ⧸ Iⁿ)`), there is an isomorphism `Rf^! ω_Y ≅ ω_X`: `Rf^!` preserves homotopy limits,
being a triangulated right adjoint, and the towers agree by
`AlgebraicGeometry.Etale.nonempty_iso_quotPowFunctor_comp_rightDerivedUpperShriek_comp`. -/
theorem nonempty_iso_rightDerivedUpperShriek_obj_dualizing {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [QuasiCompact aX] [HasCompactification aX]
    [HasCompactification aY] [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasCompactification f] [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (ωX : Cone (_root_.DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
      (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (hωX : IsHomotopyLimit ωX)
    (ωY : Cone (_root_.DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
      (R(aY)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (hωY : IsHomotopyLimit ωY) :
    Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj ωY.pt ≅ ωX.pt) := by
  subst hf
  obtain ⟨e⟩ := nonempty_iso_quotPowFunctor_comp_rightDerivedUpperShriek_comp I hϖ hI f aY
  let adj := Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])
  have := adj.commShift_of_leftAdjoint ℤ
  have : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.IsTriangulated :=
    adj.isTriangulated_rightAdjoint
  have : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.Additive := adj.right_adjoint_additive
  let E := Functor.associator _ _ _ ≪≫ e.symm
  let hc := hωY.map (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint
  let c : Cone (_root_.DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
      (R(f ≫ aY)_![ModuleCat.{u + 1} Λ]).rightAdjoint) :=
    { pt := (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj ωY.pt
      π := ((R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.mapCone ωY).π ≫ E.hom }
  obtain ⟨i, -⟩ := (hc.of_iso E c (Iso.refl _) fun n ↦ by simp [c]).exists_iso hωX
  exact ⟨i⟩

end Dualizing



section DerivedLimit

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

/-- The exceptional inverse image `Rf^!` commutes with derived limits of reductions: for a
derived complete `L ∈ D(Y_ét, Λ)` and a homotopy limit cone `c` of the tower
`n ↦ Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)`, there is an isomorphism `Rf^! L ≅ c.pt` compatible with the legs.
Indeed `Rf^!` is a triangulated right adjoint, so it carries the Milnor triangle exhibiting
`L = R lim_n L ⊗ᴸ Λ ⧸ Iⁿ` to a Milnor triangle. -/
theorem exists_iso_rightDerivedUpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {L : 𝐃(Y, Λ)}
    (hL : DerivedCategory.derivedComplete Y.smallEtaleTopology I L)
    {c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
      (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint)} (hc : Pretriangulated.IsHomotopyLimit c) :
    ∃ e : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L ≅ c.pt, ∀ n : ℕ,
      e.hom ≫ c.π.app (op n) = (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.map
        ((DerivedCategory.derivedCompletionCone Y.smallEtaleTopology I L).π.app (op n)) := by
  let adj := Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])
  have := adj.commShift_of_leftAdjoint ℤ
  have : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.IsTriangulated :=
    adj.isTriangulated_rightAdjoint
  have : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.Additive := adj.right_adjoint_additive
  exact (hL.map (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint).exists_iso hc

end DerivedLimit

/-! ### The integral exceptional adjoint -/

section Constructible

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

include hϖ hI in
/-- The dual formula for the integral exceptional adjoint: for integral dualizing
complexes `ω_X`, `ω_Y` and a completed pullback `φ : Lf^* 𝔻_Y L ⟶ N` (an isomorphism modulo
`ϖ`), the derived limit `c.pt = G_f L` is `𝔻_X N = RHom(N, ω_X)`. It is
`nonempty_iso_rightDerivedUpperShriek_obj_derivedHom_of_isIso_reductionModIdeal`
for `L ≅ 𝔻_Y 𝔻_Y L` (`theorem-verdier-biduality--2`) and `γ : Rf^! ω_Y ≅ ω_X`. -/
theorem nonempty_iso_derivedHom_of_isHomotopyLimit {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {L : 𝐃(Y, Λ)}
    (hL : DerivedCategory.boundedConstructibleIntegral I Y L)
    {c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
      (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint)} (hc : Pretriangulated.IsHomotopyLimit c)
    (ωX : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
      (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (hωX : IsHomotopyLimit ωX)
    (ωY : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
      (R(aY)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (hωY : IsHomotopyLimit ωY)
    (N : 𝐃(X, Λ)) (φ : (L((f)^*[ModuleCat.{u + 1} Λ])).obj
      (((derivedHom (ModuleCat.{u + 1} Λ) Y).obj (op L)).obj ωY.pt) ⟶ N)
    (hφ : IsIso ((reductionModIdeal Λ X I).map φ)) :
    Nonempty (c.pt ≅ ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op N)).obj ωX.pt) := by
  subst hI
  have : Finite (Λ ⧸ Ideal.span {ϖ} ^ 1) := by rw [pow_one]; infer_instance
  have := isTriangulated_rightDerivedUpperShriek (Λ := Λ) f
  have hϖI : ϖ ∈ Ideal.span {ϖ} := Ideal.mem_span_singleton_self ϖ
  have : (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint.Additive :=
    (Adjunction.ofIsLeftAdjoint _).right_adjoint_additive
  have : (R(aY)_![ModuleCat.{u + 1} Λ]).rightAdjoint.Additive :=
    (Adjunction.ofIsLeftAdjoint _).right_adjoint_additive
  obtain ⟨e, -⟩ := exists_iso_rightDerivedUpperShriek _ f hL.1 hc
  obtain ⟨γ⟩ := nonempty_iso_rightDerivedUpperShriek_obj_dualizing (Ideal.span {ϖ}) hϖ rfl
    aX aY f hf ωX hωX ωY hωY
  obtain ⟨e'⟩ := nonempty_iso_rightDerivedUpperShriek_obj_derivedHom_of_isIso_reductionModIdeal
    f hϖ (rightOrthogonal_smulInvertible_of_isHomotopyLimit_quotPowFunctor hϖI _ hωY)
    (boundedConstructibleIntegral_derivedHom_dualizing (Ideal.span {ϖ}) hϖ rfl aY ωY hωY
      hL).2.2.2
    (rightOrthogonal_smulInvertible_of_isHomotopyLimit_quotPowFunctor hϖI _ hωX) γ φ hφ
  exact ⟨e.symm ≪≫ e'⟩

include hϖ hI in
/-- Constructibility and the Tor interval for the integral exceptional adjoint: the
derived limit `c.pt = G_f L` lies in `Dᵇc(X, Λ)`, and if the reductions of `L` have Tor amplitude
in `[a, b]`, those of `G_f L` have Tor amplitude in `[a - 2 dim X, b + 2 dim Y]`. As in the
blueprint, `G_f L ≅ 𝔻_X f^*_comp 𝔻_Y L`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedHom_of_isHomotopyLimit`) for the dualizing
complexes of `proposition-sp-integral-adjunction` and the derived completion of `Lf^* 𝔻_Y L`, and
integral Verdier duality (`theorem-verdier-biduality--2`) applies twice. -/
theorem boundedConstructibleIntegral_and_torAmplitudeIn_of_isHomotopyLimit {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {L : 𝐃(Y, Λ)}
    (hL : DerivedCategory.boundedConstructibleIntegral I Y L)
    {c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
      (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint)} (hc : Pretriangulated.IsHomotopyLimit c) :
    DerivedCategory.boundedConstructibleIntegral I X c.pt ∧
    ∀ dX dY : ℕ, topologicalKrullDim X ≤ (dX : WithBot ℕ∞) →
      topologicalKrullDim Y ≤ (dY : WithBot ℕ∞) → ∀ a b : ℤ,
        (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
          ((reductionModIdeal Λ Y (I ^ (n + 1))).obj L)) →
        ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X
          (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj c.pt) := by
  subst hI
  -- the dualizing complexes and a completed pullback of `𝔻_Y L`
  obtain ⟨ωX, hωX, -⟩ := exists_isHomotopyLimit_dualizing (Ideal.span {ϖ}) hϖ rfl aX
  obtain ⟨ωY, hωY, -⟩ := exists_isHomotopyLimit_dualizing (Ideal.span {ϖ}) hϖ rfl aY
  have hVY := boundedConstructibleIntegral_derivedHom_dualizing (Ideal.span {ϖ}) hϖ rfl aY ωY
    hωY hL
  obtain ⟨N, C, φ, g, h, hT, hC, hN⟩ :=
    _root_.DerivedCategory.exists_distinguished_derivedComplete
      (J := X.smallEtaleTopology) hϖ rfl ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) Y).obj (op L)).obj ωY.pt))
  have hφ (n : ℕ) : IsIso ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).map φ) :=
    (Triangle.isZero₃_iff_isIso₁ _ ((reductionModIdeal Λ X _).map_distinguished _ hT)).1
      (isZero_reductionModIdeal_of_smulInvertible hϖ n C hC)
  obtain ⟨eN⟩ := nonempty_iso_derivedHom_of_isHomotopyLimit (Ideal.span {ϖ}) hϖ rfl aX aY f hf hL
    hc ωX hωX ωY hωY N φ (by have := hφ 1; rwa [pow_one] at this)
  have hNred (n : ℕ) {a b : ℤ}
      (hab : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((reductionModIdeal Λ Y (Ideal.span {ϖ} ^ (n + 1))).obj
            (((derivedHom (ModuleCat.{u + 1} Λ) Y).obj (op L)).obj ωY.pt)) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
          ((reductionModIdeal Λ Y (Ideal.span {ϖ} ^ (n + 1))).obj
            (((derivedHom (ModuleCat.{u + 1} Λ) Y).obj (op L)).obj ωY.pt))) :
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
          ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ (n + 1))).obj N) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
          ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ (n + 1))).obj N) := by
    have h := boundedConstructible_and_torAmplitudeIn_reductionModIdeal_leftDerivedUpperStar hϖ
      rfl f n hab
    have := hφ (n + 1)
    let ι := asIso ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ (n + 1))).map φ)
    exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso ι h.1,
      (DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso ι h.2⟩
  obtain ⟨a', b', hab'⟩ := hVY.1.2
  have hNc : DerivedCategory.boundedConstructibleIntegral (Ideal.span {ϖ}) X N :=
    ⟨hN, a', b', fun n ↦ hNred n (hab' n)⟩
  have hVX := boundedConstructibleIntegral_derivedHom_dualizing (Ideal.span {ϖ}) hϖ rfl aX ωX
    hωX hNc
  have := DerivedCategory.isClosedUnderIsomorphisms_boundedConstructibleIntegral (X := X) hϖ rfl
  refine ⟨(DerivedCategory.boundedConstructibleIntegral _ X).prop_of_iso eN.symm hVX.1,
    fun dX dY hdX hdY a b hab n ↦ ?_⟩
  have hDY := hVY.2.2.1 dY hdY a b hab
  have hDX := hVX.2.2.1 dX hdX (-b - 2 * (dY : ℤ) - 1) (-a - 1)
    (fun n ↦ (hNred n ⟨(hab' n).1, hDY n⟩).2) n
  have h₁ : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * (dX : ℤ))
      (b + 2 * (dY : ℤ)) ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ (n + 1))).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op N)).obj ωX.pt)) :=
    hDX.mono (by omega) (by omega)
  have h₂ := (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X _ _).prop_of_iso
    ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ (n + 1))).mapIso eN.symm) h₁
  exact h₂

include hϖ hI in
omit [IsDomain Λ] [IsNoetherianRing Λ] [IsAlgClosed k] in
/-- The reductions of the integral exceptional adjoint: `(G_f L) ⊗ᴸ A_n ≅ Rf^!(L ⊗ᴸ A_n)`. -/
theorem nonempty_iso_reductionModIdeal_of_isHomotopyLimit_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (f : X ⟶ Y) (_hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {L : 𝐃(Y, Λ)}
    (hL : DerivedCategory.boundedConstructibleIntegral I Y L)
    {c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
      (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint)} (hc : Pretriangulated.IsHomotopyLimit c) :
    ∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj c.pt ≅
        (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
          ((reductionModIdeal Λ Y (I ^ n)).obj L)) := by
  let adj := Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])
  have := adj.commShift_of_leftAdjoint ℤ
  have : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.IsTriangulated :=
    adj.isTriangulated_rightAdjoint
  have : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.Additive := adj.right_adjoint_additive
  obtain ⟨e, -⟩ := (hL.1.map (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint).exists_iso hc
  intro n
  subst hI
  obtain ⟨e'⟩ :=
    nonempty_iso_map_reductionModIdeal (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint hϖ n L
  exact ⟨(reductionModIdeal Λ X _).mapIso e.symm ≪≫ e'.symm⟩


include hϖ hI in
/-- The dual formula for the integral exceptional adjoint: `G_f L ≅ 𝔻_X f^*_comp 𝔻_Y L`. -/
theorem nonempty_iso_derivedHom_of_isHomotopyLimit_of_derivedComplete {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {L : 𝐃(Y, Λ)}
    (hL : DerivedCategory.boundedConstructibleIntegral I Y L)
    {c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
      (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint)} (hc : Pretriangulated.IsHomotopyLimit c) :
    ∀ (ωX : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
        (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (_ : Pretriangulated.IsHomotopyLimit ωX)
      (ωY : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
        (R(aY)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (_ : Pretriangulated.IsHomotopyLimit ωY)
      (N : 𝐃(X, Λ)) (φ : (L((f)^*[ModuleCat.{u + 1} Λ])).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) Y).obj (op L)).obj ωY.pt) ⟶ N),
      DerivedCategory.derivedComplete X.smallEtaleTopology I N →
        (∀ n : ℕ, IsIso ((reductionModIdeal Λ X (I ^ n)).map φ)) →
          Nonempty (c.pt ≅ ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op N)).obj ωX.pt) := by
  intro ωX hωX ωY hωY N φ _ hφ
  have hφ₁ := hφ 1
  rw [pow_one] at hφ₁
  exact nonempty_iso_derivedHom_of_isHomotopyLimit I hϖ hI aX aY f hf hL hc ωX hωX ωY hωY N φ
    hφ₁

include hϖ hI in
/-- The integral exceptional adjoint on constructible complexes.

For a separated finite-type `f : X ⟶ Y` of finite-type `k`-schemes and `L ∈ Dᵇc(Y, Λ)`, put
`G_f L = R lim_n Res_n Rf_n^! L_n`, the derived limit of the finite exceptional inverse images of
the reductions of `L`. As restriction of scalars commutes with `Rf^!`,
`Res_n Rf_n^! L_n = Rf^!(L ⊗ᴸ A_n)`, so `G_f L` is the point of a homotopy limit cone `c` of the
tower `n ↦ Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)`. Likewise the integral dualizing complex
`ω_{X,Λ} = R lim_n Res_n Ra_n^! A_n` is the point of a homotopy limit cone `ωX` of the tower
`n ↦ Ra_X^!(Λ ⧸ Iⁿ)`, the integral Verdier dual is `𝔻_{X,Λ} = RHom(-, ω_{X,Λ})`, and similarly
on `Y`. Then:

1. `G_f L ∈ Dᵇc(X, Λ)`, and `(G_f L) ⊗ᴸ A_n ≅ Rf^!(L ⊗ᴸ A_n)`;
2. `G_f` is right adjoint to the integral `Rf_!` on the constructible categories, with the
   canonical unit and counit: `G_f L` is identified with `Rf^! L` compatibly with the maps to the
   `Rf^!(L ⊗ᴸ A_n)` (`AlgebraicGeometry.Etale.exists_iso_rightDerivedUpperShriek`), so that the
   adjunction is `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` transported along
   this isomorphism;
3. `G_f L ≅ 𝔻_{X,Λ} f^*_comp 𝔻_{Y,Λ} L`, where the completed pullback `f^*_comp M` is the
   derived complete object `N` receiving a map from `Lf^* M` inducing isomorphisms on all
   reductions;
4. if the reductions of `L` have Tor amplitude in `[a, b]`, those of `G_f L` have Tor amplitude
   in `[a - 2 dim X, b + 2 dim Y]`. -/
theorem boundedConstructibleIntegral_exceptionalAdjoint {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {L : 𝐃(Y, Λ)}
    (hL : DerivedCategory.boundedConstructibleIntegral I Y L)
    {c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
      (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint)} (hc : Pretriangulated.IsHomotopyLimit c) :
    (DerivedCategory.boundedConstructibleIntegral I X c.pt ∧
      ∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj c.pt ≅
        (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj ((reductionModIdeal Λ Y (I ^ n)).obj L))) ∧
    (∃ e : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L ≅ c.pt, ∀ n : ℕ,
      e.hom ≫ c.π.app (op n) = (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.map
        ((DerivedCategory.derivedCompletionCone Y.smallEtaleTopology I L).π.app (op n))) ∧
    (∀ (ωX : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
        (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (_ : Pretriangulated.IsHomotopyLimit ωX)
      (ωY : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
        (R(aY)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (_ : Pretriangulated.IsHomotopyLimit ωY)
      (N : 𝐃(X, Λ)) (φ : (L((f)^*[ModuleCat.{u + 1} Λ])).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) Y).obj (op L)).obj ωY.pt) ⟶ N),
      DerivedCategory.derivedComplete X.smallEtaleTopology I N →
        (∀ n : ℕ, IsIso ((reductionModIdeal Λ X (I ^ n)).map φ)) →
          Nonempty (c.pt ≅ ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op N)).obj ωX.pt)) ∧
    ∀ dX dY : ℕ, topologicalKrullDim X ≤ (dX : WithBot ℕ∞) →
      topologicalKrullDim Y ≤ (dY : WithBot ℕ∞) → ∀ a b : ℤ,
        (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
          ((reductionModIdeal Λ Y (I ^ (n + 1))).obj L)) →
        ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X
          (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj c.pt) := by
  have hBT := boundedConstructibleIntegral_and_torAmplitudeIn_of_isHomotopyLimit I hϖ hI aX aY
    f hf hL hc
  exact ⟨⟨hBT.1, nonempty_iso_reductionModIdeal_of_isHomotopyLimit_rightDerivedUpperShriek I hϖ
      hI aX aY f hf hL hc⟩, exists_iso_rightDerivedUpperShriek I f hL.1 hc,
    nonempty_iso_derivedHom_of_isHomotopyLimit_of_derivedComplete I hϖ hI aX aY f hf hL hc,
    hBT.2⟩

end Constructible

section Matrix

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

variable [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
  {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

include hϖ hI in
/-- Blueprint `proposition-six-operations-dctf`: Preservation results and their actual hypotheses,
the integral entries (item 5).

At the integral stage (`Λ` a Noetherian domain complete for `I = (ϖ)`, `Λ ⧸ I` finite of
exponent invertible on `k`), for a separated finite-type morphism `f : X ⟶ Y` of separated
finite-type `k`-schemes:

* the internal hom commutes with reduction, both as `RHom(K, L) ⊗ᴸ A_n ≅ RHom(K, L ⊗ᴸ A_n)`
  and as `RHom_Λ(K, L) ⊗ᴸ A_n ≅ RHom_{A_n}(K_n, L_n)`, and preserves derived completeness
  (`proposition-six-operations-change-coefficients--7`), and preserves `Dᵇc(-, Λ)`
  (`proposition-six-operations-dctf--15`);
* the derived limit `G_f L` of the reduced exceptional inverse images lies in `Dᵇc(X, Λ)` and
  is identified with `Rf^! L` compatibly with the maps to the `Rf^!(L ⊗ᴸ A_n)`, so that it is
  right adjoint to `Rf_!` on the constructible categories through
  `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction`; its reductions are
  `(G_f L) ⊗ᴸ A_n ≅ Rf^!(L ⊗ᴸ A_n)`;
* the derived reductions of any object form a normalized tower, and a normalized tower is the
  tower of reductions of its derived limit, which is derived complete
  (`lemma-sp-tower-adjunction-foundation--2`). -/
theorem preservationMatrix_integral {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    (∀ (n : ℕ) (K L : 𝐃(X, Λ)),
      Nonempty ((reductionModIdeal Λ X (I ^ n)).obj
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L) ≅
        ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj
          ((reductionModIdeal Λ X (I ^ n)).obj L))) ∧
    (∀ (n : ℕ) (K L : 𝐃(X, Λ)) (Kn Ln : 𝐃(X, Λ ⧸ I ^ n))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn)
      (η' : L ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Ln),
      IsDerivedBaseChange η → IsDerivedBaseChange η' →
        Nonempty ((reductionModIdeal Λ X (I ^ n)).obj
            (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L) ≅
          (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
            (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X).obj (op Kn)).obj Ln))) ∧
    (∀ K L : 𝐃(X, Λ), DerivedCategory.derivedComplete X.smallEtaleTopology I L →
      DerivedCategory.derivedComplete X.smallEtaleTopology I
        (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L)) ∧
    (∀ K L : 𝐃(X, Λ), DerivedCategory.boundedConstructibleIntegral I X K →
      DerivedCategory.boundedConstructibleIntegral I X L →
        DerivedCategory.boundedConstructibleIntegral I X
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L)) ∧
    (∀ L : 𝐃(Y, Λ), DerivedCategory.boundedConstructibleIntegral I Y L →
      ∀ c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
        (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint), Pretriangulated.IsHomotopyLimit c →
        DerivedCategory.boundedConstructibleIntegral I X c.pt ∧
          (∃ e : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L ≅ c.pt, ∀ n : ℕ,
            e.hom ≫ c.π.app (op n) = (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.map
              ((DerivedCategory.derivedCompletionCone Y.smallEtaleTopology I L).π.app (op n))) ∧
          ∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj c.pt ≅
            (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
              ((reductionModIdeal Λ Y (I ^ n)).obj L))) ∧
    (∀ (K : 𝐃(X, Λ)) (Kn : ∀ n : ℕ, 𝐃(X, Λ ⧸ I ^ (n + 1)))
      (η : ∀ n : ℕ, K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ (n + 1))) X).obj (Kn n)),
      (∀ n : ℕ, IsDerivedBaseChange (η n)) → ∃ M : NormalizedTower I X, M.obj = Kn) ∧
    ∀ (M : NormalizedTower I X) (c : Cone M.restrict), Pretriangulated.IsHomotopyLimit c →
      (∀ n : ℕ, IsDerivedBaseChange (φ := Ideal.Quotient.mk (I ^ (n + 1))) (c.π.app (op n))) ∧
        DerivedCategory.derivedComplete X.smallEtaleTopology I c.pt :=
  ⟨fun n K L ↦ hI ▸ nonempty_iso_reductionModIdeal_derivedHom_obj hϖ n K L,
    fun n _ _ _ _ _ _ hη hη' ↦ nonempty_iso_reductionModIdeal_derivedHom I hϖ hI n hη hη',
    fun _ _ hL ↦ derivedComplete_derivedHom I hϖ hI hL,
    fun _ _ hK hL ↦ (boundedConstructibleIntegral_derivedHom I hϖ hI aX hK hL).1,
    fun _ hL _ hc ↦
      have h := boundedConstructibleIntegral_exceptionalAdjoint I hϖ hI aX aY f hf hL hc
      ⟨h.1.1, h.2.1, h.1.2⟩,
    (exists_normalizedTower_and_boundedConstructibleIntegral_iff (I := I) (X := X)).1,
    fun M _ hc ↦ M.isDerivedBaseChange_of_isHomotopyLimit hϖ hI hc⟩

end Matrix

end Etale

end AlgebraicGeometry
