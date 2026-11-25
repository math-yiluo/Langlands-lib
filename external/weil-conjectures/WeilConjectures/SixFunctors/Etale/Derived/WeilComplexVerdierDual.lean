/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierDualWeil
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplex

/-!
# Verdier duality of strict Weil complexes

Let `k` be an algebraically closed field, `Λ` a finite ring whose exponent is invertible on `k`,
`X` separated of finite type over `k` with structure morphism `a_X`, and `g : X ≅ X` an
automorphism lying over an automorphism `h` of `Spec k` (`g ≫ a_X = a_X ≫ h`, a cartesian
square); in the `ℓ`-adic formalism `g` is the geometric Frobenius of `X = X₀ ×_{k₀} k`. This file
proves the finite-stage part of blueprint `prose-10-20`: Verdier duality
preserves the category of strict Weil complexes (`AlgebraicGeometry.Etale.WeilComplex`), and
biduality is an isomorphism of Weil complexes.

* For automorphisms the exceptional base change is invertible
  (`AlgebraicGeometry.Etale.isIso_upperShriekBaseChangeMap`), so the dualizing Weil datum is
  invertible and `ω_X` is a strict Weil complex (`AlgebraicGeometry.Etale.WeilComplex.dualizing`).
* The Verdier dual `𝔻_X K = RHom(K, ω_X)` of a strict Weil complex `(K, φ)`, with the dual Weil
  datum `AlgebraicGeometry.Etale.verdierDualWeilDatumOfIsPullback` of `φ` and of the dualizing
  Weil datum, is a strict Weil complex (`AlgebraicGeometry.Etale.WeilComplex.verdierDual`): the
  dual datum is invertible because `Lg^*` is an autoequivalence.
* The double-dual map `δ_K : K ⟶ 𝔻_X 𝔻_X K` is a morphism of Weil complexes, by the Weil
  equivariance of biduality (`AlgebraicGeometry.Etale.isWeilEquivariant_verdierDualDoubleDual`),
  and an isomorphism by finite-stage biduality
  (`AlgebraicGeometry.Etale.WeilComplex.isIso_verdierDualDoubleDual`).

The rational and `ℚ̄_ℓ` stages of the blueprint statement are not formalised: the Weil category
is modelled at a finite coefficient ring, as in
`WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

section Exchange

variable {X S : Scheme.{u}} {g : X ⟶ X} {h : S ⟶ S} {a : X ⟶ S} [HasCompactification a]
  [QuasiCompact a]

variable (Λ) in
/-- For automorphisms `g` and `h` forming a cartesian square `g ≫ a = a ≫ h`, the exceptional
base change `Lg^* Ra^! ⟶ Ra^! Lh^*` is an isomorphism: it is the mate of the inverse of the
compact-support base change isomorphism, and `Lg^*`, `Lh^*` are equivalences
(`CategoryTheory.isIso_mateEquiv_of_isEquivalence`). -/
instance isIso_upperShriekBaseChangeMap (sq : IsPullback g a a h) [IsIso g] [IsIso h] :
    IsIso (upperShriekBaseChangeMap Λ sq) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  exact isIso_mateEquiv_of_isEquivalence _ _ _

/-- For automorphisms `g` and `h`, the dualizing Weil datum `Lg^* ω_X ⟶ ω_X` is an isomorphism. -/
instance isIso_dualizingComplexWeilDatum (sq : IsPullback g a a h) [IsIso g] [IsIso h] :
    IsIso (dualizingComplexWeilDatum (Λ := Λ) sq) := by
  unfold dualizingComplexWeilDatum upperShriekMateWeilDatum
  infer_instance

end Exchange

namespace WeilComplex

omit [Finite Λ] in
/-- A morphism of strict Weil complexes whose underlying morphism is an isomorphism is an
isomorphism of Weil complexes. -/
lemma isIso_of_isIso_hom {X : Scheme.{u}} {g : X ≅ X} {K L : WeilComplex (ModuleCat.{u + 1} Λ) g}
    (f : K ⟶ L) [IsIso f.hom] :
    IsIso f := by
  let finv : L ⟶ K :=
    { hom := inv f.hom
      comm := by
        rw [← cancel_epi ((DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).map f.hom),
          ← reassoc_of% f.comm, IsIso.hom_inv_id, Category.comp_id, ← Functor.map_comp_assoc,
          IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp] }
  exact ⟨⟨finv, Hom.ext (by simp [finv]), Hom.ext (by simp [finv])⟩⟩

variable {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
  {X : Scheme.{u}} (g : X ≅ X) (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasCompactification aX] {h : Spec (.of k) ⟶ Spec (.of k)} [IsIso h]
  (sq : IsPullback g.hom aX aX h)

/-- Blueprint `prose-10-20`: the dualizing complex `ω_X = Ra_X^! Λ` with
the dualizing Weil datum (`AlgebraicGeometry.Etale.dualizingComplexWeilDatum`), invertible for
automorphisms, is a strict Weil complex. -/
noncomputable def dualizing : WeilComplex (ModuleCat.{u + 1} Λ) g where
  obj := ⟨dualizingComplex _ aX, constructibleFiniteTor_dualizingComplex Λ (𝟙 _) aX
    (constructibleFiniteTor_tensorUnit Λ _)⟩
  frobenius := ObjectProperty.isoMk _ (asIso (dualizingComplexWeilDatum sq))

omit [IsSeparated aX] [LocallyOfFiniteType aX] in
@[simp]
lemma dualizing_frobenius_hom_hom :
    (dualizing g aX sq).frobenius.hom.hom = dualizingComplexWeilDatum (Λ := Λ) sq :=
  rfl

variable [IsAlgClosed k]

/-- The dual Weil datum on the Verdier dual of a strict Weil complex is invertible: `Lg^*` is an
autoequivalence and the dualizing Weil datum is invertible
(`CategoryTheory.MonoidalClosed.isIso_dualWeilDatum`). -/
instance isIso_verdierDualWeilDatumOfIsPullback (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    IsIso (verdierDualWeilDatumOfIsPullback sq
      ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius)) := by
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) g.hom
  exact MonoidalClosed.isIso_dualWeilDatum _ _ _

/-- Blueprint `prose-10-20`: **Verdier duality preserves strict Weil
complexes.** The Verdier dual `𝔻_X K = RHom(K, ω_X)` of a strict Weil complex `(K, φ)`, with the
dual Weil datum `AlgebraicGeometry.Etale.verdierDualWeilDatumOfIsPullback` of `φ` and of the
dualizing Weil datum, invertible for the automorphism `g`, is a strict Weil complex. -/
noncomputable def verdierDual (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    WeilComplex (ModuleCat.{u + 1} Λ) g where
  obj := ⟨(Etale.verdierDual Λ aX).obj (op K.obj.obj),
    constructibleFiniteTor_verdierDual Λ aX K.obj.property⟩
  frobenius := ObjectProperty.isoMk _ (asIso (verdierDualWeilDatumOfIsPullback sq
    ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius)))

@[simp]
lemma verdierDual_obj_obj (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (verdierDual g aX sq K).obj.obj = (Etale.verdierDual Λ aX).obj
      (op K.obj.obj) :=
  rfl

lemma verdierDual_frobenius_hom_hom (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (verdierDual g aX sq K).frobenius.hom.hom =
      verdierDualWeilDatumOfIsPullback sq
        ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius) :=
  rfl

/-- Blueprint `prose-10-20`: the double-dual map `δ_K : K ⟶ 𝔻_X 𝔻_X K`
is a morphism of strict Weil complexes: biduality is Weil equivariant
(`AlgebraicGeometry.Etale.isWeilEquivariant_verdierDualDoubleDual`). -/
noncomputable def verdierDualDoubleDual (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    K ⟶ verdierDual g aX sq (verdierDual g aX sq K) where
  hom := ObjectProperty.homMk
    ((Etale.verdierDualDoubleDual Λ aX).app K.obj.obj)
  comm := by
    have : IsIso (verdierDualWeilDatum Λ aX
        ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius) (dualizingComplexWeilDatum sq)) :=
      isIso_verdierDualWeilDatumOfIsPullback g aX sq K
    apply ObjectProperty.hom_ext
    exact (isWeilEquivariant_verdierDualDoubleDual Λ aX
      ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius) (dualizingComplexWeilDatum sq)).symm

/-- Blueprint `prose-10-20`: **Verdier biduality for strict Weil
complexes.** The double-dual map `K ⟶ 𝔻_X 𝔻_X K` is an isomorphism of strict Weil complexes, by
finite-stage biduality (`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`). -/
instance isIso_verdierDualDoubleDual (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    IsIso (verdierDualDoubleDual g aX sq K) := by
  have : IsIso ((DerivedCategoryFiniteTor.ι _ X).map (verdierDualDoubleDual g aX sq K).hom) :=
    isIso_verdierDualDoubleDual_app Λ aX K.obj.property
  have : (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X).ReflectsIsomorphisms :=
    inferInstanceAs (DerivedCategory.constructibleFiniteTor _ X).ι.ReflectsIsomorphisms
  have : IsIso (verdierDualDoubleDual g aX sq K).hom :=
    isIso_of_reflects_iso _ (DerivedCategoryFiniteTor.ι _ X)
  exact isIso_of_isIso_hom _

end WeilComplex

end Etale

end AlgebraicGeometry
