/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Standard truncations of intrinsic integral constructible objects
Source: Bhatt--Scholze, Proposition 6.8.11(3), and blueprint constructible-heart proof
(blueprint: lem-sf-intrinsic-integral-standard-truncations).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Integral constructible objects are bounded and preserved by standard truncations.
Source: Bhatt--Scholze, Proposition 6.8.11(3); blueprint constructible-heart proof
(blueprint: lem-sf-intrinsic-integral-standard-truncations).

Proof: finite type over the geometric finite-field base makes Y noetherian of finite
Krull dimension, with l invertible. The integral stratified-perfect characterization
identifies the intrinsic uniformly bounded reduction condition with boundedness and
constructible cohomology after the canonical completed coefficient transport. Standard
truncation preserves these cohomology conditions. Its inverse transport is exact, so
commutes with standard truncations. Transport the characterization back to obtain the
two intrinsic membership statements. The same characterization gives ambient boundedness.
The zero complex, empty scheme and every integer cutoff are included. -/
theorem sfIntegralStandardTruncations
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] :
    ∀ K : sfIntegralConstructibleCategory l E Y,
      DerivedCategory.TStructure.t.bounded K.obj ∧ ∀ n : ℤ,
        sfIntegralConstructible l E Y
          ((DerivedCategory.TStructure.t.truncLE n).obj K.obj) ∧
        sfIntegralConstructible l E Y
          ((DerivedCategory.TStructure.t.truncGE n).obj K.obj) := by
  classical
  let f := Y ↘ Spec (.of D.k)
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType f
  have hd := exists_topologicalKrullDim_le f
  have hu : IsUnit (l : Γ(Y, ⊤)) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    have hunit : IsUnit (l : D.k₀) :=
      (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit
    let g := f ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
    simpa only [map_natCast] using
      hunit.map ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ g.appTop).hom
  have hinv (y : Y) : IsUnit (l : Y.presheaf.stalk y) := by
    simpa only [map_natCast] using hu.map (Y.presheaf.germ ⊤ y trivial).hom
  have := (pbcIntegralUniformComplete_isTriangulated l E Y hd hinv).1
  let := (integralDetailedCoefficientRestriction_exact Y l E).1
  let := (integralDetailedCoefficientRestriction_exact Y l E).2
  let F := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison Y l E).hom
  have : F.Faithful := ⟨fun {M N} {f g} h ↦ by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h⟩
  intro K
  have hK := (integralStratifiedPerfectDetailed Y l E hd hu K.obj).mp K.property
  obtain ⟨a, b, _, ha, hb⟩ :=
    ((integralStratifiedPerfectCharacterization Y l E hd hu _).2.mp
      ((integralStratifiedPerfectCharacterization Y l E hd hu _).1.mp hK)).1
  have hbounded : DerivedCategory.TStructure.t.bounded
      ((integralDetailedTransport Y l E).obj K.obj) := ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨F.bounded_of_bounded_mapDerivedCategory_obj hbounded, fun n ↦ ?_⟩
  obtain ⟨hLE, hGE⟩ := (integralStratifiedPerfectClosure Y l E hd hu).2.2.1 _ hK n
  constructor
  · apply (integralStratifiedPerfectDetailed Y l E hd hu _).mpr
    exact ObjectProperty.prop_of_iso _
      ((F.mapDerivedCategoryTruncLEIso n).symm.app K.obj) hLE
  · apply (integralStratifiedPerfectDetailed Y l E hd hu _).mpr
    exact ObjectProperty.prop_of_iso _
      ((F.mapDerivedCategoryTruncGEIso n).symm.app K.obj) hGE

end WeilConjectures
