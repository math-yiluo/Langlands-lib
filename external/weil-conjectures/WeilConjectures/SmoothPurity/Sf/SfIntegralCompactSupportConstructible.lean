/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralCompactSupportTower
import WeilConjectures.SmoothPurity.Sf.SfCompactSupportTowerPresentation
import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Open.OpenFiniteConstructibilityInterval
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import Mathlib.Data.Nat.Prime.Infinite
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Integral compact-support constructibility

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tag 0GL0
(blueprint: lem-sf-integral-compact-support-constructible).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open CategoryTheory.Pretriangulated in
private theorem compactSupport_limit_iso
    {C : Type v} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T U : ℕ → C} [HasProduct T] [HasProduct U]
    (t : ∀ n, T (n + 1) ⟶ T n) (s : ∀ n, U (n + 1) ⟶ U n)
    (e : Functor.ofOpSequence t ≅ Functor.ofOpSequence s)
    {M N : C} (hM : IsDerivedLimit t M) (hN : IsDerivedLimit s N) :
    Nonempty (M ≅ N) := by
  obtain ⟨p, δ, hp⟩ := hM
  obtain ⟨q, ε, hq⟩ := hN
  let a : ∀ n : ℕ, T n ≅ U n := fun n ↦ e.app ⟨n⟩
  let P : (∏ᶜ T) ≅ ∏ᶜ U :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  have ht : ∀ n, (a (n + 1)).hom ≫ s n = t n ≫ (a n).hom := by
    intro n
    change e.hom.app ⟨n + 1⟩ ≫ s n = t n ≫ e.hom.app ⟨n⟩
    simpa only [Functor.ofOpSequence_map_homOfLE_succ] using
      (e.hom.naturality (homOfLE (Nat.le_add_right n 1)).op).symm
  let A := Triangle.mk p (towerTransitionEndomorphism t) δ
  let B := Triangle.mk q (towerTransitionEndomorphism s) ε
  let d := Pretriangulated.isoTriangleOfIso₁₂ A.rotate B.rotate
    (Pretriangulated.rot_of_distTriang A hp)
    (Pretriangulated.rot_of_distTriang B hq) P P
    (towerTransitionEndomorphism_natural_backward t s (fun n ↦ (a n).hom) ht).symm
  let d' : A ≅ B := (rotCompInvRot.app A) ≪≫
    (Pretriangulated.invRotate C).mapIso d ≪≫ (rotCompInvRot.app B).symm
  exact ⟨Triangle.π₁.mapIso d'⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

private theorem compactSupport_complete_iff
    (T : Scheme.{u}) (K : DerivedCategory (scalarReductionSource.{u, u} l E T)) :
    IsSfDerivedComplete l E T K ↔ IsDerivedCompleteUnrestricted l E T K := by
  constructor
  · intro hK
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    have : Fact p.Prime := ⟨hprime⟩
    let D : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hprime
        exponent_pos := by decide
        cardinality_eq := by simp
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl : l ≠ D.p := by change l ≠ p; omega
    exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E T D hl K).mp hK⟩
  · rintro ⟨D, hl, hK⟩
    exact (sfDerivedComplete_iff_legacy l E T D hl K).mpr hK

/-- Every derived limit of the specified finite-level compact-support tower is bounded
constructible and derived complete, with one cohomological interval for all reductions.
Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tag 0GL0
(blueprint: lem-sf-integral-compact-support-constructible).

Proof:
1. Give the compactification's middle scheme the field structure induced by its proper
map to Y. It is finite type and Noetherian, its open part is quasi-compact, and l is
invertible in its stalks.
2. Obtain the normalized slice open operation, its strict completed reduction comparison,
and the proper/support tower comparison. Identify its finite open functors and the two
whole inverse systems with the intrinsic consumer presentations.
3. Convert the input's derived completeness to the unrestricted comparison predicate.
The completed open-reduction theorem gives completeness of its extension by zero.
4. The evaluated reduction comparison identifies every reduction of that extension with
intrinsic finite extension by zero. Finite open constructibility preserves the original
common interval; isomorphism transport gives integral constructibility of the extension.
5. Apply integral direct-image constructibility to the proper map. Its ordinary image has
constructible reductions, derived completeness and one uniformly enlarged interval.
6. Compose the ordinary-to-slice, slice proper-to-support, and support-to-intrinsic tower
isomorphisms. Their product isomorphisms intertwine the Roos endomorphisms. Complete
these to an isomorphism of rotated distinguished triangles and rotate back to identify
any chosen derived limit with the constructed proper image.
7. Transport integral constructibility through that object isomorphism. No canonical
comparison between arbitrary chosen derived limits is asserted. -/
theorem sfIntegralCompactSupport_constructible
    (K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hK : sfIntegralConstructible l E X K)
    [HasProduct (sfCompactSupportTerm l E c K)]
    (M : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (_hM : IsDerivedLimit (sfCompactSupportTransition l E c K) M) :
    sfIntegralConstructible l E Y M := by
  classical
  let : c.Z.Over (Spec (.of K₀)) := ⟨c.g ≫ (Y ↘ Spec (.of K₀))⟩
  let : c.g.IsOver (Spec (.of K₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType (c.Z ↘ Spec (.of K₀)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ (Y ↘ Spec (.of K₀))))
  have : QuasiCompact (c.Z ↘ Spec (.of K₀)) :=
    inferInstanceAs (QuasiCompact (c.g ≫ (Y ↘ Spec (.of K₀))))
  have : IsLocallyNoetherian c.Z :=
    LocallyOfFiniteType.isLocallyNoetherian (c.Z ↘ Spec (.of K₀))
  have : CompactSpace c.Z :=
    QuasiCompact.compactSpace_of_compactSpace (c.Z ↘ Spec (.of K₀))
  have : IsNoetherian c.Z := ⟨⟩
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hlZ : ∀ z : c.Z, IsUnit (l : c.Z.presheaf.stalk z) := by
    intro z
    let ρ := (Scheme.ΓSpecIso (.of K₀)).inv ≫
      (c.Z ↘ Spec (.of K₀)).appTop ≫ c.Z.presheaf.germ ⊤ z trivial
    simpa only [map_natCast] using _hl.map ρ.hom
  obtain ⟨o, SV, SX, tensor, r, d, e, htower⟩ :=
    CompactSupportProperImageTower.compactSupportProperImageTower l E K₀ f _hl c
  obtain ⟨hfinite, hpresentation⟩ := sfCompactSupportTower_presentation l E c o d e
  let K' : (IntegralOpenReduction.complete l E X).FullSubcategory :=
    ⟨K, (compactSupport_complete_iff l E X K).mp _hK.1⟩
  let J := (IntegralOpenReduction.shriek l E c.i o).obj K
  have hJ : sfIntegralConstructible l E c.Z J := by
    refine ⟨(compactSupport_complete_iff l E c.Z J).mpr (r.extensionComplete K'), ?_⟩
    obtain ⟨a, b, hab, hred⟩ := _hK.2
    refine ⟨a, b, hab, fun n ↦ ?_⟩
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
    have := (sfIntrinsicExtensionByZero_exact c.i
      (Padic.coefficientExtensionRing l E (n + 1))).1
    have := (sfIntrinsicExtensionByZero_exact c.i
      (Padic.coefficientExtensionRing l E (n + 1))).2.1
    have := (sfIntrinsicExtensionByZero_exact c.i
      (Padic.coefficientExtensionRing l E (n + 1))).2.2
    obtain ⟨en⟩ := hfinite n
    let α := CompactSupportProperImageTower.alpha.{u, u} l E c.i o SV SX tensor r K' n ≪≫
      (Functor.mapDerivedCategoryNatIso en).app
        ((scalarReductionDerivedExtension l E X n).obj K)
    have hout := open_finite_constructibility_interval l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) c.i hlZ a b hab
      ((scalarReductionDerivedExtension l E X n).obj K) (hred n).1 (hred n).2
    have : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) c.Z) :=
      (proEtale_bounded_constructible_isTriangulated c.Z A).1
    refine ⟨ObjectProperty.prop_of_iso _ α.symm hout.1, ?_⟩
    intro i hi
    apply hout.2.1
    intro hz
    exact hi (((DerivedCategory.homologyFunctor _ i).mapIso α).isZero_iff.mpr hz)
  obtain ⟨hprod, ⟨L⟩⟩ := (sfIntegralDirectImage_constructible K₀ l _hl E c.g J hJ).1
  let := hprod
  have hL := (sfIntegralDirectImage_constructible K₀ l _hl E c.g J hJ).2.1 L
  obtain ⟨b, _⟩ := (htower K').2
  obtain ⟨⟨left⟩, ⟨right⟩⟩ := hpresentation K'
  obtain ⟨dM⟩ := compactSupport_limit_iso (sfDirectImageTransition l E c.g J)
    (sfCompactSupportTransition l E c K) (left ≪≫ b ≪≫ right)
      ⟨L.projection, L.boundary, L.roos⟩ _hM
  exact ObjectProperty.prop_of_iso _ dM hL.1

end WeilConjectures
