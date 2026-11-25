/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportStrictReductionComparison
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportFiniteComparison
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

set_option linter.privateModule false

/-! # Existence of a normalized compact-support comparison

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: lem-qcqs-compact-support-normalized-iso-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

private theorem projection_transpose
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    {F : C ⥤ D} {R : D ⥤ C} (a : F ⊣ R)
    {S : C ⥤ T} {L : T ⥤ C} (b : S ⊣ L)
    (ev : T ⥤ D) (π : L ⟶ ev ⋙ R) (e : S ⋙ ev ≅ F)
    (hu : ∀ P, b.unit.app P ≫ π.app (S.obj P) =
      a.unit.app P ≫ R.map (e.inv.app P))
    {P Q : C} {N : T} {V : D} (β : S.obj P ⟶ N) (γ : Q ≅ L.obj N)
    (ε : ev.obj N ⟶ V) (d : F.obj Q ⟶ V)
    (hγ : γ.hom ≫ π.app N ≫ R.map ε = a.unit.app Q ≫ R.map d) :
    F.map (b.unit.app P ≫ L.map β ≫ γ.inv) ≫ d =
      e.inv.app P ≫ ev.map β ≫ ε := by
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have hn := a.unit.naturality (b.unit.app P ≫ L.map β ≫ γ.inv)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hn
  calc
    a.unit.app P ≫ R.map (F.map (b.unit.app P ≫ L.map β ≫ γ.inv) ≫ d) =
        (b.unit.app P ≫ L.map β ≫ γ.inv) ≫ a.unit.app Q ≫ R.map d := by
      rw [R.map_comp, ← Category.assoc, ← hn]
      simp only [Category.assoc]
    _ = (b.unit.app P ≫ L.map β ≫ γ.inv) ≫
        γ.hom ≫ π.app N ≫ R.map ε := by rw [hγ]
    _ = b.unit.app P ≫ L.map β ≫ π.app N ≫ R.map ε := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = b.unit.app P ≫ π.app (S.obj P) ≫ R.map (ev.map β) ≫ R.map ε := by
      have hp := π.naturality β
      simp only [Functor.comp_map] at hp
      rw [← Category.assoc (L.map β), hp]
      simp only [Category.assoc]
    _ = a.unit.app P ≫ R.map (e.inv.app P ≫ ev.map β ≫ ε) := by
      rw [← Category.assoc (b.unit.app P), hu]
      simp only [Functor.map_comp, Category.assoc]

private theorem complete_zero_of_reductions
    (W : Scheme.{u}) (A : DerivedCategory (scalarReductionSource l E W))
    (hA : IsSfDerivedComplete l E W A)
    (hzero : ∀ n : ℕ, IsZero ((scalarReductionDerivedExtension l E W n).obj A)) :
    IsZero A := by
  obtain ⟨hp, δ, hδ⟩ := hA
  let := hp
  have hz : IsZero (∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj A) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Pi.hom_ext
    intro n
    have := (scalarReductionRestriction_exact l E W n).1
    have := (scalarReductionRestriction_exact l E W n).2
    have : (scalarReductionDerivedRestriction l E W n).Additive := by
      dsimp only [scalarReductionDerivedRestriction]
      infer_instance
    exact ((scalarReductionDerivedRestriction l E W n).map_isZero (hzero n)).eq_of_tgt _ _
  exact Pretriangulated.Triangle.isZero₁_of_isZero₂₃ _ hδ hz hz

private theorem constructible_of_complete_reduction_isos
    (W : Scheme.{u}) {A B : DerivedCategory (scalarReductionSource l E W)}
    (hA : IsSfDerivedComplete l E W A) (hB : sfIntegralConstructible l E W B)
    (e : ∀ n : ℕ, (scalarReductionDerivedExtension l E W n).obj A ≅
      (scalarReductionDerivedExtension l E W n).obj B) :
    sfIntegralConstructible l E W A := by
  obtain ⟨_, a, b, hab, hred⟩ := hB
  refine ⟨hA, a, b, hab, fun n ↦ ?_⟩
  let R := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite R := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) W) :=
    (proEtale_bounded_constructible_isTriangulated W R).1
  refine ⟨ObjectProperty.prop_of_iso _ (e n).symm (hred n).1, ?_⟩
  intro i hi
  apply (hred n).2
  intro hz
  exact hi (((DerivedCategory.homologyFunctor _ i).mapIso (e n)).isZero_iff.mpr hz)

private theorem constructible_isIso_of_reductions
    (W : Scheme.{u}) {A B : DerivedCategory (scalarReductionSource l E W)}
    (a : A ⟶ B) (hA : sfIntegralConstructible l E W A)
    (hB : sfIntegralConstructible l E W B)
    (ha : ∀ n : ℕ, IsIso ((scalarReductionDerivedExtension l E W n).map a)) :
    IsIso a := by
  obtain ⟨C, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle a
  obtain ⟨C', hC', ⟨e⟩⟩ := ObjectProperty.ext_of_isTriangulatedClosed₃'
    (sfIntegralConstructible l E W) _ hT hA hB
  have hz : IsZero C' := by
    apply complete_zero_of_reductions l E W C' hC'.1
    intro n
    let R := scalarReductionDerivedExtension l E W n
    obtain ⟨hshift, htri⟩ :=
      (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.2.1
    let : R.CommShift ℤ := hshift
    have : R.IsTriangulated := htri
    have hzC : IsZero (R.obj C) :=
      Pretriangulated.Triangle.isZero₃_of_isIso₁ _ (R.map_distinguished _ hT) (ha n)
    exact hzC.of_iso (R.mapIso e).symm
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).mp (hz.of_iso e)

end WeilConjectures
