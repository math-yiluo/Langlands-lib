/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.RationalStage
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.ProEtale.Adic.Retract
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Karoubian

/-!
# Properties of the field coefficient stages

Three remarks of blueprint `theorem-f-shriek-ell-adic-coefficients--4` point to properties of the
field coefficient stages proved elsewhere in the blueprint:

* the rationalization `Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[1/ϖ]` is idempotent complete, so that the
  canonical functor into its Karoubi envelope is an equivalence;
* the common-stage category `Dᵇc(X, ℚ̄_ℓ)` is idempotent complete, so that the canonical functor
  into its Karoubi envelope is an equivalence;
* at a field coefficient, every bounded constructible complex has finite Tor amplitude, so that
  `Dᵇctf = Dᵇc` (`proposition-ctf-equals-bc`, from `proposition-ctf-equals-bc`).

## Implementation notes

* The Karoubi envelopes carry no triangulated structure in this repository, so "exact
  equivalence" is rendered as an equivalence of categories.
* The stage `ℚ̄_ℓ` is `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic`, the
  Bhatt–Scholze model of the common-stage category.
* The derived tensor product of the field stages is only available, in this repository, for
  étale sheaves of modules over a discrete coefficient field `F`; the Tor amplitude statements
  are made there.
* The idempotent completeness of `Dᵇc(X, ℚ̄_ℓ)` and the lemma `proposition-ctf-equals-bc` belong
  to other parts of the blueprint. In the Bhatt–Scholze model, idempotent completeness of
  `Dᵇc(X, ℚ̄_ℓ)` needs no descent to finite stages: an idempotent of a bounded object of
  `D(X_proét, ℚ̄_ℓ)` splits (`CategoryTheory.Triangulated.TStructure.isSplit_of_isGE_of_isLE`),
  and `Dᵇc(X, ℚ̄_ℓ)` is stable under retracts, retracts of constructible sheaves being
  constructible (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.of_retract`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace DerivedCategory

open Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A triangulated property of objects of `D(C)`, closed under isomorphisms, which holds for
every object of `C` placed in degree `0` holds for every bounded object: by induction on the
length of the range of `K`, along the truncation triangle `τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶` whose
third term is `Hᵇ K` placed in degree `b`. -/
lemma prop_of_isGE_of_isLE_of_forall_singleFunctor (P : ObjectProperty (DerivedCategory C))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (h : ∀ G : C, P ((singleFunctor C 0).obj G)) (K : DerivedCategory C) (a b : ℤ)
    [K.IsGE a] [K.IsLE b] : P K := by
  suffices H : ∀ (m : ℕ) (a : ℤ) (K : DerivedCategory C), K.IsGE a → K.IsLE (a + m - 1) → P K
    from H (b - a + 1).toNat a K inferInstance (TStructure.t.isLE_of_le K b _ (by lia))
  intro m
  induction m with
  | zero =>
    intro a K _ _
    have : K.IsLE (a - 1) := by simpa using ‹K.IsLE (a + ↑(0 : ℕ) - 1)›
    exact P.prop_of_isZero (TStructure.t.isZero K (a - 1) a (by lia))
  | succ m ih =>
    intro a K _ _
    set b : ℤ := a + m
    let T := (TStructure.t.triangleLTGE b).obj K
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K
    have : T.obj₃.IsLE b := by
      have : K.IsLE b := TStructure.t.isLE_of_le K (a + ↑(m + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b)
    have : T.obj₃.IsGE b := inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE b).obj K) b)
    obtain ⟨G, ⟨eG⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ b
    have h₃ : P T.obj₃ :=
      P.prop_of_iso ((((singleFunctors C).shiftIso (-b) b 0 (by lia)).app G) ≪≫ eG.symm)
        (P.le_shift (-b) _ (h G))
    have h₁ : P T.obj₁ := ih a T.obj₁
      (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a))
      (TStructure.t.isLE_truncLT_obj _ _ _ (by lia))
    exact P.ext_of_isTriangulatedClosed₂ _ hT h₁ h₃

end DerivedCategory

namespace AlgebraicGeometry

section Rational

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Pointer to the properties of the rationalization.

The rationalization `Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[1/ϖ_E]`, in which no idempotent is adjoined, is
nevertheless idempotent complete, so that the canonical functor into its Karoubi envelope is an
equivalence. -/
theorem Etale.DerivedCategory.isIdempotentComplete_and_isEquivalence_toKaroubi_rational
    (X : Scheme.{u}) :
    IsIdempotentComplete
        (Etale.DerivedCategory.boundedConstructibleRational l E X).FullSubcategory ∧
      (Idempotents.toKaroubi
        (Etale.DerivedCategory.boundedConstructibleRational l E X).FullSubcategory).IsEquivalence :=
  ⟨Etale.DerivedCategory.isIdempotentComplete_boundedConstructibleRational l E X,
    Etale.DerivedCategory.isEquivalence_toKaroubi_boundedConstructibleRational l E X⟩

end Rational

section AlgebraicClosure

variable (l : ℕ) [Fact l.Prime]

/-- The common-stage category `Dᵇc(X, ℚ̄_ℓ)` is stable under retracts: the homology sheaves of a
retract are retracts of constructible sheaves
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.of_retract`). -/
instance ProEtale.DerivedCategory.isStableUnderRetracts_boundedConstructibleAdic
    (X : Scheme.{u}) :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l X).IsStableUnderRetracts where
  of_retract {M N} e := by
    rintro ⟨hb, hc⟩
    obtain ⟨a, b, hab⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded N).2 hb
    exact ⟨(_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded M).1
      ⟨a, b, (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_retract e hab⟩,
      fun n ↦ (ProEtale.adicConstructibleSheaf l X).prop_of_retract
        (e.map (_root_.DerivedCategory.homologyFunctor _ n)) (hc n)⟩

/-- Idempotent completeness of the common-stage category.

The common-stage category `Dᵇc(X, ℚ̄_ℓ)` (in its Bhatt–Scholze model
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic`) is idempotent complete. -/
theorem ProEtale.DerivedCategory.isIdempotentComplete_boundedConstructibleAdic
    (X : Scheme.{u}) :
    IsIdempotentComplete (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory :=
  Idempotents.isIdempotentComplete_iff_isSplit.2 fun K p hp ↦ by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
  have : _root_.DerivedCategory.TStructure.t.IsLE K.obj (a + ((b - a).toNat : ℕ)) :=
    _root_.DerivedCategory.TStructure.t.isLE_of_le K.obj b _ (by lia)
  obtain ⟨Y, i, r, hir, hri⟩ := Triangulated.TStructure.isSplit_of_isGE_of_isLE
    _root_.DerivedCategory.TStructure.t (b - a).toNat K.obj a p.hom
    ((ObjectProperty.ι _).congr_map hp)
  exact ⟨⟨Y, (ProEtale.DerivedCategory.boundedConstructibleAdic l X).prop_of_retract
    ⟨i, r, hir⟩ K.property⟩, ObjectProperty.homMk i, ObjectProperty.homMk r,
    by cat_disch, by cat_disch⟩

/-- Pointer to the properties of the common-stage category.

The common-stage category `Dᵇc(X, ℚ̄_ℓ)`, in which no idempotent is adjoined, is nevertheless
idempotent complete, so that the canonical functor into its Karoubi envelope is an equivalence. -/
theorem ProEtale.DerivedCategory.isIdempotentComplete_and_isEquivalence_toKaroubi_adic
    (X : Scheme.{u}) :
    IsIdempotentComplete (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory ∧
      (Idempotents.toKaroubi
        (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory).IsEquivalence :=
  have := ProEtale.DerivedCategory.isIdempotentComplete_boundedConstructibleAdic l X
  ⟨this, inferInstance⟩

end AlgebraicClosure

section FieldTorAmplitude

variable (F : Type (u + 1)) [Field F] (X : Scheme.{u})

/-- Blueprint `proposition-ctf-equals-bc`: Finite Tor amplitude at field coefficients.

For a coefficient field `F`, every bounded constructible complex `K` of étale sheaves of
`F`-modules has finite Tor amplitude: there are `a ≤ b` with `𝓗ʳ(K ⊗ᴸ_F M) = 0` for `r ∉ [a, b]`
and every sheaf `M` of `F`-modules.

The blueprint node is stated for the rationalized category `Dᵇc(Y, E)` and for the common-stage
category `Dᵇc(Y, ℚ̄_ℓ)`. In this repository these have no derived tensor product with sheaves, so
the statement is formalised for étale sheaves of modules over a discrete field `F`.

Every sheaf of `F`-modules is flat (its stalks are `F`-vector spaces), so each sheaf placed in
degree `0` has Tor amplitude in `[0, 0]`; finite Tor amplitude is a triangulated property, so it
holds for every bounded complex, by induction along truncation triangles. -/
theorem Etale.DerivedCategory.finiteTorAmplitude_of_boundedConstructible_of_field
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} F))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) X K) :
    Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) X K := by
  obtain ⟨⟨⟨a, _⟩, ⟨b, _⟩⟩, -⟩ := hK
  refine _root_.DerivedCategory.prop_of_isGE_of_isLE_of_forall_singleFunctor _ (fun G ↦ ?_) K a b
  refine ⟨0, 0, Etale.torAmplitudeIn_singleFunctor_zero_of_flat _ G ?_⟩
  exact (Etale.flat_iff_forall_flat_sheafFiber_obj G).2 fun _ ↦
    (ModuleCat.flat_iff_flat _).2 inferInstance

/-- Blueprint `proposition-ctf-equals-bc`: Pointer to the properties of finite Tor
amplitude.

At a field coefficient `F` the finite-Tor category is the bounded constructible one,
`Dᵇctf(X, F) = Dᵇc(X, F)`, consistently with the amplitude condition: every bounded constructible
complex at a field coefficient has finite Tor amplitude (blueprint
`proposition-ctf-equals-bc`). -/
theorem Etale.DerivedCategory.constructibleFiniteTor_eq_boundedConstructible_of_field :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} F) X =
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) X := by
  ext K
  exact ⟨fun h ↦ h.1, fun h ↦
    ⟨h, Etale.DerivedCategory.finiteTorAmplitude_of_boundedConstructible_of_field F X h⟩⟩

end FieldTorAmplitude

end AlgebraicGeometry
