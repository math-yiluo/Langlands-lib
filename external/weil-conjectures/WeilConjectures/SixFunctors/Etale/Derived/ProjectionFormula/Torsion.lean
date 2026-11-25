/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.ReductionLeft
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# The projection formula for torsion objects

Let `Λ` be a principal ideal domain (for instance `Λ = 𝒪_E`). This file proves the projection
formula `PF_{f, K, L} : Rf_! K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)` over `Λ` when `K` is *torsion* (killed
by a nonzero integer) and bounded below, `K ⊗ᴸ Lf^* L` is bounded below, and `L` is bounded
constructible. The coefficient ring itself need not be torsion.

The proof is that of the finite projection formula, `sk-thm-sf-pf-finite`, run at the geometric
points of `Y`:

* geometric points detect isomorphisms
  (`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map`);
* the projection map commutes with compactly supported base change
  (`AlgebraicGeometry.Etale.projectionMapOfCompactification_baseChange'`), and the base change
  maps occurring there are invertible by proper base change for bounded below complexes with
  torsion cohomology (`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`);
* on a geometric fibre `Spec Ω` the pullback of `L` is bounded with constructible, hence constant
  and finitely generated, cohomology sheaves. Over the principal ideal domain `Λ` a finitely
  generated module is the cokernel of an injective map `Λᵇ ⟶ Λᵃ`, and the constant complexes
  `(Λᵃ)` are dualizable, so the projection formula holds there by dévissage
  (`DerivedCategory.prop_of_bounded`).

## Main statements

- `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_of_forall_algClosurePoint`:
  the geometric-point criterion.
- `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_of_isSepClosed`: the
  projection formula over a separably closed field, at bounded constructible objects.
- `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_of_nsmul_id_eq_zero`: the
  projection formula for torsion objects.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)`. -/
local notation "𝐃(" X ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-! ### Torsion and proper base change -/

/-- If a nonzero integer kills an object of `D(X_ét, Λ)`, its cohomology sheaves are torsion. -/
lemma isTorsionModuleSheaf_homology_of_nsmul_id_eq_zero {X : Scheme.{u}} {M : 𝐃(X)} {N : ℕ}
    (hN : N ≠ 0) (hM : N • 𝟙 M = 0) (q : ℤ) :
    IsTorsionModuleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj M) := by
  set H := (_root_.DerivedCategory.homologyFunctor _ q).obj M
  have hH : N • 𝟙 H = 0 := by
    rw [← (_root_.DerivedCategory.homologyFunctor _ q).map_id, ← Functor.map_nsmul, hM,
      Functor.map_zero]
  rw [isTorsionModuleSheaf_iff_isTorsion]
  refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U s ↦ ?_
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, Nat.pos_of_ne_zero hN, ?_⟩
  have h2 : ∀ n : ℕ, (n • 𝟙 H).hom.app U = n • 𝟙 (H.obj.obj U) := by
    intro n
    induction n with
    | zero => rw [zero_smul, zero_smul]; rfl
    | succ n ih => rw [succ_nsmul, Sheaf.Hom.add_app, ih, succ_nsmul]; rfl
  have h3 := congr_arg (fun φ : H ⟶ H ↦ (φ.hom.app U).hom s) hH
  simp only [h2, ModuleCat.hom_nsmul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
    id_eq] at h3
  exact h3

/-- **Proper base change for torsion objects**: the unbounded derived base change map of a
cartesian square with `f` proper is invertible at a bounded below object killed by a nonzero
integer. -/
theorem isIso_derivedBaseChangeMap_app_of_nsmul_id_eq_zero {X Y X' Y' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f]
    (sq : IsPullback g' f' f g) (M : 𝐃(X)) (n : ℤ) [M.IsGE n] {N : ℕ} (hN : N ≠ 0)
    (hM : N • 𝟙 M = 0) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app M) :=
  (isIso_derivedBaseChangeMap_app_ι_obj_iff _ sq.toCommSq ⟨M, n, ‹_›⟩).2
    (isIso_baseChange_of_isProper_of_torsionHomology Λ sq _
      fun q ↦ isTorsionModuleSheaf_homology_of_nsmul_id_eq_zero hN hM q)

/-! ### General coefficients -/

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  [HasSmallSiteSheafify A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

omit [CommRing Λ] in
private lemma isIso_of_comp_eq {C : Type*} [Category C] {P Q R : C} {a : P ⟶ Q} {g : Q ⟶ R}
    {r : P ⟶ R} (h : a ≫ g = r) [IsIso g] [IsIso r] : IsIso a := by
  have : a = r ≫ inv g := by rw [← h]; simp
  rw [this]
  infer_instance

/-- **The pullback of the projection map to a base change.** For a commutative square
`g' ≫ f = f' ≫ g`, a compactification `c` of `f` and a compactification `c'` of `f'` lying over
`c`, the pullback `Lg^* PF_{c, K, L}` of the projection map is an isomorphism as soon as the
derived base change maps of the proper parts are invertible at `i_! K` and `i_!(K ⊗ᴸ Lf^* L)`
and the projection formula for `c'` holds at `(Lg'^* K, Lg^* L)`. -/
theorem isIso_leftDerivedUpperStar_map_projectionMapOfCompactification {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (c : Compactification f) (c' : Compactification f') (q : c'.Z ⟶ c.Z)
    (hi : IsPullback g' c'.i c.i q) (hp : CommSq q c'.g c.g g)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h₁ : IsIso ((derivedBaseChangeMap A hp).app (D((c.i)_!open[A]).obj K)))
    (h₂ : IsIso ((derivedBaseChangeMap A hp).app
      (D((c.i)_!open[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)))))
    (h₃ : HasProjectionFormulaOfCompactification A c' ((L((g')^*[A])).obj K)
      ((L((g)^*[A])).obj L)) :
    IsIso ((L((g)^*[A])).map (((projectionMapOfCompactification A c).app K).app L)) := by
  have key := projectionMapOfCompactification_baseChange' A sq c c' q hi hp K L
  have : IsIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi hp).app
      K) := by
    rw [rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app]
    infer_instance
  have : IsIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi hp).app
      (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L))) := by
    rw [rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app]
    infer_instance
  have : IsIso (((projectionMapOfCompactification A c').app ((L((g')^*[A])).obj K)).app
      ((L((g)^*[A])).obj L)) := h₃
  exact isIso_of_comp_eq key

omit [HasSmallSiteSheafify A] in
/-- The projection formula at the first two objects of a distinguished triangle gives it at the
third. -/
lemma HasProjectionFormulaOfCompactification.obj₃ {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    {T : Pretriangulated.Triangle (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))}
    (hT : T ∈ distTriang _) (h₁ : HasProjectionFormulaOfCompactification A c K T.obj₁)
    (h₂ : HasProjectionFormulaOfCompactification A c K T.obj₂) :
    HasProjectionFormulaOfCompactification A c K T.obj₃ := by
  let τ : (-⊗ᴸ-(Y)[A]).obj ((Rf_!(c)[A]).obj K) ⟶
      (L((f)^*[A]) ⋙ (-⊗ᴸ-(X)[A]).obj K) ⋙ Rf_!(c)[A] :=
    (projectionMapOfCompactification A c).app K
  have h₁ : IsIso (τ.app T.obj₁) := h₁
  have h₂ : IsIso (τ.app T.obj₂) := h₂
  exact NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂ τ hT h₁ h₂

omit [HasSmallSiteSheafify A] in
/-- **Dévissage of the projection formula in the second variable.** If the projection formula
holds at `(K, F[0])` for every sheaf `F` with a property `P`, it holds at `(K, L)` for every
bounded `L` whose cohomology sheaves have the property `P`. -/
lemma HasProjectionFormulaOfCompactification.of_bounded {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (P : ObjectProperty (Sheaf Y.smallEtaleTopology A)) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ F, P F → HasProjectionFormulaOfCompactification A c K
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hL : _root_.DerivedCategory.TStructure.t.bounded L)
    (hLP : ∀ n, P ((_root_.DerivedCategory.homologyFunctor _ n).obj L)) :
    HasProjectionFormulaOfCompactification A c K L := by
  let τ : (-⊗ᴸ-(Y)[A]).obj ((Rf_!(c)[A]).obj K) ⟶
      (L((f)^*[A]) ⋙ (-⊗ᴸ-(X)[A]).obj K) ⋙ Rf_!(c)[A] :=
    (projectionMapOfCompactification A c).app K
  exact _root_.DerivedCategory.prop_of_bounded τ.isoLocus P hP L hL hLP

omit [CommRing Λ] in
private lemma nsmul_id_eq_zero_of_iso {C : Type*} [Category C] [Preadditive C] {P Q : C}
    (e : P ≅ Q) {N : ℕ} (h : N • 𝟙 Q = 0) : N • 𝟙 P = 0 := by
  have h2 : e.hom ≫ (N • 𝟙 Q) ≫ e.inv = N • 𝟙 P := by
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, e.hom_inv_id]
  rw [← h2, h, zero_comp, comp_zero]

omit [CommRing Λ] [Etale.UpperStarPreservesFlat A] [HasSmallSiteSheafify A] in
/-- An integer killing `K` kills `K ⊗ᴸ M`. -/
lemma nsmul_id_derivedTensor_obj_obj {X : Scheme.{u}}
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) {N : ℕ} (hK : N • 𝟙 K = 0) :
    N • 𝟙 (((-⊗ᴸ-(X)[A]).obj K).obj M) = 0 := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf X.smallEtaleTopology A)
  refine nsmul_id_eq_zero_of_iso (β_ K M) ?_
  change N • 𝟙 (((-⊗ᴸ-(X)[A]).obj M).obj K) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hK, Functor.map_zero]

end General

/-! ### The geometric point criterion -/

/-- **The projection formula can be checked on geometric fibres.** Let `c` be a compactification
of `f : X ⟶ Y`. Suppose that at every geometric point `x : Spec Ω ⟶ Y` the derived base change
maps of the proper part of `c` are invertible at `i_! K` and at `i_!(K ⊗ᴸ Lf^* L)`, and that the
projection formula holds on the fibre over `x` for the pullbacks of `K` and `L`. Then the
projection formula holds at `(K, L)`. -/
theorem hasProjectionFormulaOfCompactification_of_forall_algClosurePoint {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) (K : 𝐃(X)) (L : 𝐃(Y))
    (h₁ : ∀ y : Y, IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback c.g (Y.algClosurePoint y)).toCommSq).app
        (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj K)))
    (h₂ : ∀ y : Y, IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback c.g (Y.algClosurePoint y)).toCommSq).app
        (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)))))
    (h₃ : ∀ y : Y, HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ)
      (c.ofIsPullback (IsPullback.of_hasPullback f (Y.algClosurePoint y)))
      ((L((pullback.fst f (Y.algClosurePoint y))^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ])).obj L)) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c K L :=
  isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map Λ _ fun y ↦
    isIso_leftDerivedUpperStar_map_projectionMapOfCompactification _
      (IsPullback.of_hasPullback f (Y.algClosurePoint y)).toCommSq c
      (c.ofIsPullback (IsPullback.of_hasPullback f (Y.algClosurePoint y)))
      (pullback.fst c.g (Y.algClosurePoint y))
      (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f (Y.algClosurePoint y)))
      (IsPullback.of_hasPullback c.g (Y.algClosurePoint y)).toCommSq K L (h₁ y) (h₂ y) (h₃ y)

/-! ### Separably closed fields -/

variable (Λ) in
/-- The projection formula holds at the constant complex `(Λᵐ)` placed in degree `0`, which is
dualizable. -/
lemma hasProjectionFormulaOfCompactification_constantSheaf_pi {X' Y' : Scheme.{u}}
    {f' : X' ⟶ Y'} (c' : Compactification f') (E : 𝐃(X')) (m : ℕ) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c' E
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin m → Λ)))) := by
  refine hasProjectionFormulaOfCompactification_of_isDualizable _ c' E ?_
  let F := (constantSheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ (Fin m → Λ))
  refine isDualizableEtale_of_trivialization
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) 0 0 inferInstance inferInstance
    (fun n ↦ ?_) ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app F)
  by_cases hn : n = 0
  · subst hn
    exact ⟨m, ⟨Retract.ofIso (HomologicalComplex.singleObjXSelf _ 0 F)⟩⟩
  · exact ⟨0, ⟨{ i := 0, r := 0, retract :=
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn).eq_of_src _ _ }⟩⟩

variable (Λ) in
/-- Over a principal ideal domain a finitely generated module `M` sits in a short exact sequence
`0 ⟶ Λᵇ ⟶ Λᵃ ⟶ M ⟶ 0`. -/
lemma exists_shortExact_pi [IsPrincipalIdealRing Λ] [IsDomain Λ] (M : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ M] :
    ∃ (a b : ℕ) (S : ShortComplex (ModuleCat.{u + 1} Λ)), S.ShortExact ∧
      Nonempty (S.X₁ ≅ ModuleCat.of Λ (Fin b → Λ)) ∧
      Nonempty (S.X₂ ≅ ModuleCat.of Λ (Fin a → Λ)) ∧ Nonempty (S.X₃ ≅ M) := by
  obtain ⟨a, φ, hφ⟩ := Module.Finite.exists_fin' Λ M
  let K := LinearMap.ker φ
  have : Module.Finite Λ K := Module.IsNoetherian.finite Λ K
  have : Module.Free Λ K := Module.free_of_finite_type_torsion_free'
  let S : ShortComplex (ModuleCat.{u + 1} Λ) :=
    ShortComplex.mk (ModuleCat.ofHom K.subtype) (ModuleCat.ofHom φ) (by
      ext x
      exact x.2)
  refine ⟨a, Module.finrank Λ K, S, ModuleCat.shortComplex_shortExact S ?_ ?_ ?_,
    ⟨(Module.finBasis Λ K).equivFun.toModuleIso⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  · intro y
    change φ y = 0 ↔ ∃ x : K, (x : Fin a → Λ) = y
    exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩
  · exact Subtype.val_injective
  · exact hφ

/-- **The projection formula over a separably closed field.** Let `Λ` be a principal ideal
domain, `Ω` a separably closed field and `c'` a compactification of `f' : X' ⟶ Spec Ω`. The
projection formula holds at `(E, C)` for every `E` and every bounded constructible `C`: the
cohomology sheaves of `C` are constant with finitely generated values, built out of the
dualizable constant complexes `(Λᵃ)` by cones. -/
theorem hasProjectionFormulaOfCompactification_of_isSepClosed [IsPrincipalIdealRing Λ]
    [IsDomain Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of Ω)} (c' : Compactification f') (E : 𝐃(X')) {C : 𝐃(Spec (.of Ω))}
    (hC : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of Ω)) C) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c' E C := by
  let e := constantSheafEquivalenceOfIsSepClosed Λ (k := Ω)
  -- the projection formula at a constant sheaf with finitely generated value
  have hM : ∀ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M →
      HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c' E
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (e.functor.obj M)) := by
    intro M _
    obtain ⟨a, b, S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_shortExact_pi Λ M
    have hT := (hS.map_of_exact e.functor).singleTriangle_distinguished
    refine HasProjectionFormulaOfCompactification.of_iso_right _ c'
      ((_root_.DerivedCategory.singleFunctor _ 0).mapIso (e.functor.mapIso e₃))
      (HasProjectionFormulaOfCompactification.obj₃ _ c' E hT ?_ ?_)
    · exact HasProjectionFormulaOfCompactification.of_iso_right _ c'
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso (e.functor.mapIso e₁)).symm
        (hasProjectionFormulaOfCompactification_constantSheaf_pi Λ c' E b)
    · exact HasProjectionFormulaOfCompactification.of_iso_right _ c'
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso (e.functor.mapIso e₂)).symm
        (hasProjectionFormulaOfCompactification_constantSheaf_pi Λ c' E a)
  refine HasProjectionFormulaOfCompactification.of_bounded _ c' E
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) (Spec (.of Ω))) (fun F hF ↦ ?_) C hC.1 hC.2
  have : IsConstructibleSheaf F := hF
  have hfin := finite_Γ_of_isConstructibleSheaf (Λ := Λ) (k := Ω) F
  have : Module.Finite Λ (e.inverse.obj F) :=
    Module.Finite.equiv ((Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) isTerminalEtalePoint).app F).toLinearEquiv
  exact HasProjectionFormulaOfCompactification.of_iso_right _ c'
    ((_root_.DerivedCategory.singleFunctor _ 0).mapIso (e.counitIso.app F)) (hM _ this)

/-! ### Torsion objects -/

/-- **The projection formula for torsion objects.** Let `Λ` be a principal ideal domain and `c`
a compactification of `f : X ⟶ Y`. If `K` is killed by a nonzero integer and bounded below,
`K ⊗ᴸ Lf^* L` is bounded below and `L` is bounded constructible, the projection formula holds at
`(K, L)`. -/
theorem hasProjectionFormulaOfCompactification_of_nsmul_id_eq_zero [IsPrincipalIdealRing Λ]
    [IsDomain Λ] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : 𝐃(X)) (L : 𝐃(Y))
    {N : ℕ} (hN : N ≠ 0) (hK : N • 𝟙 K = 0) (n₁ : ℤ) [K.IsGE n₁] (n₂ : ℤ)
    [(((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)).IsGE n₂]
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y L) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c K L := by
  have : IsProper c.g := c.isProper
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have hKL := nsmul_id_derivedTensor_obj_obj _ K (L((f)^*[ModuleCat.{u + 1} Λ]).obj L) hK
  have hi : ∀ T : 𝐃(X), N • 𝟙 T = 0 →
      N • 𝟙 (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj T) = 0 := fun T hT ↦ by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hT, Functor.map_zero]
  refine hasProjectionFormulaOfCompactification_of_forall_algClosurePoint c K L
    (fun y ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_)
  · have := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).isGE_mapDerivedCategory_obj
      K n₁
    exact isIso_derivedBaseChangeMap_app_of_nsmul_id_eq_zero
      (IsPullback.of_hasPullback c.g (Y.algClosurePoint y)) _ n₁ hN (hi K hK)
  · have := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).isGE_mapDerivedCategory_obj
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) n₂
    exact isIso_derivedBaseChangeMap_app_of_nsmul_id_eq_zero
      (IsPullback.of_hasPullback c.g (Y.algClosurePoint y)) _ n₂ hN (hi _ hKL)
  · exact hasProjectionFormulaOfCompactification_of_isSepClosed _ _
      (boundedConstructible_leftDerivedUpperStar _ _ hL)

end Etale

end AlgebraicGeometry
