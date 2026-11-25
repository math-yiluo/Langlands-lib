/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DenseCompactification
public import WeilConjectures.AlgebraicGeometry.GenericFiber.GeometricGenericFiber
public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualProper
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Duality
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBiduality
public import WeilConjectures.SixFunctors.Etale.Derived.PointBiduality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation

/-!
# Finite-stage étale Verdier biduality: the dimension induction

This file assembles the proof of blueprint `theorem-verdier-biduality--1`: for a finite
ring `Λ`, an algebraically closed field `k` on which the exponent of `Λ` is invertible, and `X`
separated, quasi-compact and locally of finite type over `k`, the double-dual map
`δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for every `K ∈ Dctf(X, Λ)`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_isAlgClosed`: the theorem.
- `AlgebraicGeometry.Etale.bidualityInDim`: the induction on `d ≥ dim X`, simultaneously for all
  algebraically closed fields (`AlgebraicGeometry.Etale.BidualityInDim`).
- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_forall_isProper`: the reduction to
  proper `X` through affine opens and dense compactifications.
- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_isProper`: the proper case, from
  the closed-point step and proper push-forward to the point.
- `AlgebraicGeometry.Etale.isZero_sheafFiber_homology_of_not_mem_closedPoints`: the cone of `δ_K`
  vanishes at non-closed points, by the induction hypothesis on geometric generic fibres.
- `AlgebraicGeometry.Etale.isIso_map_verdierDualDoubleDual_app_leftDerivedUpperStar_iff`: the
  restriction statement `corollary-verdier-exchange-formulas--5` after any further functor `H`,
  which compares `Lg^* Lι^* δ_K` with `Lg^* δ_{Lι^* K}` for an open immersion `ι` and a further
  pullback `g`.

## Implementation notes

The dimension-zero case needs no separate treatment: if `dim X ≤ 0`, every point is closed, so
the closed-point step applies directly; in the generic-fibre step the geometric generic fibre is
nonempty, which forces `d ≥ 1`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- Blueprint `corollary-verdier-exchange-formulas--5` (auxiliary): whether the unit of an
adjunction becomes an isomorphism after applying a functor `H` only depends on the left adjoint up
to isomorphism. -/
lemma isIso_map_unit_app_iff_of_iso {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C} (adj₁ : F₁ ⊣ G₁)
    (adj₂ : F₂ ⊣ G₂) (e : F₁ ≅ F₂) (H : C ⥤ E) (X : C) :
    IsIso (H.map (adj₁.unit.app X)) ↔ IsIso (H.map (adj₂.unit.app X)) := by
  rw [← unit_rightAdjointUniq_hom_app (adj₁.ofNatIsoLeft e) adj₂ X]
  have h : (adj₁.ofNatIsoLeft e).unit.app X = adj₁.unit.app X ≫ G₁.map (e.hom.app X) := rfl
  rw [h, H.map_comp, H.map_comp, isIso_comp_right_iff, isIso_comp_right_iff]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {Y W : Scheme.{u}} (ωY : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
  (ωW : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)) (j : W ⟶ Y) [IsOpenImmersion j]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- Blueprint `corollary-verdier-exchange-formulas--5`, the extension-by-zero step, after a further
functor `H`: for an open immersion `j : W ⟶ Y` and a Verdier exchange `e : 𝔻_Y ∘ j_! ≅ Rj_* ∘ 𝔻_W`
(relative to arbitrary objects `ω_Y`, `ω_W`), `H δ_M` is an isomorphism if and only if
`H (j^* δ_{j_! M})` is. This is the proof of
`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_iff_lowerShriek` (the case `H = 𝟭`). -/
theorem isIso_map_verdierDualDoubleDual_app_iff_lowerShriek
    (e : D((j)_!open[A]) ⋙ ((RHom(Y)[A]).flip.obj ωY).rightOp ≅
      ((RHom(W)[A]).flip.obj ωW).rightOp ⋙ (R((j)_*[A])).op)
    {E : Type*} [Category* E] (H : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A) ⥤ E)
    (M : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    IsIso (H.map ((derivedHomToIhomIhomNatTrans A W ωW).app M)) ↔
      IsIso (H.map (D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app
        (D((j)_!open[A]).obj M)))) := by
  let adjY : ((RHom(Y)[A]).flip.obj ωY).rightOp ⊣ (RHom(Y)[A]).flip.obj ωY :=
    MonoidalClosed.ihomFlipSelfAdjunction _
  let adjW : ((RHom(W)[A]).flip.obj ωW).rightOp ⊣ (RHom(W)[A]).flip.obj ωW :=
    MonoidalClosed.ihomFlipSelfAdjunction _
  let p := mapDerivedUpperStarLowerStarAdjunction A j
  let q := derivedOpenImmersionLowerShriekUpperStarAdjunction A j
  have h := Adjunction.isIso_map_unit_app_iff_of_iso (q.comp adjY) (adjW.comp p.op) e H M
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app, H.map_comp, H.map_comp] at h
  have : IsIso (p.op.unit.app (((RHom(W)[A]).flip.obj ωW).rightOp.obj M)) := by
    dsimp
    infer_instance
  rw [isIso_comp_left_iff, isIso_comp_right_iff, MonoidalClosed.ihomFlipSelfAdjunction_unit_app,
    MonoidalClosed.ihomFlipSelfAdjunction_unit_app] at h
  exact h.symm

set_option maxRecDepth 8000 in
/-- Blueprint `corollary-verdier-exchange-formulas--5`, the cone step, after a further functor `H`:
if `f : K' ⟶ K` becomes invertible on the open `W`, then `H (j^* δ_K)` is an isomorphism if and
only if `H (j^* δ_{K'})` is (relative to an arbitrary object `ω_Y`). This is the proof of
`AlgebraicGeometry.Etale.isIso_upperStar_map_verdierDualDoubleDual_app_iff_of_isIso`. -/
theorem isIso_map_upperStar_map_verdierDualDoubleDual_app_iff_of_isIso
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [Etale.UpperStarPreservesFlat A]
    [Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {E : Type*} [Category* E] (H : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A) ⥤ E)
    {K' K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (f : K' ⟶ K)
    (hf : IsIso (D((j)^*[A]).map f)) :
    IsIso (H.map (D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app K))) ↔
      IsIso (H.map (D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app K'))) := by
  have hz : ∀ Z : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A),
      IsZero (D((j)^*[A]).obj Z) →
        IsZero (D((j)^*[A]).obj (((RHom(Y)[A]).flip.obj ωY).obj (op Z))) := by
    intro Z hZ
    obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_upperStar_derivedHom (FC := FC) A j Z ωY
    exact (isZero_ihom_obj_of_isZero hZ _).of_iso e
  have hdd : IsIso (D((j)^*[A]).map
      ((((RHom(Y)[A]).flip.obj ωY).rightOp ⋙ (RHom(Y)[A]).flip.obj ωY).map f)) := by
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
    have hZ : IsZero (D((j)^*[A]).obj Z) :=
      (Triangle.isZero₃_iff_isIso₁ _ (D((j)^*[A]).map_distinguished _ hT)).2 hf
    obtain ⟨w, hw⟩ := exists_distTriang_derivedHom_flip_derivedHom_flip A ωY _ hT
    have h3 : IsZero (D((j)^*[A]).obj
        (((RHom(Y)[A]).flip.obj ωY).obj (op (((RHom(Y)[A]).flip.obj ωY).obj (op Z))))) :=
      hz (((RHom(Y)[A]).flip.obj ωY).obj (op Z)) (hz Z hZ)
    have hw' := D((j)^*[A]).map_distinguished _ hw
    have h4 : IsZero (D((j)^*[A]).obj
        ((((RHom(Y)[A]).flip.obj ωY).rightOp ⋙ (RHom(Y)[A]).flip.obj ωY).obj Z)) := h3
    exact (Triangle.isZero₃_iff_isIso₁ _ hw').1 h4
  have nat := congrArg (fun φ ↦ H.map (D((j)^*[A]).map φ))
    ((derivedHomToIhomIhomNatTrans A Y ωY).naturality f)
  simp only [Functor.id_map, Functor.map_comp] at nat
  constructor
  · intro h
    have : IsIso (H.map (D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app K')) ≫
        H.map (D((j)^*[A]).map
          ((((RHom(Y)[A]).flip.obj ωY).rightOp ⋙ (RHom(Y)[A]).flip.obj ωY).map f))) := by
      rw [← nat]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (H.map (D((j)^*[A]).map
      ((((RHom(Y)[A]).flip.obj ωY).rightOp ⋙ (RHom(Y)[A]).flip.obj ωY).map f)))
  · intro h
    have : IsIso (H.map (D((j)^*[A]).map f) ≫
        H.map (D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app K))) := by
      rw [nat]
      infer_instance
    exact IsIso.of_isIso_comp_left (H.map (D((j)^*[A]).map f)) _

/-- Blueprint `corollary-verdier-exchange-formulas--5`, after a further functor `H`: for an open
immersion `j : W ⟶ Y` and a Verdier exchange `e : 𝔻_Y ∘ j_! ≅ Rj_* ∘ 𝔻_W` (relative to arbitrary
objects `ω_Y`, `ω_W`), `H δ_{j^* K}` is an isomorphism if and only if `H (j^* δ_K)` is. -/
theorem isIso_map_verdierDualDoubleDual_app_mapDerivedCategory_upperStar_iff
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [Etale.UpperStarPreservesFlat A]
    [Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (e : D((j)_!open[A]) ⋙ ((RHom(Y)[A]).flip.obj ωY).rightOp ≅
      ((RHom(W)[A]).flip.obj ωW).rightOp ⋙ (R((j)_*[A])).op)
    {E : Type*} [Category* E] (H : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A) ⥤ E)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (H.map ((derivedHomToIhomIhomNatTrans A W ωW).app (D((j)^*[A]).obj K))) ↔
      IsIso (H.map (D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app K))) := by
  rw [isIso_map_verdierDualDoubleDual_app_iff_lowerShriek A ωY ωW j e]
  let q := derivedOpenImmersionLowerShriekUpperStarAdjunction A j
  have : IsIso (D((j)^*[A]).map (q.counit.app K)) := by
    have : IsIso (q.unit.app (D((j)^*[A]).obj K) ≫ D((j)^*[A]).map (q.counit.app K)) := by
      rw [q.right_triangle_components K]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (q.unit.app _) _
  exact (isIso_map_upperStar_map_verdierDualDoubleDual_app_iff_of_isIso (FC := FC) A ωY j H
    (q.counit.app K) this).symm

end General

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- Blueprint `definition-verdier-dual-evaluation--4`: the double-dual morphism only depends on the
structure morphism, not on the (propositional) instances attached to it. -/
lemma isIso_map_verdierDualDoubleDual_app_congr {X S : Scheme.{u}} {a b : X ⟶ S} (h : a = b)
    [HasCompactification a] [HasCompactification b] {E : Type*} [Category* E]
    (H : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ E)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (H.map ((verdierDualDoubleDual Λ a).app K)) ↔
      IsIso (H.map ((verdierDualDoubleDual Λ b).app K)) := by
  subst h
  rfl

/-- Blueprint `definition-verdier-dual-evaluation--4`: by naturality of `δ`, whether `H δ_K` is an
isomorphism only depends on `K` up to isomorphism. -/
lemma isIso_map_verdierDualDoubleDual_app_iff_of_iso {X S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a] {E : Type*} [Category* E]
    (H : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ E)
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : K ≅ K') :
    IsIso (H.map ((verdierDualDoubleDual Λ a).app K)) ↔
      IsIso (H.map ((verdierDualDoubleDual Λ a).app K')) := by
  have nat := congrArg H.map ((verdierDualDoubleDual Λ a).naturality e.hom)
  simp only [Functor.id_map, Functor.map_comp] at nat
  have : IsIso (H.map (((verdierDual Λ a).rightOp ⋙ verdierDual Λ a).map e.hom)) := by
    infer_instance
  constructor
  · intro h
    have : IsIso (H.map e.hom ≫ H.map ((verdierDualDoubleDual Λ a).app K')) := by
      rw [nat]
      infer_instance
    exact IsIso.of_isIso_comp_left (H.map e.hom) _
  · intro h
    have : IsIso (H.map ((verdierDualDoubleDual Λ a).app K) ≫
        H.map (((verdierDual Λ a).rightOp ⋙ verdierDual Λ a).map e.hom)) := by
      rw [← nat]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (H.map (((verdierDual Λ a).rightOp ⋙ verdierDual Λ a).map e.hom))

/-- Blueprint `corollary-verdier-exchange-formulas--5`, after a further functor `H`: for a
quasi-compact open immersion `j : W ⟶ Y` and finite coefficients, `H δ_{Lj^* K}` (relative to
`ω_W = R(j ≫ a)^! Λ`) is an isomorphism if and only if `H (Lj^* δ_K)` is. For `H = 𝟭` this is
`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_leftDerivedUpperStar_iff`; with `H` a
further pullback, it compares the double-dual maps on a geometric generic fibre. -/
theorem isIso_map_verdierDualDoubleDual_app_leftDerivedUpperStar_iff {Y W S : Scheme.{u}}
    (a : Y ⟶ S) (j : W ⟶ Y) [HasCompactification j] [HasCompactification a]
    [HasCompactification (j ≫ a)] [QuasiCompact (j ≫ a)] [IsOpenImmersion j] [QuasiCompact j]
    {E : Type*} [Category* E]
    (H : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ E)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (H.map ((verdierDualDoubleDual _ (j ≫ a)).app
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))) ↔
      IsIso (H.map ((L((j)^*[ModuleCat.{u + 1} Λ])).map
        ((verdierDualDoubleDual _ a).app K))) := by
  let e := verdierDualLowerShriekIso _ j (dualizingComplex Λ a) (dualizingComplex Λ (j ≫ a))
    (derivedHomRightDerivedLowerShriekIsoOfFinite Λ j)
    (nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ j a).some
    (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j)
  let ι := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j
  rw [isIso_map_verdierDualDoubleDual_app_iff_of_iso _ _ H (ι.app K)]
  have h := isIso_map_verdierDualDoubleDual_app_mapDerivedCategory_upperStar_iff _
    (dualizingComplex Λ a) (dualizingComplex Λ (j ≫ a)) j e H K
  refine h.trans ?_
  exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight ι H) _).symm

/-- Blueprint `theorem-verdier-biduality--1`, the induction statement in dimension `d`:
for every algebraically closed field `k` (in universe `u`) on which the exponent of `Λ` is
invertible, every separated quasi-compact `X` locally of finite type over `k` with
`dim X ≤ d`, and every `K ∈ Dctf(X, Λ)`, the double-dual map `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an
isomorphism. -/
def BidualityInDim (d : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX], topologicalKrullDim X ≤ d →
    ∀ {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
    IsIso ((verdierDualDoubleDual Λ aX).app K)

/-- Blueprint `theorem-verdier-biduality--1`, proof, third and fourth paragraphs: **the
cone of `δ_K` vanishes at non-closed points.** Assume biduality in all dimensions `< d`, and let
`X` be separated of finite type over an algebraically closed `k` with `dim X ≤ d`,
`K ∈ Dctf(X, Λ)` and `K ⟶ 𝔻𝔻K ⟶ Δ ⟶ K[1]` a distinguished triangle on `δ_K` with `Δ` bounded
constructible. Then every cohomology sheaf of `Δ` has zero stalk at every non-closed point `x`.

Choose an affine open `ι : V ⟶ X` containing `x`; `x` is not closed in `V` (`X` is Jacobson).
A coordinate `p : V ⟶ 𝔸¹_k` sends `x` to the generic point, and factors through a closed
immersion into `𝔸ⁿ_{𝔸¹_k}`. The geometric generic fibre `g : V' ⟶ V` of `p` has dimension
`≤ d - 1` (and is nonempty, so `d ≥ 1`), so by induction `δ_{Lg^* Lι^* K}` relative to
`V' ⟶ Spec \overline{k(t)}` is an isomorphism. By `lemma-double-dual-geometric-generic-fibre--1`
(`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_generic`,
with braidedness `AlgebraicGeometry.Etale.leftDerivedUpperStarBraided`) so is `Lg^* δ_{Lι^* K}`,
hence by `corollary-verdier-exchange-formulas--5`
(`AlgebraicGeometry.Etale.isIso_map_verdierDualDoubleDual_app_leftDerivedUpperStar_iff`) so is
`Lg^* Lι^* δ_K`, and `Lg^* Lι^* Δ = 0`. The geometric point over `x` factors through `V'`, and
for the constructible `H^q Δ` vanishing at one geometric point over `x` suffices. -/
theorem isZero_sheafFiber_homology_of_not_mem_closedPoints (d : ℕ)
    (ih : ∀ d' < d, BidualityInDim Λ d')
    {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] (hd : topologicalKrullDim X ≤ d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    {Z : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (g : ((verdierDual _ aX).rightOp ⋙ verdierDual _ aX).obj K ⟶ Z) (h : Z ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((verdierDualDoubleDual Λ aX).app K) g h ∈ distTriang _)
    (hZ : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X Z)
    (q : ℤ) (x : X) (hx : x ∉ closedPoints X) :
    IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj Z)) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ (⊤ : X.Opens) from trivial)
  have : IsAffine U := hU
  let ι : (U : Scheme.{u}) ⟶ X := Scheme.Opens.ι U
  let x' : U := ⟨x, hxU⟩
  have hx' : ¬ IsClosed ({x'} : Set U) := by
    intro hc
    apply hx
    have hmem : x' ∈ closedPoints U := hc
    rw [← ι.isOpenEmbedding.preimage_closedPoints] at hmem
    exact hmem
  let aV := ι ≫ aX
  obtain ⟨p, hp, hpx⟩ := exists_hom_affineLine_over_apply_eq_genericPoint aV hx'
  obtain ⟨n, _, i, hi, hip⟩ := exists_isClosedImmersion_affineSpace_affineLine aV p hp
  obtain ⟨_, _, _, _, _⟩ := geometricGenericFiber_properties aV p hp
  let S := 𝔸(PUnit; Spec (.of k))
  let aS : S ⟶ Spec (.of k) := S ↘ Spec (.of k)
  let t := affineLineGeometricGenericPoint k
  let proj : 𝔸(n; S) ⟶ S := 𝔸(n; S) ↘ S
  let g' := pullback.fst p t
  let fT := pullback.snd p t
  let i' : pullback p t ⟶ pullback proj t :=
    pullback.lift (g' ≫ i) fT (by rw [Category.assoc, hip, pullback.condition])
  have hi'T : i' ≫ pullback.snd proj t = fT := pullback.lift_snd _ _ _
  have sqP := IsPullback.of_hasPullback proj t
  have sqX : IsPullback g' i' i (pullback.fst proj t) :=
    IsPullback.of_bot (by rw [hi'T, hip]; exact IsPullback.of_hasPullback p t)
      (pullback.lift_fst _ _ _).symm sqP
  have : HasInvertibleExponent Λ S := .of_hom aS
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure (S.residueField
    (genericPoint S))))) := .of_hom (t ≫ aS)
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback sqX hi
  have hM := constructibleFiniteTor_leftDerivedUpperStar _ ι hK
  have hM' := constructibleFiniteTor_leftDerivedUpperStar _ g' hM
  have hdimU : topologicalKrullDim U ≤ d :=
    ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hd
  obtain ⟨s', hs'⟩ := exists_comp_geometricGenericFiber_fst_eq_algClosurePoint p hpx
  have hd1 : 1 ≤ d := by
    have h1 := (topologicalKrullDim_geometricGenericFiber_add_one_le aV p hp).trans hdimU
    have : Nonempty (TopologicalSpace.IrreducibleCloseds (geometricGenericFiber p)) :=
      ⟨⟨closure {s'.base (IsLocalRing.closedPoint _)}, isIrreducible_singleton.closure,
        isClosed_closure⟩⟩
    have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (geometricGenericFiber p) :=
      Order.krullDim_nonneg
    by_contra hd0
    have : d = 0 := by omega
    subst this
    have h2 := (add_le_add_left h0 1).trans h1
    norm_num at h2
  have hδ' := ih (d - 1) (by omega) _ fT
    (topologicalKrullDim_geometricGenericFiber_le aV p hp hdimU) hM'
  have hgen := (isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_generic Λ aS
    (isInvertible_dualizingComplex (d := Nat.card PUnit.{u + 1}) Λ aS) t
    (fun _ ↦ Scheme.algClosurePoint_base _ _ _) proj (Nat.card n) sqP i sqX aV
    (by rw [← Category.assoc, hip, hp]) fT hi'T (leftDerivedUpperStarBraided _ g') hM).2 hδ'
  have h₁ := (isIso_map_verdierDualDoubleDual_app_leftDerivedUpperStar_iff Λ aX ι
    (L((g')^*[ModuleCat.{u + 1} Λ])) K).1 hgen
  let e : L((ι)^*[ModuleCat.{u + 1} Λ]) ⋙ L((g')^*[ModuleCat.{u + 1} Λ]) ≅
      D((ι)^*[ModuleCat.{u + 1} Λ]) ⋙ D((g')^*[ModuleCat.{u + 1} Λ]) :=
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ ι) _ ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ g')
  have h₂ := (NatIso.isIso_map_iff e ((verdierDualDoubleDual _ aX).app K)).1 h₁
  have hz : IsZero ((D((ι)^*[ModuleCat.{u + 1} Λ]) ⋙ D((g')^*[ModuleCat.{u + 1} Λ])).obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ _ ((D((ι)^*[ModuleCat.{u + 1} Λ]) ⋙
      D((g')^*[ModuleCat.{u + 1} Λ])).map_distinguished _ hT)).2 h₂
  let F := (_root_.DerivedCategory.homologyFunctor _ q).obj Z
  have hz1 : IsZero (((g')^*[ModuleCat.{u + 1} Λ]).obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj (D((ι)^*[ModuleCat.{u + 1} Λ]).obj Z))) :=
    ((_root_.DerivedCategory.homologyFunctor _ q).map_isZero hz).of_iso
      ((((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app _)
  have hz2 : IsZero (((g')^*[ModuleCat.{u + 1} Λ]).obj (((ι)^*[ModuleCat.{u + 1} Λ]).obj F)) :=
    hz1.of_iso (((g')^*[ModuleCat.{u + 1} Λ]).mapIso
      ((((ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app Z))
  have hs := isZero_sheafFiber_algClosurePoint_of_isZero_upperStar _ p hpx _ hz2
  have hs2 : IsZero ((pointSmallEtale ((U : Scheme.{u}).algClosurePoint x' ≫ ι)).sheafFiber.obj
      F) :=
    hs.of_iso ((upperStarCompSheafFiberIso _ ι _).app F).symm
  have : IsConstructibleSheaf F := hZ.2 q
  have hmem := mem_stalkZeroLocus_of_isZero_sheafFiber F _ hs2
  exact hmem _ (X.algClosurePoint x) (by simp [ι, x'])

/-- Blueprint `theorem-verdier-biduality--1`, proof, the proper case: assume biduality in
all dimensions `< d`, and let `a : X ⟶ Spec k` be proper with `k` algebraically closed and
`dim X ≤ d`. Then `δ_K` is an isomorphism for every `K ∈ Dctf(X, Λ)`.

The cone `Δ` of `δ_K` lies in `Dctf` (`lemma-verdier-duality-preserves-constructibility--1`), and
its cohomology vanishes at non-closed points
(`AlgebraicGeometry.Etale.isZero_sheafFiber_homology_of_not_mem_closedPoints`). `Ra_* K` lies in
`Dctf(Spec k)` (`proposition-six-operations-dctf--2`), so `δ_{Ra_* K}` is an isomorphism
(`lemma-perfect-complexes-geometric-point--8`), hence so is `Ra_* δ_K`
(`lemma-internal-adjunction-two-exchange-formulas--4`). The closed-point step
`AlgebraicGeometry.Etale.isZero_obj₃_of_isIso_rightDerivedLowerStar_map` gives `Δ = 0`. -/
theorem isIso_verdierDualDoubleDual_app_of_isProper (d : ℕ)
    (ih : ∀ d' < d, BidualityInDim Λ d')
    {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsProper aX] (hd : topologicalKrullDim X ≤ d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ aX).app K) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  obtain ⟨Z, g, h, hT⟩ :=
    distinguished_cocone_triangle ((verdierDualDoubleDual Λ aX).app K)
  have hDD : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((verdierDual _ aX).rightOp ⋙ verdierDual _ aX).obj K) := by
    obtain ⟨hbc, a, b, hta⟩ := hK
    obtain ⟨h₁, h₂⟩ :=
      constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField Λ aX d hd a b hbc hta
    exact (constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField Λ aX d hd _ _
      h₁.1 h₂).1
  have hZ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X Z :=
    (DerivedCategory.constructibleFiniteTor _ X).ext_of_isTriangulatedClosed₃ _ hT hK hDD
  have hRK := constructibleFiniteTor_rightDerivedLowerStar Λ aX (𝟙 _) aX (Category.comp_id _) hK
  have ha := (isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff_of_finite Λ
    (𝟙 (Spec (.of k))) aX (leftDerivedUpperStarBraided _ aX) K).2
    (isIso_verdierDualDoubleDual_app_id_of_subsingleton Λ hRK)
  rw [isIso_map_verdierDualDoubleDual_app_congr _ (Category.comp_id aX)] at ha
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  exact isZero_obj₃_of_isIso_rightDerivedLowerStar_map Λ aX _ hT hZ.1
    (fun q x hx ↦ isZero_sheafFiber_homology_of_not_mem_closedPoints Λ d ih aX hd hK g h hT hZ.1
      q x hx) ha

/-- Blueprint `theorem-verdier-biduality--1`, proof, second paragraph: **reduction to the
proper case.** If biduality holds on every proper `k`-scheme of dimension `≤ d`, it holds on
every separated quasi-compact `X` locally of finite type over `k` with `dim X ≤ d`. Biduality
is local (`corollary-verdier-exchange-formulas--5`), so it suffices to treat the affine opens `U` of
`X`. Such a `U` is a dense open of a proper `Ū` of the same dimension
(`theorem-nagata-s-compactification-theorem--1`, `AlgebraicGeometry.exists_dense_compactification`),
`j_! (K|_U) ∈ Dctf(Ū)`, and `δ_{j_! (K|_U)}` restricts to `δ_{K|_U}`. -/
theorem isIso_verdierDualDoubleDual_app_of_forall_isProper (d : ℕ)
    {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    (hprop : ∀ {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsProper aY],
      topologicalKrullDim Y ≤ d →
      ∀ {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N →
      IsIso ((verdierDualDoubleDual Λ aY).app N))
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] (hd : topologicalKrullDim X ≤ d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ aX).app K) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  refine isIso_of_forall_isIso_leftDerivedUpperStar_map Λ
    (fun U : X.affineOpens ↦ Scheme.Opens.ι (U : X.Opens)) ?_ _ fun U ↦ ?_
  · intro x
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨U, hU⟩, ⟨x, hxU⟩, rfl⟩
  have : IsAffine (U : X.Opens) := U.2
  let ι := Scheme.Opens.ι (U : X.Opens)
  have : QuasiCompact ι := inferInstance
  have : HasCompactification ι := inferInstance
  change IsIso ((L((ι)^*[ModuleCat.{u + 1} Λ])).map _)
  rw [← isIso_verdierDualDoubleDual_app_leftDerivedUpperStar_iff Λ aX ι]
  obtain ⟨Y, aY, j, hY, hj, hcomm, -, hdim⟩ := exists_dense_compactification (ι ≫ aX)
  have : QuasiCompact (j ≫ aY) := hcomm ▸ inferInstance
  have : QuasiCompact j := QuasiCompact.of_comp j aY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : HasCompactification j := (Compactification.ofIsOpenImmersion j).hasCompactification
  let M := (L((ι)^*[ModuleCat.{u + 1} Λ])).obj K
  have hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) _ M :=
    constructibleFiniteTor_leftDerivedUpperStar _ ι hK
  obtain ⟨a, b, hab⟩ :=
    (DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor M).2 hM
  have hN := (DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor _).1
    ⟨a, b, constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek Λ j a b hab⟩
  have hdY : topologicalKrullDim Y ≤ d :=
    hdim ▸ ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hd
  have hδ := hprop aY hdY hN
  have h₁ := (isIso_verdierDualDoubleDual_app_leftDerivedUpperStar_iff Λ aY j
    (D((j)_!open[ModuleCat.{u + 1} Λ]).obj M)).2 (Functor.map_isIso _ _)
  let q := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
  let eN : (L((j)^*[ModuleCat.{u + 1} Λ])).obj (D((j)_!open[ModuleCat.{u + 1} Λ]).obj M) ≅ M :=
    (leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫ (asIso (q.unit.app M)).symm
  have h₂ := (isIso_verdierDualDoubleDual_app_iff_of_iso _ (j ≫ aY) eN).1 h₁
  exact (isIso_map_verdierDualDoubleDual_app_congr _ hcomm (𝟭 _) M).1 h₂

/-- Blueprint `theorem-verdier-biduality--1`: the dimension induction, simultaneously for
all algebraically closed fields. -/
theorem bidualityInDim (d : ℕ) : BidualityInDim Λ d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro k _ _ _ X aX _ _ _ hd K hK
  exact isIso_verdierDualDoubleDual_app_of_forall_isProper Λ d
    (fun aY _ hY _ hN ↦ isIso_verdierDualDoubleDual_app_of_isProper Λ d ih aY hY hN) aX hd hK

/-- Blueprint `theorem-verdier-biduality--1`: **finite-stage étale Verdier biduality.**
Let `Λ` be a finite ring, `k` an algebraically closed field on which the exponent of `Λ` is
invertible, and `X` separated, quasi-compact and locally of finite type over `k`. For every
`K ∈ Dctf(X, Λ)` the double-dual map `δ_K : K ⟶ 𝔻_X 𝔻_X K` (relative to `a_X : X ⟶ Spec k`) is
an isomorphism. -/
theorem isIso_verdierDualDoubleDual_app_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ aX).app K) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  exact bidualityInDim Λ d k aX hd hK
end Finite

end Etale

end AlgebraicGeometry
