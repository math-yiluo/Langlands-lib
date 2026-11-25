/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!
# The double-dual morphism under restriction and proper push-forward

This file continues `WeilConjectures.SixFunctors.Etale.Derived.DoubleDual` for the blueprint
nodes `corollary-verdier-exchange-formulas--5` and
`lemma-internal-adjunction-two-exchange-formulas--4`. There the double-dual morphism
`δ_K : K ⟶ 𝔻 𝔻 K` is the unit of the self-adjunction of `𝔻 = RHom(-, ω)`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_leftDerivedUpperStar_iff`
  (`corollary-verdier-exchange-formulas--5`): for a quasi-compact open immersion `j : W ⟶ Y` and
  finite coefficients, `δ_{Lj^* K}` (relative to `ω_W = R(j ≫ a)^! Λ`) is an isomorphism if and only
  if `Lj^* δ_K` is.
- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_iff_of_openCover`
  (`corollary-verdier-exchange-formulas--5`): biduality is local, so `δ_K` is an isomorphism if and
  only if `δ_{Lj_i^* K}` is, for a jointly surjective family of open immersions `j_i`.
- `AlgebraicGeometry.Etale.map_verdierDualDoubleDual_app_comp_mateEquiv`
  (`lemma-internal-adjunction-two-exchange-formulas--4`, formal core):
  `Rf_* δ_K ≫ m_{𝔻 K} = δ_{Rf_* K} ≫ 𝔻 α_K` for every square `α : 𝔻_Y Rf_* ⟶ Rf_* 𝔻_X` and its mate
  `m`.
- `AlgebraicGeometry.Etale.isIso_map_verdierDualDoubleDual_app_iff_of_isIso_app_mateEquiv`:
  `Rf_* δ_K` is an isomorphism if and only if `δ_{Rf_* K}` is, provided a square
  `α : 𝔻_Y Rf_* ⟶ Rf_* 𝔻_X` is invertible at `K` and its mate at `𝔻_X K`; for proper `f` and
  finite coefficients, `α` is the Verdier exchange
  `AlgebraicGeometry.Etale.verdierDualRightDerivedLowerStarSquare`.

## Implementation notes

The restriction statement avoids any compatibility of `Lj^*` with the braiding. The adjunction
`j_! ⊣ j^*` composed with the self-adjunction of `𝔻_Y`, and the self-adjunction of `𝔻_W` composed
with `j^* ⊣ Rj_*`, have left adjoints identified by the Verdier exchange `𝔻_Y j_! ≅ Rj_* 𝔻_W`
(`AlgebraicGeometry.Etale.verdierDualLowerShriekIso`). Hence their units, which are `j^* δ_{j_! M}`
and `δ_M` up to isomorphisms, are invertible at the same objects. A cone argument replaces
`j_! j^* K` by `K`.

## Proper push-forward

The conditional push-forward statement below, through the mate of the Verdier exchange, is
superseded by the unconditional one in
`WeilConjectures.SixFunctors.Etale.Derived.DoubleDualProper`, which uses the canonical
comparison `Rf_* 𝔻_X M ⟶ 𝔻_Y Rf_* M` instead.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section OpenImmersion

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {Y W : Scheme.{u}} (ωY : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
  (ωW : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)) (j : W ⟶ Y) [IsOpenImmersion j]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- Blueprint `corollary-verdier-exchange-formulas--5` (auxiliary): for an open immersion `j` the
counit `D(j^*) Rj_* ⟶ 𝟭` is an isomorphism, `D(j_!) ⊣ D(j^*) ⊣ Rj_*` being an adjoint triple whose
first unit is invertible. -/
instance isIso_mapDerivedUpperStarLowerStarAdjunction_counit :
    IsIso (mapDerivedUpperStarLowerStarAdjunction A j).counit :=
  (Adjunction.Triple.mk (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
    (mapDerivedUpperStarLowerStarAdjunction A j)).isIso_unit_iff_isIso_counit.1 inferInstance

/-- Blueprint `corollary-verdier-exchange-formulas--5`: the extension-by-zero step. Let `j : W ⟶ Y`
be an open immersion and `e : 𝔻_Y ∘ j_! ≅ Rj_* ∘ 𝔻_W` an isomorphism (the Verdier exchange,
`AlgebraicGeometry.Etale.verdierDualLowerShriekIso`). Then `δ_M` is an isomorphism on `W` if and
only if `j^* δ_{j_! M}` is one on `Y`.

The double-dual morphism is the unit of the self-adjunction of `𝔻`
(`CategoryTheory.MonoidalClosed.ihomFlipSelfAdjunction`). The composite adjunctions
`𝔻_Y ∘ j_! ⊣ j^* ∘ 𝔻_Y` and `Rj_* ∘ 𝔻_W ⊣ 𝔻_W ∘ j^*` have isomorphic left adjoints (by `e`), so
their units are invertible at the same objects
(`CategoryTheory.Adjunction.isIso_unit_app_iff_of_iso`). These units are `j^* δ_{j_! M}` and
`δ_M`, up to the invertible unit of `j_! ⊣ j^*` and counit of `j^* ⊣ Rj_*`. -/
theorem isIso_verdierDualDoubleDual_app_iff_lowerShriek
    (e : D((j)_!open[A]) ⋙ ((RHom(Y)[A]).flip.obj ωY).rightOp ≅
      ((RHom(W)[A]).flip.obj ωW).rightOp ⋙ (R((j)_*[A])).op)
    (M : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    IsIso ((derivedHomToIhomIhomNatTrans A W ωW).app M) ↔
      IsIso (D((j)^*[A]).map
        ((derivedHomToIhomIhomNatTrans A Y ωY).app (D((j)_!open[A]).obj M))) := by
  let adjY : ((RHom(Y)[A]).flip.obj ωY).rightOp ⊣ (RHom(Y)[A]).flip.obj ωY :=
    MonoidalClosed.ihomFlipSelfAdjunction _
  let adjW : ((RHom(W)[A]).flip.obj ωW).rightOp ⊣ (RHom(W)[A]).flip.obj ωW :=
    MonoidalClosed.ihomFlipSelfAdjunction _
  let p := mapDerivedUpperStarLowerStarAdjunction A j
  let q := derivedOpenImmersionLowerShriekUpperStarAdjunction A j
  have h := Adjunction.isIso_unit_app_iff_of_iso (q.comp adjY) (adjW.comp p.op) e M
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  have : IsIso (p.op.unit.app (((RHom(W)[A]).flip.obj ωW).rightOp.obj M)) := by
    dsimp
    infer_instance
  rw [isIso_comp_left_iff, isIso_comp_right_iff, MonoidalClosed.ihomFlipSelfAdjunction_unit_app,
    MonoidalClosed.ihomFlipSelfAdjunction_unit_app] at h
  exact h.symm

set_option maxRecDepth 8000 in
/-- Blueprint `corollary-verdier-exchange-formulas--5`: the cone step. If `f : K' ⟶ K` becomes
invertible on the open `W`, then so does `𝔻_Y 𝔻_Y f`, because restriction to `W` commutes with
`RHom` (`AlgebraicGeometry.Etale.nonempty_iso_mapDerivedCategory_upperStar_derivedHom`) and kills
the cone of `f`. By naturality, `j^* δ_K` is then invertible if and only if `j^* δ_{K'}` is. -/
theorem isIso_upperStar_map_verdierDualDoubleDual_app_iff_of_isIso
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [Etale.UpperStarPreservesFlat A]
    [Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {K' K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (f : K' ⟶ K)
    (hf : IsIso (D((j)^*[A]).map f)) :
    IsIso (D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app K)) ↔
      IsIso (D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app K')) := by
  have hz : ∀ Z : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A),
      IsZero (D((j)^*[A]).obj Z) →
        IsZero (D((j)^*[A]).obj (((RHom(Y)[A]).flip.obj ωY).obj (op Z))) := by
    intro Z hZ
    obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_upperStar_derivedHom (FC := FC) A j Z
      (ωY)
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
    have key := (Triangle.isZero₃_iff_isIso₁ _ hw').1 h4
    exact key
  have nat := congrArg D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).naturality f)
  simp only [Functor.id_map, Functor.map_comp] at nat
  constructor
  · intro h
    have : IsIso (D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app K') ≫
        D((j)^*[A]).map
          ((((RHom(Y)[A]).flip.obj ωY).rightOp ⋙ (RHom(Y)[A]).flip.obj ωY).map f)) := by
      rw [← nat]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (D((j)^*[A]).map ((((RHom(Y)[A]).flip.obj ωY).rightOp ⋙ (RHom(Y)[A]).flip.obj ωY).map f))
  · intro h
    have : IsIso (D((j)^*[A]).map f ≫
        D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app K)) := by
      rw [nat]
      infer_instance
    exact IsIso.of_isIso_comp_left (D((j)^*[A]).map f) _

/-- Blueprint `corollary-verdier-exchange-formulas--5`: the double-dual morphism restricts. For an
open immersion `j : W ⟶ Y` and a Verdier exchange `e : 𝔻_Y ∘ j_! ≅ Rj_* ∘ 𝔻_W`, the morphism
`δ_{j^* K}` on `W` is an isomorphism if and only if `j^* δ_K` is. Apply the extension-by-zero step
to `M = j^* K` and the cone step to the counit `j_! j^* K ⟶ K`. -/
theorem isIso_verdierDualDoubleDual_app_mapDerivedCategory_upperStar_iff
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [Etale.UpperStarPreservesFlat A]
    [Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (e : D((j)_!open[A]) ⋙ ((RHom(Y)[A]).flip.obj ωY).rightOp ≅
      ((RHom(W)[A]).flip.obj ωW).rightOp ⋙ (R((j)_*[A])).op)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso ((derivedHomToIhomIhomNatTrans A W ωW).app (D((j)^*[A]).obj K)) ↔
      IsIso (D((j)^*[A]).map ((derivedHomToIhomIhomNatTrans A Y ωY).app K)) := by
  rw [isIso_verdierDualDoubleDual_app_iff_lowerShriek A ωY ωW j e]
  let q := derivedOpenImmersionLowerShriekUpperStarAdjunction A j
  have : IsIso (D((j)^*[A]).map (q.counit.app K)) := by
    have : IsIso (q.unit.app (D((j)^*[A]).obj K) ≫ D((j)^*[A]).map (q.counit.app K)) := by
      rw [q.right_triangle_components K]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (q.unit.app _) _
  exact (isIso_upperStar_map_verdierDualDoubleDual_app_iff_of_isIso (FC := FC) A ωY j
    (q.counit.app K) this).symm
end OpenImmersion

section Exchange

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {Y W : Scheme.{u}} (j : W ⟶ Y) [HasCompactification j]
  (ωY : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
  (ωW : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A))

/-- Blueprint `corollary-verdier-exchange-formulas--5` and
`lemma-internal-adjunction-two-exchange-formulas--4`: the Verdier exchange `𝔻_Y ∘ G ≅ Rj_* ∘ 𝔻_W` as
an isomorphism of functors `D(W) ⥤ D(Y)ᵒᵖ`, for any `G ≅ Rj_!`. It is built from a tensor–Hom
exchange `χ : Rj_* RHom(M, Rj^! N) ≅ RHom(Rj_! M, N)`
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`, for any functor `Rj^!`) and
`γ : Rj^! ω_Y ≅ ω_W`, for arbitrary objects `ω_Y`, `ω_W` (the dualizing complexes). -/
noncomputable def verdierDualLowerShriekIso
    {G : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (A)) ⥤
      _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (A))}
    {Rj : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)}
    (χ : RHom(W)[A] ⋙ (Functor.whiskeringLeft _ _ _).obj Rj ⋙
        (Functor.whiskeringRight _ _ _).obj R((j)_*[A]) ≅ (R(j)_![A]).op ⋙ RHom(Y)[A])
    (γ : Rj.obj (ωY) ≅ ωW)
    (ι : R(j)_![A] ≅ G) :
    G ⋙ ((RHom(Y)[A]).flip.obj ωY).rightOp ≅
      ((RHom(W)[A]).flip.obj ωW).rightOp ⋙ (R((j)_*[A])).op := by
  let i : ∀ M : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (A)),
      (R((j)_*[A])).obj (((RHom(W)[A]).flip.obj ωW).obj (op M)) ≅
        ((RHom(Y)[A]).flip.obj ωY).obj (op (G.obj M)) := fun M ↦
    (R((j)_*[A])).mapIso
        ((RHom(W)[A].obj (op M)).mapIso γ.symm) ≪≫
      (χ.app (op M)).app (ωY) ≪≫
        (RHom(Y)[A].mapIso (ι.app M).symm.op).app (ωY)
  have hnat : ∀ {M M' : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (A))}
      (g : M ⟶ M'), (i M').hom ≫ ((RHom(Y)[A]).flip.obj ωY).map (G.map g).op =
        (R((j)_*[A])).map (((RHom(W)[A]).flip.obj ωW).map g.op) ≫ (i M).hom := by
    intro M M' g
    have h₁ : ((RHom(W)[A]).flip.obj ωW).map g.op ≫
        (RHom(W)[A].obj (op M)).map γ.inv =
        (RHom(W)[A].obj (op M')).map γ.inv ≫
          (RHom(W)[A].map g.op).app _ :=
      (((RHom(W)[A]).map g.op).naturality γ.inv).symm
    have h₂ := congr_app (χ.hom.naturality g.op) (ωY)
    have h₃ : (RHom(Y)[A].map ((R(j)_![A]).map g).op).app
          (ωY) ≫
        (RHom(Y)[A].map (ι.inv.app M).op).app (ωY) =
        (RHom(Y)[A].map (ι.inv.app M').op).app (ωY) ≫
          ((RHom(Y)[A]).flip.obj ωY).map (G.map g).op := by
      rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, ← ι.inv.naturality, op_comp,
        Functor.map_comp, NatTrans.comp_app]
      rfl
    dsimp only [i, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.op_hom]
    simp only [Category.assoc, Iso.op_hom, Iso.symm_hom, Iso.app_inv]
    rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc]
    simp only [NatTrans.comp_app] at h₂
    erw [reassoc_of% h₂]
    simp only [Functor.op_map, Quiver.Hom.unop_op]
    erw [h₃]
  refine NatIso.ofComponents (fun M ↦ (i M).op) fun {M M'} g ↦ ?_
  apply Quiver.Hom.unop_inj
  exact hnat g

end Exchange

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {Y W S : Scheme.{u}} (a : Y ⟶ S)
  (j : W ⟶ Y) [HasCompactification j] [HasCompactification a] [HasCompactification (j ≫ a)]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- Blueprint `corollary-verdier-exchange-formulas--5`: the double-dual morphism restricts. For a
quasi-compact open immersion `j : W ⟶ Y` and finite coefficients `Λ`, `δ_{Lj^* K}` (relative to
`ω_W = R(j ≫ a)^! Λ`) is an isomorphism if and only if `Lj^* δ_K` is. -/
theorem isIso_verdierDualDoubleDual_app_leftDerivedUpperStar_iff [IsOpenImmersion j]
    [QuasiCompact j]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((verdierDualDoubleDual Λ (j ≫ a)).app ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) ↔
      IsIso ((L((j)^*[ModuleCat.{u + 1} Λ])).map ((verdierDualDoubleDual Λ a).app K)) := by
  let e := verdierDualLowerShriekIso _ j (dualizingComplex Λ a) (dualizingComplex Λ (j ≫ a))
    (derivedHomRightDerivedLowerShriekIsoOfFinite Λ j)
    (nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ j a).some
    (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j)
  rw [isIso_verdierDualDoubleDual_app_iff_of_iso _ _
      ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app K),
    NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ j)]
  exact isIso_verdierDualDoubleDual_app_mapDerivedCategory_upperStar_iff _ (dualizingComplex Λ a)
    (dualizingComplex Λ (j ≫ a)) j e K

end Finite

/-- Blueprint `corollary-verdier-exchange-formulas--5` (auxiliary): isomorphisms of `D(X_ét, Λ)` are
detected after pullback along a jointly surjective family `u_i : U_i ⟶ X`. -/
theorem isIso_of_forall_isIso_leftDerivedUpperStar_map (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} {ι : Type u} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X)
    (hu : ∀ x : X, ∃ (i : ι) (y : U i), (u i).base y = x)
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) (h : ∀ i, IsIso ((L((u i)^*[ModuleCat.{u + 1} Λ])).map φ)) : IsIso φ := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) u hu _
    fun i ↦ ?_
  have h' : IsIso (D((u i)^*[ModuleCat.{u + 1} Λ]).map φ) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ (u i)) φ).1 (h i)
  exact (NatIso.isIso_map_iff
    (((u i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      (D((u i)^*[ModuleCat.{u + 1} Λ]).map φ))

/-- Blueprint `corollary-verdier-exchange-formulas--5`: biduality is local. For a jointly surjective
family of quasi-compact open immersions `j_i : W_i ⟶ Y` and finite coefficients, `δ_K` is an
isomorphism if and only if every `δ_{Lj_i^* K}` (relative to `ω_{W_i} = R(j_i ≫ a)^! Λ`) is one. -/
theorem isIso_verdierDualDoubleDual_app_iff_of_openCover (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {Y S : Scheme.{u}} (a : Y ⟶ S) [HasCompactification a] {ι : Type u}
    {W : ι → Scheme.{u}} (j : ∀ i, W i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    [∀ i, HasCompactification (j i)] [∀ i, QuasiCompact (j i)]
    [∀ i, HasCompactification (j i ≫ a)] [∀ i, QuasiCompact (j i ≫ a)]
    (hj : ∀ y : Y, ∃ (i : ι) (x : W i), (j i).base x = y)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((verdierDualDoubleDual Λ a).app K) ↔
      ∀ i, IsIso ((verdierDualDoubleDual Λ (j i ≫ a)).app
        ((L((j i)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  simp only [isIso_verdierDualDoubleDual_app_leftDerivedUpperStar_iff]
  exact ⟨fun _ _ ↦ inferInstance, isIso_of_forall_isIso_leftDerivedUpperStar_map Λ j hj _⟩

section Proper

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X Y : Scheme.{u}} (ωX : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
  (ωY : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) (f : X ⟶ Y)

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4` (formal core): for any square
`α : 𝔻_Y ∘ Rf_* ⟶ Rf_* ∘ 𝔻_X` (components `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_* K`), its mate `m` under the
self-adjunctions of `𝔻_X` and `𝔻_Y` satisfies `Rf_* δ_K ≫ m_{𝔻_X K} = δ_{Rf_* K} ≫ 𝔻_Y α_K`. -/
theorem map_verdierDualDoubleDual_app_comp_mateEquiv
    (α : TwoSquare R((f)_*[A]) ((RHom(X)[A]).flip.obj ωX).rightOp ((RHom(Y)[A]).flip.obj ωY).rightOp
      (R((f)_*[A])).op)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (R((f)_*[A])).map ((derivedHomToIhomIhomNatTrans A X ωX).app K) ≫
        (mateEquiv (MonoidalClosed.ihomFlipSelfAdjunction (ωX))
          (MonoidalClosed.ihomFlipSelfAdjunction (ωY)) α).app
            (op (((RHom(X)[A]).flip.obj ωX).obj (op K))) =
      (derivedHomToIhomIhomNatTrans A Y ωY).app ((R((f)_*[A])).obj K) ≫
        ((RHom(Y)[A]).flip.obj ωY).map (α.app K) := by
  have := unit_mateEquiv
    (MonoidalClosed.ihomFlipSelfAdjunction (ωX))
    (MonoidalClosed.ihomFlipSelfAdjunction (ωY)) α K
  rw [MonoidalClosed.ihomFlipSelfAdjunction_unit_app,
    MonoidalClosed.ihomFlipSelfAdjunction_unit_app] at this
  exact this

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4`, conditional form over a general
coefficient category: if the square `α : 𝔻_Y ∘ Rf_* ⟶ Rf_* ∘ 𝔻_X` is invertible at `K` and its mate
is invertible at `𝔻_X K`, then `Rf_* δ_K` is an isomorphism if and only if `δ_{Rf_* K}` is.
It is stated for arbitrary objects `ω_X`, `ω_Y` in place of the dualizing complexes; for proper
`f` and finite coefficients the square is
`AlgebraicGeometry.Etale.verdierDualRightDerivedLowerStarSquare`. -/
theorem isIso_map_verdierDualDoubleDual_app_iff_of_isIso_app_mateEquiv
    (α : TwoSquare R((f)_*[A]) ((RHom(X)[A]).flip.obj ωX).rightOp ((RHom(Y)[A]).flip.obj ωY).rightOp
      (R((f)_*[A])).op)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) [IsIso (α.app K)]
    (hm : IsIso ((mateEquiv (MonoidalClosed.ihomFlipSelfAdjunction (ωX))
      (MonoidalClosed.ihomFlipSelfAdjunction (ωY)) α).app
        (op (((RHom(X)[A]).flip.obj ωX).obj (op K))))) :
    IsIso ((R((f)_*[A])).map ((derivedHomToIhomIhomNatTrans A X ωX).app K)) ↔
      IsIso ((derivedHomToIhomIhomNatTrans A Y ωY).app ((R((f)_*[A])).obj K)) := by
  rw [← isIso_comp_right_iff ((derivedHomToIhomIhomNatTrans A Y ωY).app _)
    (((RHom(Y)[A]).flip.obj ωY).map (α.app K)),
    ← map_verdierDualDoubleDual_app_comp_mateEquiv A ωX ωY f α K, isIso_comp_right_iff]

end Proper

section ProperFinite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S : Scheme.{u}} (a : Y ⟶ S)
  (f : X ⟶ Y) [IsProper f] [HasCompactification f] [HasCompactification a]
  [HasCompactification (f ≫ a)]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4`: the Verdier exchange
`𝔻_Y Rf_* ≅ Rf_* 𝔻_X` for proper `f` (`Rf_! ≅ Rf_*`) and finite coefficients, as a square. -/
noncomputable def verdierDualRightDerivedLowerStarSquare :
    TwoSquare R((f)_*[ModuleCat.{u + 1} Λ]) (verdierDual Λ (f ≫ a)).rightOp
      (verdierDual Λ a).rightOp (R((f)_*[ModuleCat.{u + 1} Λ])).op :=
  (verdierDualLowerShriekIso _ f (dualizingComplex Λ a) (dualizingComplex Λ (f ≫ a))
    (derivedHomRightDerivedLowerShriekIsoOfFinite Λ f)
    (nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ f a).some
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f)).hom

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4`: the components of the Verdier
exchange square are isomorphisms. -/
instance isIso_verdierDualRightDerivedLowerStarSquare_app
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((verdierDualRightDerivedLowerStarSquare Λ a f).app K) := by
  dsimp only [verdierDualRightDerivedLowerStarSquare]
  infer_instance

end ProperFinite

end Etale

end AlgebraicGeometry
