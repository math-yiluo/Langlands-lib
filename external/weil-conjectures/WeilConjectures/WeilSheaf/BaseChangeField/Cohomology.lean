/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeField
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.WeilSheaf.BaseChangeField.Comparison
public import WeilConjectures.WeilSheaf.BaseChangeField.Derived
public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import WeilConjectures.WeilSheaf.BaseChangeField.GlobalSections
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.StalkFrobeniusPow

/-!
# Cohomology under a finite extension of the base field

Let `k₀'/k₀` be an extension of finite fields of degree `r` and `X` a `k₀`-scheme of finite
type. The geometric fibers of `X` and of its base change `X' = X ×_{k₀} k₀'` are identified,
`θ : X̄ ≅ X̄'`, with the geometric Galois Frobenius of `X̄'` relative to `k₀'` corresponding to
the `r`-th power of that of `X̄` relative to `k₀`, `Frob_{q^r} = Frob_q^r`
(`WeilConjectures.WeilSheaf.BaseChangeField.Geometric`). Transporting Weil sheaves along `θ`
(`AlgebraicGeometry.ProEtaleWeilSheaf.transport`) commutes with the derived direct image to the
base and carries `ℚ̄_ℓ` to `ℚ̄_ℓ` (`WeilConjectures.WeilSheaf.BaseChangeField.Comparison`), so
`Hⁱ(X' ⊗ k̄, ℚ̄_ℓ)` is `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` with the geometric Frobenius of `k₀'` acting as the
`r`-th power `Fʳ` of that of `k₀`
(`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_adicConstant_baseChangeField`).

## Main statements

- `AlgebraicGeometry.ProEtaleWeilSheaf.transportRightDerivedLowerStarIso`: the derived direct
  image commutes with transport.
- `AlgebraicGeometry.WeilSheaf.exists_linearEquiv_globalSections_of_iso_transport`: a Weil sheaf
  isomorphic to the transport of `H` has the global sections of `H`, with Frobenius `Fʳ`.
- `AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_adicConstant_baseChangeField`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

noncomputable section

namespace AlgebraicGeometry

open ProEtale

namespace ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  {k₀' : Type u} [Field k₀'] [Finite k₀'] {X' Y' : Scheme.{u}}
  [X'.Over (Spec (CommRingCat.of k₀'))] [Y'.Over (Spec (CommRingCat.of k₀'))]
  (θ : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (X' ↘ Spec (CommRingCat.of k₀')).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (X' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θ.hom)
  (θY : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber)
  (hθY : θY.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θY.hom)
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
  (φ' : X' ⟶ Y') [φ'.IsOver (Spec (CommRingCat.of k₀'))]
  (hsq : θ.hom ≫ Scheme.Hom.geometricFiberMap φ' (comp_over φ' _) =
    Scheme.Hom.geometricFiberMap φ (comp_over φ _) ≫ θY.hom)

/-- On underlying sheaves, transport along `θ` is the pushforward `θ_*`. -/
def transportCompForgetIso :
    transport (l := l) θ r hθ ⋙ IsoAlgebra.forget _ ≅ IsoAlgebra.forget _ ⋙ (θ.hom)_*ᵃ[l] :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
    (Category.comp_id _).trans (Category.id_comp _).symm

include hsq in
/-- The derived direct images commute with transport along the identifications `θ`, `θ_Y` of
geometric fibers: `Rφ'_* ∘ θ_* ≅ θ_Y_* ∘ Rφ_*` on derived categories of pro-étale Weil sheaves.
It is the composite of `R(θ_* ⋙ φ'_*) ≅ θ_* ⋙ Rφ'_*`, the transport being exact with underlying
functor the equivalence `θ_*`, the commutation `θ_* ⋙ φ'_* ≅ φ_* ⋙ θ_Y_*` and
`R(φ_* ⋙ θ_Y_*) ≅ Rφ_* ⋙ θ_Y_*`, the transport being exact. -/
def transportRightDerivedLowerStarIso :
    (transport θ r hθ).mapDerivedCategory ⋙ (lowerStar k₀' l φ').rightDerivedFunctor ≅
      (lowerStar k₀ l φ).rightDerivedFunctor ⋙ (transport θY r hθY).mapDerivedCategory :=
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X' ↘ Spec (CommRingCat.of k₀')).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X' ↘ Spec (CommRingCat.of k₀')).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber) ℤ
  (IsoAlgebra.rightDerivedFunctorCompMapOfNatIsoIsoOfIso (transport θ r hθ)
    (transportCompForgetIso θ r hθ)
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ' (comp_over φ' _))).symm ≪≫
  Functor.rightDerivedFunctorNatIso (transportLowerStarIso θ r hθ θY hθY φ φ' hsq) ≪≫
  Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _

end ProEtaleWeilSheaf

namespace WeilSheaf

open ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  {k₀' : Type u} [Field k₀'] [Finite k₀'] [Fact (ringChar k₀' ≠ l)] {Y' : Scheme.{u}}
  [Y'.Over (Spec (CommRingCat.of k₀'))] [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀'))]
  [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀'))]
  (θ : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θ.hom)

set_option maxRecDepth 10000 in
-- the Frobenius of the global sections unfolds through deep composites of isomorphisms
/-- A Weil sheaf `H'` on a `k₀'`-scheme `Y'` isomorphic to the transport of a Weil sheaf `H` on a
`k₀`-scheme `Y` along `θ : Ȳ ≅ Ȳ'`, `θ ≫ Fr' = Frʳ ≫ θ`, has the global sections of `H`, the
Frobenius of `H'` corresponding to the `r`-th power of that of `H`. -/
theorem exists_linearEquiv_globalSections_of_iso_transport (H : WeilSheaf k₀ l Y)
    (H' : WeilSheaf k₀' l Y') (α : H'.obj ≅ (transport θ r hθ).obj H.obj) :
    ∃ e : H'.globalSections.carrier ≃ₗ[PadicAlgCl l] H.globalSections.carrier,
      ∀ x, e (H'.globalSections.frobenius x) = (H.globalSections.frobeniusEnd ^ r) (e x) := by
  let E := (Sheaf.Γ _ _).mapIso ((AdicSheaf.forget _).mapIso ((IsoAlgebra.forget _).mapIso α)) ≪≫
    (globalSectionsLowerStarIso (WeilCoefficients.{u} l) θ.hom).app H.obj.carrier.X
  have key : H'.obj.globalSectionsFrobenius ≫ E.hom =
      E.hom ≫ H.obj.globalSectionsFrobeniusPow r :=
    globalSectionsFrobenius_comp_of_iso_transport θ r hθ H.obj α
  refine ⟨WeilCoefficients.linearEquivOfIso E, fun x ↦ ?_⟩
  calc WeilCoefficients.linearEquivOfIso E (H'.globalSections.frobenius x)
      = ((WeilCoefficients.toModuleCat l).map (H'.obj.globalSectionsFrobenius ≫ E.hom)).hom x :=
        (toModuleCat_map_comp_apply _ _ x).symm
    _ = ((WeilCoefficients.toModuleCat l).map (E.hom ≫ H.obj.globalSectionsFrobeniusPow r)).hom
        x := congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom x) key
    _ = ((WeilCoefficients.toModuleCat l).map (H.obj.globalSectionsFrobeniusPow r)).hom
        (WeilCoefficients.linearEquivOfIso E x) := toModuleCat_map_comp_apply _ _ x
    _ = (H.globalSections.frobeniusEnd ^ r) (WeilCoefficients.linearEquivOfIso E x) := by
      rw [globalSectionsFrobeniusPow_apply, Module.End.pow_apply]
      rfl

end WeilSheaf

namespace WeilSheaf

open ProEtaleWeilSheaf Scheme.Hom

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The cohomology of the constant Weil sheaf under a finite extension `k₀'/k₀` of degree `r`
of the base field: `Hⁱ((X ×_{k₀} k₀') ⊗ k̄, ℚ̄_ℓ) ≅ Hⁱ(X ⊗ k̄, ℚ̄_ℓ)`, the geometric Frobenius of
`k₀'` corresponding to the `r`-th power `Fʳ` of the geometric Frobenius of `k₀`. -/
theorem exists_linearEquiv_cohomology_adicConstant_baseChangeField
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (k₀' : Type u) [Field k₀'] [Finite k₀'] [Algebra k₀ k₀'] [Fact (ringChar k₀' ≠ l)] (i : ℤ) :
    ∃ e : ((adicConstant k₀' l (X.baseChangeField k₀ k₀')).cohomology i).carrier ≃ₗ[PadicAlgCl l]
        ((adicConstant k₀ l X).cohomology i).carrier,
      ∀ x, e (((adicConstant k₀' l (X.baseChangeField k₀ k₀')).cohomology i).frobenius x) =
        (((adicConstant k₀ l X).cohomology i).frobeniusEnd ^ Module.finrank k₀ k₀') (e x) := by
  set r := Module.finrank k₀ k₀'
  have hr : Nat.card k₀' = Nat.card k₀ ^ r := Module.natCard_eq_pow_finrank
  have hg : IsPullback (pullback.fst (X ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀'))))
      (X.baseChangeField k₀ k₀' ↘ Spec (CommRingCat.of k₀')) (X ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀'))) :=
    IsPullback.of_hasPullback _ _
  have hS : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀')))
      (Spec (CommRingCat.of k₀') ↘ Spec (CommRingCat.of k₀'))
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀'))) :=
    IsPullback.id_vert _
  let θ := geometricFiberBaseChangeIso hg
  let θS := geometricFiberBaseChangeIso hS
  have hθ := geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius hg r hr
  have hθS := geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius hS r hr
  have hsq := geometricFiberBaseChangeIso_hom_comp_geometricFiberMap hg hS
    (φ := X ↘ Spec (CommRingCat.of k₀)) (Category.comp_id _)
    (φ' := X.baseChangeField k₀ k₀' ↘ Spec (CommRingCat.of k₀')) (Category.comp_id _)
    pullback.condition.symm
  let T := transport (l := l) θ r hθ
  let TS := transport (l := l) θS r hθS
  let α : ((WeilComplex.homologySheaf i).obj ((WeilComplex.derivedLowerStar
      (X.baseChangeField k₀ k₀' ↘ Spec (CommRingCat.of k₀'))).obj
        (toComplex.obj (adicConstant k₀' l (X.baseChangeField k₀ k₀'))))).obj ≅
      TS.obj ((WeilComplex.homologySheaf i).obj ((WeilComplex.derivedLowerStar
        (X ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj (adicConstant k₀ l X)))).obj :=
    (DerivedCategory.homologyFunctor _ i).mapIso
      ((ProEtaleWeilSheaf.lowerStar k₀' l
        (X.baseChangeField k₀ k₀' ↘ Spec (CommRingCat.of k₀'))).rightDerivedFunctor.mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso (adicConstantTransportIso θ r hθ) ≪≫
            (T.mapDerivedCategorySingleFunctor 0).symm.app _) ≪≫
        (transportRightDerivedLowerStarIso θ r hθ θS hθS _ _ hsq).app _) ≪≫
    (TS.mapDerivedCategoryHomologyFunctorIso i).symm.app _
  exact exists_linearEquiv_globalSections_of_iso_transport θS r hθS _ _ α

end WeilSheaf

end AlgebraicGeometry
