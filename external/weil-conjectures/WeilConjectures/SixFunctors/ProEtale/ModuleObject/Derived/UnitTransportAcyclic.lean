/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisActionUnitTransportInputs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitRetraction

/-!
# The derived unit transport on acyclic complexes

Let `g : Y ⟶ X` be a morphism of schemes and `s : Y' ⟶ Y` with `s ≫ g = p₁`. For a bounded below
complex `K` of module objects over `Λ_X` such that every `g^*(Kⁿ)` is `g_*`-acyclic, the isomorphism
`Adjunction.derivedUnitIso : g_* g^* K ≅ Rg_* Lg^* K` identifies `Rg_* Lg^* K` with the complex
`g_* g^* K`. This file shows that under these identifications (for `g` and `p₁`), the derived unit
transport `Rg_* Lg^* ⟶ Rp₁_* Lp₁^*` along `s` (`ProEtale.CondensedRing.derivedUnitTransport`) is
the underived unit transport `ProEtale.CondensedRing.unitTransport` applied levelwise. No
finiteness or exactness of the pushforwards is needed.

## Main results

- `ProEtale.CondensedRing.derivedUnitIso_hom_comp_derivedUnitTransport`: the comparison for an
  arbitrary factorization `s ≫ g = p₁`.
- `ProEtale.CondensedRing.derivedUnitIso_hom_comp_derivedUnitTransport_self`: the case
  `s ≫ g = g`, e.g. for an automorphism `s` of `Y` over `X`: the derived action of `s` on
  `Rg_* Lg^* K` is, through `Adjunction.derivedUnitIso`, the levelwise action on `g_* g^* K`.

## Implementation notes

The proof applies the abstract comparison `CategoryTheory.unitTransport_derived_fac` on the image
of `K` in the homotopy category, together with
`ProEtale.CondensedRing.unitTransportHomotopyCompatible`, and the naturality of the derived unit
transport along the isomorphism `Qh(K) ≅ Q(K)`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

/-- The diagram chase behind
`ProEtale.CondensedRing.derivedUnitIso_hom_comp_derivedUnitTransport`. -/
lemma comp_eq_comp_of_naturality {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ Q₀ Q₁ Q₂ Q₃
    Q₄ Q₅ : C} (e : P₀ ⟶ P₁) (u : P₁ ⟶ P₂) (r : P₂ ⟶ P₃) (φ : P₃ ⟶ P₄) (t₁ : P₄ ⟶ P₅)
    (t₂ : P₅ ⟶ P₆) (t₃ : P₆ ⟶ P₇) (w : P₀ ⟶ Q₀) (e' : Q₀ ⟶ Q₁) (u' : Q₁ ⟶ Q₂) (r' : Q₂ ⟶ Q₃)
    (φ' : Q₃ ⟶ P₇) (t₁' : P₃ ⟶ Q₄) (t₂' : Q₄ ⟶ Q₅) (t₃' : Q₅ ⟶ Q₃) (x : P₁ ⟶ Q₁)
    (hn : φ ≫ t₁ ≫ t₂ ≫ t₃ = t₁' ≫ t₂' ≫ t₃' ≫ φ')
    (h : u ≫ r ≫ t₁' ≫ t₂' ≫ t₃' = x ≫ u' ≫ r') (hq : w ≫ e' = e ≫ x) :
    e ≫ u ≫ r ≫ φ ≫ t₁ ≫ t₂ ≫ t₃ = w ≫ e' ≫ u' ≫ r' ≫ φ' := by
  rw [hn, reassoc_of% h, reassoc_of% hq]

/-- Transport a comparison square along a morphism using naturality, without expanding the
components of the natural transformation. -/
private lemma comp_eq_comp_of_app_naturality {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (τ : F ⟶ G) {X Y : C} (f : X ⟶ Y) {P₀ P₁ P₂ Q₀ Q₁ Q₂ : D}
    (e : P₀ ⟶ P₁) (u : P₁ ⟶ P₂) (r : P₂ ⟶ F.obj X) (w : P₀ ⟶ Q₀)
    (e' : Q₀ ⟶ Q₁) (u' : Q₁ ⟶ Q₂) (r' : Q₂ ⟶ G.obj X) (x : P₁ ⟶ Q₁)
    (h : u ≫ r ≫ τ.app X = x ≫ u' ≫ r') (hq : w ≫ e' = e ≫ x) :
    e ≫ u ≫ r ≫ F.map f ≫ τ.app Y = w ≫ e' ≫ u' ≫ r' ≫ G.map f := by
  rw [τ.naturality, reassoc_of% h, reassoc_of% hq]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open scoped CategoryTheory.Obj CategoryTheory.Functor

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The unit transport along `s` of `g_* g^*` on the homotopy categories, read through the
identity isomorphisms `Functor.mapHomotopyCategoryCompIso (Iso.refl _)`, is on the image of a
complex `K` the image of the levelwise unit transport. -/
lemma unitTransport_mapHomotopyCategory_app_quotient {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y)
    (g : Y ⟶ X)
    (K : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl ((g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧)) _).hom.app
        ((HomotopyCategory.quotient _ _).obj K) ≫
      (NatTrans.mapHomotopyCategory (unitTransport Λ s (p₁ := s ≫ g) (q₁ := s ≫ g) rfl rfl)
        _).app ((HomotopyCategory.quotient _ _).obj K) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl ((s ≫ g)^*⟦Λ⟧ ⋙ (s ≫ g)_*⟦Λ⟧)) _).inv.app
        ((HomotopyCategory.quotient _ _).obj K) =
    (HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex (unitTransport Λ s (p₁ := s ≫ g) (q₁ := s ≫ g) rfl rfl)
        (.up ℤ)).app K) := by
  rw [Functor.mapHomotopyCategoryCompIso_hom_app_quotient,
    Functor.mapHomotopyCategoryCompIso_inv_app_quotient, NatTrans.mapHomotopyCategory_app_quotient,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- **The derived unit transport on acyclic complexes**: for a bounded below complex `K` such that
all `g^*(Kⁿ)` are `g_*`-acyclic and all `p₁^*(Kⁿ)` are `p₁_*`-acyclic, the derived unit transport
along `s` (for `s ≫ g = p₁`) at `K` is, through the isomorphisms
`Adjunction.derivedUnitIso : g_* g^* K ≅ Rg_* Lg^* K` and `p₁_* p₁^* K ≅ Rp₁_* Lp₁^* K`, the
unit transport of module objects applied levelwise. -/
theorem derivedUnitIso_hom_comp_derivedUnitTransport {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y)
    (g : Y ⟶ X) {p₁ : Y' ⟶ X} (hp : s ≫ g = p₁)
    (K : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, ((g)_*⟦Λ⟧).rightAcyclic (((g)^*⟦Λ⟧).obj (K.X n)))
    (hK₁ : ∀ n, ((p₁)_*⟦Λ⟧).rightAcyclic (((p₁)^*⟦Λ⟧).obj (K.X n))) :
    (Adjunction.derivedUnitIso (f := (g)^*⟦Λ⟧) (g := (g)_*⟦Λ⟧) K a hK).hom ≫
        derivedUnitTransport Λ s hp hp (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (unitTransport Λ s hp hp) _).app K) ≫
        (Adjunction.derivedUnitIso (f := (p₁)^*⟦Λ⟧) (g := (p₁)_*⟦Λ⟧) K a hK₁).hom := by
  subst hp
  have h := unitTransport_derived_fac ((upperStarLowerStarAdjunction Λ s).mapHomotopyCategory _)
    (derivedUpperStarLowerStarAdjunction Λ s) _ _ _ _ _ _
    (upperStarCompHomotopy Λ s g) (leftDerivedUpperStarComp Λ s g)
    (lowerStarCompHomotopy Λ s g) (rightDerivedLowerStarComp Λ s g).hom
    (rightDerivedLowerStarComp_hom_app_Qh_fac Λ s g)
    (leftDerivedUpperStarComp_hom_app_Qh_fac Λ s g)
    (fun M ↦ ((upperStarLowerStarAdjunction Λ s).mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ _) _ _ M) ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  have ht := (unitTransportHomotopyCompatible Λ s g
    ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).trans
      (unitTransport_mapHomotopyCategory_app_quotient Λ s g K)
  have h' := h.trans (congrArg (fun t ↦ DerivedCategory.Qh.map t ≫
    ((s ≫ g)_*⟦Λ⟧).rightDerivedFunctorUnit.app
      ((((s ≫ g)^*⟦Λ⟧).mapHomotopyCategory _).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
    ((s ≫ g)_*⟦Λ⟧).rightDerivedFunctor.map
      (inv (((s ≫ g)^*⟦Λ⟧).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)))) ht)
  rw [derivedUnitTransport_rfl]
  change _ ≫ (derivedUnitTransportNatTrans Λ s g g).app (DerivedCategory.Q.obj K) = _
  simp only [Adjunction.derivedUnitIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, asIso_hom,
    Functor.mapIso_hom, Iso.app_hom, asIso_inv, Functor.map_comp, Category.assoc]
  exact comp_eq_comp_of_app_naturality (derivedUnitTransportNatTrans Λ s g g)
    ((DerivedCategory.quotientCompQhIso _).hom.app K) _ _ _ _ _ _ _ _ h'
    (DerivedCategory.quotientCompQhIso_inv_naturality _)

/-- **The derived unit transport along `s` with `s ≫ g = g` on acyclic complexes**: for a bounded
below complex `K` such that all `g^*(Kⁿ)` are `g_*`-acyclic, under the isomorphism
`Adjunction.derivedUnitIso : g_* g^* K ≅ Rg_* Lg^* K` the derived unit transport along `s` (e.g.
the action of an automorphism `s` of `Y` over `X`) is the levelwise unit transport. -/
theorem derivedUnitIso_hom_comp_derivedUnitTransport_self {X Y : Scheme.{u}} (g : Y ⟶ X)
    (s : Y ⟶ Y) (hs : s ≫ g = g)
    (K : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, ((g)_*⟦Λ⟧).rightAcyclic (((g)^*⟦Λ⟧).obj (K.X n))) :
    (Adjunction.derivedUnitIso (f := (g)^*⟦Λ⟧) (g := (g)_*⟦Λ⟧) K a hK).hom ≫
        derivedUnitTransport Λ s hs hs (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (unitTransport Λ s hs hs) _).app K) ≫
        (Adjunction.derivedUnitIso (f := (g)^*⟦Λ⟧) (g := (g)_*⟦Λ⟧) K a hK).hom :=
  derivedUnitIso_hom_comp_derivedUnitTransport Λ s g hs K a hK hK

end AlgebraicGeometry.ProEtale.CondensedRing
