/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerAction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherenceLowerStar

/-!
# The derived unit transport as a derived functor

For `s : Y' ⟶ Y` and `g : Y ⟶ X`, the derived unit transport
`Rg_* Lg^* ⟶ R(s ≫ g)_* L(s ≫ g)^*` (`ProEtale.CondensedRing.derivedUnitTransport`) is the unit of
`Ls^* ⊣ Rs_*` followed by the composition isomorphisms. This file compares it with the derived
functor of the underived unit transport `g_* g^* ⟶ (s ≫ g)_* (s ≫ g)^*` of module objects
(`ProEtale.CondensedRing.unitTransport`), for finite morphisms `s`, `g` (whose pushforwards are
exact).

## Main results

- `CategoryTheory.unitTransport_derived_fac`: the abstract comparison, for adjunctions "derived"
  from adjunctions through comparison morphisms `α`, `β` as for `Adjunction.derived`.
- `CategoryTheory.Adjunction.derivedHom`: the morphism `Lf₁ ⋙ Rg₁ ⟶ Lf₂ ⋙ Rg₂` induced by a
  morphism of composites of exact functors (generalizing `Adjunction.derivedEndo`), and its
  computation on the image of a complex
  (`CategoryTheory.Adjunction.derivedCompQhComparison_comp_derivedHom_app`).
- `ProEtale.CondensedRing.derivedUnitTransport_eq_derivedHom_app`: the derived unit transport is
  `derivedHom` of the unit transport of module objects.
- `ProEtale.CondensedRing.derivedUnitTransport_eq_derivedGaloisAction_app`: hence, for a Galois
  covering, the unit transport along `ρ σ` is the derived Galois action
  `ProEtale.CondensedRing.derivedGaloisAction` of `a`, provided the underived unit transport is
  the Galois action `ProEtale.CondensedRing.galoisAction` of `a`.

## Implementation notes

Both results take as a hypothesis the identity on homotopy categories
`ProEtale.CondensedRing.UnitTransportHomotopyCompatible` (the unit transport built from the
adjunctions and composition isomorphisms induced on homotopy categories is the unit transport of
module objects applied levelwise), which is not proved here; nor is the underived identification
of the unit transport with the Galois action.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

/-- **The unit transport commutes with derivation**, in abstract categories: let `G ⊣ F` be
adjunctions with "derived" versions `G' ⊣ F'` (only needed for `s`), related through comparison
morphisms `α : L ⋙ G' ⟶ G ⋙ L` (invertible) and `β : F ⋙ L ⟶ L ⋙ F'` compatible with the units,
and let `c`, `c'` be composition isomorphisms with compatible conjugates `r`, `r'`. Then the
derived unit transport along `s`, read through `β ≫ F'(α⁻¹)`, is `L` of the unit transport. -/
lemma unitTransport_derived_fac {C_X C_Y C_Y' D_X D_Y D_Y' : Type*} [Category C_X]
    [Category C_Y] [Category C_Y'] [Category D_X] [Category D_Y] [Category D_Y']
    {L_X : C_X ⥤ D_X} {L_Y : C_Y ⥤ D_Y} {L_Y' : C_Y' ⥤ D_Y'}
    {Gg : C_X ⥤ C_Y} {Fg : C_Y ⥤ C_X} {Gs : C_Y ⥤ C_Y'} {Fs : C_Y' ⥤ C_Y}
    {Gsg : C_X ⥤ C_Y'} {Fsg : C_Y' ⥤ C_X}
    {G'g : D_X ⥤ D_Y} {F'g : D_Y ⥤ D_X} {G's : D_Y ⥤ D_Y'} {F's : D_Y' ⥤ D_Y}
    {G'sg : D_X ⥤ D_Y'} {F'sg : D_Y' ⥤ D_X}
    (adj_s : Gs ⊣ Fs) (adj'_s : G's ⊣ F's)
    (α_g : L_X ⋙ G'g ⟶ Gg ⋙ L_Y) (α_s : L_Y ⋙ G's ⟶ Gs ⋙ L_Y')
    (α_sg : L_X ⋙ G'sg ⟶ Gsg ⋙ L_Y')
    (β_g : Fg ⋙ L_X ⟶ L_Y ⋙ F'g) (β_s : Fs ⋙ L_Y ⟶ L_Y' ⋙ F's)
    (β_sg : Fsg ⋙ L_X ⟶ L_Y' ⋙ F'sg) [IsIso α_g] [IsIso α_s] [IsIso α_sg]
    (c : Gsg ≅ Gg ⋙ Gs) (c' : G'sg ≅ G'g ⋙ G's) (r : Fs ⋙ Fg ⟶ Fsg) (r' : F's ⋙ F'g ⟶ F'sg)
    (hconj : ∀ M : C_Y', β_g.app (Fs.obj M) ≫ F'g.map (β_s.app M) ≫ r'.app (L_Y'.obj M) =
      L_X.map (r.app M) ≫ β_sg.app M)
    (hc : ∀ M : C_X, c'.hom.app (L_X.obj M) ≫ G's.map (α_g.app M) ≫ α_s.app (Gg.obj M) =
      α_sg.app M ≫ L_Y'.map (c.hom.app M))
    (hη : ∀ M : C_Y, adj'_s.unit.app (L_Y.obj M) ≫ F's.map (α_s.app M) =
      L_Y.map (adj_s.unit.app M) ≫ β_s.app (Gs.obj M))
    (K : C_X) :
    β_g.app (Gg.obj K) ≫ F'g.map (inv (α_g.app K)) ≫
        (F'g.map (adj'_s.unit.app (G'g.obj (L_X.obj K))) ≫
          r'.app (G's.obj (G'g.obj (L_X.obj K))) ≫ F'sg.map (c'.inv.app (L_X.obj K))) =
      L_X.map (Fg.map (adj_s.unit.app (Gg.obj K)) ≫ r.app (Gs.obj (Gg.obj K)) ≫
          Fsg.map (c.inv.app K)) ≫
        β_sg.app (Gsg.obj K) ≫ F'sg.map (inv (α_sg.app K)) := by
  have hc' : inv (α_s.app (Gg.obj K)) ≫ G's.map (inv (α_g.app K)) ≫ c'.inv.app (L_X.obj K) =
      L_Y'.map (c.inv.app K) ≫ inv (α_sg.app K) := by
    calc _ = inv (c'.hom.app (L_X.obj K) ≫ G's.map (α_g.app K) ≫ α_s.app (Gg.obj K)) := by
          simp [Functor.map_inv]
      _ = inv (α_sg.app K ≫ L_Y'.map (c.hom.app K)) := by simp only [hc]
      _ = _ := by
        rw [IsIso.inv_comp, ← Functor.map_inv]
        simp
  have hη' : F'g.map (inv (α_g.app K)) ≫ F'g.map (adj'_s.unit.app (G'g.obj (L_X.obj K))) =
      F'g.map (L_Y.map (adj_s.unit.app (Gg.obj K)) ≫ β_s.app (Gs.obj (Gg.obj K)) ≫
        F's.map (inv (α_s.app (Gg.obj K))) ≫ F's.map (G's.map (inv (α_g.app K)))) := by
    rw [← Functor.map_comp]
    congr 1
    have h1 := adj'_s.unit.naturality (inv (α_g.app K))
    have h2 := hη (Gg.obj K)
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h1 h2
    rw [h1, ← reassoc_of% h2, ← F's.map_comp_assoc]
    simp
  have hr' : F'g.map (F's.map (inv (α_s.app (Gg.obj K)))) ≫
      F'g.map (F's.map (G's.map (inv (α_g.app K)))) ≫ r'.app (G's.obj (G'g.obj (L_X.obj K))) ≫
        F'sg.map (c'.inv.app (L_X.obj K)) =
      r'.app (L_Y'.obj (Gs.obj (Gg.obj K))) ≫ F'sg.map (L_Y'.map (c.inv.app K)) ≫
        F'sg.map (inv (α_sg.app K)) := by
    have h := r'.naturality (inv (α_s.app (Gg.obj K)) ≫ G's.map (inv (α_g.app K)))
    simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc] at h
    rw [reassoc_of% h, ← F'sg.map_comp, ← F'sg.map_comp, ← F'sg.map_comp, hc']
  have hβg := β_g.naturality (adj_s.unit.app (Gg.obj K))
  have hβsg := β_sg.naturality (c.inv.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hβg hβsg
  simp only [Functor.map_comp, Category.assoc] at hη' ⊢
  rw [reassoc_of% hη', hr', ← reassoc_of% hβg, reassoc_of% (hconj _), reassoc_of% hβsg]

/-- The homotopy category counterpart of `Functor.mapDerivedCategoryNatTrans_fac`. -/
@[reassoc]
lemma Functor.mapDerivedCategoryNatTrans_fach {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ G)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (Functor.mapDerivedCategoryNatTrans τ).app (DerivedCategory.Qh.obj K) ≫
        G.mapDerivedCategoryFactorsh.hom.app K =
      F.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hnt : (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) := rfl
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, Functor.mapDerivedCategoryFactorsh_hom_app, hnt,
    ← NatTrans.naturality_assoc, Functor.mapDerivedCategoryNatTrans_fac_assoc,
    reassoc_of% (DerivedCategory.quotientCompQhIso_inv_naturality
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K))]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Category.assoc]
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp]
  simp

/-- The inverse of the composition isomorphism `D(f ⋙ g) ≅ D(f) ⋙ D(g)` on the image of a complex,
through the factorizations through `DerivedCategory.Qh`. -/
lemma Functor.mapDerivedCategoryFactorsh_inv_comp_compIso_inv {C D E : Type*} [Category C]
    [Category D] [Category E] [Abelian C] [Abelian D] [Abelian E] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] (f : C ⥤ D) (g : D ⥤ E) [f.Additive]
    [g.Additive] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    g.mapDerivedCategoryFactorsh.inv.app ((f.mapHomotopyCategory _).obj K) ≫
        g.mapDerivedCategory.map (f.mapDerivedCategoryFactorsh.inv.app K) ≫
        (Functor.mapDerivedCategoryCompIso f g).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (f ⋙ g)) _).hom.app K) ≫
        (f ⋙ g).mapDerivedCategoryFactorsh.inv.app K := by
  rw [← cancel_mono ((f ⋙ g).mapDerivedCategoryFactorsh.hom.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← Functor.mapDerivedCategoryCompIso_fach f g K]
  simp [← Functor.map_comp_assoc]

namespace Adjunction

open MonoidalCategory Abelian

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]

/-- The comparison `Qh (g (f K)) ⟶ Rg (Lf (Qh K))` of a composite of exact functors on the image
of a complex: the unit of the right derived functor followed by the inverse of the counit of the
left derived functor. -/
noncomputable def derivedCompQhComparison (f : C ⥤ D) (g : D ⥤ C) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.obj ((g.mapHomotopyCategory _).obj ((f.mapHomotopyCategory _).obj K)) ⟶
      g.rightDerivedFunctor.obj (f.leftDerivedFunctor.obj (DerivedCategory.Qh.obj K)) :=
  g.rightDerivedFunctorUnit.app ((f.mapHomotopyCategory _).obj K) ≫
    g.rightDerivedFunctor.map (inv (f.leftDerivedFunctorCounit.app K))

/-- `derivedCompQhComparison` followed by the comparison `Lf ⋙ Rg ≅ D(f) ⋙ D(g)` is the inverse of
the factorizations of `D(f)` and `D(g)` through `DerivedCategory.Qh`. -/
lemma derivedCompQhComparison_comp_hom (f : C ⥤ D) (g : D ⥤ C) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    derivedCompQhComparison f g K ≫
        (derivedCompIsoMapDerivedCategoryComp (f := f) (g := g)).hom.app
          (DerivedCategory.Qh.obj K) =
      g.mapDerivedCategoryFactorsh.inv.app ((f.mapHomotopyCategory _).obj K) ≫
        g.mapDerivedCategory.map (f.mapDerivedCategoryFactorsh.inv.app K) := by
  have hl : inv (f.leftDerivedFunctorCounit.app K) ≫
      f.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj K) =
      f.mapDerivedCategoryFactorsh.inv.app K := by
    have h := congr_app f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    rw [IsIso.inv_comp_eq, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hρ := congr_app g.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((f.mapHomotopyCategory _).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hρ
  simp only [derivedCompQhComparison, derivedCompIsoMapDerivedCategoryComp, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc, Functor.comp_obj]
  rw [← Functor.map_comp_assoc, hl, g.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality,
    reassoc_of% hρ]

variable {D' : Type*} [Category D'] [Abelian D'] [HasDerivedCategory D']
  [HasKInjectiveResolutions D']
  {f₁ : C ⥤ D} {g₁ : D ⥤ C} {f₂ : C ⥤ D'} {g₂ : D' ⥤ C}
  [f₁.Additive] [f₂.Additive] [g₁.Additive] [g₂.Additive]
  [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]

/-- The morphism `Lf₁ ⋙ Rg₁ ⟶ Lf₂ ⋙ Rg₂` induced by a morphism `f₁ ⋙ g₁ ⟶ f₂ ⋙ g₂` of composites
of exact functors; for `f₁ = f₂` and `g₁ = g₂` this is `CategoryTheory.Adjunction.derivedEndo`. -/
noncomputable def derivedHom (τ : f₁ ⋙ g₁ ⟶ f₂ ⋙ g₂) :
    f₁.leftDerivedFunctor ⋙ g₁.rightDerivedFunctor ⟶
      f₂.leftDerivedFunctor ⋙ g₂.rightDerivedFunctor :=
  derivedCompIsoMapDerivedCategoryComp.hom ≫ (Functor.mapDerivedCategoryCompIso f₁ g₁).hom ≫
    Functor.mapDerivedCategoryNatTrans τ ≫ (Functor.mapDerivedCategoryCompIso f₂ g₂).inv ≫
    derivedCompIsoMapDerivedCategoryComp.inv

/-- `derivedEndo` is the special case of `derivedHom` for endomorphisms. -/
lemma derivedEndo_eq_derivedHom (τ : f₁ ⋙ g₁ ⟶ f₁ ⋙ g₁) : derivedEndo τ = derivedHom τ := by
  simp [derivedEndo, derivedHom, mapDerivedCategoryEndo]

/-- **`derivedHom` on the image of a complex** is the morphism induced on the homotopy
categories, through the comparisons `derivedCompQhComparison`. -/
lemma derivedCompQhComparison_comp_derivedHom_app (τ : f₁ ⋙ g₁ ⟶ f₂ ⋙ g₂)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    derivedCompQhComparison f₁ g₁ K ≫ (derivedHom τ).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ g₁)) _).hom.app K ≫
          (NatTrans.mapHomotopyCategory τ _).app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₂ ⋙ g₂)) _).inv.app K) ≫
        derivedCompQhComparison f₂ g₂ K := by
  rw [← cancel_mono ((derivedCompIsoMapDerivedCategoryComp (f := f₂) (g := g₂)).hom.app
      (DerivedCategory.Qh.obj K)),
    ← cancel_mono ((Functor.mapDerivedCategoryCompIso f₂ g₂).hom.app (DerivedCategory.Qh.obj K)),
    ← cancel_mono ((f₂ ⋙ g₂).mapDerivedCategoryFactorsh.hom.app K)]
  simp only [derivedHom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% (derivedCompQhComparison_comp_hom f₁ g₁ K),
    reassoc_of% (derivedCompQhComparison_comp_hom f₂ g₂ K),
    Functor.mapDerivedCategoryNatTrans_fach τ K,
    ← Functor.mapDerivedCategoryCompIso_fach f₁ g₁ K,
    ← Functor.mapDerivedCategoryCompIso_fach f₂ g₂ K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp]

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open scoped CategoryTheory.Obj CategoryTheory.Functor

universe u

attribute [local instance] preservesFiniteColimits_lowerStar_of_isFinite

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The **unit transport** of module objects along `s : G ⟶ G'` of `p_* q^*`, for
`s ≫ p = p₁` and `s ≫ q = q₁`: the unit of `s^* ⊣ s_*` followed by the composition
isomorphisms, `p_* q^* ⟶ p_* s_* s^* q^* ≅ (s ≫ p)_* (s ≫ q)^* = p₁_* q₁^*`. It is the underived
version of `ProEtale.CondensedRing.derivedUnitTransport`. -/
noncomputable def unitTransport {G G' T S : Scheme.{u}} (s : G ⟶ G') {p : G' ⟶ T}
    {q : G' ⟶ S} {p₁ : G ⟶ T} {q₁ : G ⟶ S} (hp : s ≫ p = p₁) (hq : s ≫ q = q₁) :
    (q)^*⟦Λ⟧ ⋙ (p)_*⟦Λ⟧ ⟶ (q₁)^*⟦Λ⟧ ⋙ (p₁)_*⟦Λ⟧ :=
  Functor.whiskerLeft (q)^*⟦Λ⟧
      (Functor.whiskerRight (upperStarLowerStarAdjunction Λ s).unit (p)_*⟦Λ⟧) ≫
    Functor.whiskerLeft ((q)^*⟦Λ⟧ ⋙ (s)^*⟦Λ⟧) (lowerStarComp Λ s p).hom ≫
    Functor.whiskerRight (upperStarComp Λ s q).inv (s ≫ p)_*⟦Λ⟧ ≫ eqToHom (by rw [hp, hq])

/-- The unit transport of `ProEtale.CondensedRing.derivedUnitTransport`, along `s : G ⟶ G'`, as a
natural transformation `R(p)_* L(q)^* ⟶ R(s ≫ p)_* L(s ≫ q)^*`. -/
noncomputable def derivedUnitTransportNatTrans {G G' T S : Scheme.{u}} (s : G ⟶ G')
    (p : G' ⟶ T) (q : G' ⟶ S) :
    L((q)^*⟦Λ⟧) ⋙ R((p)_*⟦Λ⟧) ⟶ L((s ≫ q)^*⟦Λ⟧) ⋙ R((s ≫ p)_*⟦Λ⟧) :=
  Functor.whiskerLeft L((q)^*⟦Λ⟧)
      (Functor.whiskerRight (derivedUpperStarLowerStarAdjunction Λ s).unit R((p)_*⟦Λ⟧)) ≫
    Functor.whiskerLeft (L((q)^*⟦Λ⟧) ⋙ L((s)^*⟦Λ⟧)) (rightDerivedLowerStarComp Λ s p).hom ≫
    Functor.whiskerRight (leftDerivedUpperStarComp Λ s q).inv R((s ≫ p)_*⟦Λ⟧)

/-- The homotopy-category identity behind `derivedUnitTransport_eq_derivedHom`: the unit transport
on the homotopy categories, built from the induced adjunctions and composition isomorphisms, is
the unit transport of module objects applied levelwise. -/
def UnitTransportHomotopyCompatible {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X) : Prop :=
  ∀ K : HomotopyCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ComplexShape.up ℤ),
    (((g)_*⟦Λ⟧).mapHomotopyCategory _).map
        (((upperStarLowerStarAdjunction Λ s).mapHomotopyCategory _).unit.app
          ((((g)^*⟦Λ⟧).mapHomotopyCategory _).obj K)) ≫
      (lowerStarCompHomotopy Λ s g).app _ ≫
      (((s ≫ g)_*⟦Λ⟧).mapHomotopyCategory _).map ((upperStarCompHomotopy Λ s g).inv.app K) =
    (Functor.mapHomotopyCategoryCompIso (Iso.refl ((g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧)) _).hom.app K ≫
      (NatTrans.mapHomotopyCategory (unitTransport Λ s (p₁ := s ≫ g) (q₁ := s ≫ g) rfl rfl)
        _).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl ((s ≫ g)^*⟦Λ⟧ ⋙ (s ≫ g)_*⟦Λ⟧)) _).inv.app K

-- the instances of the general lemmas are found for each of the categories of module objects
/-- **The derived unit transport is the derived functor of the unit transport** of module
objects, for finite morphisms (whose pushforwards are exact). -/
theorem derivedUnitTransportNatTrans_eq_derivedHom {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y)
    (g : Y ⟶ X) [IsFinite s] [IsFinite g] [LocallyOfFinitePresentation s]
    [LocallyOfFinitePresentation g] (hC : UnitTransportHomotopyCompatible Λ s g) :
    derivedUnitTransportNatTrans Λ s g g =
      Adjunction.derivedHom (unitTransport Λ s (p₁ := s ≫ g) (q₁ := s ≫ g) rfl rfl) := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) fun K ↦ ?_
  have : IsIso (Adjunction.derivedCompQhComparison (g)^*⟦Λ⟧ (g)_*⟦Λ⟧ K) := by
    unfold Adjunction.derivedCompQhComparison
    infer_instance
  rw [← cancel_epi (Adjunction.derivedCompQhComparison (g)^*⟦Λ⟧ (g)_*⟦Λ⟧ K),
    Adjunction.derivedCompQhComparison_comp_derivedHom_app, ← hC K]
  simp only [derivedUnitTransportNatTrans, Adjunction.derivedCompQhComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc, Functor.comp_obj]
  exact unitTransport_derived_fac ((upperStarLowerStarAdjunction Λ s).mapHomotopyCategory _)
    (derivedUpperStarLowerStarAdjunction Λ s) _ _ _ _ _ _
    (upperStarCompHomotopy Λ s g) (leftDerivedUpperStarComp Λ s g)
    (lowerStarCompHomotopy Λ s g) (rightDerivedLowerStarComp Λ s g).hom
    (rightDerivedLowerStarComp_hom_app_Qh_fac Λ s g)
    (leftDerivedUpperStarComp_hom_app_Qh_fac Λ s g)
    (fun M ↦ ((upperStarLowerStarAdjunction Λ s).mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ _) _ _ M) K

/-- **The derived unit transport is the derived functor of the unit transport** of module
objects, pointwise and for an arbitrary factorization `s ≫ g = p₁`. -/
theorem derivedUnitTransport_eq_derivedHom_app {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    {p₁ : Y' ⟶ X} (hp : s ≫ g = p₁) [IsFinite s] [IsFinite g] [LocallyOfFinitePresentation s]
    [LocallyOfFinitePresentation g] [IsFinite p₁] [LocallyOfFinitePresentation p₁]
    (hC : UnitTransportHomotopyCompatible Λ s g)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    derivedUnitTransport Λ s hp hp A = (Adjunction.derivedHom (unitTransport Λ s hp hp)).app A := by
  subst hp
  exact (derivedUnitTransport_rfl Λ s g g A).trans
    (congr_app (derivedUnitTransportNatTrans_eq_derivedHom Λ s g hC) A)

/-- **The unit transport along an automorphism of a Galois covering is a derived Galois action**,
provided the underived unit transport is the underived Galois action of `a`
(`ProEtale.CondensedRing.galoisAction`) and the compatibility
`ProEtale.CondensedRing.UnitTransportHomotopyCompatible` holds. -/
theorem derivedUnitTransport_eq_derivedGaloisAction_app {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsFinite g] [Etale g] [Surjective g] {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)
    (σ a : Γ) [IsFinite (ρ σ)] [LocallyOfFinitePresentation (ρ σ)]
    (hC : UnitTransportHomotopyCompatible Λ (ρ σ) g)
    (hact : galoisAction Λ g hρ a = unitTransport Λ (ρ σ) (hρ σ) (hρ σ))
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    derivedUnitTransport Λ (ρ σ) (hρ σ) (hρ σ) B = (derivedGaloisAction Λ g hρ a).app B := by
  rw [derivedUnitTransport_eq_derivedHom_app Λ (ρ σ) g (hρ σ) hC, derivedGaloisAction,
    Adjunction.derivedEndo_eq_derivedHom, hact]

end AlgebraicGeometry.ProEtale.CondensedRing
