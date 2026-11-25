/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportProperTriangle
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.Compactification.RefinementOfIsPullback
import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Tactic.Convert

/-!
# Local open-adjunction equation for compactification refinement

Source: blueprint proposition-composition-base-change-rf-shriek--4, proof (3), before applying
Rp'_*.
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private abbrev pulledRefinement
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (v : Y' ⟶ Y)
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c) :
    detSfBoundaryCompactification (d.obj.obj.baseChange v) ⟶
      detSfBoundaryCompactification (c.obj.obj.baseChange v) := by
  let r₀ := h.hom.hom.ofIsPullback (IsPullback.of_hasPullback f v)
  let r : (d.obj.obj.baseChange v).Refinement (c.obj.obj.baseChange v) :=
    { hom := compactSupportTrianglePullback h.hom.hom.hom c.obj.obj.g d.obj.obj.g
        h.hom.hom.hom_g v
      i_hom := r₀.i_hom
      hom_g := r₀.hom_g }
  refine ⟨⟨r⟩, ?_⟩
  have hp : IsPullback (𝟙 X) d.obj.obj.i c.obj.obj.i h.hom.hom.hom :=
    IsOpenImmersion.isPullback _ _ _ _
      (by simpa only [Category.id_comp] using h.hom.hom.i_hom) h.property
  have hs := (h.hom.hom.isPullback_ofIsPullback
    (IsPullback.of_hasPullback f v) hp.flip).flip
  change r.hom ⁻¹ᵁ (c.obj.obj.baseChange v).i.opensRange =
    (d.obj.obj.baseChange v).i.opensRange
  exact (Scheme.Hom.opensRange_pullbackSnd _ _).symm.trans
    ((Scheme.Hom.opensRange_comp_of_isIso hs.isoPullback.hom _).symm.trans
      (by congr 1; exact hs.isoPullback_hom_snd))

private def pulledRefinementExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (v : Y' ⟶ Y)
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c) :
    R((h.hom.hom.hom)_*⟦Λ⟧) ⋙
        detSfDerivedPullback Λ (pullback.fst c.obj.obj.g v) ⟶
      detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v) ⋙
        R(((pulledRefinement v h).hom.hom.hom)_*⟦Λ⟧) :=
  condensedAmbientExchange Λ (compactSupportTrianglePullbackSquare h.hom.hom.hom
    c.obj.obj.g d.obj.obj.g h.hom.hom.hom_g v)

private theorem pulledRefinementExchange_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (v : Y' ⟶ Y)
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c) :
    pulledRefinementExchange Λ v h =
      condensedAmbientExchange Λ (compactSupportTrianglePullbackSquare h.hom.hom.hom
        c.obj.obj.g d.obj.obj.g h.hom.hom.hom_g v) := by
  rfl

private theorem pullComp_conversion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (leftDerivedUpperStarComp Λ a b).hom.app M ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ a).hom.app
          ((detSfDerivedPullback Λ b).obj M) =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (a ≫ b)).hom.app M ≫
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ a b)).hom.app M ≫
        (upperStar Λ a).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ b).inv.app M) := by
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app,
    leftDerivedUpperStarIsoMapDerivedCategory, Functor.mapDerivedCategoryTriangleIso]
  exact congrArg (fun t ↦
    (upperStar Λ (a ≫ b)).leftDerivedFunctorIsoMapDerivedCategory.hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (upperStarComp Λ a b)).hom.app M ≫
      (Functor.mapDerivedCategoryCompIso (upperStar Λ b) (upperStar Λ a)).inv.app M ≫ t)
    (Category.comp_id ((upperStar Λ a).mapDerivedCategory.map
      ((upperStar Λ b).leftDerivedFunctorIsoMapDerivedCategory.inv.app M)))

private def openPullAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i] :
    D((i)_!open⟦Λ⟧) ⊣ detSfDerivedPullback Λ i :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm

private def transportIso
    {A : Type*} [Category A] {I : Type*} (F : I → A)
    {x₀ x : I} {H : A} (k : F x₀ ≅ H) (e : x₀ = x) : F x ≅ H :=
  eqToIso (congrArg F e.symm) ≪≫ k

private def pullTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X A B : Scheme.{u}} (i : X ⟶ A) (h : A ⟶ B) (j : X ⟶ B)
    (e : i ≫ h = j) :
    detSfDerivedPullback Λ j ≅ detSfDerivedPullback Λ h ⋙ detSfDerivedPullback Λ i :=
  transportIso (fun j : X ⟶ B ↦ detSfDerivedPullback Λ j)
    (leftDerivedUpperStarComp Λ i h) e

private theorem pullTriangle_conversion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X A B : Scheme.{u}} (i : X ⟶ A) (h : A ⟶ B) (j : X ⟶ B)
    (e : i ≫ h = j)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))) :
    (pullTriangle Λ i h j e).hom.app M ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ i).hom.app
          ((detSfDerivedPullback Λ h).obj M) =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom.app M ≫
        (Functor.mapDerivedCategoryTriangleIso
          (eqToIso (congrArg (upperStar Λ) e.symm) ≪≫ upperStarComp Λ i h)).hom.app M ≫
        (upperStar Λ i).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ h).inv.app M) := by
  subst j
  simpa only [pullTriangle, transportIso, eqToIso_refl, Iso.refl_trans] using
    pullComp_conversion Λ i h M

private def restrictionOfTriangle
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : C ⥤ B} {R : B ⥤ C} (adj : F ⊣ R)
    {U : B ⥤ A} {V : C ⥤ A} (k : V ≅ F ⋙ U) : R ⋙ V ⟶ U :=
  Functor.whiskerLeft R k.hom ≫ (Functor.associator R F U).inv ≫
    Functor.whiskerRight adj.counit U ≫ (Functor.leftUnitor U).hom

private theorem restrictionOfTriangle_app
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : C ⥤ B} {R : B ⥤ C} (adj : F ⊣ R)
    {U : B ⥤ A} {V : C ⥤ A} (k : V ≅ F ⋙ U) (M : B) :
    (restrictionOfTriangle adj k).app M =
      k.hom.app (R.obj M) ≫ U.map (adj.counit.app M) := by
  dsimp only [restrictionOfTriangle, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app]
  simp only [Category.id_comp]
  exact congrArg (fun t ↦ k.hom.app (R.obj M) ≫ t)
    (Category.comp_id (U.map (adj.counit.app M)))

-- Normalize the two presentations of derived pullback without unfolding their data.
private def pullRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    R((r.hom.hom.hom)_*⟦Λ⟧) ⋙ detSfDerivedPullback Λ c.obj.obj.i ⟶
      detSfDerivedPullback Λ d.obj.obj.i :=
  restrictionOfTriangle (derivedUpperStarLowerStarAdjunction Λ r.hom.hom.hom)
    (pullTriangle Λ d.obj.obj.i r.hom.hom.hom c.obj.obj.i r.hom.hom.i_hom)

private theorem pullRestriction_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    pullRestriction Λ r =
      restrictionOfTriangle (derivedUpperStarLowerStarAdjunction Λ r.hom.hom.hom)
        (pullTriangle Λ d.obj.obj.i r.hom.hom.hom c.obj.obj.i r.hom.hom.i_hom) := by
  rfl

private theorem restriction_conversion
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F H : C ⥤ B} {G : B ⥤ C} (adj : F ⊣ G)
    {Lc Dc : C ⥤ A} {Ld Dd : B ⥤ A}
    (k : Lc ≅ F ⋙ Ld) (kd : Dc ≅ H ⋙ Dd)
    (eH : F ≅ H) (ec : Lc ≅ Dc) (ed : Ld ≅ Dd)
    (hk : ∀ N, k.hom.app N ≫ ed.hom.app (F.obj N) =
      ec.hom.app N ≫ kd.hom.app N ≫ Dd.map (eH.inv.app N)) (M : B) :
    (Functor.whiskerLeft G k.hom ≫ (Functor.associator G F Ld).inv ≫
      Functor.whiskerRight adj.counit Ld ≫ (Functor.leftUnitor Ld).hom).app M ≫
        ed.hom.app M = ec.hom.app (G.obj M) ≫
      (Functor.whiskerLeft G kd.hom ≫ (Functor.associator G H Dd).inv ≫
        Functor.whiskerRight (Functor.whiskerLeft G eH.inv ≫ adj.counit) Dd ≫
        (Functor.leftUnitor Dd).hom).app M := by
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app]
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]
  have hn := ed.hom.naturality (adj.counit.app M)
  simp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [CategoryTheory.Category.id_comp (ed.hom.app M), hn, ← Category.assoc, hk]
  simp only [Category.assoc]
  exact congrArg (fun t ↦ ec.hom.app (G.obj M) ≫ kd.hom.app (G.obj M) ≫
    Dd.map (eH.inv.app (G.obj M)) ≫ t)
    (CategoryTheory.Category.comp_id (Dd.map (adj.counit.app M))).symm

private theorem restriction_conversion_nat
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F H : C ⥤ B} {G : B ⥤ C} (adj : F ⊣ G)
    {Lc Dc : C ⥤ A} {Ld Dd : B ⥤ A}
    (k : Lc ≅ F ⋙ Ld) (kd : Dc ≅ H ⋙ Dd)
    (eH : F ≅ H) (ec : Lc ≅ Dc) (ed : Ld ≅ Dd)
    (hk : ∀ N, k.hom.app N ≫ ed.hom.app (F.obj N) =
      ec.hom.app N ≫ kd.hom.app N ≫ Dd.map (eH.inv.app N)) :
    (Functor.whiskerLeft G k.hom ≫ (Functor.associator G F Ld).inv ≫
      Functor.whiskerRight adj.counit Ld ≫ (Functor.leftUnitor Ld).hom) ≫ ed.hom =
      Functor.whiskerLeft G ec.hom ≫
        (Functor.whiskerLeft G kd.hom ≫ (Functor.associator G H Dd).inv ≫
          Functor.whiskerRight (Functor.whiskerLeft G eH.inv ≫ adj.counit) Dd ≫
          (Functor.leftUnitor Dd).hom) := by
  ext M
  exact restriction_conversion adj k kd eH ec ed hk M

private theorem pullRestriction_conversion_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    pullRestriction Λ r ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ d.obj.obj.i).hom =
      Functor.whiskerLeft R((r.hom.hom.hom)_*⟦Λ⟧)
        (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.i).hom ≫
        refinementOpenRestriction Λ r.hom.hom := by
  exact restriction_conversion_nat
    (derivedUpperStarLowerStarAdjunction Λ r.hom.hom.hom)
    (pullTriangle Λ d.obj.obj.i r.hom.hom.hom c.obj.obj.i r.hom.hom.i_hom)
    (Functor.mapDerivedCategoryTriangleIso
      (eqToIso (congrArg (upperStar Λ) r.hom.hom.i_hom.symm) ≪≫
        upperStarComp Λ d.obj.obj.i r.hom.hom.hom))
    (leftDerivedUpperStarIsoMapDerivedCategory Λ r.hom.hom.hom)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.i)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ d.obj.obj.i)
    (fun N ↦ pullTriangle_conversion Λ d.obj.obj.i r.hom.hom.hom c.obj.obj.i
      r.hom.hom.i_hom N)

private theorem pullRestriction_conversion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology d.obj.obj.Z) Ab.{u + 1})
      (condensedRingObj Λ d.obj.obj.Z))) :
    (pullRestriction Λ r).app M ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ d.obj.obj.i).hom.app M =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.i).hom.app
          (R((r.hom.hom.hom)_*⟦Λ⟧).obj M) ≫
        (refinementOpenRestriction Λ r.hom.hom).app M := by
  exact NatTrans.congr_app (pullRestriction_conversion_nat Λ r) M

private theorem normalized_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    {Jc : A ⥤ C} {Jd : A ⥤ B} {Dc Lc : C ⥤ A} {Dd Ld : B ⥤ A}
    {R : B ⥤ C} (a : Jc ⊣ Dc) (b : Jd ⊣ Dd)
    (ec : Lc ≅ Dc) (ed : Ld ≅ Dd)
    (td : R ⋙ Dc ⟶ Dd) (tl : R ⋙ Lc ⟶ Ld)
    (hc : ∀ M, tl.app M ≫ ed.hom.app M = ec.hom.app (R.obj M) ≫ td.app M)
    (K : A) (α : Jc.obj K ⟶ R.obj (Jd.obj K))
    (hn : a.unit.app K ≫ Dc.map α ≫ td.app (Jd.obj K) = b.unit.app K) :
    (a.ofNatIsoRight ec.symm).homEquiv _ _ α ≫ tl.app (Jd.obj K) =
      (b.ofNatIsoRight ed.symm).unit.app K := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  apply (cancel_mono (ed.hom.app (Jd.obj K))).mp
  rw [Category.assoc, hc]
  simp only [Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc, Adjunction.homEquiv_unit, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app, Category.comp_id,
    Functor.comp_obj, Functor.id_obj]
  exact hn

private theorem pullRestriction_normalized
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (openPullAdjunction Λ c.obj.obj.i).homEquiv _ _ (localizingRefinementMap Λ r K) ≫
        (pullRestriction Λ r).app (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) =
      (openPullAdjunction Λ d.obj.obj.i).unit.app K := by
  exact normalized_transport
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.i)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ d.obj.obj.i)
    (refinementOpenRestriction Λ r.hom.hom) (pullRestriction Λ r)
    (pullRestriction_conversion Λ r) K (localizingRefinementMap Λ r K)
    (localizingRefinementMap_normalized Λ r K)

private theorem exchangeLeft_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P Q : B ⥤ A} {J' : C ⥤ D} {P' Q' : D ⥤ C}
    {U : A ⥤ C} {V : B ⥤ D}
    (a : J ⊣ P) (b : J' ⊣ P') (e : P ≅ Q) (e' : P' ≅ Q')
    (θ : Q ⋙ U ≅ V ⋙ Q') :
    Adjunction.exchangeLeft a b
        (Functor.isoWhiskerRight e U ≪≫ θ ≪≫ Functor.isoWhiskerLeft V e'.symm) =
      Adjunction.exchangeLeft (a.ofNatIsoRight e) (b.ofNatIsoRight e') θ := by
  ext K
  simp only [Adjunction.exchangeLeft_app, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]

private theorem expanded_exchangeLeft_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P Q : B ⥤ A} {J' : C ⥤ D} {P' Q' : D ⥤ C}
    {U : A ⥤ C} {V : B ⥤ D}
    (a : J ⊣ P) (b : J' ⊣ P') (e : Q ≅ P) (e' : Q' ≅ P')
    (θ : Q ⋙ U ≅ V ⋙ Q') :
    (Functor.leftUnitor _).inv ≫ Functor.whiskerRight a.unit (U ⋙ J') ≫
      (Functor.squareTransport J J'
        (Functor.isoWhiskerRight e.symm U ≪≫ θ ≪≫ Functor.isoWhiskerLeft V e')).hom ≫
      Functor.whiskerLeft (J ⋙ V) b.counit ≫ (Functor.rightUnitor _).hom =
        Adjunction.exchangeLeft (a.ofNatIsoRight e.symm) (b.ofNatIsoRight e'.symm) θ := by
  simpa only [Adjunction.exchangeLeft, Category.assoc, Iso.symm_symm_eq] using
    exchangeLeft_transport a b e.symm e'.symm θ

private theorem exchangeLeft_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    {U : A ⥤ C} {V : B ⥤ D}
    (a : J ⊣ P) (b : J' ⊣ P') (θ : P ⋙ U ≅ V ⋙ P') (K : A) :
    b.unit.app (U.obj K) ≫ P'.map ((Adjunction.exchangeLeft a b θ).app K) =
      U.map (a.unit.app K) ≫ θ.hom.app (J.obj K) := by
  have h := (b.homEquiv _ _).apply_symm_apply
    (U.map (a.unit.app K) ≫ θ.hom.app (J.obj K))
  simpa only [Adjunction.exchangeLeft_app, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Functor.comp_obj, Functor.id_obj] using h

private def openPullSquare
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f) :
    ChosenCartesianSquare (pullback.fst f v) (c.baseChange v).i c.i
      (pullback.fst c.g v) :=
  let sq := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)
  ⟨sq.toCommSq, sq.isoPullback, sq.isoPullback_hom_fst, sq.isoPullback_hom_snd⟩

-- Transport the open adjunction across the two derived pullback presentations.
private theorem openBaseChange_exchangeLeft
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f) :
    detSfOpenBaseChangeMap Λ f v c =
      Adjunction.exchangeLeft (openPullAdjunction Λ c.i)
        (openPullAdjunction Λ (c.baseChange v).i)
        (condensedAmbientPullbackComparison Λ (openPullSquare f v c)).symm := by
  exact expanded_exchangeLeft_transport
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (c.baseChange v).i)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ c.i)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ (c.baseChange v).i)
    (condensedAmbientPullbackComparison Λ (openPullSquare f v c)).symm

private theorem comparison_transport_nat
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {I J : Type*} (F : I → C ⥤ A) (G : J → D ⥤ B)
    (V : C ⥤ D) (U : A ⥤ B) (P : I → J → Prop)
    (θ : ∀ x y, P x y → (V ⋙ G y ≅ F x ⋙ U))
    {x₀ x : I} {y₀ y : J} {H : C ⥤ A} {H' : D ⥤ B}
    (k : F x₀ ≅ H) (k' : G y₀ ≅ H')
    (e : x₀ = x) (e' : y₀ = y) (p₀ : P x₀ y₀) (p : P x y)
    (v : V ⋙ H' ⟶ H ⋙ U)
    (h : Functor.whiskerLeft V k'.hom ≫ v =
      (θ x₀ y₀ p₀).hom ≫ Functor.whiskerRight k.hom U) :
    Functor.whiskerLeft V (transportIso G k' e').hom ≫ v =
      (θ x y p).hom ≫
        Functor.whiskerRight (transportIso F k e).hom U := by
  subst x
  subst y
  simpa only [transportIso, eqToIso_refl, Iso.refl_trans] using h

private theorem triangle_cancel
    {A : Type*} [Category A] {X Y P : A}
    (e : X ≅ Y) (a : P ⟶ Y) (b : P ⟶ X) (h : b = a ≫ e.inv) :
    a = b ≫ e.hom := by
  rw [h, Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem square_pasting_from_components
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (F' : C' ⥤ D') (G' : D' ⥤ E')
    (V : C ⥤ C') (W : D ⥤ D') (U : E ⥤ E')
    {T : C ⥤ E} {T' : C' ⥤ E'} (k : T ≅ F ⋙ G) (k' : T' ≅ F' ⋙ G')
    (θh : V ⋙ F' ≅ F ⋙ W) (θi : W ⋙ G' ≅ G ⋙ U) (θt : V ⋙ T' ≅ T ⋙ U)
    (h : ∀ M, θt.hom.app M = k'.hom.app (V.obj M) ≫
      G'.map (θh.hom.app M) ≫ θi.hom.app (F.obj M) ≫ U.map (k.inv.app M)) :
    Functor.whiskerLeft V k'.hom ≫ (Functor.associator V F' G').inv ≫
        Functor.whiskerRight θh.hom G' ≫ (Functor.associator F W G').hom ≫
        Functor.whiskerLeft F θi.hom ≫ (Functor.associator F G U).inv =
      θt.hom ≫ Functor.whiskerRight k.hom U := by
  apply triangle_cancel (Functor.isoWhiskerRight k U)
  ext M
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc, Functor.isoWhiskerRight_inv] using h M

-- Unifying native unbounded derived pullback objects exceeds the default kernel allowance.
private theorem pullSquare_base_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X A B X' A' B' : Scheme.{u}}
    (i : X ⟶ A) (h : A ⟶ B)
    (i' : X' ⟶ A') (h' : A' ⟶ B')
    (u' : X' ⟶ X) (va : A' ⟶ A) (vb : B' ⟶ B)
    (si : CommSq u' i' i va) (sh : CommSq va h' h vb) :
    Functor.whiskerLeft (L((vb)^*⟦Λ⟧)) (leftDerivedUpperStarComp Λ i' h').hom ≫
        (Functor.associator (L((vb)^*⟦Λ⟧))
          (L((h')^*⟦Λ⟧)) (L((i')^*⟦Λ⟧))).inv ≫
        Functor.whiskerRight (pullbackSquareComparison Λ sh).hom
          (L((i')^*⟦Λ⟧)) ≫
        (Functor.associator (L((h)^*⟦Λ⟧))
          (L((va)^*⟦Λ⟧)) (L((i')^*⟦Λ⟧))).hom ≫
        Functor.whiskerLeft (L((h)^*⟦Λ⟧))
          (pullbackSquareComparison Λ si).hom ≫
        (Functor.associator (L((h)^*⟦Λ⟧))
          (L((i)^*⟦Λ⟧)) (L((u')^*⟦Λ⟧))).inv =
      (pullbackSquareComparison Λ (si.vert_comp sh)).hom ≫
        Functor.whiskerRight (leftDerivedUpperStarComp Λ i h).hom (L((u')^*⟦Λ⟧)) := by
  exact square_pasting_from_components _ _ _ _ _ _ _
    (leftDerivedUpperStarComp Λ i h) (leftDerivedUpperStarComp Λ i' h')
    (pullbackSquareComparison Λ sh) (pullbackSquareComparison Λ si)
    (pullbackSquareComparison Λ (si.vert_comp sh))
    (pullbackSquareComparison_paste_horizontal Λ si sh)

private theorem pullSquare_triangle_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X A B X' A' B' : Scheme.{u}}
    (i : X ⟶ A) (h : A ⟶ B) (j : X ⟶ B)
    (i' : X' ⟶ A') (h' : A' ⟶ B') (j' : X' ⟶ B')
    (u' : X' ⟶ X) (va : A' ⟶ A) (vb : B' ⟶ B)
    (e : i ≫ h = j) (e' : i' ≫ h' = j')
    (si : CommSq u' i' i va) (sh : CommSq va h' h vb) (sj : CommSq u' j' j vb) :
    Functor.whiskerLeft (detSfDerivedPullback Λ vb) (pullTriangle Λ i' h' j' e').hom ≫
        (Functor.associator (detSfDerivedPullback Λ vb)
          (detSfDerivedPullback Λ h') (detSfDerivedPullback Λ i')).inv ≫
        Functor.whiskerRight (pullbackSquareComparison Λ sh).hom
          (detSfDerivedPullback Λ i') ≫
        (Functor.associator (detSfDerivedPullback Λ h)
          (detSfDerivedPullback Λ va) (detSfDerivedPullback Λ i')).hom ≫
        Functor.whiskerLeft (detSfDerivedPullback Λ h)
          (pullbackSquareComparison Λ si).hom ≫
        (Functor.associator (detSfDerivedPullback Λ h)
          (detSfDerivedPullback Λ i) (detSfDerivedPullback Λ u')).inv =
      (pullbackSquareComparison Λ sj).hom ≫
        Functor.whiskerRight (pullTriangle Λ i h j e).hom (detSfDerivedPullback Λ u') := by
  apply comparison_transport_nat
    (fun j : X ⟶ B ↦ detSfDerivedPullback Λ j)
    (fun j' : X' ⟶ B' ↦ detSfDerivedPullback Λ j')
    (detSfDerivedPullback Λ vb) (detSfDerivedPullback Λ u')
    (fun j j' ↦ CommSq u' j' j vb) (fun _ _ sq ↦ pullbackSquareComparison Λ sq)
    (leftDerivedUpperStarComp Λ i h) (leftDerivedUpperStarComp Λ i' h')
    e e' (si.vert_comp sh) sj
  exact pullSquare_base_nat Λ i h i' h' u' va vb si sh

private theorem ambient_exchange_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X X' Y Y' : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare u' f' f v) :
    condensedAmbientExchange Λ sq =
      (mateEquiv (derivedUpperStarLowerStarAdjunction Λ f)
        (derivedUpperStarLowerStarAdjunction Λ f')
        (TwoSquare.mk L((v)^*⟦Λ⟧) L((f)^*⟦Λ⟧) L((f')^*⟦Λ⟧) L((u')^*⟦Λ⟧)
          (condensedAmbientPullbackComparison Λ sq).hom)) := by
  rfl

set_option backward.defeqAttrib.useBackward true in
-- Derived adjunctions require additional definitional comparison during specialization.
private theorem ambient_exchange_counit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X X' Y Y' : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare u' f' f v)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    L((f')^*⟦Λ⟧).map ((condensedAmbientExchange Λ sq).app M) ≫
        (derivedUpperStarLowerStarAdjunction Λ f').counit.app (L((u')^*⟦Λ⟧).obj M) =
      (condensedAmbientPullbackComparison Λ sq).hom.app (R((f)_*⟦Λ⟧).obj M) ≫
        L((u')^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ f).counit.app M) := by
  rw [ambient_exchange_eq]
  have hc := mateEquiv_counit
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ f')
    (.mk L((v)^*⟦Λ⟧) L((f)^*⟦Λ⟧) L((f')^*⟦Λ⟧) L((u')^*⟦Λ⟧)
      (condensedAmbientPullbackComparison Λ sq).hom) M
  exact hc

private theorem ambient_comparison_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X X' Y Y' : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare u' f' f v) :
    condensedAmbientPullbackComparison Λ sq =
      pullbackSquareComparison Λ sq.toCommSq := by
  rfl

private theorem pullRestriction_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology d.obj.obj.Z) Ab.{u + 1})
      (condensedRingObj Λ d.obj.obj.Z))) : IsIso ((pullRestriction Λ r).app M) := by
  let _ := refinementOpenRestriction_isIso Λ r
  have : IsIso ((pullRestriction Λ r).app M ≫
      (leftDerivedUpperStarIsoMapDerivedCategory Λ d.obj.obj.i).hom.app M) := by
    rw [pullRestriction_conversion]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ d.obj.obj.i).hom.app M)

private theorem restriction_mate_nat
    {CA DA EA CB DB EB : Type*}
    [Category CA] [Category DA] [Category EA] [Category CB] [Category DB] [Category EB]
    {FA : EA ⥤ DA} {RA : DA ⥤ EA} {FB : EB ⥤ DB} {RB : DB ⥤ EB}
    (adjA : FA ⊣ RA) (adjB : FB ⊣ RB)
    (U₁A : DA ⥤ CA) (U₂A : EA ⥤ CA) (U₁B : DB ⥤ CB) (U₂B : EB ⥤ CB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (kA : U₂A ≅ FA ⋙ U₁A) (kB : U₂B ≅ FB ⋙ U₁B)
    (l₁ : Q₁ ⋙ U₁B ≅ U₁A ⋙ QX) (l₂ : Q₂ ⋙ U₂B ≅ U₂A ⋙ QX)
    (lv : Q₂ ⋙ FB ≅ FA ⋙ Q₁) (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (hc : ∀ M, FB.map (χ.app M) ≫ adjB.counit.app (Q₁.obj M) =
      lv.hom.app (RA.obj M) ≫ Q₁.map (adjA.counit.app M))
    (hk : ∀ N, kB.hom.app (Q₂.obj N) ≫ U₁B.map (lv.hom.app N) ≫
      l₁.hom.app (FA.obj N) = l₂.hom.app N ≫ QX.map (kA.hom.app N)) :
    Functor.whiskerRight χ U₂B ≫ (Functor.associator Q₁ RB U₂B).hom ≫
        Functor.whiskerLeft Q₁ (restrictionOfTriangle adjB kB) ≫ l₁.hom =
      (Functor.associator RA Q₂ U₂B).hom ≫ Functor.whiskerLeft RA l₂.hom ≫
        (Functor.associator RA U₂A QX).inv ≫
        Functor.whiskerRight (restrictionOfTriangle adjA kA) QX := by
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj, Category.assoc, restrictionOfTriangle_app, Functor.map_comp]
  exact AlgebraicGeometry.Etale.restriction_coefficient_mate adjA adjB
    U₁A U₂A U₁B U₂B QX Q₁ Q₂ kA kB l₁ l₂ lv χ hc hk M

private theorem restriction_mate_nat_of_pasting
    {CA DA EA CB DB EB : Type*}
    [Category CA] [Category DA] [Category EA] [Category CB] [Category DB] [Category EB]
    {FA : EA ⥤ DA} {RA : DA ⥤ EA} {FB : EB ⥤ DB} {RB : DB ⥤ EB}
    (adjA : FA ⊣ RA) (adjB : FB ⊣ RB)
    (U₁A : DA ⥤ CA) (U₂A : EA ⥤ CA) (U₁B : DB ⥤ CB) (U₂B : EB ⥤ CB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (kA : U₂A ≅ FA ⋙ U₁A) (kB : U₂B ≅ FB ⋙ U₁B)
    (l₁ : Q₁ ⋙ U₁B ≅ U₁A ⋙ QX) (l₂ : Q₂ ⋙ U₂B ≅ U₂A ⋙ QX)
    (lv : Q₂ ⋙ FB ≅ FA ⋙ Q₁) (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (hc : ∀ M, FB.map (χ.app M) ≫ adjB.counit.app (Q₁.obj M) =
      lv.hom.app (RA.obj M) ≫ Q₁.map (adjA.counit.app M))
    (hk : Functor.whiskerLeft Q₂ kB.hom ≫ (Functor.associator Q₂ FB U₁B).inv ≫
      Functor.whiskerRight lv.hom U₁B ≫ (Functor.associator FA Q₁ U₁B).hom ≫
      Functor.whiskerLeft FA l₁.hom ≫ (Functor.associator FA U₁A QX).inv =
      l₂.hom ≫ Functor.whiskerRight kA.hom QX) :
    Functor.whiskerRight χ U₂B ≫ (Functor.associator Q₁ RB U₂B).hom ≫
        Functor.whiskerLeft Q₁ (restrictionOfTriangle adjB kB) ≫ l₁.hom =
      (Functor.associator RA Q₂ U₂B).hom ≫ Functor.whiskerLeft RA l₂.hom ≫
        (Functor.associator RA U₂A QX).inv ≫
        Functor.whiskerRight (restrictionOfTriangle adjA kA) QX := by
  apply restriction_mate_nat adjA adjB U₁A U₂A U₁B U₂B QX Q₁ Q₂ kA kB l₁ l₂ lv χ hc
  intro N
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Functor.comp_obj, Category.assoc] using NatTrans.congr_app hk N

private theorem restriction_mate_component
    {CA DA EA CB DB EB : Type*}
    [Category CA] [Category DA] [Category EA] [Category CB] [Category DB] [Category EB]
    (RA : DA ⥤ EA) (RB : DB ⥤ EB)
    (U₁A : DA ⥤ CA) (U₂A : EA ⥤ CA) (U₁B : DB ⥤ CB) (U₂B : EB ⥤ CB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (tA : RA ⋙ U₂A ⟶ U₁A) (tB : RB ⋙ U₂B ⟶ U₁B)
    (l₁ : Q₁ ⋙ U₁B ≅ U₁A ⋙ QX) (l₂ : Q₂ ⋙ U₂B ≅ U₂A ⋙ QX)
    (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (h : Functor.whiskerRight χ U₂B ≫ (Functor.associator Q₁ RB U₂B).hom ≫
        Functor.whiskerLeft Q₁ tB ≫ l₁.hom =
      (Functor.associator RA Q₂ U₂B).hom ≫ Functor.whiskerLeft RA l₂.hom ≫
        (Functor.associator RA U₂A QX).inv ≫ Functor.whiskerRight tA QX) (M : DA) :
    U₂B.map (χ.app M) ≫ tB.app (Q₁.obj M) ≫ l₁.hom.app M =
      l₂.hom.app (RA.obj M) ≫ QX.map (tA.app M) := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj, Category.assoc] using NatTrans.congr_app h M

set_option backward.defeqAttrib.useBackward true in
-- Derived adjunctions require additional definitional comparison during specialization.
private theorem triangle_restriction_mate_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X A B X' A' B' : Scheme.{u}}
    (i : X ⟶ A) (h : A ⟶ B) (j : X ⟶ B)
    (i' : X' ⟶ A') (h' : A' ⟶ B') (j' : X' ⟶ B')
    (u' : X' ⟶ X) (va : A' ⟶ A) (vb : B' ⟶ B)
    (e : i ≫ h = j) (e' : i' ≫ h' = j')
    (si : ChosenCartesianSquare u' i' i va) (sh : ChosenCartesianSquare va h' h vb)
    (sj : ChosenCartesianSquare u' j' j vb) :
    Functor.whiskerRight (condensedAmbientExchange Λ sh) (detSfDerivedPullback Λ j') ≫
        (Functor.associator (detSfDerivedPullback Λ va) R((h')_*⟦Λ⟧)
          (detSfDerivedPullback Λ j')).hom ≫
        Functor.whiskerLeft (detSfDerivedPullback Λ va)
          (restrictionOfTriangle (derivedUpperStarLowerStarAdjunction Λ h')
            (pullTriangle Λ i' h' j' e')) ≫
        (condensedAmbientPullbackComparison Λ si).hom =
      (Functor.associator R((h)_*⟦Λ⟧) (detSfDerivedPullback Λ vb)
        (detSfDerivedPullback Λ j')).hom ≫
        Functor.whiskerLeft R((h)_*⟦Λ⟧) (condensedAmbientPullbackComparison Λ sj).hom ≫
        (Functor.associator R((h)_*⟦Λ⟧) (detSfDerivedPullback Λ j)
          (detSfDerivedPullback Λ u')).inv ≫
        Functor.whiskerRight
          (restrictionOfTriangle (derivedUpperStarLowerStarAdjunction Λ h)
            (pullTriangle Λ i h j e)) (detSfDerivedPullback Λ u') := by
  refine restriction_mate_nat_of_pasting
    (derivedUpperStarLowerStarAdjunction Λ h) (derivedUpperStarLowerStarAdjunction Λ h')
    (detSfDerivedPullback Λ i) (detSfDerivedPullback Λ j)
    (detSfDerivedPullback Λ i') (detSfDerivedPullback Λ j')
    (detSfDerivedPullback Λ u') (detSfDerivedPullback Λ va) (detSfDerivedPullback Λ vb)
    (pullTriangle Λ i h j e) (pullTriangle Λ i' h' j' e')
    (condensedAmbientPullbackComparison Λ si) (condensedAmbientPullbackComparison Λ sj)
    (condensedAmbientPullbackComparison Λ sh) (condensedAmbientExchange Λ sh) ?_ ?_
  · exact ambient_exchange_counit Λ sh
  · exact pullSquare_triangle_nat Λ i h j i' h' j' u' va vb e e'
      si.toCommSq sh.toCommSq sj.toCommSq

-- Keep scheme pullbacks as named objects while matching their derived-functor formulas.
attribute [local irreducible] limit limit.cone

-- Specialize coherent pullback and restriction identities at the functor level.
private theorem pullRestriction_baseChange_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (v : Y' ⟶ Y)
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c) :
    let r := pulledRefinement v h
    let c' := detSfBoundaryCompactification (c.obj.obj.baseChange v)
    let _d' := detSfBoundaryCompactification (d.obj.obj.baseChange v)
    let sc := openPullSquare f v c.obj.obj
    let sd := openPullSquare f v d.obj.obj
    let _sh :=
      compactSupportTrianglePullbackSquare h.hom.hom.hom c.obj.obj.g d.obj.obj.g
        h.hom.hom.hom_g v
    Functor.whiskerRight (pulledRefinementExchange Λ v h)
        (detSfDerivedPullback Λ c'.obj.obj.i) ≫
      (Functor.associator (detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v))
        R((r.hom.hom.hom)_*⟦Λ⟧) (detSfDerivedPullback Λ c'.obj.obj.i)).hom ≫
      Functor.whiskerLeft (detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v))
        (pullRestriction Λ r) ≫ (condensedAmbientPullbackComparison Λ sd).hom =
    (Functor.associator R((h.hom.hom.hom)_*⟦Λ⟧)
        (detSfDerivedPullback Λ (pullback.fst c.obj.obj.g v))
        (detSfDerivedPullback Λ c'.obj.obj.i)).hom ≫
      Functor.whiskerLeft R((h.hom.hom.hom)_*⟦Λ⟧)
        (condensedAmbientPullbackComparison Λ sc).hom ≫
      (Functor.associator R((h.hom.hom.hom)_*⟦Λ⟧)
        (detSfDerivedPullback Λ c.obj.obj.i)
        (detSfDerivedPullback Λ (pullback.fst f v))).inv ≫
      Functor.whiskerRight (pullRestriction Λ h)
        (detSfDerivedPullback Λ (pullback.fst f v)) := by
  let r := pulledRefinement v h
  let c' := detSfBoundaryCompactification (c.obj.obj.baseChange v)
  let d' := detSfBoundaryCompactification (d.obj.obj.baseChange v)
  let sc := openPullSquare f v c.obj.obj
  let sd := openPullSquare f v d.obj.obj
  let sh := compactSupportTrianglePullbackSquare h.hom.hom.hom c.obj.obj.g d.obj.obj.g
    h.hom.hom.hom_g v
  exact triangle_restriction_mate_nat Λ
    d.obj.obj.i h.hom.hom.hom c.obj.obj.i d'.obj.obj.i r.hom.hom.hom c'.obj.obj.i
    (pullback.fst f v) (pullback.fst d.obj.obj.g v) (pullback.fst c.obj.obj.g v)
    h.hom.hom.i_hom r.hom.hom.i_hom sd sh sc

private theorem coefficient_refinement_of_natural_comparisons
    {CA DA EA CB DB EB : Type*}
    [Category* CA] [Category* DA] [Category* EA]
    [Category* CB] [Category* DB] [Category* EB]
    {J₁A : CA ⥤ DA} {J₂A : CA ⥤ EA}
    {U₁A : DA ⥤ CA} {U₂A : EA ⥤ CA}
    {J₁B : CB ⥤ DB} {J₂B : CB ⥤ EB}
    {U₁B : DB ⥤ CB} {U₂B : EB ⥤ CB}
    (a₁A : J₁A ⊣ U₁A) (a₂A : J₂A ⊣ U₂A)
    (a₁B : J₁B ⊣ U₁B) (a₂B : J₂B ⊣ U₂B)
    (RA : DA ⥤ EA) (RB : DB ⥤ EB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (tA : RA ⋙ U₂A ⟶ U₁A) (tB : RB ⋙ U₂B ⟶ U₁B)
    (l₁ : Q₁ ⋙ U₁B ≅ U₁A ⋙ QX) (l₂ : Q₂ ⋙ U₂B ≅ U₂A ⋙ QX)
    (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (hχ : Functor.whiskerRight χ U₂B ≫ (Functor.associator Q₁ RB U₂B).hom ≫
        Functor.whiskerLeft Q₁ tB ≫ l₁.hom =
      (Functor.associator RA Q₂ U₂B).hom ≫ Functor.whiskerLeft RA l₂.hom ≫
        (Functor.associator RA U₂A QX).inv ≫ Functor.whiskerRight tA QX)
    (K : CA) (αA : J₂A.obj K ⟶ RA.obj (J₁A.obj K))
    (αB : J₂B.obj (QX.obj K) ⟶ RB.obj (J₁B.obj (QX.obj K)))
    (b₁ : J₁A ⋙ Q₁ ≅ QX ⋙ J₁B)
    (b₂ : J₂A ⋙ Q₂ ≅ QX ⋙ J₂B)
    (hb₁ : b₁.inv = Adjunction.exchangeLeft a₁A a₁B l₁.symm)
    (hb₂ : b₂.inv = Adjunction.exchangeLeft a₂A a₂B l₂.symm)
    (hA : a₂A.homEquiv _ _ αA ≫ tA.app (J₁A.obj K) = a₁A.unit.app K)
    (hB : a₂B.homEquiv _ _ αB ≫ tB.app (J₁B.obj (QX.obj K)) =
      a₁B.unit.app (QX.obj K))
    [Mono (tB.app (J₁B.obj (QX.obj K)))] :
    Q₂.map αA ≫ χ.app (J₁A.obj K) ≫ RB.map (b₁.hom.app K) = b₂.hom.app K ≫ αB := by
  exact AlgebraicGeometry.Etale.coefficient_refinement_of_restriction
    a₁A a₂A a₁B a₂B RA RB QX Q₁ Q₂ tA tB l₁ l₂ χ
    (restriction_mate_component RA RB U₁A U₂A U₁B U₂B QX Q₁ Q₂ tA tB l₁ l₂ χ hχ)
    K αA αB
    (b₁.app K) (b₂.app K)
    (by
      change a₁B.unit.app (QX.obj K) ≫ U₁B.map (b₁.inv.app K) = _
      rw [hb₁]
      exact exchangeLeft_unit a₁A a₁B l₁.symm K)
    (by
      change a₂B.unit.app (QX.obj K) ≫ U₂B.map (b₂.inv.app K) = _
      rw [hb₂]
      exact exchangeLeft_unit a₂A a₂B l₂.symm K)
    hA hB

set_option backward.defeqAttrib.useBackward true in
-- Specializing four derived adjunctions compares large module category expressions.
private theorem local_refinement_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (v : Y' ⟶ Y)
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c)
    (oc : D((c.obj.obj.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.obj.obj.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.obj.obj.baseChange v).i)_!open⟦Λ⟧))
    (od : D((d.obj.obj.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((d.obj.obj.baseChange v).i)_!open⟦Λ⟧))
    (hoc : oc.inv = detSfOpenBaseChangeMap Λ f v c.obj.obj)
    (hod : od.inv = detSfOpenBaseChangeMap Λ f v d.obj.obj)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (detSfDerivedPullback Λ (pullback.fst c.obj.obj.g v)).map
        (localizingRefinementMap Λ h K) ≫
      (pulledRefinementExchange Λ v h).app
        (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) ≫
      R(((pulledRefinement v h).hom.hom.hom)_*⟦Λ⟧).map (od.hom.app K) =
    oc.hom.app K ≫ localizingRefinementMap Λ (pulledRefinement v h)
      ((detSfDerivedPullback Λ (pullback.fst f v)).obj K) := by
  let r := pulledRefinement v h
  let sc := openPullSquare f v c.obj.obj
  let sd := openPullSquare f v d.obj.obj
  let sh := compactSupportTrianglePullbackSquare h.hom.hom.hom c.obj.obj.g d.obj.obj.g
    h.hom.hom.hom_g v
  let _ := pullRestriction_isIso Λ r
    (D((((detSfBoundaryCompactification
      (d.obj.obj.baseChange v)).obj.obj.i))_!open⟦Λ⟧).obj
      ((detSfDerivedPullback Λ (pullback.fst f v)).obj K))
  refine coefficient_refinement_of_natural_comparisons
    (openPullAdjunction Λ d.obj.obj.i) (openPullAdjunction Λ c.obj.obj.i)
    (openPullAdjunction Λ
      (detSfBoundaryCompactification (d.obj.obj.baseChange v)).obj.obj.i)
    (openPullAdjunction Λ
      (detSfBoundaryCompactification (c.obj.obj.baseChange v)).obj.obj.i)
    R((h.hom.hom.hom)_*⟦Λ⟧) R((r.hom.hom.hom)_*⟦Λ⟧)
    (detSfDerivedPullback Λ (pullback.fst f v))
    (detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v))
    (detSfDerivedPullback Λ (pullback.fst c.obj.obj.g v))
    (pullRestriction Λ h) (pullRestriction Λ r)
    (condensedAmbientPullbackComparison Λ sd) (condensedAmbientPullbackComparison Λ sc)
    (pulledRefinementExchange Λ v h) ?_ K
    (localizingRefinementMap Λ h K)
    (localizingRefinementMap Λ r ((detSfDerivedPullback Λ (pullback.fst f v)).obj K))
    od oc ?_ ?_ ?_ ?_
  · exact pullRestriction_baseChange_nat Λ v h
  · exact hod.trans (openBaseChange_exchangeLeft Λ f v d.obj.obj)
  · exact hoc.trans (openBaseChange_exchangeLeft Λ f v c.obj.obj)
  · exact pullRestriction_normalized Λ h K
  · exact pullRestriction_normalized Λ r
      ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)

private theorem refinement_triangle_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d w : Compactification.BoundaryCompactification f}
    (r : d ⟶ c) (s : w ⟶ d) (t : w ⟶ c)
    (e : s.hom.hom.hom ≫ r.hom.hom.hom = t.hom.hom.hom)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    localizingRefinementMap Λ r K ≫
        R((r.hom.hom.hom)_*⟦Λ⟧).map (localizingRefinementMap Λ s K) ≫
        (compactSupportPushforwardTriangle Λ s.hom.hom.hom r.hom.hom.hom
          t.hom.hom.hom e).hom.app (D((w.obj.obj.i)_!open⟦Λ⟧).obj K) =
      localizingRefinementMap Λ t K := by
  have ht : s ≫ r = t := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact Compactification.Refinement.ext e
  subst t
  rw [← Category.assoc, ← localizingRefinementMap_comp]
  simp only [compactSupportPushforwardTriangle, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  have he : lowerStarCongr Λ e = Iso.refl _ := by rfl
  rw [he]
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]

private theorem refinement_pasting_algebra
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' T : D} {P Q S : C}
    (a : A ⟶ B) (b : B ⟶ F.obj P) (d : P ⟶ Q) (e : Q ⟶ S)
    (k : F.obj S ⟶ T) (o : A ⟶ A') (r : A' ⟶ F.obj Q) (t : A' ⟶ T)
    (hb : a ≫ b ≫ F.map d = o ≫ r) (he : r ≫ F.map e ≫ k = t) :
    a ≫ b ≫ F.map (d ≫ e) ≫ k = o ≫ t := by
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hb, he]

-- Match the large derived functors in the normalized coefficient equations.
private theorem boundary_refinement_pasting
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (c d : Compactification.BoundaryCompactification f)
    (oc : D((c.obj.obj.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.obj.obj.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.obj.obj.baseChange v).i)_!open⟦Λ⟧))
    (od : D((d.obj.obj.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((d.obj.obj.baseChange v).i)_!open⟦Λ⟧))
    (hoc : oc.inv = detSfOpenBaseChangeMap Λ f v c.obj.obj)
    (hod : od.inv = detSfOpenBaseChangeMap Λ f v d.obj.obj)
    (h : d ⟶ c)
    (w : Compactification.BoundaryCompactification (pullback.snd f v))
    (hd : w ⟶ detSfBoundaryCompactification (d.obj.obj.baseChange v))
    (hc : w ⟶ detSfBoundaryCompactification (c.obj.obj.baseChange v))
    (esr : hd.hom.hom.hom ≫
        (pulledRefinement v h).hom.hom.hom =
      hc.hom.hom.hom)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (detSfDerivedPullback Λ (pullback.fst c.obj.obj.g v)).map (localizingRefinementMap Λ h K) ≫
      (pulledRefinementExchange Λ v h).app (D((d.obj.obj.i)_!open⟦Λ⟧).obj K) ≫
      R(((pulledRefinement v h).hom.hom.hom)_*⟦Λ⟧).map
        (od.hom.app K ≫ localizingRefinementMap Λ hd
          ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) ≫
      (compactSupportPushforwardTriangle Λ hd.hom.hom.hom
        ((pulledRefinement v h).hom.hom.hom)
        hc.hom.hom.hom esr).hom.app
          (D((w.obj.obj.i)_!open⟦Λ⟧).obj
            ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)) =
    oc.hom.app K ≫ localizingRefinementMap Λ hc
      ((detSfDerivedPullback Λ (pullback.fst f v)).obj K) := by
  have hb := local_refinement_pullback Λ v h oc od hoc hod K
  have he := refinement_triangle_comp Λ (pulledRefinement v h) hd hc esr
    ((detSfDerivedPullback Λ (pullback.fst f v)).obj K)
  exact refinement_pasting_algebra
    R(((pulledRefinement v h).hom.hom.hom)_*⟦Λ⟧) _ _ _ _ _ _ _ _ hb he

private def adjointNatural
    {C D : Type*} [Category* C] [Category* D]
    {J : C ⥤ D} {U : D ⥤ C} (a : J ⊣ U)
    (T : C ⥤ D) (g : 𝟭 C ⟶ T ⋙ U) : J ⟶ T :=
  (Functor.leftUnitor J).inv ≫ ((a.whiskerRight C).homEquiv (𝟭 C) T).symm g

private theorem adjointNatural_app
    {C D : Type*} [Category* C] [Category* D]
    {J : C ⥤ D} {U : D ⥤ C} (a : J ⊣ U)
    (T : C ⥤ D) (g : 𝟭 C ⟶ T ⋙ U) (K : C) :
    (adjointNatural a T g).app K = (a.homEquiv K (T.obj K)).symm (g.app K) := by
  simp [adjointNatural, Adjunction.homEquiv, Adjunction.whiskerRight]

private def refinementNatural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    D((c.obj.obj.i)_!open⟦Λ⟧) ⟶
      D((d.obj.obj.i)_!open⟦Λ⟧) ⋙ R((r.hom.hom.hom)_*⟦Λ⟧) := by
  let := refinementOpenRestriction_isIso Λ r
  let Jd := D((d.obj.obj.i)_!open⟦Λ⟧)
  let Rr := R((r.hom.hom.hom)_*⟦Λ⟧)
  let Uc := D((c.obj.obj.i)^*⟦Λ⟧)
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i
  let t := Functor.whiskerLeft Jd (refinementOpenRestriction Λ r.hom.hom)
  let g : 𝟭 _ ⟶ (Jd ⋙ Rr) ⋙ Uc :=
    b.unit ≫ (asIso t).inv ≫ (Functor.associator Jd Rr Uc).inv
  exact adjointNatural a (Jd ⋙ Rr) g

-- Compare adjuncts of the same inverse restriction and open unit.
private theorem refinementNatural_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (refinementNatural Λ r).app K = localizingRefinementMap Λ r K := by
  let := refinementOpenRestriction_isIso Λ r
  simp only [refinementNatural, adjointNatural_app, localizingRefinementMap,
    refinementTheta, Iso.trans_inv, Iso.symm_inv, asIso_hom, asIso_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, NatIso.isIso_inv_app,
    Functor.associator_inv_app, Category.comp_id, Functor.comp_obj]

-- Lift the proved component equation to natural transformations.
private theorem boundary_refinement_pasting_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (v : Y' ⟶ Y)
    (c d : Compactification.BoundaryCompactification f)
    (oc : D((c.obj.obj.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.obj.obj.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.obj.obj.baseChange v).i)_!open⟦Λ⟧))
    (od : D((d.obj.obj.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((d.obj.obj.baseChange v).i)_!open⟦Λ⟧))
    (hoc : oc.inv = detSfOpenBaseChangeMap Λ f v c.obj.obj)
    (hod : od.inv = detSfOpenBaseChangeMap Λ f v d.obj.obj)
    (h : d ⟶ c)
    (w : Compactification.BoundaryCompactification (pullback.snd f v))
    (hd : w ⟶ detSfBoundaryCompactification (d.obj.obj.baseChange v))
    (hc : w ⟶ detSfBoundaryCompactification (c.obj.obj.baseChange v))
    (esr : hd.hom.hom.hom ≫
        (pulledRefinement v h).hom.hom.hom =
      hc.hom.hom.hom) :
    let r := pulledRefinement v h
    let Jd := D((d.obj.obj.i)_!open⟦Λ⟧)
    let Jw := D((w.obj.obj.i)_!open⟦Λ⟧)
    let Rh := R((h.hom.hom.hom)_*⟦Λ⟧)
    let Rr := R((r.hom.hom.hom)_*⟦Λ⟧)
    let Rs := R((hd.hom.hom.hom)_*⟦Λ⟧)
    let Rt := R((hc.hom.hom.hom)_*⟦Λ⟧)
    let Vc := detSfDerivedPullback Λ (pullback.fst c.obj.obj.g v)
    let Vd := detSfDerivedPullback Λ (pullback.fst d.obj.obj.g v)
    let U := detSfDerivedPullback Λ (pullback.fst f v)
    let κ := compactSupportPushforwardTriangle Λ hd.hom.hom.hom r.hom.hom.hom
      hc.hom.hom.hom esr
    Functor.whiskerRight (refinementNatural Λ h) Vc ≫
      (Functor.associator Jd Rh Vc).hom ≫
      Functor.whiskerLeft Jd (pulledRefinementExchange Λ v h) ≫
      (Functor.associator Jd Vd Rr).inv ≫
      Functor.whiskerRight
        (od.hom ≫ Functor.whiskerLeft U (refinementNatural Λ hd) ≫
          (Functor.associator U Jw Rs).inv) Rr ≫
      (Functor.associator (U ⋙ Jw) Rs Rr).hom ≫
      Functor.whiskerLeft (U ⋙ Jw) κ.hom ≫
      (Functor.associator U Jw Rt).hom =
    oc.hom ≫ Functor.whiskerLeft U (refinementNatural Λ hc) := by
  apply NatTrans.ext
  funext K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, refinementNatural_app,
    Functor.comp_obj, Functor.map_comp, Functor.map_id, Category.id_comp,
    Category.comp_id, Category.assoc] using
    boundary_refinement_pasting Λ f v c d oc od hoc hod h w hd hc esr K

private theorem coefficient_components_of_natural_pasting
    {A0 A1 C0 D0 C1 D1 W : Type*}
    [Category* A0] [Category* A1] [Category* C0] [Category* D0]
    [Category* C1] [Category* D1] [Category* W]
    (Vc : C0 ⥤ C1) (Vd : D0 ⥤ D1) (U : A0 ⥤ A1)
    (Jc : A0 ⥤ C0) (Jd : A0 ⥤ D0) (Jc' : A1 ⥤ C1) (Jd' : A1 ⥤ D1)
    (Jw : A1 ⥤ W) (Rh : D0 ⥤ C0) (Rr : D1 ⥤ C1) (Rs : W ⥤ D1) (Rt : W ⥤ C1)
    (Eh : Jc ⟶ Jd ⋙ Rh) (Ehd : Jd' ⟶ Jw ⋙ Rs) (Ehc : Jc' ⟶ Jw ⋙ Rt)
    (oc : Jc ⋙ Vc ≅ U ⋙ Jc') (od : Jd ⋙ Vd ≅ U ⋙ Jd')
    (χ : Rh ⋙ Vc ⟶ Vd ⋙ Rr) (κ : Rs ⋙ Rr ≅ Rt)
    (eh : (K : A0) → Jc.obj K ⟶ Rh.obj (Jd.obj K))
    (ehd : (K : A1) → Jd'.obj K ⟶ Rs.obj (Jw.obj K))
    (ehc : (K : A1) → Jc'.obj K ⟶ Rt.obj (Jw.obj K))
    (hEh : Eh.app = eh) (hEhd : Ehd.app = ehd) (hEhc : Ehc.app = ehc)
    (hn : Functor.whiskerRight Eh Vc ≫
      (Functor.associator Jd Rh Vc).hom ≫ Functor.whiskerLeft Jd χ ≫
      (Functor.associator Jd Vd Rr).inv ≫
      Functor.whiskerRight
        (od.hom ≫ Functor.whiskerLeft U Ehd ≫ (Functor.associator U Jw Rs).inv) Rr ≫
      (Functor.associator (U ⋙ Jw) Rs Rr).hom ≫
      Functor.whiskerLeft (U ⋙ Jw) κ.hom ≫ (Functor.associator U Jw Rt).hom =
      oc.hom ≫ Functor.whiskerLeft U Ehc) (K : A0) :
    Vc.map (eh K) ≫ χ.app (Jd.obj K) ≫
      Rr.map (od.hom.app K ≫ ehd (U.obj K)) ≫ κ.hom.app (Jw.obj (U.obj K)) =
      oc.hom.app K ≫ ehc (U.obj K) := by
  have hh := NatTrans.congr_app hn K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    hEh, hEhd, hEhc, Functor.map_id, Category.id_comp, Category.comp_id] using hh

private theorem refinementNatural_apps
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    (refinementNatural Λ r).app = localizingRefinementMap Λ r := by
  funext K
  exact refinementNatural_app Λ r K

-- Kernel-checked structural congruence, following CoordinateSectionSiteTransport.
-- Reduce only identity and composite functors at object projections.
-- Other chosen derived functors stay folded during the structural congruence proof.
private meta def normalizeComparisonHeadAux (fuel : Nat) (e : Lean.Expr) :
    Lean.MetaM Lean.Expr := do
  let e ← Lean.instantiateMVars e
  match fuel with
  | 0 => pure e
  | n + 1 =>
    let e ← Lean.Meta.withReducible <| Lean.Meta.whnf e
    let f := e.getAppFn
    if f.isConstOf ``CategoryTheory.Functor.id || f.isConstOf ``CategoryTheory.Functor.comp then
      let f ← Lean.Meta.deltaExpand f fun name ↦
        name == ``CategoryTheory.Functor.id || name == ``CategoryTheory.Functor.comp
      normalizeComparisonHeadAux n (Lean.mkAppN f e.getAppArgs).headBeta
    else if let .proj structName idx arg := f then
      let arg' ← normalizeComparisonHeadAux n arg
      if arg' == arg then return e
      normalizeComparisonHeadAux n (Lean.mkAppN (.proj structName idx arg') e.getAppArgs)
    else
      pure e

private meta def normalizeComparisonHead (e : Lean.Expr) : Lean.MetaM Lean.Expr :=
  normalizeComparisonHeadAux 50 e

-- Build ordinary heterogeneous congruence proofs with every argument explicit.
-- Definitional equality of a whole chosen functor can otherwise unfold large localization data.
-- Only closed congruence proofs may be reused across local proof contexts.
private meta def structuralComparisonCongr
    (cache : IO.Ref (Array (Lean.Expr × Nat × Bool × Lean.Meta.CongrTheorem)))
    (fixIdentical : Bool) (fuel : Nat) (g : Lean.MVarId) :
    Lean.MetaM (List Lean.MVarId) := g.withContext do
  let g ← g.iffOfEq
  let ty ← Lean.instantiateMVars (← g.getType)
  if let some (_, a, b) := ty.consumeMData.eq? then
    if a.cleanupAnnotations == b.cleanupAnnotations then
      g.assign (← Lean.Meta.mkEqRefl a)
      return []
  if let some (_, a, _, b) := ty.consumeMData.heq? then
    if a.cleanupAnnotations == b.cleanupAnnotations then
      g.assign (← Lean.Meta.mkHEqRefl a)
      return []
  match fuel with
  | 0 => return [g]
  | n + 1 =>
    if ty.consumeMData.isForall then
      let (_, h) ← g.intro1
      return ← structuralComparisonCongr cache fixIdentical n h
    let goal ← g.eqOfHEq
    if ← goal.proofIrrelHeq then return []
    let gt ← Lean.instantiateMVars (← goal.getType)
    let some (_, lhs, _, rhs) := gt.consumeMData.heq? | return [goal]
    let lhs ← normalizeComparisonHead lhs.cleanupAnnotations
    let rhs ← normalizeComparisonHead rhs.cleanupAnnotations
    if lhs == rhs then
      goal.assign (← Lean.Meta.mkHEqRefl lhs)
      return []
    let goal ← Lean.Meta.withTransparency .default <|
      goal.change (← Lean.Meta.mkHEq lhs rhs)
    let xs := lhs.getAppArgs
    let ys := rhs.getAppArgs
    if xs.isEmpty || xs.size != ys.size then return [goal]
    let f := lhs.getAppFn
    let f' := rhs.getAppFn
    let info ← Lean.Meta.getFunInfoNArgs f xs.size
    let fixed := (xs.zip ys).map fun (x, y) ↦ fixIdentical && x == y
    let sameFun := f == f'
    let fType ← Lean.Meta.inferType f
    let saved ← cache.get
    let cthm ← match saved.find? (fun (t, k, same, _) ↦
        t == fType && k == xs.size && same == sameFun) with
      | some (_, _, _, cthm) => pure cthm
      | none =>
        let cthm ← Lean.Meta.mkRichHCongr (forceHEq := true) fType info
          (fixedFun := sameFun) (fixedParams := fixed)
        if !cthm.proof.hasFVar && !cthm.proof.hasMVar then
          cache.modify fun saved ↦ saved.push (fType, xs.size, sameFun, cthm)
        pure cthm
    let (ct, cp) := if sameFun then
      (cthm.type.bindingBody!.instantiate1 f, cthm.proof.beta #[f])
      else (cthm.type.bindingBody!.bindingBody!.instantiateRev #[f, f'],
        cthm.proof.beta #[f, f'])
    let goal ← goal.assert (← Lean.mkFreshUserName `structural_congr) ct cp
    let (id, goal) ← goal.intro1P
    let gs ← Lean.Meta.withReducible <|
      goal.apply (Lean.mkFVar id) {synthAssignedInstances := false}
    let mut rest := []
    for h in gs do
      let h ← h.tryClear id
      rest := rest ++ (← structuralComparisonCongr cache fixIdentical n h)
    return rest

end AlgebraicGeometry.ProEtale.CondensedRing
