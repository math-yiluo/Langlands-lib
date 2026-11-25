/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization

set_option linter.privateModule false

/-! # Restriction of the specified open scalar comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem transportRestriction_open
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (e' : B ≌ D) (J : A ⥤ B) (R : B ⥤ A)
    (F : C ⥤ D) (Q : D ⥤ C)
    (d : J ⋙ e'.functor ≅ e.functor ⋙ F)
    (p : R ⋙ e.functor ≅ e'.functor ⋙ Q)
    (r : J ⋙ R ≅ 𝟭 A) (rho : F ⋙ Q ≅ 𝟭 C)
    (h : ∀ M, Q.map (d.hom.app M) ≫ rho.hom.app (e.functor.obj M) =
      p.inv.app (J.obj M) ≫ e.functor.map (r.hom.app M)) (M : A) :
    (scalarSixTransportRestriction e e' F R Q p rho).hom.app M =
      R.map ((scalarSixTransportOpen e e' J F d).hom.app M) ≫ r.hom.app M := by
  let o := scalarSixTransportOpen e e' J F d
  have ho : e'.functor.map (o.hom.app M) =
      e'.counitIso.hom.app (F.obj (e.functor.obj M)) ≫ d.inv.app M := by
    dsimp only [o, scalarSixTransportOpen, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    simp only [Category.comp_id, Functor.map_comp]
    erw [e'.functor.map_id, Category.comp_id]
    have ht : e'.functor.map (e'.unitIso.inv.app (J.obj M)) =
        e'.counitIso.hom.app (e'.functor.obj (J.obj M)) := by
      apply (cancel_epi (e'.counitIso.inv.app (e'.functor.obj (J.obj M)))).mp
      simpa only [Functor.id_obj, Iso.inv_hom_id_app] using e'.counitInv_functor_comp (J.obj M)
    rw [ht]
    exact e'.counitIso.hom.naturality (d.inv.app M)
  have hi : Q.map (d.inv.app M) ≫ p.inv.app (J.obj M) ≫
      e.functor.map (r.hom.app M) = rho.hom.app (e.functor.obj M) := by
    rw [← h, ← Q.map_comp_assoc, Iso.inv_hom_id_app, Q.map_id, Category.id_comp]
  have hp := p.hom.naturality (o.hom.app M)
  simp only [Functor.comp_map] at hp
  have ht : e.functor.map (R.map (o.hom.app M) ≫ r.hom.app M) =
      p.hom.app ((e.functor ⋙ F ⋙ e'.inverse).obj M) ≫
        Q.map (e'.counitIso.hom.app (F.obj (e.functor.obj M))) ≫
          rho.hom.app (e.functor.obj M) := by
    rw [Functor.map_comp]
    rw [← Iso.hom_inv_id_app_assoc p (J.obj M) (e.functor.map (r.hom.app M)),
      ← Category.assoc, hp, ho, Q.map_comp]
    simp only [Category.assoc, hi]
  simp only [scalarSixTransportRestriction, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc]
  erw [e.inverse.map_id, Category.id_comp]
  rw [← e.inverse.map_comp_assoc, ← e.inverse.map_comp_assoc]
  simp only [Category.assoc]
  erw [← ht]
  have hn := e.unitIso.hom.naturality (R.map (o.hom.app M) ≫ r.hom.app M)
  simp only [Functor.id_map, Functor.comp_map] at hn
  erw [← reassoc_of% hn, Iso.hom_inv_id_app, Category.comp_id]

private abbrev localizedRho
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) (R : B ⥤ A) [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (rho : F ⋙ R ≅ 𝟭 A) :=
  Functor.mapDerivedCategoryCompNatIso rho ≪≫ Functor.mapDerivedCategoryIdIso A

private theorem localizedRestrictionSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (J : A ⥤ B) (R : B ⥤ A) (F : C ⥤ D) (Q : D ⥤ C)
    (e : A ⥤ C) (e' : B ⥤ D)
    [J.Additive] [R.Additive] [F.Additive] [Q.Additive] [e.Additive] [e'.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits e] [PreservesFiniteColimits e]
    [PreservesFiniteLimits e'] [PreservesFiniteColimits e']
    (r : J ⋙ R ≅ 𝟭 A) (rho : F ⋙ Q ≅ 𝟭 C)
    (d : J ⋙ e' ≅ e ⋙ F) (p : R ⋙ e ≅ e' ⋙ Q)
    (hq : ∀ M, e.map (r.inv.app M) ≫ p.hom.app (J.obj M) ≫ Q.map (d.hom.app M) =
      rho.inv.app (e.obj M)) (M : DerivedCategory A) :
    Q.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso d).hom.app M) ≫
        (localizedRho F Q rho).hom.app (e.mapDerivedCategory.obj M) =
      (Functor.mapDerivedCategorySquareIso p).inv.app (J.mapDerivedCategory.obj M) ≫
        e.mapDerivedCategory.map ((localizedRho J R r).hom.app M) := by
  let z : (𝟭 A) ⋙ e ≅ e ⋙ (𝟭 C) := Iso.refl e
  have h := Functor.exactSquare_comp_forward J R (𝟭 A) F Q (𝟭 C) e e' e
    d p z r.symm rho.symm (by
      intro N
      change e.map (r.inv.app N) ≫ p.hom.app (J.obj N) ≫ Q.map (d.hom.app N) =
        𝟙 (e.obj N) ≫ rho.inv.app (e.obj N)
      erw [Category.id_comp]
      exact hq N) M
  have hz : (Functor.mapDerivedCategorySquareIso z).hom.app M ≫
      (Functor.mapDerivedCategoryIdIso C).hom.app (e.mapDerivedCategory.obj M) =
      e.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso A).hom.app M) := by
    have hc := congr_app (Functor.mapDerivedCategoryCompIso_comp_id e) M
    have ha := congr_app (Functor.mapDerivedCategoryCompIso_id_comp e) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.id_app] at hc ha
    dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app]
    have hz0 : (Functor.mapDerivedCategoryNatIso z).hom = 𝟙 _ :=
      Functor.mapDerivedCategoryNatIso_refl
    rw [hz0]
    simp only [NatTrans.id_app, Category.id_comp, Category.assoc, hc]
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (𝟭 A) e).inv.app M)).mp
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Category.comp_id] using ha.symm
  have hi (L : DerivedCategory A) :
      (Functor.mapDerivedCategoryNatIso r.symm ≪≫
          (Functor.mapDerivedCategoryCompIso J R).symm).hom.app L =
        (Functor.mapDerivedCategoryIdIso A).hom.app L ≫
          (localizedRho J R r).inv.app L := by
    simp only [localizedRho, Functor.mapDerivedCategoryCompNatIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      Functor.mapDerivedCategoryNatIso_symm, Iso.hom_inv_id_app_assoc]
  have hj (L : DerivedCategory C) :
      (Functor.mapDerivedCategoryNatIso rho.symm ≪≫
          (Functor.mapDerivedCategoryCompIso F Q).symm).hom.app L =
        (Functor.mapDerivedCategoryIdIso C).hom.app L ≫
          (localizedRho F Q rho).inv.app L := by
    simp only [localizedRho, Functor.mapDerivedCategoryCompNatIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      Functor.mapDerivedCategoryNatIso_symm, Iso.hom_inv_id_app_assoc]
  rw [hi, hj, e.mapDerivedCategory.map_comp, Category.assoc,
    ← Category.assoc ((Functor.mapDerivedCategorySquareIso z).hom.app M), hz] at h
  have hh := (cancel_epi
    (e.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso A).hom.app M))).mp h
  have he := congrArg (fun t ↦
    (Functor.mapDerivedCategorySquareIso p).inv.app (J.mapDerivedCategory.obj M) ≫
      e.mapDerivedCategory.map ((localizedRho J R r).hom.app M) ≫ t ≫
      (localizedRho F Q rho).hom.app (e.mapDerivedCategory.obj M)) hh
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app] at he
  erw [e.mapDerivedCategory.map_id] at he
  simpa only [Functor.id_obj, Functor.comp_obj, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Category.comp_id] using he

private def openRho (Λ : ScalarSixRing.{u}) {S X : Scheme.{u}} (j : S ⟶ X)
    [IsOpenImmersion j] :
    openImmersionLowerShriek Λ.X j ⋙ upperStar Λ.X j ≅ 𝟭 _ := by
  letI : IsCommMonObj Λ.X := Λ.comm
  let adj := openImmersionLowerShriekUpperStarAdjunction Λ.X j
  have : IsIso adj.unit := openUnit Λ.X j
  exact (asIso adj.unit).symm

-- Keep the concrete derived models folded during transport.
private theorem restriction_localized (E : LocallyClosedExtensionData.{u})
    (D : E.DerivedCoherence) {S X : LocallyClosedCoefficients.{u}}
    (b : LocallyClosedCoefficientImmersion S X) :
    D.restriction b = localizedRho (E.extension b) b.pull (E.restriction b) := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (proEtaleRingModules S.scheme S.ring) (.up ℤ))
  intro K
  exact (D.restrictionTermwise b K).trans (E.restrictionTermwise b K).symm

-- Keep the concrete derived models folded during transport.
private theorem openRestriction
    (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) {k : Type u} [Field k]
    (O : ScalarSixOpenComparison E G k) (Λ : ScalarSixRing.{u})
    {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)) :
    (scalarSixRestriction E D G Λ j).hom.app M =
      (scalarSixPull Λ j.left).map ((scalarSixOpenIso E G O Λ j).hom.app M) ≫
        (localizedRho (openImmersionLowerShriek Λ.X j.left) (upperStar Λ.X j.left)
          (openRho Λ j.left)).hom.app M := by
  letI : IsCommMonObj Λ.X := Λ.comm
  let b := scalarSixImmersion G Λ j
  letI := E.additive b
  letI := E.finiteLimits b
  letI := E.finiteColimits b
  let e := ModuleRingedComparison.equivalence Λ.X S.left
  let e' := ModuleRingedComparison.equivalence Λ.X X.left
  letI : e.functor.Additive := scalarSixEquivalenceAdditive Λ S.left
  letI : e.inverse.Additive := scalarSixEquivalenceInverseAdditive Λ S.left
  letI : e'.functor.Additive := scalarSixEquivalenceAdditive Λ X.left
  letI : e'.inverse.Additive := scalarSixEquivalenceInverseAdditive Λ X.left
  let J := openImmersionLowerShriek Λ.X j.left
  let R := upperStar Λ.X j.left
  let adj := openImmersionLowerShriekUpperStarAdjunction Λ.X j.left
  have hrho (N) : (E.restriction b).inv.app N =
      (E.openAdjunction b (inferInstanceAs (IsOpenImmersion j.left))).unit.app N := by
    apply (cancel_mono ((E.restriction b).hom.app N)).mp
    rw [Iso.inv_hom_id_app]
    exact (E.openNormalization b (inferInstanceAs (IsOpenImmersion j.left)) N).symm
  have hq (N) : e.functor.map ((openRho Λ j.left).inv.app N) ≫
      (G.pull Λ j.left).hom.app (J.obj N) ≫ b.pull.map ((O.comparison Λ j).hom.app N) =
        (E.restriction b).inv.app (e.functor.obj N) := by
    have hh := unit_mateEquiv adj
      (E.openAdjunction b (inferInstanceAs (IsOpenImmersion j.left)))
      (.mk _ _ _ _ (O.comparison Λ j).inv) N
    change e.functor.map (adj.unit.app N) ≫
        (mateEquiv adj (E.openAdjunction b
          (inferInstanceAs (IsOpenImmersion j.left)))
          (.mk _ _ _ _ (O.comparison Λ j).inv)).app (J.obj N) =
      (E.openAdjunction b (inferInstanceAs (IsOpenImmersion j.left))).unit.app
        (e.functor.obj N) ≫ b.pull.map ((O.comparison Λ j).inv.app N) at hh
    rw [O.normalization] at hh
    change e.functor.map (adj.unit.app N) ≫ _ ≫ _ = _
    rw [← Category.assoc, hh, Category.assoc, ← b.pull.map_comp,
      Iso.inv_hom_id_app]
    erw [b.pull.map_id, Category.comp_id, hrho]
  have hs := localizedRestrictionSquare J R (E.extension b) b.pull e.functor e'.functor
    (openRho Λ j.left) (E.restriction b) (O.comparison Λ j) (G.pull Λ j.left) hq
  have ht := transportRestriction_open e.mapDerivedCategory e'.mapDerivedCategory
    J.mapDerivedCategory R.mapDerivedCategory (E.extension b).mapDerivedCategory
    b.pull.mapDerivedCategory (Functor.mapDerivedCategorySquareIso (O.comparison Λ j))
    (Functor.mapDerivedCategorySquareIso (G.pull Λ j.left))
    (localizedRho J R (openRho Λ j.left))
    (localizedRho (E.extension b) b.pull (E.restriction b)) hs M
  change (scalarSixTransportRestriction _ _ _ _ _ _ (D.restriction b)).hom.app M = _
  rw [restriction_localized]
  exact ht

end AlgebraicGeometry.ProEtale.CondensedRing
