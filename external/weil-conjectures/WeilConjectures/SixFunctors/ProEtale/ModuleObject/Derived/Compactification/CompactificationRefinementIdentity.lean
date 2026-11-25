/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
/-!
# Identity refinement on dense compactifications

The categorical derived unit law and the existing normalized open refinement identity
identify the actual compactification refinement component with the identity.
Source: blueprint main-20261015, proposition-construction-independence-rf-shriek, proof step 4
(blueprint: lem-sfb-compactification-refinement-component-id).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe v w u
namespace RefinementId
variable {C D : Type u} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [HasKInjectiveResolutions C]
private noncomputable def did : (𝟭 C).rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso C
private theorem did_fac (K : HomotopyCategory C (.up ℤ)) :
    (𝟭 C).rightDerivedFunctorUnit.app K ≫ (did (C := C)).hom.app
        (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom.app K) := by
  have h := congrArg (fun e ↦ e.hom.app K) (Functor.mapDerivedCategoryIdIso_factorsh C)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app] at h
  dsimp only [did, Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc]
  have hh := NatTrans.congr_app (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hh
  erw [Category.comp_id, Category.comp_id] at h
  rw [hh, h, Iso.inv_hom_id_app_assoc]

private noncomputable def derivedId (F : C ⥤ C) [F.Additive] (e : F ≅ 𝟭 C) :
    F.rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  Functor.rightDerivedFunctorNatIso e ≪≫ did

private theorem derivedId_fac (F : C ⥤ C) [F.Additive] (e : F ≅ 𝟭 C)
    (K : HomotopyCategory C (.up ℤ)) :
    F.rightDerivedFunctorUnit.app K ≫ (derivedId F e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  have h := NatTrans.congr_app (Functor.rightDerivedNatTrans_fac
    F.rightDerivedFunctor (𝟭 C).rightDerivedFunctor
    F.rightDerivedFunctorUnit (𝟭 C).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
      DerivedCategory.Qh)) K
  dsimp only [derivedId, Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc]
  change _ ≫ (did (C := C)).hom.app _ = _
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  change F.rightDerivedFunctorUnit.app K ≫
    (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj K) = _ at h
  erw [h, Category.assoc, did_fac, Functor.mapHomotopyCategoryIdIso_hom_app_eq_id,
    DerivedCategory.Qh.map_id, Category.comp_id]

private theorem derivedId_inv_app (F : C ⥤ C) [F.Additive] (e : F ≅ 𝟭 C)
    (K : HomotopyCategory C (.up ℤ)) :
    (derivedId F e).inv.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app K) ≫
        F.rightDerivedFunctorUnit.app K := by
  rw [← cancel_mono ((derivedId F e).hom.app (DerivedCategory.Qh.obj K)),
    Iso.inv_hom_id_app, Category.assoc, derivedId_fac,
    ← DerivedCategory.Qh.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  exact (DerivedCategory.Qh.map_id _).symm

private theorem derivedId_comp (F : C ⥤ C) (G : C ⥤ D) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes]
    (i : F ≅ 𝟭 C) (e : F ⋙ G ≅ G)
    (he : Functor.whiskerRight i.inv G ≫ e.hom = 𝟙 G) :
    Functor.whiskerRight (derivedId F i).inv G.rightDerivedFunctor ≫
        (Functor.rightDerivedFunctorCompIso' F G e).hom =
      𝟙 G.rightDerivedFunctor := by
  refine Functor.rightDerived_ext G.rightDerivedFunctor G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ)) _ _ _ ?_
  ext K : 2
  have hnat := G.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory i.inv (.up ℤ)).app K)
  have hfac : Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
        DerivedCategory.Qh ≫ G.rightDerivedFunctorUnit := by
    have hcomp : (F ⋙ G).rightDerivedFunctorUnit ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.rightDerivedFunctorCompIso F G).hom =
        Functor.rightDerivedFunctorCompUnit F G := by
      simp [Functor.rightDerivedFunctorCompIso]
    rw [← hcomp, Category.assoc, ← Functor.whiskerLeft_comp]
    simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
    rw [Iso.hom_inv_id_assoc]
    exact Functor.rightDerivedNatTrans_fac _ _ _ _
      (HomotopyCategory.quasiIso C (.up ℤ)) _
  have hfac2 := NatTrans.congr_app hfac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hfac2 ⊢
  rw [derivedId_inv_app, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_map] at hnat
  erw [← reassoc_of% hnat]
  dsimp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hfac2
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hfac2
  have hid : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) K
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  erw [hid, DerivedCategory.Qh.map_id] at hfac2
  erw [Category.id_comp] at hfac2
  erw [hfac2, ← DerivedCategory.Qh.map_comp_assoc]
  have hcomp : (G.mapHomotopyCategory (.up ℤ)).map
      ((NatTrans.mapHomotopyCategory i.inv (.up ℤ)).app K) ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K = 𝟙 _ := by
    change (NatTrans.mapHomotopyCategory (Functor.whiskerRight i.inv G) (.up ℤ)).app K ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K = _
    erw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, he,
      NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
    rfl
  erw [hcomp, DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id]

private theorem derive_trans {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (e : F ≅ G) (e' : G ≅ H) :
    (Functor.rightDerivedFunctorNatIso (e ≪≫ e')).hom =
      (Functor.rightDerivedFunctorNatIso e).hom ≫
        (Functor.rightDerivedFunctorNatIso e').hom := by
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    ← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp]

private theorem derive_eqToIso {α : Type*} (κ : α → C ⥤ D)
    [∀ a, (κ a).Additive] {a b : α} (h : a = b) :
    (Functor.rightDerivedFunctorNatIso (eqToIso (congrArg κ h))).hom =
      (eqToIso (congrArg (fun a ↦ (κ a).rightDerivedFunctor) h)).hom := by
  cases h
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]

end RefinementId

open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
private theorem refinement_comp_id (S T : Scheme.{u}) (g : S ⟶ T) :
    Functor.whiskerRight (refinementDerivedLowerStarId Λ S).inv
        (lowerStar Λ g).rightDerivedFunctor ≫
      (refinementDerivedLowerStarComp Λ (𝟙 S) g).inv ≫
      (eqToIso (congrArg (fun g ↦ (lowerStar Λ g).rightDerivedFunctor)
        (Category.id_comp g))).hom = 𝟙 (lowerStar Λ g).rightDerivedFunctor := by
  let F := lowerStar Λ (𝟙 S)
  let G := lowerStar Λ g
  let e : F ⋙ G ≅ G := lowerStarComp Λ (𝟙 S) g ≪≫ lowerStarCongr Λ (Category.id_comp g)
  have hi : refinementLowerStarId Λ S = lowerStarId Λ S := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply Mod.hom_ext
    rfl
  have he : Functor.whiskerRight (refinementLowerStarId Λ S).inv G ≫ e.hom = 𝟙 G := by
    dsimp only [e]
    rw [hi, lowerStarComp_id_left]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Category.assoc]
    rw [← Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id]
    ext M
    simp [G, lowerStarCongr]
    rfl
  let := (upperStarLowerStarAdjunction Λ (𝟙 S)).preservesKInjectiveComplexes
  have h := RefinementId.derivedId_comp F G (refinementLowerStarId Λ S) e he
  have htrans := RefinementId.derive_trans (lowerStarComp Λ (𝟙 S) g)
    (lowerStarCongr Λ (Category.id_comp g))
  have heq : (Functor.rightDerivedFunctorNatIso
      (lowerStarCongr Λ (Category.id_comp g))).hom =
      (eqToIso (congrArg (fun g ↦ (lowerStar Λ g).rightDerivedFunctor)
        (Category.id_comp g))).hom := by
    exact RefinementId.derive_eqToIso (lowerStar Λ) (Category.id_comp g)
  dsimp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom] at h
  dsimp only [e] at h
  rw [htrans, heq] at h
  simpa only [RefinementId.derivedId, RefinementId.did, refinementDerivedLowerStarId,
    refinementDerivedLowerStarComp, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
    Functor.rightDerivedFunctorNatIso, Functor.whiskerRight_comp, Category.assoc,
    Iso.symm_hom, F, G] using h

private theorem identityOfNormalized {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h : localizingRefinementMap Λ (𝟙 c) K ≫
        (refinementDerivedLowerStarId Λ c.obj.obj.Z).hom.app
          ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K) = 𝟙 _) :
    compactificationRefinementComponent Λ (𝟙 c) K = 𝟙 _ := by
  let J := (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K
  have hmap : localizingRefinementMap Λ (𝟙 c) K =
      (refinementDerivedLowerStarId Λ c.obj.obj.Z).inv.app J := by
    apply (cancel_mono ((refinementDerivedLowerStarId Λ c.obj.obj.Z).hom.app J)).1
    rw [h, Iso.inv_hom_id_app]
    rfl
  unfold compactificationRefinementComponent
  rw [show (Functor.rightDerivedFunctorNatIso
      (lowerStarCongr Λ (Category.id_comp c.obj.obj.g))).hom =
      (eqToIso (congrArg (fun g ↦ (lowerStar Λ g).rightDerivedFunctor)
        (Category.id_comp c.obj.obj.g))).hom from
    RefinementId.derive_eqToIso (lowerStar Λ) (Category.id_comp c.obj.obj.g)]
  change (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map
      (localizingRefinementMap Λ (𝟙 c) K) ≫
      (refinementDerivedLowerStarComp Λ (𝟙 c.obj.obj.Z) c.obj.obj.g).inv.app J ≫
      (eqToIso (congrArg (fun g ↦ (lowerStar Λ g).rightDerivedFunctor)
        (Category.id_comp c.obj.obj.g))).hom.app J = 𝟙 _
  rw [hmap]
  exact congrArg (fun q ↦ q.app J) (refinement_comp_id Λ c.obj.obj.Z Y c.obj.obj.g)
/-- The canonical refinement component of a dense identity compactification is the identity.

Source: blueprint main-20261015, proposition-construction-independence-rf-shriek, proof step 4,
and proposition-construction-independence-rf-shriek--7, clause (3)
(blueprint: lem-sfb-compactification-refinement-component-id).

Proof: The identity clause of localizingRefinement_coherence identifies the normalized
open refinement arrow with the inverse canonical derived identity comparison. The derived
compositor for identity followed by the proper map cancels this comparison: test the
natural-transformation equality against the right-derived-functor unit, use naturality,
and then the underived left unit law lowerStarComp_id_left. The derived universal property
makes this test injective. Apply that natural equality to j!K, and substitute the normalized
open arrow. The final structural equality is Category.id_comp. This argument works for
every ambient unbounded K; no localizing-membership hypothesis is needed. -/
theorem compactificationRefinementComponent_id
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification.DenseBoundaryCompactification f)
    (K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    compactificationRefinementComponent Λ (𝟙 c.obj) K = 𝟙 _ := by
  have h := (localizingRefinement_coherence Λ ℓ k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) hΛ f).2.2.1 c K
  exact identityOfNormalized Λ c.obj K h

end AlgebraicGeometry.ProEtale.CondensedRing
