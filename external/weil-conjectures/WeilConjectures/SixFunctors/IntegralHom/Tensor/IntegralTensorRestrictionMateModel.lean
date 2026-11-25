/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

import all WeilConjectures.Algebra.Homology.ScalarHomCancellation.ScalarHomTensorCancellation
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility
import all WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement

/-! # One-level representative formula for the tensor mate

Source: Stacks Project, Modules on Sites, Tag 03CZ, and Cohomology on Sites,
Tag 07A4; the coefficient calculation in the integral Verdier proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralHom.MateModel
private noncomputable instance (priority := 2000) fixedSmall (Y : Scheme.{u}) :
    EssentiallySmall.{u + 1} Y.ProEt :=
  integralReductionSiteEssentiallySmall.{u, u} Y

private noncomputable instance (priority := 2000) fixedSheafify (Y : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Y

private noncomputable instance (priority := 2000) fixedLocallyBijective (Y : Scheme.{u}) :
    (Scheme.ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Y

private noncomputable instance (priority := 2000) fixedDerived (Y : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    HasDerivedCategory (Modules.{u, u} Y R) := HasDerivedCategory.standard _

end WeilConjectures.IntegralHom.MateModel
/- The mate calculation below only uses naturality, adjunction identities,
   and cancellation of the comparison and resolution isomorphisms. -/
namespace GenericMate
variable {C D : Type*} [Category C] [Category D]
  (T : C × C ⥤ C) (S : D × D ⥤ D)
  (L : C ⥤ D) (U : D ⥤ C) (adj : L ⊣ U)
  (μ : T ⋙ L ≅ L.prod L ⋙ S)

private def mate (p q : C) :=
  adj.homEquiv _ _ (μ.hom.app (p, U.obj (L.obj q)) ≫
    S.map (Prod.mkHom (𝟙 (L.obj p)) (adj.counit.app (L.obj q))) ≫ μ.inv.app (p, q))

private theorem mate_precomp (p q s : C) (f : L.obj s ⟶ L.obj q) :
    T.map (Prod.mkHom (𝟙 p) (adj.homEquiv _ _ f)) ≫ mate T S L U adj μ p q =
      adj.homEquiv _ _ (μ.hom.app (p, s) ≫
        S.map (Prod.mkHom (𝟙 (L.obj p)) f) ≫ μ.inv.app (p, q)) := by
  rw [mate, ← adj.homEquiv_naturality_left]
  congr 1
  have h := μ.hom.naturality
    (Prod.mkHom (𝟙 p) (adj.homEquiv _ _ f))
  change L.map (T.map (Prod.mkHom (𝟙 p) (adj.homEquiv _ _ f))) ≫
    μ.hom.app (p, U.obj (L.obj q)) =
      μ.hom.app (p, s) ≫
        S.map (Prod.mkHom (L.map (𝟙 p)) (L.map (adj.homEquiv _ _ f))) at h
  rw [reassoc_of% h, L.map_id, ← S.map_comp_assoc]
  have hp : Prod.mkHom (𝟙 (L.obj p)) (L.map (adj.homEquiv _ _ f)) ≫
      Prod.mkHom (𝟙 (L.obj p)) (adj.counit.app (L.obj q)) =
        Prod.mkHom (𝟙 (L.obj p)) f := by
    apply Prod.ext
    · simp
    · change L.map (adj.homEquiv _ _ f) ≫ adj.counit.app (L.obj q) = f
      simpa only [Adjunction.homEquiv_counit] using
        (adj.homEquiv s (L.obj q)).symm_apply_apply f
  rw [hp]

private theorem mate_paste {p q s z x y v : C} {w w' : D}
    (eS : x ≅ T.obj (p, s)) (eQ : y ≅ T.obj (p, q)) (eZ : v ≅ T.obj (p, z))
    (c : U.obj (L.obj q) ≅ z) (t : s ⟶ z) [IsIso t]
    (a : x ⟶ v) (b : v ⟶ U.obj w')
    (cX : L.obj x ⟶ w) (cY : L.obj y ⟶ w')
    (f : L.obj s ⟶ L.obj q) (g : w ⟶ w')
    (ht : eS.hom ≫ T.map (Prod.mkHom (𝟙 p) t) = a ≫ eZ.hom)
    (hf : adj.homEquiv _ _ f = t ≫ c.inv)
    (hμ : L.map eS.hom ≫ μ.hom.app (p, s) ≫
      S.map (Prod.mkHom (𝟙 (L.obj p)) f) ≫ μ.inv.app (p, q) ≫
      L.map eQ.inv ≫ cY = cX ≫ g)
    (hg : adj.homEquiv _ _ (cX ≫ g) = a ≫ b) :
    T.map (Prod.mkHom (𝟙 p) c.hom) ≫ eZ.inv ≫ b =
      mate T S L U adj μ p q ≫ U.map (L.map eQ.inv) ≫ U.map cY := by
  have : IsIso (Prod.mkHom (𝟙 p) (t ≫ c.inv)) := by
    rw [isIso_prod_iff]
    exact ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (eS.hom ≫ T.map (Prod.mkHom (𝟙 p) (t ≫ c.inv)))).1
  simp only [Category.assoc]
  have hc : T.map (Prod.mkHom (𝟙 p) (t ≫ c.inv)) ≫
      T.map (Prod.mkHom (𝟙 p) c.hom) = T.map (Prod.mkHom (𝟙 p) t) := by
    rw [← T.map_comp]
    congr 1
    apply Prod.ext <;> simp
  rw [reassoc_of% hc, ← Category.assoc eS.hom, ht]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hf, reassoc_of% mate_precomp T S L U adj μ p q s f]
  have h := congrArg (adj.homEquiv x w') hμ
  have hg' := hg
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] at h hg' ⊢
  rw [adj.unit_naturality_assoc eS.hom] at h
  exact (h.trans hg').symm

private theorem normalize_conjugate
    {A : Type*} [Category A] (B : A × A ⥤ A)
    {p s q p' s' q' x y w w' : A}
    (aS : x ≅ B.obj (p, s)) (aQ : y ≅ B.obj (p, q))
    (cP : p ≅ p') (cS : s ≅ s') (cQ : q ≅ q')
    (dS : w ≅ B.obj (p', s')) (dQ : w' ≅ B.obj (p', q'))
    (cX : x ⟶ w) (cY : y ⟶ w') (t : s' ⟶ q')
    (hS : aS.hom ≫ B.map (Prod.mkHom cP.hom cS.hom) = cX ≫ dS.hom)
    (hQ : aQ.hom ≫ B.map (Prod.mkHom cP.hom cQ.hom) = cY ≫ dQ.hom) :
    aS.hom ≫ B.map (Prod.mkHom (𝟙 p) (cS.hom ≫ t ≫ cQ.inv)) ≫ aQ.inv ≫ cY =
      cX ≫ dS.hom ≫ B.map (Prod.mkHom (𝟙 p') t) ≫ dQ.inv := by
  apply (cancel_mono dQ.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hh : aQ.inv ≫ cY ≫ dQ.hom = B.map (Prod.mkHom cP.hom cQ.hom) := by
    rw [← hQ, Iso.inv_hom_id_assoc]
  rw [hh, ← B.map_comp]
  have hp : Prod.mkHom (𝟙 p) (cS.hom ≫ t ≫ cQ.inv) ≫
      Prod.mkHom cP.hom cQ.hom =
      Prod.mkHom cP.hom cS.hom ≫ Prod.mkHom (𝟙 p') t := by
    apply Prod.ext <;> simp
  rw [hp, B.map_comp, ← Category.assoc, hS, Category.assoc]

section Comparison
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (q : A ⥤ C) (r : B ⥤ D)
    (F : A ⥤ B) (V : B ⥤ A) (a : F ⊣ V)
    (L : C ⥤ D) (U : D ⥤ C) (adj : L ⊣ U)
    (e : q ⋙ L ⟶ F ⋙ r) (h : r ⋙ U ≅ V ⋙ q)

private theorem transpose_comparison (X : A) (Y : B) (f : F.obj X ⟶ Y)
    (hunit : adj.unit.app (q.obj X) ≫ U.map (e.app X) ≫ h.hom.app (F.obj X) =
      q.map (a.unit.app X)) :
    adj.homEquiv _ _ (e.app X ≫ r.map f) ≫ h.hom.app Y =
      q.map (a.homEquiv _ _ f) := by
  rw [Adjunction.homEquiv_unit, U.map_comp]
  simp only [Category.assoc]
  have hn := h.hom.naturality f
  change U.map (r.map f) ≫ h.hom.app Y =
    h.hom.app (F.obj X) ≫ q.map (V.map f) at hn
  rw [hn, reassoc_of% hunit, ← q.map_comp, Adjunction.homEquiv_unit]

private theorem transpose_iso_target (X Y : A) (f : F.obj X ⟶ F.obj Y)
    [IsIso (e.app Y)]
    (hunit : adj.unit.app (q.obj X) ≫ U.map (e.app X) ≫ h.hom.app (F.obj X) =
      q.map (a.unit.app X)) :
    adj.homEquiv _ _ (e.app X ≫ r.map f ≫ inv (e.app Y)) =
      q.map (a.homEquiv _ _ f) ≫
        (U.mapIso (asIso (e.app Y)) ≪≫ h.app (F.obj Y)).inv := by
  apply (Iso.eq_comp_inv (U.mapIso (asIso (e.app Y)) ≪≫ h.app (F.obj Y))).2
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, ← adj.homEquiv_naturality_right]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact transpose_comparison q r F V a L U adj e h X (F.obj Y) f hunit
end Comparison

private theorem tensor_representative_naturality_second
    (K : ObjectProperty C) (B : C ⥤ C ⥤ C) (q : C ⥤ D) (S : D × D ⥤ D)
    (rep : (K.ι.prod K.ι) ⋙ Functor.uncurry.obj B ⋙ q ≅
      (K.ι ⋙ q).prod (K.ι ⋙ q) ⋙ S)
    {P Z Q : C} (hP : K P) (hZ : K Z) (hQ : K Q) (f : Z ⟶ Q) :
    (rep.app (⟨P, hP⟩, ⟨Z, hZ⟩)).hom ≫
        S.map (Prod.mkHom (𝟙 (q.obj P)) (q.map f)) =
      q.map ((B.obj P).map f) ≫ (rep.app (⟨P, hP⟩, ⟨Q, hQ⟩)).hom := by
  have hn := rep.hom.naturality
    (X := (⟨P, hP⟩, ⟨Z, hZ⟩)) (Y := (⟨P, hP⟩, ⟨Q, hQ⟩))
    (𝟙 _, ObjectProperty.homMk f)
  change q.map ((B.map (𝟙 P)).app Z ≫ (B.obj P).map f) ≫ _ =
    _ ≫ S.map (Prod.mkHom (q.map (𝟙 P)) (q.map f)) at hn
  erw [B.map_id, NatTrans.id_app, Category.id_comp, q.map_id] at hn
  exact hn.symm

section Representatives
variable {A B : Type*} [Category A] [Category B]

private theorem representative_mate
    (q : A ⥤ C) (r : B ⥤ D)
    (F : A ⥤ B) (V : B ⥤ A) (a : F ⊣ V)
    (c : q ⋙ L ⟶ F ⋙ r) (h : r ⋙ U ≅ V ⋙ q)
    (P Q Z : A) (TP : A ⥤ A) (SP : B ⥤ B)
    (e : TP ⋙ q ≅ q ⋙ (Functor.curry.obj T).obj (q.obj P))
    (t : Z ⟶ V.obj (F.obj Q)) [IsIso (q.map t)]
    [IsIso (c.app P)] [IsIso (c.app Z)] [IsIso (c.app Q)]
    (b : TP.obj (V.obj (F.obj Q)) ⟶ V.obj (F.obj (TP.obj Q)))
    (βZ : SP.obj (F.obj Z) ⟶ F.obj (TP.obj Z)) [IsIso βZ]
    (βQ : SP.obj (F.obj Q) ⟶ F.obj (TP.obj Q)) [IsIso βQ]
    (aZ : q.obj (TP.obj Z) ≅ T.obj (q.obj P, q.obj Z))
    (aQ : q.obj (TP.obj Q) ≅ T.obj (q.obj P, q.obj Q))
    (heZ : e.hom.app Z = aZ.hom) (heQ : e.hom.app Q = aQ.hom)
    (dZ : r.obj (SP.obj (F.obj Z)) ≅ S.obj (r.obj (F.obj P), r.obj (F.obj Z)))
    (dQ : r.obj (SP.obj (F.obj Q)) ≅ S.obj (r.obj (F.obj P), r.obj (F.obj Q)))
    (hnZ : L.map aZ.hom ≫ μ.hom.app (q.obj P, q.obj Z) ≫
      S.map (Prod.mkHom (c.app P) (c.app Z)) ≫ dZ.inv ≫ r.map βZ = c.app (TP.obj Z))
    (hnQ : L.map aQ.hom ≫ μ.hom.app (q.obj P, q.obj Q) ≫
      S.map (Prod.mkHom (c.app P) (c.app Q)) ≫ dQ.inv ≫ r.map βQ = c.app (TP.obj Q))
    (hr : dZ.hom ≫ S.map
      (Prod.mkHom (𝟙 (r.obj (F.obj P))) (r.map ((a.homEquiv _ _).symm t))) =
        r.map (SP.map ((a.homEquiv _ _).symm t)) ≫ dQ.hom)
    (ho : a.homEquiv _ _ (inv βZ ≫ SP.map ((a.homEquiv _ _).symm t) ≫ βQ) =
      TP.map t ≫ b)
    (huZ : adj.unit.app (q.obj Z) ≫ U.map (c.app Z) ≫ h.hom.app (F.obj Z) =
      q.map (a.unit.app Z))
    (huTPZ : adj.unit.app (q.obj (TP.obj Z)) ≫ U.map (c.app (TP.obj Z)) ≫
      h.hom.app (F.obj (TP.obj Z)) = q.map (a.unit.app (TP.obj Z))) :
    T.map (Prod.mkHom (𝟙 (q.obj P)) (U.map (c.app Q) ≫ h.hom.app (F.obj Q))) ≫
      e.inv.app (V.obj (F.obj Q)) ≫ q.map b =
      mate T S L U adj μ (q.obj P) (q.obj Q) ≫ U.map (L.map (e.inv.app Q)) ≫
        U.map (c.app (TP.obj Q)) ≫ h.hom.app (F.obj (TP.obj Q)) := by
  let t' := (a.homEquiv Z (F.obj Q)).symm t
  let ψ := inv βZ ≫ SP.map t' ≫ βQ
  let eZ := L.mapIso (e.app Z) ≪≫ μ.app (q.obj P, q.obj Z)
  let eQ := L.mapIso (e.app Q) ≪≫ μ.app (q.obj P, q.obj Q)
  let kZ := (r.mapIso (asIso βZ)).symm ≪≫ dZ
  let kQ := (r.mapIso (asIso βQ)).symm ≪≫ dQ
  have hNZ : eZ.hom ≫ S.map (Prod.mkHom (c.app P) (c.app Z)) =
      c.app (TP.obj Z) ≫ kZ.hom := by
    have hh := congrArg (fun k ↦ k ≫ r.map (inv βZ) ≫ dZ.hom) hnZ
    rw [← heZ] at hh
    simpa only [eZ, kZ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.mapIso_inv, asIso_inv, Iso.app_hom, Category.assoc,
      ← r.map_comp_assoc, IsIso.hom_inv_id, r.map_id, Category.id_comp,
      Iso.inv_hom_id, Category.comp_id] using hh
  have hNQ : eQ.hom ≫ S.map (Prod.mkHom (c.app P) (c.app Q)) =
      c.app (TP.obj Q) ≫ kQ.hom := by
    have hh := congrArg (fun k ↦ k ≫ r.map (inv βQ) ≫ dQ.hom) hnQ
    rw [← heQ] at hh
    simpa only [eQ, kQ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.mapIso_inv, asIso_inv, Iso.app_hom, Category.assoc,
      ← r.map_comp_assoc, IsIso.hom_inv_id, r.map_id, Category.id_comp,
      Iso.inv_hom_id, Category.comp_id] using hh
  have hμ := normalize_conjugate S eZ eQ
    (asIso (c.app P)) (asIso (c.app Z)) (asIso (c.app Q))
    kZ kQ (c.app (TP.obj Z)) (c.app (TP.obj Q)) (r.map t') hNZ hNQ
  simp only [eZ, eQ, kZ, kQ, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, asIso_hom, asIso_inv, Category.assoc] at hμ
  erw [reassoc_of% hr, Iso.hom_inv_id_assoc] at hμ
  simp only [← r.map_comp] at hμ
  have hf := transpose_iso_target q r F V a L U adj c h Z Q t' huZ
  rw [(a.homEquiv Z (F.obj Q)).apply_symm_apply t] at hf
  have hg := transpose_comparison q r F V a L U adj c h
    (TP.obj Z) (F.obj (TP.obj Q)) ψ huTPZ
  have hg' : adj.homEquiv _ _ (c.app (TP.obj Z) ≫ r.map ψ) =
      q.map (TP.map t) ≫ q.map b ≫ h.inv.app (F.obj (TP.obj Q)) := by
    rw [ho, q.map_comp] at hg
    apply (cancel_mono (h.hom.app (F.obj (TP.obj Q)))).1
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app, Category.comp_id]
    exact hg
  have hn : (e.app Z).hom ≫ T.map (Prod.mkHom (𝟙 (q.obj P)) (q.map t)) =
      q.map (TP.map t) ≫ (e.app (V.obj (F.obj Q))).hom :=
    (e.hom.naturality t).symm
  have hh := mate_paste T S L U adj μ
    (e.app Z) (e.app Q) (e.app (V.obj (F.obj Q)))
    (U.mapIso (asIso (c.app Q)) ≪≫ h.app (F.obj Q)) (q.map t)
    (q.map (TP.map t)) (q.map b ≫ h.inv.app (F.obj (TP.obj Q)))
    (c.app (TP.obj Z)) (c.app (TP.obj Q))
    (c.app Z ≫ r.map t' ≫ inv (c.app Q)) (r.map ψ) hn hf hμ hg'
  have hh' := congrArg (fun k ↦ k ≫ h.hom.app (F.obj (TP.obj Q))) hh
  simp only [Category.assoc, Iso.inv_hom_id_app, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, Iso.app_hom, Iso.app_inv] at hh'
  erw [Category.comp_id] at hh'
  exact hh'

end Representatives

section Quotient
variable [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]

private theorem counit_quotient_eq
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    L.map ((DerivedCategory.quotientCompQhIso C).app P).inv ≫
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).app P).hom ≫
      ((DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom =
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
  change L.map (𝟙 _) ≫ ε.app _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  exact Category.comp_id _

private theorem restrictionFactors_quotient_eq
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]

end Quotient
end GenericMate

/- Compare the derived scalar counit and unit with their ordinary
   representatives, retaining the specified exact-restriction comparison. -/
namespace WeilConjectures.IntegralHom.MateDerived
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (n : ℕ)

private theorem reductionExtension_def :
    integralReductionChangeOfRings l E X D hl n = scalarReductionExtension l E X n := rfl

-- Comparing the quotient and coefficient wrappers needs additional elaboration time.
private def reductionNat :
    DerivedCategory.Q ⋙ scalarReductionDerivedExtension l E X n ⟶
      (scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (integralDerivedReduction l E X D hl n) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
      (integralDerivedReductionCounit l E X D hl n) ≫
    Functor.whiskerRight
      ((integralReductionChangeOfRings l E X D hl n).mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft
      ((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

-- Comparing the quotient and coefficient wrappers needs additional elaboration time.
private theorem reductionNat_app
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (reductionNat l E X D hl n).app P = reductionCounit l E X D hl n P := rfl

-- Comparing the quotient and coefficient wrappers needs additional elaboration time.
private theorem reductionCounit_isIso
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) P) :
    IsIso (reductionCounit l E X D hl n P) := by
  unfold reductionCounit
  exact IsIso.comp_isIso' (Functor.map_isIso _ _)
    (IsIso.comp_isIso' (integralDerivedReduction_counit_isIso l E X D hl n P hP)
      (IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance))

-- Comparing the quotient and coefficient wrappers needs additional elaboration time.
private theorem restrictionComparison_eq
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (scalarReductionDerivedRestriction l E X n).map (reductionCounit l E X D hl n P) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P) =
      sfReductionRepresentativeComparison l E X n P := by
  have hc : reductionCounit l E X D hl n P =
      (scalarReductionCounit l E X n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    unfold reductionCounit
    rw [GenericMate.counit_quotient_eq]
    rfl
  have hf := GenericMate.restrictionFactors_quotient_eq
    (scalarReductionRestriction l E X n)
    (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P)
  change _ = (scalarReductionDerivedRestriction l E X n).map
    ((scalarReductionCounit l E X n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ _
  exact congrArg₂ (fun f g ↦ (scalarReductionDerivedRestriction l E X n).map f ≫ g)
    hc hf.symm

-- Comparing the quotient and coefficient wrappers needs additional elaboration time.
private theorem unit_compatibility
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) P) :
    (derivedScalarExtensionRestrictionAdjunction l E X n).choose.unit.app
        (DerivedCategory.Q.obj P) ≫
      (scalarReductionDerivedRestriction l E X n).map
        ((reductionNat l E X D hl n).app P) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex
          (.up ℤ)).unit.app P) := by
  exact (congrArg (fun k ↦
    (derivedScalarExtensionRestrictionAdjunction l E X n).choose.unit.app
      (DerivedCategory.Q.obj P) ≫ k)
    (restrictionComparison_eq l E X D hl n P)).trans
      (sfUnitComparison l E X n P hP)

end WeilConjectures.IntegralHom.MateDerived

/- The coefficient comparison is built from scalar restriction commuting with
   sheafification. This is the construction used for ordinary tensor contraction
   (Stacks 05V4 and 07A4), with its action on pure sections proved here. -/
namespace WeilConjectures.IntegralHom.MateCoefficient
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

variable (X : Scheme.{u})
  (R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) (c : R ⟶ S)

private noncomputable abbrev forgetRing
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A

private noncomputable abbrev restriction :=
  SheafOfModules.restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)

private noncomputable abbrev coefficient : Modules.{u, u} X R :=
  (restriction X R S c).obj (SheafOfModules.unit (forgetRing X S))

private noncomputable local instance (priority := 3000) fixedSmall :
    EssentiallySmall.{u + 1} X.ProEt :=
  WeilConjectures.integralReductionSiteEssentiallySmall.{u, u} X

attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

attribute [local irreducible] SheafOfModules.monoidalCategory

private noncomputable def rawIso (M : Modules.{u, u} X R) :
    (PresheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c).hom).obj
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M) ≅
      (coefficient X R S c).val ⊗ M.val :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro U V f
    ext z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul s x =>
      exact (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap c M f) s x))

attribute [-instance] tensorLocalization abSheafify abLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall in
private noncomputable def coefficientIso (M : Modules.{u, u} X R) :
    (restriction X R S c).obj (SheafOfModules.changeOfRings.{u, u + 1, u + 1} c M) ≅
      ((ordinaryTensor.{u, u} X R).obj (coefficient X R S c)).obj M :=
  (SheafOfModules.ScalarHomCancellation.cancellationRestrictSheafifyIso
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M)).symm ≪≫
    (PresheafOfModules.sheafification.{u + 1} (𝟙 (forgetRing X R).obj)).mapIso
      (rawIso X R S c M) ≪≫
    (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
      (R := R) (coefficient X R S c) M).symm

-- Compare the scalar and module sheafifications explicitly.
attribute [-instance] tensorLocalization abSheafify abLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall in
private theorem coefficientIso_pure (M : Modules.{u, u} X R) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (coefficientIso X R S c M).hom.val.app U
      ((toSheafify (Scheme.ProEt.topology X)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M).presheaf).app U
          (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
      pair.{u, u} X R (coefficient X R S c) M U s x := by
  let A := forgetRing X R
  let B := forgetRing X S
  let α := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M
  let a := PresheafOfModules.sheafification.{u + 1} (𝟙 A.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 A.obj)
  let e := SheafOfModules.ScalarHomCancellation.cancellationRestrictSheafifyIso α P
  have he : e.hom.val.app U
      ((adj.unit.app ((PresheafOfModules.restrictScalars.{u + 1} α.hom).obj P)).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
      (toSheafify (Scheme.ProEt.topology X) P.presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x) := by
    have h := SheafOfModules.ScalarHomCancellation.cancellationRestrictSheafifyHom_toSheaf
      α P
    exact congrArg (fun f ↦ f.hom.app U
      ((toSheafify (Scheme.ProEt.topology X) P.presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))) h
  have hei : e.inv.val.app U
      ((toSheafify (Scheme.ProEt.topology X) P.presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
      (adj.unit.app ((PresheafOfModules.restrictScalars.{u + 1} α.hom).obj P)).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x) := by
    rw [← he]
    exact congrArg (fun f ↦ f.val.app U
      ((adj.unit.app ((PresheafOfModules.restrictScalars.{u + 1} α.hom).obj P)).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))) e.hom_inv_id
  change (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
    (R := R) (coefficient X R S c) M).inv.val.app U
    ((a.map (rawIso X R S c M).hom).val.app U (e.inv.val.app U _)) = _
  rw [hei]
  have hn := congrArg (fun f ↦ f.app U
    (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))
    (adj.unit.naturality (rawIso X R S c M).hom)
  exact congrArg ((SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
    (R := R) (coefficient X R S c) M).inv.val.app U) hn.symm

section Levels

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private noncomputable abbrev base := completedIntegralCommRingSheafUnrestricted l E X
private noncomputable abbrev level (n : ℕ) := integralCoefficientCommRingSheaf l E X n
private noncomputable abbrev projection (n : ℕ) :=
  completedIntegralCommRingProjectionUnrestricted l E X n
private noncomputable abbrev coeff (n : ℕ) :=
  coefficient X (base X l E) (level X l E n) (projection X l E n)

attribute [local irreducible] scalarReductionExistence
  completedIntegralCoefficientSheafUnrestricted constantSheaf
attribute [local implicit_reducible] scalarReductionExtension
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted

private noncomputable def levelIso (n : ℕ) (M : scalarReductionSource l E X) :
    (sfReductionRestricted l E X n).obj M ≅
      ((ordinaryTensor.{u, u} X (base X l E)).obj (coeff X l E n)).obj M :=
  (scalarReductionRestriction l E X n).mapIso
    (eqToIso ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose M)) ≪≫
    coefficientIso X (base X l E) (level X l E n) (projection X l E n) M

private theorem levelIso_pure (n : ℕ) (M : scalarReductionSource l E X)
    (U : X.ProEtᵒᵖ) (s : (level X l E n).obj.obj U) (x : M.val.obj U) :
    (levelIso X l E n M).hom.val.app U (sfReductionTensor l E X n M U s x) =
      pair.{u, u} X (base X l E) (coeff X l E n) M U s x := by
  let h := (scalarReductionExistence.{u, u} l E X n).choose_spec.choose M
  change (coefficientIso X (base X l E) (level X l E n)
    (projection X l E n) M).hom.val.app U
      (((eqToHom h.symm ≫ eqToHom h).val.app U) _) = _
  simp only [eqToHom_trans, eqToHom_refl]
  exact coefficientIso_pure X (base X l E) (level X l E n) (projection X l E n) M U s x

private theorem levelIso_inv_pure (n : ℕ) (M : scalarReductionSource l E X)
    (U : X.ProEtᵒᵖ) (s : (level X l E n).obj.obj U) (x : M.val.obj U) :
    (levelIso X l E n M).inv.val.app U
      (pair.{u, u} X (base X l E) (coeff X l E n) M U s x) =
      sfReductionTensor l E X n M U s x := by
  rw [← levelIso_pure X l E n M U s x]
  exact congrArg (fun f ↦ f.val.app U (sfReductionTensor l E X n M U s x))
    (levelIso X l E n M).hom_inv_id

end Levels
end WeilConjectures.IntegralHom.MateCoefficient

/- Extend the normalization from scalar generators to all local sections,
   then use total-summand extensionality to identify the ordinary transpose. -/
namespace WeilConjectures.IntegralHom.MateOrdinary

attribute [local irreducible] scalarReductionExistence constantSheaf
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  completedIntegralCommRingSheafUnrestricted

variable (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})

private def totalPairAdd (P Q : CochainComplex (Modules.{u, u} X R) ℤ)
    (i j : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X i).val.obj U) :
    (Q.X j).val.obj U →+
      ((((totalTensor.{u, u} X R).obj P).obj Q).X (i + j)).val.obj U where
  toFun := fun y ↦ totalPair.{u, u} X R P Q i j U x y
  map_zero' := by simp only [totalPair, pair, TensorProduct.tmul_zero, map_zero]
  map_add' := by
    intro y z
    simp only [totalPair, pair, TensorProduct.tmul_add, map_add]

private theorem totalPair_smul_right (P Q : CochainComplex (Modules.{u, u} X R) ℤ)
    (i j : ℤ) (U : X.ProEtᵒᵖ) (r : R.obj.obj U)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    totalPair.{u, u} X R P Q i j U x (r • y) =
      r • totalPair.{u, u} X R P Q i j U x y := by
  simp only [totalPair, pair, TensorProduct.tmul_smul, map_smul]

private theorem totalPair_restrict (P Q : CochainComplex (Modules.{u, u} X R) ℤ)
    (i j : ℤ) {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    ((((totalTensor.{u, u} X R).obj P).obj Q).X (i + j)).val.map f
        (totalPair.{u, u} X R P Q i j U x y) =
      totalPair.{u, u} X R P Q i j V
        ((P.X i).val.map f x) ((Q.X j).val.map f y) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := countableColimits.{u, u} X R
  let := ordinaryTensorZero.{u, u} X R
  let : ∀ M : Modules.{u, u} X R,
      ((ordinaryTensor.{u, u} X R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{u, u} X R M
  let ι := CochainComplex.ιMapBifunctor P Q (ordinaryTensor.{u, u} X R) i j (i + j) rfl
  exact (PresheafOfModules.naturality_apply ι.val f
    (pair.{u, u} X R (P.X i) (Q.X j) U x y)).symm.trans
      (congrArg (ι.val.app V)
        (CategoryTheory.CochainPullback.moduleTmul_restrict.{u + 1, u + 1, u}
          (P.X i) (Q.X j) f x y))

private theorem totalPair_map {P P' Q Q' : CochainComplex (Modules.{u, u} X R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (i j : ℤ) (U : X.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    ((((totalTensor.{u, u} X R).map f).app Q ≫
      ((totalTensor.{u, u} X R).obj P').map g).f (i + j)).val.app U
        (totalPair.{u, u} X R P Q i j U x y) =
      totalPair.{u, u} X R P' Q' i j U ((f.f i).val.app U x) ((g.f j).val.app U y) := by
  exact CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
    (J := Scheme.ProEt.topology X) f g i j (i + j) rfl U x y

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev B := completedIntegralCommRingSheafUnrestricted l E X
private abbrev S (n : ℕ) := integralCoefficientCommRingSheaf l E X n
private abbrev F (n : ℕ) :=
  (scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)
private abbrev U (n : ℕ) :=
  (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)

private theorem reduction_smul (n : ℕ) (M : scalarReductionSource l E X)
    (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V) (x : M.val.obj V) :
    sfReductionTensor l E X n M V s x = s • sfReductionTensor l E X n M V 1 x := by
  exact WeilConjectures.identifiedSection_smul
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (scalarReductionExtension l E X n)
    ((scalarReductionExistence l E X n).choose_spec.choose) M V s x

private theorem beta_scalar (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (beta : ((totalTensor.{u, u} X (S X l E n)).obj ((F X l E n).obj P)).obj
      ((F X l E n).obj Q) ⟶
      (F X l E n).obj (((totalTensor.{u, u} X (B X l E)).obj P).obj Q))
    (hbeta : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (beta.f (i + j)).val.app V
        (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
          i j V (sfReductionTensor l E X n (P.X i) V 1 x)
            (sfReductionTensor l E X n (Q.X j) V 1 y)) =
      sfReductionTensor l E X n _ V 1
        (totalPair.{u, u} X (B X l E) P Q i j V x y))
    (i j : ℤ) (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V)
    (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V) :
    (beta.f (i + j)).val.app V
      (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j V (sfReductionTensor l E X n (P.X i) V 1 x)
          (sfReductionTensor l E X n (Q.X j) V s y)) =
    sfReductionTensor l E X n _ V s
      (totalPair.{u, u} X (B X l E) P Q i j V x y) := by
  rw [reduction_smul X l E n (Q.X j) V s y]
  erw [totalPair_smul_right, map_smul, hbeta]
  exact (reduction_smul X l E n _ V s _).symm

-- The unit normalization crosses the finite coefficient wrappers.
private theorem unit_restrict (n : ℕ) (M : scalarReductionSource l E X)
    {V W : X.ProEtᵒᵖ} (i : V ⟶ W) (x : M.val.obj V) :
    ((scalarReductionExtension l E X n).obj M).val.map i
        (sfReductionTensor l E X n M V 1 x) =
      sfReductionTensor l E X n M W 1 (M.val.map i x) := by
  have hu (W : X.ProEtᵒᵖ) (y : M.val.obj W) :
      (((scalarReductionExtension_adjunction l E X n).choose.unit.app M).val.app W y) =
        sfReductionTensor l E X n M W 1 y :=
    (scalarReductionExtension_adjunction l E X n).choose_spec M W y
  exact (congrArg (((scalarReductionExtension l E X n).obj M).val.map i)
    (hu V x).symm).trans
      ((PresheafOfModules.naturality_apply
        ((scalarReductionExtension_adjunction l E X n).choose.unit.app M).val i x).symm.trans
          (hu W (M.val.map i x)))

private theorem beta_restricted (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (beta : ((totalTensor.{u, u} X (S X l E n)).obj ((F X l E n).obj P)).obj
      ((F X l E n).obj Q) ⟶
      (F X l E n).obj (((totalTensor.{u, u} X (B X l E)).obj P).obj Q))
    (b : ((totalTensor.{u, u} X (B X l E)).obj P).obj
        ((U X l E n).obj ((F X l E n).obj Q)) ⟶
      (U X l E n).obj ((F X l E n).obj
        (((totalTensor.{u, u} X (B X l E)).obj P).obj Q)))
    (hbeta : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (beta.f (i + j)).val.app V
        (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
          i j V (sfReductionTensor l E X n (P.X i) V 1 x)
            (sfReductionTensor l E X n (Q.X j) V s y)) =
      sfReductionTensor l E X n _ V s
        (totalPair.{u, u} X (B X l E) P Q i j V x y))
    (hb : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (b.f (i + j)).val.app V
        (totalPair.{u, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
          i j V x (sfReductionTensor l E X n (Q.X j) V s y)) =
      sfReductionTensor l E X n _ V s
        (totalPair.{u, u} X (B X l E) P Q i j V x y))
    (i j : ℤ) (V : X.ProEtᵒᵖ) (x : (P.X i).val.obj V)
    (z : (((F X l E n).obj Q).X j).val.obj V) :
    (beta.f (i + j)).val.app V
      (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j V (sfReductionTensor l E X n (P.X i) V 1 x) z) =
    (b.f (i + j)).val.app V
      (totalPair.{u, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
        i j V x z) := by
  let M : Modules.{u, u} X (B X l E) :=
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted l E X n))).obj
      (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S X l E n)))
  let H := ((U X l E n).obj ((F X l E n).obj
    (((totalTensor.{u, u} X (B X l E)).obj P).obj Q))).X (i + j)
  let e : (((U X l E n).obj ((F X l E n).obj Q)).X j) ≅
      ((ordinaryTensor.{u, u} X (B X l E)).obj M).obj (Q.X j) :=
    WeilConjectures.IntegralHom.MateCoefficient.levelIso X l E n (Q.X j)
  let f (W : X.ProEtᵒᵖ) (x : (P.X i).val.obj W) :=
    (beta.f (i + j)).val.app W |>.hom.toAddMonoidHom.comp
      ((totalPairAdd X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j W (sfReductionTensor l E X n (P.X i) W 1 x)).comp
          (e.inv.val.app W).hom.toAddMonoidHom)
  let g (W : X.ProEtᵒᵖ) (x : (P.X i).val.obj W) :=
    (b.f (i + j)).val.app W |>.hom.toAddMonoidHom.comp
      ((totalPairAdd X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
        i j W x).comp (e.inv.val.app W).hom.toAddMonoidHom)
  have hf {V W : X.ProEtᵒᵖ} (a : V ⟶ W) (x : (P.X i).val.obj V) (z) :
      H.val.map a (f V x z) =
        f W ((P.X i).val.map a x) (((ordinaryTensor.{u, u} X (B X l E)).obj M).obj
          (Q.X j) |>.val.map a z) := by
    have hn := (PresheafOfModules.naturality_apply (beta.f (i + j)).val a
      (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j V (sfReductionTensor l E X n (P.X i) V 1 x) (e.inv.val.app V z))).symm
    have hp := totalPair_restrict X (S X l E n)
      ((F X l E n).obj P) ((F X l E n).obj Q) i j a
      (sfReductionTensor l E X n (P.X i) V 1 x) (e.inv.val.app V z)
    have hu := unit_restrict X l E n (P.X i) a x
    have he := (PresheafOfModules.naturality_apply e.inv.val a z).symm
    exact hn.trans (congrArg ((beta.f (i + j)).val.app W)
      (hp.trans (congrArg₂
        (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
          i j W) hu he)))
  have hg {V W : X.ProEtᵒᵖ} (a : V ⟶ W) (x : (P.X i).val.obj V) (z) :
      H.val.map a (g V x z) =
        g W ((P.X i).val.map a x) (((ordinaryTensor.{u, u} X (B X l E)).obj M).obj
          (Q.X j) |>.val.map a z) := by
    have hn := (PresheafOfModules.naturality_apply (b.f (i + j)).val a
      (totalPair.{u, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
        i j V x (e.inv.val.app V z))).symm
    have hp := totalPair_restrict X (B X l E)
      P ((U X l E n).obj ((F X l E n).obj Q)) i j a x (e.inv.val.app V z)
    have he := (PresheafOfModules.naturality_apply e.inv.val a z).symm
    exact hn.trans (congrArg ((b.f (i + j)).val.app W)
      (hp.trans (congrArg
        (totalPair.{u, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
          i j W ((P.X i).val.map a x)) he)))
  have hp (W : X.ProEtᵒᵖ) (x : (P.X i).val.obj W)
      (s : M.val.obj W) (y : (Q.X j).val.obj W) :
      f W x (pair.{u, u} X (B X l E) M (Q.X j) W s y) =
        g W x (pair.{u, u} X (B X l E) M (Q.X j) W s y) := by
    change (beta.f (i + j)).val.app W
      (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j W (sfReductionTensor l E X n (P.X i) W 1 x) (e.inv.val.app W _)) =
      (b.f (i + j)).val.app W
        (totalPair.{u, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
          i j W x (e.inv.val.app W _))
    have hc : e.inv.val.app W (pair.{u, u} X (B X l E) M (Q.X j) W s y) =
        sfReductionTensor l E X n (Q.X j) W s y :=
      WeilConjectures.IntegralHom.MateCoefficient.levelIso_inv_pure
        X l E n (Q.X j) W s y
    have hleft := congrArg (fun z ↦ (beta.f (i + j)).val.app W
      (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j W (sfReductionTensor l E X n (P.X i) W 1 x) z)) hc
    have hright := congrArg (fun z ↦ (b.f (i + j)).val.app W
      (totalPair.{u, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
        i j W x z)) hc
    exact (hleft.trans (hbeta i j W s x y)).trans
      (hright.trans (hb i j W s x y)).symm
  have hh := WeilConjectures.pure_local_ext (B X l E) M (Q.X j) H
    ((P.X i).val.presheaf) f g hf hg hp V x (e.hom.val.app V z)
  have he : e.inv.val.app V (e.hom.val.app V z) = z := by
    have hh := congrArg (fun f ↦
      fun w : ((((U X l E n).obj ((F X l E n).obj Q)).X j).val.obj V) ↦
        f.val.app V w) e.hom_inv_id
    exact congrFun hh z
  change (beta.f (i + j)).val.app V
      (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j V (sfReductionTensor l E X n (P.X i) V 1 x)
          (e.inv.val.app V (e.hom.val.app V z))) =
    (b.f (i + j)).val.app V
      (totalPair.{u, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
        i j V x (e.inv.val.app V (e.hom.val.app V z))) at hh
  rw [he] at hh
  exact hh

private theorem totalPair_map_second
    {P Q Q' : CochainComplex (Modules.{u, u} X R) ℤ}
    (g : Q ⟶ Q') (i j : ℤ) (V : X.ProEtᵒᵖ)
    (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V) :
    ((((totalTensor.{u, u} X R).obj P).map g).f (i + j)).val.app V
        (totalPair.{u, u} X R P Q i j V x y) =
      totalPair.{u, u} X R P Q' i j V x ((g.f j).val.app V y) := by
  simpa using totalPair_map X R (𝟙 P) g i j V x y

private theorem ordinary_square (n : ℕ)
    (P Q Z : CochainComplex (scalarReductionSource l E X) ℤ)
    (t : Z ⟶ (U X l E n).obj ((F X l E n).obj Q))
    (betaZ : ((totalTensor.{u, u} X (S X l E n)).obj ((F X l E n).obj P)).obj
      ((F X l E n).obj Z) ⟶
      (F X l E n).obj (((totalTensor.{u, u} X (B X l E)).obj P).obj Z))
    [IsIso betaZ]
    (betaQ : ((totalTensor.{u, u} X (S X l E n)).obj ((F X l E n).obj P)).obj
      ((F X l E n).obj Q) ⟶
      (F X l E n).obj (((totalTensor.{u, u} X (B X l E)).obj P).obj Q))
    (b : ((totalTensor.{u, u} X (B X l E)).obj P).obj
        ((U X l E n).obj ((F X l E n).obj Q)) ⟶
      (U X l E n).obj ((F X l E n).obj
        (((totalTensor.{u, u} X (B X l E)).obj P).obj Q)))
    (hZ : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj V) (z : (Z.X j).val.obj V),
      (betaZ.f (i + j)).val.app V
        (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Z)
          i j V (sfReductionTensor l E X n (P.X i) V 1 x)
            (sfReductionTensor l E X n (Z.X j) V 1 z)) =
      sfReductionTensor l E X n _ V 1
        (totalPair.{u, u} X (B X l E) P Z i j V x z))
    (hQ : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (betaQ.f (i + j)).val.app V
        (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
          i j V (sfReductionTensor l E X n (P.X i) V 1 x)
            (sfReductionTensor l E X n (Q.X j) V 1 y)) =
      sfReductionTensor l E X n _ V 1
        (totalPair.{u, u} X (B X l E) P Q i j V x y))
    (hb : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (b.f (i + j)).val.app V
        (totalPair.{u, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
          i j V x (sfReductionTensor l E X n (Q.X j) V s y)) =
      sfReductionTensor l E X n _ V s
        (totalPair.{u, u} X (B X l E) P Q i j V x y)) :
    let adj := (scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex (.up ℤ)
    let t' := (adj.homEquiv _ _).symm t
    adj.homEquiv _ _ (inv betaZ ≫
        ((totalTensor.{u, u} X (S X l E n)).obj ((F X l E n).obj P)).map t' ≫ betaQ) =
      ((totalTensor.{u, u} X (B X l E)).obj P).map t ≫ b := by
  dsimp only
  let adj := (scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex (.up ℤ)
  let t' := (adj.homEquiv _ _).symm t
  rw [Adjunction.homEquiv_unit]
  ext k : 1
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u}
    P Z k _
  intro i j hij V x z
  subst k
  have hu (M : scalarReductionSource l E X) (V : X.ProEtᵒᵖ) (x : M.val.obj V) :
      ((scalarReductionExtension_adjunction l E X n).choose.unit.app M).val.app V x =
        sfReductionTensor l E X n M V 1 x :=
    (scalarReductionExtension_adjunction l E X n).choose_spec M V x
  have ht := congrArg (fun a ↦ (a.f j).val.app V z)
    ((adj.homEquiv _ _).apply_symm_apply t)
  change (t'.f j).val.app V
      (((scalarReductionExtension_adjunction l E X n).choose.unit.app (Z.X j)).val.app V z) =
    (t.f j).val.app V z at ht
  rw [hu] at ht
  have hz := congrArg (fun a ↦ (inv betaZ).f (i + j) |>.val.app V a) (hZ i j V x z)
  have hi (a) : ((inv betaZ).f (i + j)).val.app V ((betaZ.f (i + j)).val.app V a) = a :=
    ConcreteCategory.congr_hom
      (congrArg (fun f ↦ (f.f (i + j)).val.app V) (asIso betaZ).hom_inv_id) a
  rw [hi] at hz
  change (betaQ.f (i + j)).val.app V
      (((((totalTensor.{u, u} X (S X l E n)).obj ((F X l E n).obj P)).map t').f
        (i + j)).val.app V
        (((inv betaZ).f (i + j)).val.app V
          (((scalarReductionExtension_adjunction l E X n).choose.unit.app
            ((((totalTensor.{u, u} X (B X l E)).obj P).obj Z).X (i + j))).val.app V
              (totalPair.{u, u} X (B X l E) P Z i j V x z)))) =
    (b.f (i + j)).val.app V
      (((((totalTensor.{u, u} X (B X l E)).obj P).map t).f (i + j)).val.app V
        (totalPair.{u, u} X (B X l E) P Z i j V x z))
  rw [hu, ← hz, totalPair_map_second, totalPair_map_second]
  erw [ht]
  exact beta_restricted X l E n P Q betaQ b
    (beta_scalar X l E n P Q betaQ hQ) hb i j V x ((t.f j).val.app V z)

private theorem ordinary_square_reductionUnits
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (n : ℕ)
    (P Q Z : CochainComplex (scalarReductionSource l E X) ℤ)
    (t : Z ⟶ (U X l E n).obj ((F X l E n).obj Q))
    (betaZ : ((totalTensor.{u, u} X (S X l E n)).obj ((F X l E n).obj P)).obj
      ((F X l E n).obj Z) ⟶
      (F X l E n).obj (((totalTensor.{u, u} X (B X l E)).obj P).obj Z))
    [IsIso betaZ]
    (betaQ : ((totalTensor.{u, u} X (S X l E n)).obj ((F X l E n).obj P)).obj
      ((F X l E n).obj Q) ⟶
      (F X l E n).obj (((totalTensor.{u, u} X (B X l E)).obj P).obj Q))
    (b : ((totalTensor.{u, u} X (B X l E)).obj P).obj
        ((U X l E n).obj ((F X l E n).obj Q)) ⟶
      (U X l E n).obj ((F X l E n).obj
        (((totalTensor.{u, u} X (B X l E)).obj P).obj Q)))
    (hZ : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj V) (z : (Z.X j).val.obj V),
      (betaZ.f (i + j)).val.app V
        (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Z)
          i j V ((reductionUnit l E X D hl n (P.X i)).val.app V x)
            ((reductionUnit l E X D hl n (Z.X j)).val.app V z)) =
      (reductionUnit l E X D hl n _).val.app V
        (totalPair.{u, u} X (B X l E) P Z i j V x z))
    (hQ : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (betaQ.f (i + j)).val.app V
        (totalPair.{u, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
          i j V ((reductionUnit l E X D hl n (P.X i)).val.app V x)
            ((reductionUnit l E X D hl n (Q.X j)).val.app V y)) =
      (reductionUnit l E X D hl n _).val.app V
        (totalPair.{u, u} X (B X l E) P Q i j V x y))
    (hb : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (b.f (i + j)).val.app V
        (totalPair.{u, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
          i j V x (sfReductionTensor l E X n (Q.X j) V s y)) =
      sfReductionTensor l E X n _ V s
        (totalPair.{u, u} X (B X l E) P Q i j V x y)) :
    let adj := (scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex (.up ℤ)
    let t' := (adj.homEquiv _ _).symm t
    adj.homEquiv _ _ (inv betaZ ≫
        ((totalTensor.{u, u} X (S X l E n)).obj ((F X l E n).obj P)).map t' ≫ betaQ) =
      ((totalTensor.{u, u} X (B X l E)).obj P).map t ≫ b := by
  have hu (M : completedIntegralModuleSheaves l E X D hl) (W : X.ProEtᵒᵖ)
      (x : M.val.obj W) :
      (reductionUnit l E X D hl n M).val.app W x = sfReductionTensor l E X n M W 1 x :=
    (scalarReductionExtension_adjunction l E X n).choose_spec M W x
  simp only [hu] at hZ hQ
  exact ordinary_square X l E n P Q Z t betaZ betaQ b hZ hQ hb

end WeilConjectures.IntegralHom.MateOrdinary

namespace WeilConjectures.IntegralHom

namespace MateModel

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

private def extendIso
    {A B E K : Type*} [Category A] [Category B] [Category E] [Category K]
    (W : MorphismProperty A) (q : A ⥤ B) [q.IsLocalization W]
    (I : K ⥤ A) [(I ⋙ q).IsLocalization (W.inverseImage I)]
    (F : B ⥤ E) (H : A ⥤ E) (hH : W.IsInvertedBy H)
    (e : I ⋙ H ≅ I ⋙ q ⋙ F) :
    { c : H ≅ q ⋙ F // ∀ X, c.app (I.obj X) = e.app X } := by
  let H' := Localization.lift H hH q
  let φ := Localization.fac H hH q
  let b : (I ⋙ q) ⋙ H' ≅ (I ⋙ q) ⋙ F := Functor.isoWhiskerLeft I φ ≪≫ e
  let ff := Localization.fullyFaithfulWhiskeringLeft (I ⋙ q) (W.inverseImage I) E
  let b' := ff.preimageIso b
  refine ⟨φ.symm ≪≫ Functor.isoWhiskerLeft q b', ?_⟩
  intro X
  apply Iso.ext
  have hb := congr_app (ff.map_preimage b.hom) X
  change φ.inv.app (I.obj X) ≫ b'.hom.app (q.obj (I.obj X)) = (e.app X).hom
  rw [show b'.hom.app (q.obj (I.obj X)) = b.hom.app X from hb]
  simp [b]

variable (Y : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})

private theorem tensor_inverts (P : CochainComplex (Modules.{u, u} Y R) ℤ)
    (hP : flat.{u, u} Y R P) :
    (HomologicalComplex.quasiIso (Modules.{u, u} Y R) (.up ℤ)).IsInvertedBy
      ((totalTensor.{u, u} Y R).obj P ⋙ DerivedCategory.Q) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let : MonoidalCategory (Modules.{u, u} Y R) := SheafOfModules.monoidalCategory R
  let : MonoidalPreadditive (Modules.{u, u} Y R) :=
    SheafOfModules.cochainModulesPreadditive R
  have hk := (HomotopyCategory.kFlat_quotient_obj_iff P).1
    (CategoryTheory.RingedDerivedNative.kFlat.{u + 1, u, u} (Scheme.ProEt.topology Y) R P hP)
  intro A B f hf
  change IsIso (DerivedCategory.Q.map (((totalTensor.{u, u} Y R).obj P).map f))
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  exact hk.1 f hf

private theorem comparison_exists (a : TensorPresentation.{u, u} Y R)
    (P : CochainComplex (Modules.{u, u} Y R) ℤ) (hP : flat.{u, u} Y R P) :
    ∃ e : (totalTensor.{u, u} Y R).obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (Functor.curry.obj a.tensor).obj (DerivedCategory.Q.obj P),
      ∀ (Q : CochainComplex (Modules.{u, u} Y R) ℤ) (hQ : flat.{u, u} Y R Q),
        e.hom.app Q = a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) := by
  let I := (flat.{u, u} Y R).ι
  let A := (Functor.curry.obj a.tensor).obj (DerivedCategory.Q.obj P)
  let H := (totalTensor.{u, u} Y R).obj P ⋙ DerivedCategory.Q
  let e : I ⋙ H ≅ I ⋙ DerivedCategory.Q ⋙ A :=
    NatIso.ofComponents (fun Q ↦ a.representative.app (⟨P, hP⟩, Q)) (by
      intro Q Q' f
      have h := a.representative.hom.naturality
        (X := (⟨P, hP⟩, Q)) (Y := (⟨P, hP⟩, Q')) (𝟙 _, f)
      simpa [I, H, A, totalTensor] using h)
  let : (I ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (Modules.{u, u} Y R) (.up ℤ)).inverseImage I) :=
    CategoryTheory.RingedDerivedNative.kFlatLocalization.{u + 1, u, u, u + 2}
      (Scheme.ProEt.topology Y) R
  let c := extendIso (HomologicalComplex.quasiIso (Modules.{u, u} Y R) (.up ℤ))
    DerivedCategory.Q I A H (tensor_inverts Y R P hP) e
  refine ⟨c.val, ?_⟩
  intro Q hQ
  exact congrArg Iso.hom (c.property ⟨Q, hQ⟩)

end MateModel

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

attribute [-instance] MateModel.fixedSmall MateModel.fixedSheafify
  MateModel.fixedLocallyBijective MateModel.fixedDerived

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  integralReductionExistence integralReductionDerivedExistence constantSheaf
  completedIntegralCoefficientSheafUnrestricted HasDerivedCategory.standard

attribute [local implicit_reducible] completedIntegralCommRingSheaf
  completedIntegralCommRingSheafUnrestricted integralCoefficientCommRingSheaf
  integralCoefficientSheaf

-- Keep the coefficient wrappers folded while elaborating the comparison squares.
/-- The scalar-adjunction tensor mate is represented by the ordinary contraction.
This is a one-level calculation: no consecutive quotient map occurs in it.

Source: Stacks 03CZ, lemma-adjointness-tensor-restrict; 06YY,
lemma-derived-base-change; 07A4, lemma-pullback-tensor-product.

Proof: fix the K-flat first factor P. Tensoring with P sends acyclic complexes
to acyclic complexes, hence preserves quasi-isomorphisms, by the native K-flat
tensor API. Extend a.representative in the second argument along the K-flat
localization. This gives e, natural on all complexes, with its prescribed value
on K-flat Q. To calculate the mate, resolve the restricted extension of Q by a
K-flat complex S. Use naturality to replace e there by its value on S. Transpose
through the scalar adjunction. Its ordinary counit multiplies scalar factors.
ReductionPresentation.normalization fixes the two tensor comparisons on the
K-flat pairs (P, S) and (P, Q). Cancel these comparisons and the resolution of S.
On each homogeneous pure tensor the resulting chain map sends
x tensor (s tensor y) to s tensor (x tensor y). Thus it is b by the tensor
universal property, sheafification, and total-summand extensionality. Localize
this identity. The restriction comparison is the exact-restriction factor of
the scalar counit, giving precisely the displayed equation. The construction
of e is independent of the coefficient level; the calculation applies separately
to every n and every normalized m, so it assumes no compatibility between them.
(blueprint: lem-sf-integral-tensor-restriction-mate-model). -/
theorem restrictionTensor_mate_model
    (a : TensorPresentation.{u, u} X (completedIntegralCommRingSheaf l E X D hl))
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) P) :
    let R := completedIntegralCommRingSheafUnrestricted l E X
    let F := fun n : ℕ ↦ (sfReductionRestricted l E X n).mapHomologicalComplex (.up ℤ)
    let T := totalTensor.{u, u} X R
    let A := (Functor.curry.obj a.tensor).obj (DerivedCategory.Q.obj P)
    ∃ e : (T.obj P) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ A,
      (∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
          (hQ : flat.{u, u} X R Q),
        e.hom.app Q = a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) ∧
      ∀ (n : ℕ) (m : ReductionPresentation l E X D hl a n)
          (b : ∀ Q : CochainComplex (scalarReductionSource l E X) ℤ,
            (T.obj P).obj ((F n).obj Q) ⟶ (F n).obj ((T.obj P).obj Q)),
        (∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
            (i j : ℤ) (U : X.ProEtᵒᵖ)
            (s : (integralCoefficientCommRingSheaf l E X n).obj.obj U)
            (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
          ((b Q).f (i + j)).val.app U
              (totalPair.{u, u} X R P ((F n).obj Q) i j U x
                (sfReductionTensor l E X n (Q.X j) U s y)) =
            sfReductionTensor l E X n (((T.obj P).obj Q).X (i + j)) U s
              (totalPair.{u, u} X R P Q i j U x y)) →
        ∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
            (_hQ : flat.{u, u} X R Q),
          A.map (sfReductionRepresentativeComparison l E X n Q) ≫
              e.inv.app ((F n).obj Q) ≫ DerivedCategory.Q.map (b Q) =
            (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.homEquiv _ _
              (m.mu.hom.app (DerivedCategory.Q.obj P,
                  (sfDerivedReductionRestricted l E X n).obj (DerivedCategory.Q.obj Q)) ≫
                m.target.tensor.map
                  (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj
                    (DerivedCategory.Q.obj P)))
                    ((derivedScalarExtensionRestrictionAdjunction.{u, u}
                      l E X n).choose.counit.app
                        ((scalarReductionDerivedExtension l E X n).obj
                          (DerivedCategory.Q.obj Q)))) ≫
                m.mu.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
              (sfDerivedReductionRestricted l E X n).map (e.inv.app Q) ≫
              sfReductionRepresentativeComparison l E X n ((T.obj P).obj Q) := by
  classical
  let : EssentiallySmall.{u + 1} X.ProEt := MateModel.fixedSmall X
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    MateModel.fixedSheafify X
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    MateModel.fixedLocallyBijective X
  let : HasDerivedCategory (scalarReductionSource.{u, u} l E X) :=
    HasDerivedCategory.standard _
  dsimp only
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let q := @DerivedCategory.Q (scalarReductionSource.{u, u} l E X) _ _
    (HasDerivedCategory.standard _)
  let T := totalTensor.{u, u} X R
  let A := (Functor.curry.obj a.tensor).obj (q.obj P)
  let a₀ : TensorPresentation.{u, u} X R := a
  have hP₀ : flat.{u, u} X R P := hP
  have hh := MateModel.comparison_exists.{u} X R a₀ P hP₀
  obtain ⟨e, he⟩ := hh
  refine ⟨e, he, ?_⟩
  intro n m b hb Q hQ
  let : HasDerivedCategory (scalarReductionTarget.{u, u} l E X n) :=
    HasDerivedCategory.standard _
  let S := integralCoefficientCommRingSheaf l E X n
  let r := @DerivedCategory.Q (scalarReductionTarget.{u, u} l E X n) _ _
    (HasDerivedCategory.standard _)
  let F := (scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)
  let U := (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)
  let L := scalarReductionDerivedExtension l E X n
  let V := scalarReductionDerivedRestriction l E X n
  let adj := (derivedScalarExtensionRestrictionAdjunction l E X n).choose
  let adj₀ := (scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex (.up ℤ)
  let c : q ⋙ L ⟶ F ⋙ r := MateDerived.reductionNat l E X D hl n
  let h := (scalarReductionRestriction l E X n).mapDerivedCategoryFactors
  let TP := T.obj P
  let T' := (totalTensor.{u, u} X S).obj (F.obj P)
  let G : CochainComplex (Modules.{u, u} X R) ℤ := U.obj (F.obj Q)
  have hres := CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
    (C := X.ProEt) (J := Scheme.ProEt.topology X) (R := R) G
  obtain ⟨Z, t, hZ, _, ht, _⟩ := hres
  have : IsIso (q.map t) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Modules.{u, u} X R) t).2 ht
  have hcP : IsIso (c.app P) := by
    simpa only [c, MateDerived.reductionNat_app] using
      (MateDerived.reductionCounit_isIso l E X D hl n P hP)
  have hcZ : IsIso (c.app Z) := by
    simpa only [c, MateDerived.reductionNat_app] using
      (MateDerived.reductionCounit_isIso l E X D hl n Z hZ)
  have hcQ : IsIso (c.app Q) := by
    simpa only [c, MateDerived.reductionNat_app] using
      (MateDerived.reductionCounit_isIso l E X D hl n Q hQ)
  let t' : F.obj Z ⟶ F.obj Q := (adj₀.homEquiv Z (F.obj Q)).symm t
  have hZ₀ : flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) Z := hZ
  have normZ := m.normalization P Z hP hZ₀
  dsimp only [MateDerived.reductionExtension_def] at normZ
  obtain ⟨hFP, hFZ, betaZ₀, hiZ₀, hbZ, hnZ⟩ := normZ
  have hQ₀ : flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) Q := hQ
  have normQ := m.normalization P Q hP hQ₀
  dsimp only [MateDerived.reductionExtension_def] at normQ
  obtain ⟨hFP', hFQ, betaQ₀, hiQ₀, hbQ, hnQ⟩ := normQ
  let betaZ := betaZ₀
  let betaQ := betaQ₀
  have hiZ : IsIso betaZ := hiZ₀
  have hiQ : IsIso betaQ := hiQ₀
  have ho :=
    MateOrdinary.ordinary_square_reductionUnits X l E D hl n P Q Z t betaZ betaQ
      (b Q) hbZ hbQ (hb Q)
  let repZ := m.target.representative.app (⟨F.obj P, hFP⟩, ⟨F.obj Z, hFZ⟩)
  let repQ := m.target.representative.app (⟨F.obj P, hFP'⟩, ⟨F.obj Q, hFQ⟩)
  have hr' := GenericMate.tensor_representative_naturality_second
    (flat.{u, u} X S) (totalTensor.{u, u} X S) r m.target.tensor
    m.target.representative hFP hFZ hFQ t'
  have hTPZ : flat.{u, u} X R (TP.obj Z) :=
    coefficientTotalTensor_isKFlat.{u, u + 1, u} (Scheme.ProEt.topology X) R P Z hP hZ
  have hm := GenericMate.representative_mate a.tensor m.target.tensor L V adj m.mu
    q r F U adj₀ c h P Q Z TP T' e t (b Q) betaZ betaQ
    (a.representative.app (⟨P, hP⟩, ⟨Z, hZ⟩))
    (a.representative.app (⟨P, hP⟩, ⟨Q, hQ⟩)) (he Z hZ) (he Q hQ) repZ repQ
  -- Rewrite the counit wrapper before matching the concrete normalization proofs.
  simp only [c, MateDerived.reductionNat_app] at hm
  have huZ := MateDerived.unit_compatibility l E X D hl n Z hZ
  have huTPZ := MateDerived.unit_compatibility l E X D hl n (TP.obj Z)
    hTPZ
  simp only [MateDerived.reductionNat_app] at huZ huTPZ
  have hh := hm hnZ hnQ hr' ho huZ huTPZ
  have hc (K : CochainComplex (scalarReductionSource l E X) ℤ) :
      V.map (reductionCounit l E X D hl n K) ≫ h.hom.app (F.obj K) =
        sfReductionRepresentativeComparison l E X n K :=
    MateDerived.restrictionComparison_eq l E X D hl n K
  rw [hc Q, hc (TP.obj Q)] at hh
  exact hh

end WeilConjectures.IntegralHom
