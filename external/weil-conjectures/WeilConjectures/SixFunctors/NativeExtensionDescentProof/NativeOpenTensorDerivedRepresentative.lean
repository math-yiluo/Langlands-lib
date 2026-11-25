/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
import Mathlib.CategoryTheory.Localization.Prod

/-! # Descending an open tensor comparison with its representative square

Source: Stacks 06YN and 0GL1; the universal property of localization.
(blueprint: lem-sf-native-open-tensor-derived-representative)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace NativeExtensionDescentProof

attribute [local instance] OpenTensorDescentInput.e_add OpenTensorDescentInput.r_add
  OpenTensorDescentInput.e_lim OpenTensorDescentInput.e_colim
  OpenTensorDescentInput.r_lim OpenTensorDescentInput.r_colim
  OpenTensorDescentInput.e_zero OpenTensorDescentInput.r_zero

/-- Descent along the full K-flat localizations retains every representative square.

Source: Stacks 06YN and 0GL1; Mathlib's fully faithful localization precomposition.
(blueprint: lem-sf-native-open-tensor-derived-representative)

Proof: restrict the two complexes to their full K-flat subcategories. Naturality
of the fixed tensor models assembles their components into natural isomorphisms.
Compose the extension factorization, ambient tensor model, quotient of the total
comparison, inverse extension factorization, inverse open tensor model, and inverse
restriction factorization. The product of the two quotient localizations is a
localization. Fully faithful precomposition therefore descends this isomorphism.
Evaluate its defining preimage equation at any two K-flat representatives. The
inverse model and factorization pairs cancel and give the claimed square. -/
theorem native_open_tensor_derived_representative
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    (hE : ∀ P, c.flatA P → c.flatB ((c.E.mapHomologicalComplex (.up ℤ)).obj P))
    (hR : ∀ T, c.flatB T → c.flatA ((c.R.mapHomologicalComplex (.up ℤ)).obj T))
    (hnA : ∀ P P' T T' (hP : c.flatA P) (hP' : c.flatA P')
      (hT : c.flatA T) (hT' : c.flatA T') (f : P ⟶ P') (g : T ⟶ T'),
      c.DA.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (m.modelA P' T' hP' hT').hom =
        (m.modelA P T hP hT).hom ≫ DerivedCategory.Q.map
          (((c.TA.map f).app T) ≫ (c.TA.obj P').map g))
    (hnB : ∀ P P' T T' (hP : c.flatB P) (hP' : c.flatB P')
      (hT : c.flatB T) (hT' : c.flatB T') (f : P ⟶ P') (g : T ⟶ T'),
      c.DB.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (m.modelB P' T' hP' hT').hom =
        (m.modelB P T hP hT).hom ≫ DerivedCategory.Q.map
          (((c.TB.map f).app T) ≫ (c.TB.obj P').map g))
    (g : (c.E.mapHomologicalComplex (.up ℤ)).prod (𝟭 _) ⋙
        Functor.uncurry.obj c.TB ≅
      (𝟭 _).prod (c.R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj c.TA ⋙ c.E.mapHomologicalComplex (.up ℤ))
    [((ObjectProperty.ι c.flatA) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso A (.up ℤ)).inverseImage (ObjectProperty.ι c.flatA))]
    [((ObjectProperty.ι c.flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso B (.up ℤ)).inverseImage (ObjectProperty.ι c.flatB))] :
    ∃ gamma : c.E.mapDerivedCategory.prod (𝟭 _) ⋙ c.DB ≅
        (𝟭 _).prod c.R.mapDerivedCategory ⋙ c.DA ⋙ c.E.mapDerivedCategory,
      OpenTensorRepresentativeNormalization c.E c.R c.TA c.TB c.DA c.DB
        c.flatA c.flatB hE hR m.modelA m.modelB (fun P T ↦ g.app (P, T)) gamma := by
  let iA := ObjectProperty.ι c.flatA
  let iB := ObjectProperty.ι c.flatB
  let qA := iA ⋙ DerivedCategory.Q
  let qB := iB ⋙ DerivedCategory.Q
  let WA := (HomologicalComplex.quasiIso A (.up ℤ)).inverseImage iA
  let WB := (HomologicalComplex.quasiIso B (.up ℤ)).inverseImage iB
  let Ec := c.E.mapHomologicalComplex (.up ℤ)
  let Rc := c.R.mapHomologicalComplex (.up ℤ)
  let ef := c.E.mapDerivedCategoryFactors
  let rf := c.R.mapDerivedCategoryFactors
  let mL : ((iA ⋙ Ec) ⋙ DerivedCategory.Q).prod qB ⋙ c.DB ≅
      (iA ⋙ Ec).prod iB ⋙ Functor.uncurry.obj c.TB ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun PT ↦ m.modelB _ _ (hE _ PT.1.property) PT.2.property)
      (fun {PT PT'} fg ↦ hnB _ _ _ _ (hE _ PT.1.property) (hE _ PT'.1.property)
        PT.2.property PT'.2.property (Ec.map fg.1.hom) fg.2.hom)
  let mA : qA.prod ((iB ⋙ Rc) ⋙ DerivedCategory.Q) ⋙ c.DA ≅
      iA.prod (iB ⋙ Rc) ⋙ Functor.uncurry.obj c.TA ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun PT ↦ m.modelA _ _ PT.1.property (hR _ PT.2.property))
      (fun {PT PT'} fg ↦ hnA _ _ _ _ PT.1.property PT'.1.property
        (hR _ PT.2.property) (hR _ PT'.2.property) fg.1.hom (Rc.map fg.2.hom))
  let gg : qA.prod qB ⋙ (c.E.mapDerivedCategory.prod (𝟭 _) ⋙ c.DB) ≅
      qA.prod qB ⋙ ((𝟭 _).prod c.R.mapDerivedCategory ⋙ c.DA ⋙ c.E.mapDerivedCategory) :=
    Functor.isoWhiskerRight
        (NatIso.prod (Functor.isoWhiskerLeft iA ef) (Iso.refl qB)) c.DB ≪≫
      mL ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (iA.prod iB) g) DerivedCategory.Q ≪≫
      (Functor.isoWhiskerLeft (iA.prod (iB ⋙ Rc) ⋙ Functor.uncurry.obj c.TA) ef).symm ≪≫
      Functor.isoWhiskerRight mA.symm c.E.mapDerivedCategory ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight
          (NatIso.prod (Iso.refl qA) (Functor.isoWhiskerLeft iB rf).symm) c.DA)
        c.E.mapDerivedCategory
  let ff := Localization.fullyFaithfulWhiskeringLeft (qA.prod qB) (WA.prod WB)
    (DerivedCategory B)
  let gamma := ff.preimageIso gg
  refine ⟨gamma, ?_⟩
  intro P T hP hT
  have h := NatTrans.congr_app (ff.map_preimage gg.hom)
    (⟨P, hP⟩, ⟨T, hT⟩)
  change gamma.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) =
    gg.hom.app (⟨P, hP⟩, ⟨T, hT⟩) at h
  rw [h]
  dsimp only [gg, mL, mA, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerLeft_inv, Iso.symm_hom,
    NatIso.prod_hom, NatTrans.prod, Iso.refl_hom, NatTrans.id_app,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app]
  dsimp only [iA, iB, qA, qB, Ec, Rc, ef, rf, Functor.comp_obj, Functor.prod_obj,
    Functor.uncurry_obj_obj, Functor.id_obj, ObjectProperty.ι_obj]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp, prod_comp,
    Iso.inv_hom_id_app, Category.comp_id, ← prod_id, Iso.app_hom]
  erw [c.DA.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id]
  erw [c.E.mapDerivedCategory.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end NativeExtensionDescentProof
