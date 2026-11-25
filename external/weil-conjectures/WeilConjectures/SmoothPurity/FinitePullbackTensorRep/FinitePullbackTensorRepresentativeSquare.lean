/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeData

/-! # The finite tensor representative square

Source: Stacks 07A4 and 00YV.
(blueprint: lem-pur-finite-pullback-tensor-representative-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
private theorem transport_square
    {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (r : F ≅ G)
    (A A' : C × C ⥤ C) (s : A ≅ A')
    (B B' : D × D ⥤ D) (t : B ≅ B')
    (P Q R : C) (U V W : D)
    (a : R ⟶ A.obj (P, Q)) (b : W ⟶ B.obj (U, V))
    (eP : F.obj P ⟶ U) (eQ : F.obj Q ⟶ V)
    (eR : F.obj R ⟶ W)
    (beta : F.obj (A.obj (P, Q)) ⟶ B.obj (F.obj P, F.obj Q))
    (h : F.map a ≫ beta ≫ B.map (Prod.mkHom eP eQ) = eR ≫ b) :
    G.map (a ≫ s.hom.app (P, Q)) ≫
        (r.inv.app (A'.obj (P, Q)) ≫ F.map (s.inv.app (P, Q)) ≫ beta ≫
          t.hom.app (F.obj P, F.obj Q) ≫
          B'.map (Prod.mkHom (r.hom.app P) (r.hom.app Q))) ≫
        B'.map (Prod.mkHom (r.inv.app P ≫ eP) (r.inv.app Q ≫ eQ)) =
      (r.inv.app R ≫ eR) ≫ b ≫ t.hom.app (U, V) := by
  have hp : Prod.mkHom (r.hom.app P) (r.hom.app Q) ≫
      Prod.mkHom (r.inv.app P ≫ eP) (r.inv.app Q ≫ eQ) =
      Prod.mkHom eP eQ := by
    ext <;> simp
  have hn := r.inv.naturality (a ≫ s.hom.app (P, Q))
  change G.map (a ≫ s.hom.app (P, Q)) ≫ r.inv.app (A'.obj (P, Q)) =
    r.inv.app R ≫ F.map (a ≫ s.hom.app (P, Q)) at hn
  simp only [Category.assoc]
  rw [← B'.map_comp, hp]
  calc
    _ = r.inv.app R ≫ F.map a ≫ beta ≫ t.hom.app (F.obj P, F.obj Q) ≫
        B'.map (Prod.mkHom eP eQ) := by
      rw [← Category.assoc, hn]
      simp only [Functor.map_comp, Category.assoc, ← F.map_comp_assoc,
        Iso.hom_inv_id_app, F.map_id, Category.id_comp]
    _ = r.inv.app R ≫ (F.map a ≫ beta ≫ B.map (Prod.mkHom eP eQ)) ≫
        t.hom.app (U, V) := by
      rw [← t.hom.naturality]
      simp only [Category.assoc]
    _ = _ := by rw [h]; simp only [Category.assoc]

namespace WeilConjectures.FinitePullbackTensorRep
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf finiteIntrinsicDerivedTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local semireducible] pull
attribute [local instance] modules_abelian modules_derived ordinary_additive
  ordinary_limits ordinary_colimits
attribute [local implicit_reducible] modules_abelian modules_derived

/-- The constructed finite comparison satisfies the single-pullback representative square.
Source: Stacks 07A4 and 00YV
(blueprint: lem-pur-finite-pullback-tensor-representative-square).
Proof: use the defining representative square of proEtaleCanonicalTensorComparison.
Compose the source representative with pullbackTensorFiniteModelIso. Naturality of
mapDerivedCategoryNatIso moves the inverse realization across this source map.
Naturality of the target model identification moves it across the two computation
maps. The realization and its inverse cancel in both tensor factors. What remains
is exactly the original canonical square, followed by the target model identification.
The two flatness witnesses are the preservation witnesses in that original square. -/
theorem square {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) P)
    (hQ : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) Q) :
    ∃ (hP' : proEtaleFlatRepresentatives X (integralCoefficientCommRingSheaf l E X n)
        ((pull l E f n).obj P))
      (hQ' : proEtaleFlatRepresentatives X (integralCoefficientCommRingSheaf l E X n)
        ((pull l E f n).obj Q)),
      (finiteDerivedPullback l E n f).map (representative l E Y n P Q hP hQ).hom ≫
        ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        (finiteIntrinsicDerivedTensor l E X n).map
          (Prod.mkHom ((factors l E f n).hom.app P) ((factors l E f n).hom.app Q)) =
      (factors l E f n).hom.app (tensor l E Y n P Q) ≫
        DerivedCategory.Q.map (comparison l E f n P Q) ≫
        (representative l E X n _ _ hP' hQ').hom := by
  let a := pullbackTensorFiniteModel l E Y n
  let b := pullbackTensorFiniteModel l E X n
  obtain ⟨hP', hQ', hn⟩ := (Classical.choose_spec
    (proEtaleCanonicalTensorPullback f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n)
      (pullbackTensorCoefficientIso l E f n) a b).2.exists) P Q hP hQ
  refine ⟨hP', hQ', ?_⟩
  have ht := transport_square
    (derived l E f n) (finiteDerivedPullback l E n f)
    (realization l E f n)
    a.tensor (finiteIntrinsicDerivedTensor l E Y n) (pullbackTensorFiniteModelIso l E Y n)
    b.tensor (finiteIntrinsicDerivedTensor l E X n) (pullbackTensorFiniteModelIso l E X n)
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
    (DerivedCategory.Q.obj (tensor l E Y n P Q))
    (DerivedCategory.Q.obj ((pull l E f n).obj P))
    (DerivedCategory.Q.obj ((pull l E f n).obj Q))
    (DerivedCategory.Q.obj (tensor l E X n ((pull l E f n).obj P)
      ((pull l E f n).obj Q)))
    (a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩))
    (b.representative.hom.app (⟨_, hP'⟩, ⟨_, hQ'⟩))
    ((ordinaryFactors l E f n).hom.app P)
    ((ordinaryFactors l E f n).hom.app Q)
    ((ordinaryFactors l E f n).hom.app (tensor l E Y n P Q) ≫
      DerivedCategory.Q.map (comparison l E f n P Q))
    ((proEtaleCanonicalTensorComparison f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n)
      (pullbackTensorCoefficientIso l E f n) a b).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (by
      unfold comparison
      dsimp only [id, derived, ordinaryFactors, tensor, totalTensor]
      erw [Category.assoc]
      exact hn)
  unfold finitePullbackTensorConstruction representative factors
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Iso.prod_hom]
  simp only [Category.assoc, realization, a, b] at ht
  convert ht using 1 <;>
    dsimp only [id, Iso.trans, Iso.app, Iso.symm, realization, derived, quotient, pull,
      ordinary] <;>
    simp only [NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app, Category.assoc]

end WeilConjectures.FinitePullbackTensorRep
