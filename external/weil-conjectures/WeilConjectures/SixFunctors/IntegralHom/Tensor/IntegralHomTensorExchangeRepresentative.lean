/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralHomTensorAdjunctionExchange
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
/-! # Adjunction exchange on signed tensor representatives

Source: Stacks Tags 08J9 and 06YU.
(blueprint: lem-sfb-integral-hom-tensor-exchange-representative)
-/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace WeilConjectures.IntegralHom
private theorem total_generator_ext
    (Y : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (P Q I : CochainComplex (Modules.{u, u} Y R) ℤ)
    {f g : (coefficientTotalTensor.{u, u + 1, u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (P, Q) ⟶ I}
    (h : ∀ (i j k : ℤ) (hij : i + j = k) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (f.f k).val.app U (coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R P Q i j k hij U x y) =
      (g.f k).val.app U (coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R P Q i j k hij U x y)) : f = g := by
  letI := tensorLocalization.{u, u} Y R
  letI := countableColimits.{u, u} Y R
  letI := ordinaryTensorZero.{u, u} Y R
  letI := ordinaryTensorObjZero.{u, u} Y R
  ext k : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
    (R := R) (P.X i) (Q.X j)).inv).mp
  apply (adj.homEquiv _ (I.X k)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h i j k hij U x y

private theorem evaluate_eq_projection
    {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (P I : CochainComplex (Modules.{u, u} X R) ℤ) (j i : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
    (f : ((homComplex (R := R) P I).X j).val.obj U) (x : (P.X i).val.obj U) :
    evaluate.{u, u} X R P I j i U f x =
      ((homReductionProjection R P I j i (i + j) rfl).val.app U f).app
        (op (Over.mk (𝟙 U.unop))) x := by
  rfl

attribute [local irreducible] homComplexFunctor derivedInternalHomOfUniverses

-- Keep derived Hom opaque during the representative comparison.
attribute [-instance] derivedCategory in
/-- Signed interchange on representatives induces the adjunction exchange.

Source: Stacks Tags 08J9 and 06YU. Proof: compose with the inverse model comparison
and a K-injective resolution of the target tensor. The normalized model curries
that augmentation to a Hom-complex map. The presentation evaluation is its signed
uncurrying. The assumed interchange formula makes these chain maps equal on all
pure generators. Tensor and totalization generation give equality, and cancellation
of the localized augmentation and representative isomorphisms proves the claim.
(blueprint: lem-sfb-integral-hom-tensor-exchange-representative) -/
theorem tensorAdjunctionExchange_representative
    {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R) (b : HomReductionTensorModel R)
    (P Q : CochainComplex (Modules.{u, u} X R) ℤ)
    (hP : flat.{u, u} X R P) (hQ : flat.{u, u} X R Q)
    (σ : ((totalTensor.{u, u} X R).obj P).obj Q ⟶ homReductionTotal R Q P)
    (hσ : ∀ (i j k : ℤ) (hij : i + j = k) (hji : j + i = k)
      (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (σ.f k).val.app U (coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology X) R P Q i j k hij U x y) =
      (i * j).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology X) R Q P j i k hji U y x) :
    a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        tensorAdjunctionExchange R a b (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map σ ≫ (b.compute Q P hQ hP).hom := by
  classical
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    (AlgebraicGeometry.Scheme.ProEt.topology X) R).1
  let C := homReductionTotal R Q P
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u + 1} (Modules.{u, u} X R)).obj C
  let r : C ⟶ I := (CochainComplex.toKInjectiveResolution.{u + 1} _).app C
  haveI : I.IsKInjective := CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ C
  haveI : QuasiIso r := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ C).2
  obtain ⟨c, hc, _⟩ := b.cochain_curry Q P I r
  obtain ⟨beta, hbeta, heval⟩ := a.evaluation P I Q hP hQ inferInstance c
  have hchain : beta = σ ≫ r := by
    apply total_generator_ext.{u} X R
    intro i j k hij U x y
    subst k
    change (beta.f (i + j)).val.app U
        (coefficientTensorGenerator.{u, u + 1, u}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R P Q i j (i + j) rfl U x y) =
      (r.f (i + j)).val.app U ((σ.f (i + j)).val.app U
        (coefficientTensorGenerator.{u, u + 1, u}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R P Q i j (i + j) rfl U x y))
    rw [hσ i j (i + j) rfl (add_comm j i)]
    simp only [Units.smul_def]
    erw [hbeta i j U x y]
    erw [map_zsmul]
    congr 1
    have h : ∀ (k : ℤ) (hji : j + i = k) (hij : i + j = k),
        (r.f k).val.app U (coefficientTensorGenerator.{u, u + 1, u}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R Q P j i k hji U y x) =
        ((homReductionProjection R P I j i k hij).val.app U
          ((c.f j).val.app U y)).app (op (Over.mk (𝟙 U.unop))) x := by
      intro k hji hij
      subst k
      exact hc j i U y x
    erw [evaluate_eq_projection]
    exact (h (i + j) (add_comm j i) rfl).symm
  let φ := DerivedCategory.Q.map c ≫ homModelMap.{u, u} X R P I
  have ha : a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
      ((a.adjunction (DerivedCategory.Q.obj P)).homEquiv
        (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)).symm φ =
      DerivedCategory.Q.map beta := by
    have h := congrArg
      (fun z ↦ a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫ z) heval
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
      Adjunction.homEquiv_counit, Functor.curry_obj_obj_map, φ,
      TensorPresentation.adjunction] using h.symm
  have hb := b.normalize Q P I hQ hP inferInstance r c hc
  have hunit : homReductionHomUnit R P I = homModelMap.{u, u} X R P I := by rfl
  rw [hunit] at hb
  apply (cancel_mono ((b.compute Q P hQ hP).inv ≫ DerivedCategory.Q.map r)).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hb, ← tensorAdjunctionExchange_uncurry]
  rw [ha, hchain, DerivedCategory.Q.map_comp]

end WeilConjectures.IntegralHom
