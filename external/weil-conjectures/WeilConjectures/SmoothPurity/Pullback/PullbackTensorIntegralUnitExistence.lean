/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus

/-! Existence of the integral unit comparison.

Source: Stacks Project, Tag 07A4, label lemma-pullback-tensor-product; the
integral coefficient-level unit coherence construction.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence-existence)

The normalized coherent system unit comparison is lifted through the fully
faithful integral reduction.  Its two system-level unitor equations transport
along the reduction, tensor, pullback, and unit counits to the displayed
integral equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

-- Conjugating both inputs of a reduced tensor comparison respects its square.
private theorem conjugate_tensor_comparison
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : U ⋙ R ≅ R.prod R ⋙ J) (b : V ⋙ Q ≅ Q.prod Q ⋙ I)
    (p : F ⋙ Q ≅ R ⋙ H) (ν : J ⋙ H ≅ H.prod H ⋙ I)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
        p.hom.app (U.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
          ν.hom.app (R.obj M, R.obj N))
    (M N : C) (A B : D) (K L : S)
    (d : F.obj M ≅ A) (e : F.obj N ≅ B)
    (x : Q.obj A ≅ H.obj K) (y : Q.obj B ≅ H.obj L)
    (r : R.obj M ≅ K) (s : R.obj N ≅ L)
    (hd : Q.map d.hom ≫ x.hom = p.hom.app M ≫ H.map r.hom)
    (he : Q.map e.hom ≫ y.hom = p.hom.app N ≫ H.map s.hom) :
    Q.map ((μ M N).hom ≫ V.map (Prod.mkHom d.hom e.hom)) ≫
        b.hom.app (A, B) ≫ I.map (Prod.mkHom x.hom y.hom) =
      p.hom.app (U.obj (M, N)) ≫
        H.map (a.hom.app (M, N) ≫ J.map (Prod.mkHom r.hom s.hom)) ≫
        ν.hom.app (K, L) := by
  have hb := b.hom.naturality (Prod.mkHom d.hom e.hom)
  change Q.map (V.map (Prod.mkHom d.hom e.hom)) ≫ b.hom.app (A, B) =
    b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (Q.map d.hom) (Q.map e.hom)) at hb
  rw [Q.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hb, ← I.map_comp]
  simp only [prod_comp, hd, he]
  rw [← map_pair_comp I (p.hom.app M) (p.hom.app N)
    (H.map r.hom) (H.map s.hom)]
  rw [reassoc_of% (hμ M N)]
  have hn := ν.hom.naturality (Prod.mkHom r.hom s.hom)
  change H.map (J.map (Prod.mkHom r.hom s.hom)) ≫ ν.hom.app (K, L) =
    ν.hom.app (R.obj M, R.obj N) ≫
      I.map (Prod.mkHom (H.map r.hom) (H.map s.hom)) at hn
  rw [← hn, H.map_comp]
  simp only [Category.assoc]

attribute [local irreducible] Scheme.residueField Padic
  HasDerivedCategory.standard
  pullbackTensorIntegralReductionTensor pullbackTensorIntegralReductionPullback
  pullbackTensorIntegralUnitReduction

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Existence half of integral pullback tensor unit coherence.
Source: Stacks Project, Tag 07A4; normalized coefficient-level unit comparison.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence-existence)
-/
theorem canonicalIntegralPullbackTensor_unit_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ ε : ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
      ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) ≅
        (@pullbackTensorIntegralUnit l _ E _ _ _ X hX),
      ∀ M : sfIntegralConstructibleCategory l E Y,
        (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY)
          ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) M).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
            (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ X hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
        ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
          ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ Y hY) M).hom) ∧
        (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M
          ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY))).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
            (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ X hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
        ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
          ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ Y hY) M).hom) := by
  have := (coherentReduction_fullyFaithful l E X).1
  have := (coherentReduction_fullyFaithful l E X).2
  let R := coherentReduction l E Y
  let Q := coherentReduction l E X
  let F := constructibleIntegralPullback l E f
  let H := pullbackTensorSequenceDerived l E f
  let U := constructibleIntegralTensor l E Y
  let V := constructibleIntegralTensor l E X
  let J := (pullbackTensorCalculus l E Y).systemClosed.tensor
  let I := (pullbackTensorCalculus l E X).systemClosed.tensor
  let a := reduction_tensor l E Y
  let b := reduction_tensor l E X
  let p := reduction_pullback l E f
  let ν := pullbackTensorSystemComparison l E f
  let μ := canonicalIntegralPullbackTensor l E f
  let UY := pullbackTensorIntegralUnit l E Y
  let UX := pullbackTensorIntegralUnit l E X
  let eY := pullbackTensorIntegralUnitReduction l E Y
  let eX := pullbackTensorIntegralUnitReduction l E X
  obtain ⟨εS, hS⟩ := pullbackTensorSystemComparison_unit l E f
  let ε : F.obj UY ≅ UX := Q.preimageIso
    (p.app UY ≪≫ H.mapIso eY ≪≫ εS ≪≫ eX.symm)
  have hε : Q.map ε.hom ≫ (eX ≪≫ εS.symm).hom =
      p.hom.app UY ≫ H.map eY.hom := by
    dsimp only [ε, Functor.preimageIso]
    rw [Functor.map_preimage]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id, Iso.app_hom]
  refine ⟨ε, fun M ↦ ?_⟩
  constructor
  · let a₀ := a.app (UY, M) ≪≫ J.mapIso (Iso.prod eY (Iso.refl (R.obj M)))
    let b₀ := b.app (UX, F.obj M) ≪≫
      I.mapIso (Iso.prod (eX ≪≫ εS.symm) (p.app M))
    let δ := I.mapIso (Iso.prod εS (Iso.refl (H.obj (R.obj M)))) ≪≫
      (pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor _
    have hs := reduced_square R Q F H p a₀ (Iso.refl (R.obj M)) b₀ (p.app M)
      (pullbackTensorIntegralLeftUnitor l E Y M)
      (pullbackTensorIntegralLeftUnitor l E X (F.obj M))
      ((pullbackTensorCalculus l E Y).systemClosed.monoidal.leftUnitor (R.obj M)) δ
      (μ UY M ≪≫ V.mapIso (Iso.prod ε (Iso.refl (F.obj M))))
      (Iso.refl (F.obj M)) (ν.app (_, R.obj M)) (Iso.refl (H.obj (R.obj M)))
    have h := hs ?_ ?_ ?_ ?_ ?_
    · simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
        Category.comp_id, Category.assoc] using h.symm
    · simpa only [a₀, a, reduction_tensor, R, coherentReduction, UY, eY, J,
        pullbackTensorIntegralLeftUnitor, Iso.trans_hom, Functor.mapIso_hom,
        Iso.prod_hom, Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc,
        Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
        NatIso.ofComponents_hom_app] using
        (pullbackTensorIntegralLeftUnitor_existsUnique l E Y M).exists.choose_spec
    · have hu : Q.map (pullbackTensorIntegralLeftUnitor l E X (F.obj M)).hom =
          b.hom.app (UX, F.obj M) ≫ I.map (Prod.mkHom eX.hom (𝟙 _)) ≫
            ((pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor
              (Q.obj (F.obj M))).hom :=
        (pullbackTensorIntegralLeftUnitor_existsUnique l E X (F.obj M)).exists.choose_spec
      let := (pullbackTensorCalculus l E X).systemClosed.monoidal
      have hn : I.map (Prod.mkHom (𝟙 _) (p.hom.app M)) ≫
          ((pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor
            (H.obj (R.obj M))).hom =
          ((pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor
            (Q.obj (F.obj M))).hom ≫ p.hom.app M := by
        simpa only [I, Q, R, F, H, Functor.comp_obj, MonoidalCategory.tensor_obj,
          CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
          MonoidalCategory.id_tensorHom] using
          MonoidalCategory.leftUnitor_naturality (p.hom.app M)
      dsimp only [b₀, δ, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Iso.symm_hom]
      rw [hu]
      simp only [Category.assoc]
      rw [← hn]
      simp only [← I.map_comp_assoc, prod_comp, Category.assoc, Category.id_comp,
        Category.comp_id, Iso.inv_hom_id, H, R, Functor.comp_obj]
    · simpa only [a₀, b₀, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Category.assoc] using
        conjugate_tensor_comparison R Q F H U V J I a b p ν μ
          (integralComparison_reduction l E f) UY M UX (F.obj M) _ (R.obj M)
          ε (Iso.refl _) (eX ≪≫ εS.symm) (p.app M) eY (Iso.refl _) hε
          (by simp)
    · simp
    · simpa only [δ, H, I, J, ν, Functor.comp_obj,
        Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc] using (hS (R.obj M)).1.symm
  · let a₀ := a.app (M, UY) ≪≫ J.mapIso (Iso.prod (Iso.refl (R.obj M)) eY)
    let b₀ := b.app (F.obj M, UX) ≪≫
      I.mapIso (Iso.prod (p.app M) (eX ≪≫ εS.symm))
    let δ := I.mapIso (Iso.prod (Iso.refl (H.obj (R.obj M))) εS) ≪≫
      (pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor _
    have hs := reduced_square R Q F H p a₀ (Iso.refl (R.obj M)) b₀ (p.app M)
      (pullbackTensorIntegralRightUnitor l E Y M)
      (pullbackTensorIntegralRightUnitor l E X (F.obj M))
      ((pullbackTensorCalculus l E Y).systemClosed.monoidal.rightUnitor (R.obj M)) δ
      (μ M UY ≪≫ V.mapIso (Iso.prod (Iso.refl (F.obj M)) ε))
      (Iso.refl (F.obj M)) (ν.app (R.obj M, _)) (Iso.refl (H.obj (R.obj M)))
    have h := hs ?_ ?_ ?_ ?_ ?_
    · simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
        Category.comp_id, Category.assoc] using h.symm
    · simpa only [a₀, a, reduction_tensor, R, coherentReduction, UY, eY, J,
        pullbackTensorIntegralRightUnitor, Iso.trans_hom, Functor.mapIso_hom,
        Iso.prod_hom, Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc,
        Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
        NatIso.ofComponents_hom_app] using
        (pullbackTensorIntegralRightUnitor_existsUnique l E Y M).exists.choose_spec
    · have hu : Q.map (pullbackTensorIntegralRightUnitor l E X (F.obj M)).hom =
          b.hom.app (F.obj M, UX) ≫ I.map (Prod.mkHom (𝟙 _) eX.hom) ≫
            ((pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor
              (Q.obj (F.obj M))).hom :=
        (pullbackTensorIntegralRightUnitor_existsUnique l E X (F.obj M)).exists.choose_spec
      let := (pullbackTensorCalculus l E X).systemClosed.monoidal
      have hn : I.map (Prod.mkHom (p.hom.app M) (𝟙 _)) ≫
          ((pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor
            (H.obj (R.obj M))).hom =
          ((pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor
            (Q.obj (F.obj M))).hom ≫ p.hom.app M := by
        simpa only [I, Q, R, F, H, Functor.comp_obj, MonoidalCategory.tensor_obj,
          CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
          MonoidalCategory.tensorHom_id] using
          MonoidalCategory.rightUnitor_naturality (p.hom.app M)
      dsimp only [b₀, δ, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Iso.symm_hom]
      rw [hu]
      simp only [Category.assoc]
      rw [← hn]
      simp only [← I.map_comp_assoc, prod_comp, Category.assoc, Category.id_comp,
        Category.comp_id, Iso.inv_hom_id, H, R, Functor.comp_obj]
    · simpa only [a₀, b₀, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Category.assoc] using
        conjugate_tensor_comparison R Q F H U V J I a b p ν μ
          (integralComparison_reduction l E f) M UY (F.obj M) UX (R.obj M) _
          (Iso.refl _) ε (p.app M) (eX ≪≫ εS.symm) (Iso.refl _) eY
          (by simp) hε
    · simp
    · simpa only [δ, H, I, J, ν, Functor.comp_obj,
        Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
        Iso.refl_hom, Iso.app_hom, Category.comp_id, Category.assoc] using (hS (R.obj M)).2.symm

end WeilConjectures
