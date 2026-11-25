/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneratorReduction.ShortWordCompletionIsomorphism
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.GeneratorReduction.CanonicalReductionPullComposition

set_option linter.privateModule false

/-! # Tensor, composition and adjunction reduction squares

Source: blueprint main-20261015, fix-prop-coherence.proof.md, the maps-used sentence
(blueprint: lem-sf-tensor-adjunction-reduction-squares).

The word evaluations, recursive coefficient arrows and independently normalized
ringed-site arrows are the published GeneratorReduction definitions. Only the
structural generators listed in this node are selected below.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u s i

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.GeneratorReduction

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

variable {S : Type s} {W : S → Scheme.{u}} {I : Type i} {location : I → S}

private theorem closed_uncurry {A : Type*} [Category A]
    {H : Aᵒᵖ × A ⥤ A} (T : CoefficientClosedStructure H)
    {X Y Z : A} (f : X ⟶ H.obj (Opposite.op Y, Z)) :
    (T.transpose X Y Z).symm f =
      T.tensor.map (Prod.mkHom f (𝟙 Y)) ≫ T.evaluation Y Z := by
  let := T.monoidal
  simpa only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation, MonoidalCategory.tensorRight,
    MonoidalCategory.curriedTensor, Functor.flip,
    MonoidalCategory.tensor_map, MonoidalCategory.tensor_obj,
    MonoidalCategory.tensorHom_id] using!
      (T.adjunction Y).homEquiv_counit X Z f

private theorem closed_uncurry_pre {A : Type*} [Category A]
    {H : Aᵒᵖ × A ⥤ A} (T : CoefficientClosedStructure H)
    {X X' Y Z : A} (f : X ⟶ X') (g : X' ⟶ H.obj (Opposite.op Y, Z)) :
    (T.transpose X Y Z).symm (f ≫ g) =
      T.tensor.map (Prod.mkHom f (𝟙 Y)) ≫ (T.transpose X' Y Z).symm g := by
  let := T.monoidal
  simpa only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensorRight, MonoidalCategory.curriedTensor, Functor.flip,
    MonoidalCategory.tensor_map,
    MonoidalCategory.tensorHom_id, MonoidalCategory.tensor_obj] using!
      (T.adjunction Y).homEquiv_naturality_left_symm f g

private theorem closed_composition_beta {A : Type*} [Category A]
    {H : Aᵒᵖ × A ⥤ A} (T : CoefficientClosedStructure H)
    {X Y P Q V : A} (f : X ⟶ H.obj (Opposite.op Q, V))
    (g : Y ⟶ H.obj (Opposite.op P, Q)) :
    (T.transpose (T.tensor.obj (X, Y)) P V).symm
        (T.tensor.map (Prod.mkHom f g) ≫ T.composition P Q V) =
      (T.monoidal.associator X Y P).hom ≫
        T.tensor.map (Prod.mkHom (𝟙 X) ((T.transpose Y P Q).symm g)) ≫
        (T.transpose X Q V).symm f := by
  let := T.monoidal
  rw [closed_uncurry_pre, CoefficientClosedStructure.composition, Equiv.symm_apply_apply]
  have hn := MonoidalCategory.associator_naturality f g (𝟙 P)
  change T.tensor.map (Prod.mkHom (T.tensor.map (Prod.mkHom f g)) (𝟙 P)) ≫
      (T.monoidal.associator _ _ _).hom =
    (T.monoidal.associator X Y P).hom ≫
      T.tensor.map (Prod.mkHom f (T.tensor.map (Prod.mkHom g (𝟙 P)))) at hn
  rw [← Category.assoc, hn]
  simp only [closed_uncurry]
  simp only [Category.assoc, ← T.tensor.map_comp_assoc, prod_comp,
    Category.id_comp, Category.comp_id]

private theorem enriched_associativity {A N : Type*} [Category A] [Category N]
    {HA : Aᵒᵖ × A ⥤ A} {HN : Nᵒᵖ × N ⥤ N}
    (TA : CoefficientClosedStructure HA) (TN : CoefficientClosedStructure HN)
    (F : A ⥤ N) (μ : TA.tensor ⋙ F ≅ F.prod F ⋙ TN.tensor)
    (h : CoefficientEvaluationCompatible TA TN F μ) (X Y Z : A) :
    μ.hom.app (TA.tensor.obj (X, Y), Z) ≫
        TN.tensor.map (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 (F.obj Z))) ≫
        (TN.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (TA.monoidal.associator X Y Z).hom ≫
        μ.hom.app (X, TA.tensor.obj (Y, Z)) ≫
        TN.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.hom.app (Y, Z))) := by
  let Q := TA.tensor.obj (Y, Z)
  let V := TA.tensor.obj (X, Q)
  let f := TA.transpose X Q V (𝟙 V)
  let g := TA.transpose Y Z Q (𝟙 Q)
  have hf := h.transpose X Q V (𝟙 V)
  have hg := h.transpose Y Z Q (𝟙 Q)
  have hc := h.composition Z Q V
  have hab : TA.tensor.map (Prod.mkHom f g) ≫ TA.composition Z Q V =
      TA.transpose (TA.tensor.obj (X, Y)) Z V (TA.monoidal.associator X Y Z).hom := by
    apply (TA.transpose _ Z V).symm.injective
    rw [closed_composition_beta]
    simp only [f, g, Equiv.symm_apply_apply]
    rw [show Prod.mkHom (𝟙 X) (𝟙 Q) = 𝟙 (X, Q) from rfl,
      CategoryTheory.Functor.map_id]
    let := TA.monoidal
    simp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj, Q, V,
      Category.comp_id]
  have hp := h.transpose (TA.tensor.obj (X, Y)) Z V
    (TA.monoidal.associator X Y Z).hom
  rw [← hab, F.map_comp, Category.assoc, hc] at hp
  have hn := μ.hom.naturality (Prod.mkHom f g)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn] at hp
  simp only [Category.assoc, ← TN.tensor.map_comp, prod_comp] at hp
  rw [hf, hg] at hp
  have hp := congrArg (TN.transpose (F.obj (TA.tensor.obj (X, Y)))
    (F.obj Z) (F.obj V)).symm hp
  dsimp only [Functor.comp_obj, Functor.prod_obj] at hp
  rw [closed_uncurry_pre, closed_composition_beta, Equiv.symm_apply_apply] at hp
  dsimp only [Q, V] at hp ⊢
  simp only [CategoryTheory.Functor.map_id, Category.comp_id,
    Equiv.symm_apply_apply] at hp
  apply (cancel_epi (μ.inv.app (TA.tensor.obj (X, Y), Z))).1
  have : IsIso (Prod.mkHom (𝟙 (F.obj X)) (μ.inv.app (Y, Z))) :=
    (Iso.prod (asIso _) (asIso _)).isIso_hom
  apply (cancel_mono (TN.tensor.map
    (Prod.mkHom (𝟙 (F.obj X)) (μ.inv.app (Y, Z))) ≫ μ.inv.app (X, Q))).1
  dsimp only [Functor.comp_obj, Functor.prod_obj, Q] at hp ⊢
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← TN.tensor.map_comp_assoc,
    prod_comp, Category.id_comp, Category.comp_id, Iso.hom_inv_id_app,
    ← prod_id, Functor.comp_obj,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  exact hp

private theorem comparison_associator {A N : Type*} [Category A] [Category N]
    {HA : Aᵒᵖ × A ⥤ A} {HN : Nᵒᵖ × N ⥤ N}
    (TA : CoefficientClosedStructure HA) (TN : CoefficientClosedStructure HN)
    (F : A ⥤ N) (μ : TA.tensor ⋙ F ≅ F.prod F ⋙ TN.tensor)
    (h : CoefficientEvaluationCompatible TA TN F μ)
    (T : A × A ⥤ A) (e : T = TA.tensor)
    (X Y Z : A) (X' Y' Z' : N)
    (x : F.obj X ⟶ X') (y : F.obj Y ⟶ Y') (z : F.obj Z ⟶ Z') :
    let t := Functor.whiskerRight (eqToIso e).hom F ≫ μ.hom
    t.app (T.obj (X, Y), Z) ≫
        TN.tensor.map (Prod.mkHom (t.app (X, Y) ≫ TN.tensor.map (Prod.mkHom x y)) z) ≫
        (TN.monoidal.associator X' Y' Z').hom =
      F.map ((eqToIso (congrArg (fun U : A × A ⥤ A ↦
        U.obj (U.obj (X, Y), Z)) e)).hom ≫
          (TA.monoidal.associator X Y Z).hom ≫
            (eqToIso (congrArg (fun U : A × A ⥤ A ↦
              U.obj (X, U.obj (Y, Z))) e.symm)).hom) ≫
        t.app (X, T.obj (Y, Z)) ≫
        TN.tensor.map (Prod.mkHom x (t.app (Y, Z) ≫ TN.tensor.map (Prod.mkHom y z))) := by
  subst T
  simp only [eqToIso_refl, Iso.refl_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  simp only [Category.id_comp]
  let := TA.monoidal
  let := TN.monoidal
  dsimp only [CoefficientClosedStructure.tensor] at μ
  dsimp only [CoefficientClosedStructure.tensor] at *
  have hn := MonoidalCategory.associator_naturality x y z
  change TN.tensor.map (Prod.mkHom (TN.tensor.map (Prod.mkHom x y)) z) ≫
      (TN.monoidal.associator X' Y' Z').hom =
    (TN.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      TN.tensor.map (Prod.mkHom x (TN.tensor.map (Prod.mkHom y z))) at hn
  erw [show TN.tensor.map
      (Prod.mkHom (μ.hom.app (X, Y) ≫ TN.tensor.map (Prod.mkHom x y)) z) =
    TN.tensor.map (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 _)) ≫
      TN.tensor.map (Prod.mkHom (TN.tensor.map (Prod.mkHom x y)) z) by
        rw [← TN.tensor.map_comp]; simp only [prod_comp, Category.id_comp]]
  rw [Category.assoc, hn]
  erw [reassoc_of% (enriched_associativity TA TN F μ h X Y Z)]
  simp only [← TN.tensor.map_comp, prod_comp, Category.id_comp]
  erw [Category.comp_id]
  rfl

private def tensorOrdinaryR (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    (X : Scheme.{u}) :
    (o.ringed.tensor X).ordinary.tensor ⋙
        (IntegralSystemRealization.calculus l E X).reduction ⟶
      (IntegralSystemRealization.calculus l E X).reduction.prod
        (IntegralSystemRealization.calculus l E X).reduction ⋙
          (IntegralSystemRealization.calculus l E X).systemClosed.tensor :=
  Functor.whiskerRight (eqToIso (o.ringed.tensorClosed X)).hom
    (IntegralSystemRealization.calculus l E X).reduction ≫
      (IntegralSystemRealization.calculus l E X).reductionTensor.hom

private def pushOrdinaryR (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IntegralSystemRealization.ringedPush l E f ⋙
        (IntegralSystemRealization.calculus l E Y).reduction ⟶
      (IntegralSystemRealization.calculus l E X).reduction ⋙
        IntegralSystemRealization.Operations.push l E o.system f :=
  (mateEquiv (IntegralSystemRealization.ringedAdj l E f) (o.system.direct f).adj
    (o.realization.reductionPull f).inv)

private theorem mate_reconstruction
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {RA : A ⥤ C} {LA : C ⥤ A} {RB : B ⥤ D} {LB : D ⥤ B}
    {P : B ⥤ A} {Q : A ⥤ B} {F : D ⥤ C} {G : C ⥤ D}
    (aa : RA ⊣ LA) (ab : RB ⊣ LB) (ap : P ⊣ Q) (af : F ⊣ G)
    (χ : RB ⋙ F ≅ P ⋙ RA) (K : A) :
    RB.map (Q.map (aa.unit.app K) ≫
        (conjugateIsoEquiv (ap.comp aa) (ab.comp af) χ).hom.app (RA.obj K)) ≫
        ab.counit.app (G.obj (RA.obj K)) =
      (mateEquiv ap af χ.hom).app K := by
  have hv := conjugateEquiv_counit (ap.comp aa) (ab.comp af) χ.hom (RA.obj K)
  have hn := χ.hom.naturality (Q.map (aa.unit.app K))
  have hε := ap.counit.naturality (aa.unit.app K)
  apply (af.homEquiv _ _).symm.injective
  change F.map _ ≫ af.counit.app _ = _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc]
  change _ = F.map ((mateEquiv ap af χ.hom).app K) ≫ af.counit.app _
  rw [mateEquiv_counit ap af χ.hom K]
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj] at hv
  rw [CategoryTheory.Functor.map_comp, Category.assoc, conjugateIsoEquiv_apply_hom]
  change F.map (RB.map (Q.map (aa.unit.app K))) ≫
      F.map (RB.map ((conjugateEquiv (ap.comp aa) (ab.comp af) χ.hom).app
        (RA.obj K))) ≫ _ = _
  rw [hv]
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn hε
  rw [← Category.assoc, hn, Category.assoc, ← RA.map_comp_assoc, hε,
    RA.map_comp, Category.assoc, aa.left_triangle_components,
    Category.comp_id]

private theorem mate_unit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : R ⋙ F ≅ P ⋙ T) {X : A} {Y : C} (q : R.obj X ⟶ Y) :
    q ≫ b.unit.app Y = R.map (a.unit.app X) ≫
      (mateEquiv a b χ.hom).app (P.obj X) ≫
      G.map (χ.inv.app X ≫ F.map q) := by
  have hm := unit_mateEquiv a b χ.hom X
  dsimp only [Functor.id_obj] at hm
  rw [G.map_comp, ← Category.assoc, ← Category.assoc, hm]
  simp only [Category.assoc, ← G.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.comp_obj, G.map_id, Category.id_comp]
  exact b.unit.naturality q

private theorem mate_counit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : R ⋙ F ≅ P ⋙ T) {X : B} {Y : D} (q : T.obj X ⟶ Y) :
    χ.inv.app (Q.obj X) ≫
        F.map ((mateEquiv a b χ.hom).app X ≫ G.map q) ≫ b.counit.app Y =
      T.map (a.counit.app X) ≫ q := by
  have hn := b.counit.naturality q
  have hm := mateEquiv_counit a b χ.hom X
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [F.map_comp, Category.assoc, hn]
  rw [reassoc_of% hm, Iso.inv_hom_id_app_assoc]

private theorem mate_compositor_square
    {A₀ A₁ A₂ N₀ N₁ N₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category N₀] [Category N₁] [Category N₂]
    {P : A₀ ⥤ A₁} {Q : A₁ ⥤ A₀} {P' : A₁ ⥤ A₂} {Q' : A₂ ⥤ A₁}
    {P'' : A₀ ⥤ A₂} {Q'' : A₂ ⥤ A₀}
    {F : N₀ ⥤ N₁} {G : N₁ ⥤ N₀} {F' : N₁ ⥤ N₂} {G' : N₂ ⥤ N₁}
    {F'' : N₀ ⥤ N₂} {G'' : N₂ ⥤ N₀}
    {R₀ : A₀ ⥤ N₀} {R₁ : A₁ ⥤ N₁} {R₂ : A₂ ⥤ N₂}
    (a : P ⊣ Q) (a' : P' ⊣ Q') (a'' : P'' ⊣ Q'')
    (b : F ⊣ G) (b' : F' ⊣ G') (b'' : F'' ⊣ G'')
    (χ : R₀ ⋙ F ⟶ P ⋙ R₁) (χ' : R₁ ⋙ F' ⟶ P' ⋙ R₂)
    (χ'' : R₀ ⋙ F'' ⟶ P'' ⋙ R₂)
    (α : P'' ⟶ P ⋙ P') (β : F'' ⟶ F ⋙ F')
    (h : (TwoSquare.vComp χ χ').whiskerRight β =
      (TwoSquare.mk _ _ _ _ χ'').whiskerLeft α) (X : A₂) :
    (mateEquiv a b χ).app (Q'.obj X) ≫
        G.map ((mateEquiv a' b' χ').app X) ≫
        (conjugateEquiv (b.comp b') b'' β).app (R₂.obj X) =
      R₀.map ((conjugateEquiv (a.comp a') a'' α).app X) ≫
        (mateEquiv a'' b'' χ'').app X := by
  have hh := congrArg (mateEquiv (a.comp a') b'') h
  rw [mateEquiv_conjugateEquiv_vcomp (a.comp a') (b.comp b') b'',
    conjugateEquiv_mateEquiv_vcomp (a.comp a') a'' b'',
    mateEquiv_hcomp a b a' b'] at hh
  have hx := congrArg (fun t ↦ t.app X) hh
  simpa only [TwoSquare.hComp, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Functor.comp_obj, Category.assoc] using hx

private def Word.ordinaryR (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → (B : Word W location a) →
      (IntegralSystemRealization.calculus l E (W a)).reduction.obj
        (B.ringedValue l E W location o K) ⟶
      B.systemValue l E W location o (inputReduction l E W location K)
  | _, .input _ => 𝟙 _
  | a, .unit _ => (o.unitReduction (W a)).hom
  | a, .tensor B C => (tensorOrdinaryR l E o (W a)).app
      (B.ringedValue l E W location o K, C.ringedValue l E W location o K) ≫
        (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
          (Prod.mkHom (B.ordinaryR l E o K) (C.ordinaryR l E o K))
  | _, .pull f _ _ _ B =>
      (o.realization.reductionPull f).hom.app (B.ringedValue l E W location o K) ≫
        (IntegralSystemRealization.pull l E f).map (B.ordinaryR l E o K)
  | _, .push f _ _ _ _ B =>
      (pushOrdinaryR l E o f).app (B.ringedValue l E W location o K) ≫
        (IntegralSystemRealization.Operations.push l E o.system f).map
          (B.ordinaryR l E o K)
  | _, .open j hj _ B => let := hj
      inverseOrZero ((o.realization.openReduction l E j).app
        (B.ringedValue l E W location o K)) ≫
      (IntegralSystemRealization.Operations.shriek l E o.system j).map
        (B.ordinaryR l E o K)

private theorem inverseOrZero_eq_inv {A : Type*} [Category A] [HasZeroMorphisms A]
    {X Y : A} (f : X ⟶ Y) [IsIso f] : inverseOrZero f = inv f := by
  classical
  simp only [inverseOrZero, dite_eq_left (inferInstance : IsIso f)]

private theorem inverse_mate_unit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasZeroMorphisms D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : Q ⋙ R ⟶ T ⋙ G) {X : A} {Y : C} (q : R.obj X ⟶ Y)
    [IsIso (((mateEquiv a b).symm χ).app X)] :
    q ≫ b.unit.app Y = R.map (a.unit.app X) ≫ χ.app (P.obj X) ≫
      G.map (inverseOrZero (((mateEquiv a b).symm χ).app X) ≫ F.map q) := by
  have hm := unit_mateEquiv_symm a b χ X
  rw [inverseOrZero_eq_inv, G.map_comp, ← Category.assoc, ← Category.assoc, hm]
  simp only [Category.assoc, ← G.map_comp_assoc, Functor.comp_obj,
    Functor.id_obj, IsIso.hom_inv_id, G.map_id, Category.id_comp]
  exact b.unit.naturality q

private theorem inverse_mate_counit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasZeroMorphisms D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : Q ⋙ R ⟶ T ⋙ G) {X : B} {Y : D} (q : T.obj X ⟶ Y)
    [IsIso (((mateEquiv a b).symm χ).app (Q.obj X))] :
    inverseOrZero (((mateEquiv a b).symm χ).app (Q.obj X)) ≫
        F.map (χ.app X ≫ G.map q) ≫ b.counit.app Y =
      T.map (a.counit.app X) ≫ q := by
  have hm := mateEquiv_counit_symm a b χ X
  have hn := b.counit.naturality q
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [inverseOrZero_eq_inv, F.map_comp, Category.assoc, hn,
    reassoc_of% hm, IsIso.inv_hom_id_assoc]

private theorem inverse_square {A : Type*} [Category A] [HasZeroMorphisms A]
    {X Y X' Y' : A} (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    [IsIso a] [IsIso b] (h : f ≫ b = a ≫ g) :
    g ≫ inverseOrZero b = inverseOrZero a ≫ f := by
  rw [inverseOrZero_eq_inv, inverseOrZero_eq_inv]
  apply (cancel_epi a).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem inverse_naturality {A N : Type*} [Category A] [Category N]
    [HasZeroMorphisms N] {F G : A ⥤ N} (α : F ⟶ G) {X Y : A} (f : X ⟶ Y)
    [IsIso (α.app X)] [IsIso (α.app Y)] :
    G.map f ≫ inverseOrZero (α.app Y) = inverseOrZero (α.app X) ≫ F.map f := by
  apply inverse_square
  exact α.naturality f

end WeilConjectures.GeneratorReduction
