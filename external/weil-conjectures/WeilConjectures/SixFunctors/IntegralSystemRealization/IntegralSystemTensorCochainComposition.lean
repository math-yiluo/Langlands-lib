/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Tensor normalization for two composable inverse images

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0941, 03DI, 07A7;
blueprint fix-prop-coherence, strict-system realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u c₀ v₀ r₀
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] pullbackTensorCalculus CoefficientClosedStructure.tensor
  Functor.mapDerivedCategory SheafOfModules.monoidalCategory
  Functor.leftAdjoint HasDerivedCategory.standard Scheme.residueField
  coefficientSequenceCommRingSheaf

private abbrev Complex (W : Scheme.{u}) :=
  CochainComplex (coefficientSequenceModules l E W) ℤ

private abbrev total (W : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)

private abbrev inverse {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pullbackTensorSequenceInverse l E f

private abbrev onComplex {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (inverse l E f).mapHomologicalComplex (.up ℤ)

private abbrev generator (W : Scheme.{u}) :=
  coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)

private theorem generator_restrict {C : Type c₀} [Category.{v₀} C]
    (J : GrothendieckTopology C) [EssentiallySmall.{max c₀ v₀ r₀} C]
    [HasSheafify J AddCommGrpCat.{max c₀ v₀ r₀}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c₀ v₀ r₀}]
    (R : Sheaf J CommRingCat.{max c₀ v₀ r₀})
    (P Q : CochainComplex (SheafOfModules.scalarModules J R) ℤ)
    (p q k : ℤ) (h : p + q = k) {U V : Cᵒᵖ} (a : U ⟶ V)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{r₀, c₀, v₀} J R).obj (P, Q)).X k).val.map a
        (coefficientTensorGenerator.{r₀, c₀, v₀} J R P Q p q k h U x y) =
      coefficientTensorGenerator.{r₀, c₀, v₀} J R P Q p q k h V
        ((P.X p).val.map a x) ((Q.X q).val.map a y) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let η := ((PresheafOfModules.sheafificationAdjunction.{max c₀ v₀ r₀} (𝟙 _)).unit.app
      (CategoryTheory.MonoidalCategory.tensorObj (P.X p).val (Q.X q).val)) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := R) (P.X p) (Q.X q)).inv.val ≫
    (HomologicalComplex.ιMapBifunctor P Q
      (CategoryTheory.MonoidalCategory.curriedTensor _) (.up ℤ) p q k h).val
  exact (PresheafOfModules.naturality_apply η a (x ⊗ₜ[R.obj.obj U] y)).symm

private theorem transpose_paste {C D : Type*} [Category C] [Category D]
    (R S : D ⥤ C) (b : S ⟶ R) {M : C} {A B N : D}
    (u₀ : M ⟶ R.obj A) (u₁ : M ⟶ S.obj B) (a : A ⟶ B)
    (h : u₁ ≫ b.app B = u₀ ≫ R.map a) (t : B ⟶ N) :
    u₀ ≫ R.map (a ≫ t) = u₁ ≫ S.map t ≫ b.app N := by
  rw [R.map_comp, ← Category.assoc, ← h, Category.assoc, ← b.naturality]

private theorem compositor_unit (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : coefficientSequenceModules l E Z) :
    (((pullbackTensorSequenceAdjunction l E g).comp
      (pullbackTensorSequenceAdjunction l E f)).unit.app M) ≫
        (c.ordinaryDirect f g).hom.app ((inverse l E f).obj ((inverse l E g).obj M)) =
      (pullbackTensorSequenceAdjunction l E (f ≫ g)).unit.app M ≫
        (pullbackTensorSequenceDirect l E (f ≫ g)).map ((c.ordinaryPull f g).hom.app M) := by
  have hc := congrArg Iso.hom (c.conjugate f g)
  dsimp only [conjugateIsoEquiv] at hc
  rw [← hc]
  exact unit_conjugateEquiv
    ((pullbackTensorSequenceAdjunction l E g).comp
      (pullbackTensorSequenceAdjunction l E f))
    (pullbackTensorSequenceAdjunction l E (f ≫ g)) ((c.ordinaryPull f g).hom) M

private theorem compositor_unit_sections (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : coefficientSequenceModules l E Z) (n : ℕ) (U : Z.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((c.ordinaryPull f g).hom.app M).val.app
        (op (n, (proEtaleBaseChange (f ≫ g)).obj U))
        (((pullbackTensorSequenceAdjunction l E (f ≫ g)).unit.app M).val.app
          (op (n, U)) x) =
      (((inverse l E f).obj ((inverse l E g).obj M)).val.map
        (Quiver.Hom.op (𝟙 n, (MorphismProperty.Over.pullbackComp f g).hom.app U)))
        (((pullbackTensorSequenceAdjunction l E f).unit.app
          ((inverse l E g).obj M)).val.app
            (op (n, (proEtaleBaseChange g).obj U))
          (((pullbackTensorSequenceAdjunction l E g).unit.app M).val.app
            (op (n, U)) x)) := by
  have h := congrArg (fun a ↦ a.val.app (op (n, U)) x)
    (compositor_unit l E o c f g M)
  simp only [Adjunction.comp_unit_app] at h
  change ((c.ordinaryDirect f g).hom.app _).val.app (op (n, U))
      (((pullbackTensorSequenceAdjunction l E f).unit.app
        ((inverse l E g).obj M)).val.app _
        (((pullbackTensorSequenceAdjunction l E g).unit.app M).val.app _ x)) = _ at h
  rw [c.sections] at h
  exact h.symm

private theorem cochain_formula {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Complex l E Y) (p q k : ℤ) (h : p + q = k) (V : ℕ × Y.ProEt)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)) :
    (((pullbackTensorSequenceCochain l E f).hom.app (P, Q)).f k).val.app
        (op ((pullbackTensorSequenceBase f).obj V))
        (((pullbackTensorSequenceAdjunction l E f).unit.app
          (((total l E Y).obj (P, Q)).X k)).val.app (op V)
          (generator l E Y P Q p q k h (op V) x y)) =
      generator l E X ((onComplex l E f).obj P) ((onComplex l E f).obj Q)
        p q k h (op ((pullbackTensorSequenceBase f).obj V))
        (((pullbackTensorSequenceAdjunction l E f).unit.app (P.X p)).val.app (op V) x)
        (((pullbackTensorSequenceAdjunction l E f).unit.app (Q.X q)).val.app (op V) y) := by
  exact (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose_spec
    P Q p q k h V x y

attribute [local irreducible] pullbackTensorSequenceCochain
  pullbackTensorSequenceAdjunction

private theorem composite_tensor_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P Q : Complex l E Z) (p q k : ℤ) (h : p + q = k) (V : ℕ × Z.ProEt)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)) :
    (((onComplex l E f).map ((pullbackTensorSequenceCochain l E g).hom.app (P, Q)) ≫
        (pullbackTensorSequenceCochain l E f).hom.app
          ((onComplex l E g).obj P, (onComplex l E g).obj Q)).f k).val.app
          (op ((pullbackTensorSequenceBase f).obj ((pullbackTensorSequenceBase g).obj V)))
        (((pullbackTensorSequenceAdjunction l E f).unit.app
          (((onComplex l E g).obj ((total l E Z).obj (P, Q))).X k)).val.app
          (op ((pullbackTensorSequenceBase g).obj V))
          (((pullbackTensorSequenceAdjunction l E g).unit.app
            (((total l E Z).obj (P, Q)).X k)).val.app (op V)
            (generator l E Z P Q p q k h (op V) x y))) =
      generator l E X ((onComplex l E f).obj ((onComplex l E g).obj P))
        ((onComplex l E f).obj ((onComplex l E g).obj Q)) p q k h
        (op ((pullbackTensorSequenceBase f).obj ((pullbackTensorSequenceBase g).obj V)))
        (((pullbackTensorSequenceAdjunction l E f).unit.app
          (((onComplex l E g).obj P).X p)).val.app _
          (((pullbackTensorSequenceAdjunction l E g).unit.app (P.X p)).val.app _ x))
        (((pullbackTensorSequenceAdjunction l E f).unit.app
          (((onComplex l E g).obj Q).X q)).val.app _
          (((pullbackTensorSequenceAdjunction l E g).unit.app (Q.X q)).val.app _ y)) := by
  have hn := congrArg (fun a ↦ a.val.app
      (op ((pullbackTensorSequenceBase g).obj V))
      (((pullbackTensorSequenceAdjunction l E g).unit.app
        (((total l E Z).obj (P, Q)).X k)).val.app (op V)
        (generator l E Z P Q p q k h (op V) x y)))
    ((pullbackTensorSequenceAdjunction l E f).unit.naturality
      (((pullbackTensorSequenceCochain l E g).hom.app (P, Q)).f k))
  change _ = ((inverse l E f).map
      (((pullbackTensorSequenceCochain l E g).hom.app (P, Q)).f k)).val.app _
      (((pullbackTensorSequenceAdjunction l E f).unit.app _).val.app _ _) at hn
  change (((pullbackTensorSequenceCochain l E f).hom.app _).f k).val.app _
    (((inverse l E f).map _).val.app _ _) = _
  apply Eq.trans (congrArg
    ((((pullbackTensorSequenceCochain l E f).hom.app
      ((onComplex l E g).obj P, (onComplex l E g).obj Q)).f k).val.app
      (op ((pullbackTensorSequenceBase f).obj ((pullbackTensorSequenceBase g).obj V))))
    hn.symm)
  exact (congrArg (fun z ↦
    (((pullbackTensorSequenceCochain l E f).hom.app
      ((onComplex l E g).obj P, (onComplex l E g).obj Q)).f k).val.app
      (op ((pullbackTensorSequenceBase f).obj ((pullbackTensorSequenceBase g).obj V)))
      (((pullbackTensorSequenceAdjunction l E f).unit.app
        (((total l E Y).obj ((onComplex l E g).obj P,
          (onComplex l E g).obj Q)).X k)).val.app
          (op ((pullbackTensorSequenceBase g).obj V)) z))
    (cochain_formula l E g P Q p q k h V x y)).trans
      (cochain_formula l E f ((onComplex l E g).obj P) ((onComplex l E g).obj Q)
        p q k h ((pullbackTensorSequenceBase g).obj V) _ _)

private theorem cochain_pure (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (P Q : Complex l E Z)
    (p q k : ℤ) (h : p + q = k) (n : ℕ) (U : Z.ProEt)
    (x : (P.X p).val.obj (op (n, U))) (y : (Q.X q).val.obj (op (n, U))) :
    let u := (onComplex l E f).map
        ((pullbackTensorSequenceCochain l E g).hom.app (P, Q)) ≫
      (pullbackTensorSequenceCochain l E f).hom.app
        ((onComplex l E g).obj P, (onComplex l E g).obj Q)
    let v := (pullbackTensorSequenceCochain l E (f ≫ g)).hom.app (P, Q) ≫
      (total l E X).map (Prod.mkHom
        ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app P)
        ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app Q))
    ((c.ordinaryDirect f g).hom.app _).val.app (op (n, U))
      ((u.f k).val.app _
        (((pullbackTensorSequenceAdjunction l E f).unit.app _).val.app _
          (((pullbackTensorSequenceAdjunction l E g).unit.app _).val.app _
            (generator l E Z P Q p q k h (op (n, U)) x y)))) =
    (v.f k).val.app _
      (((pullbackTensorSequenceAdjunction l E (f ≫ g)).unit.app _).val.app _
        (generator l E Z P Q p q k h (op (n, U)) x y))
    := by
  dsimp only
  let ρ : (n, (proEtaleBaseChange (f ≫ g)).obj U) ⟶
      (n, (proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)) :=
    (𝟙 n, (MorphismProperty.Over.pullbackComp f g).hom.app U)
  apply Eq.trans (c.sections f g
    (((total l E X).obj
      ((onComplex l E f).obj ((onComplex l E g).obj P),
        (onComplex l E f).obj ((onComplex l E g).obj Q))).X k) n U _)
  have hs := congrArg
    ((((total l E X).obj
      ((onComplex l E f).obj ((onComplex l E g).obj P),
        (onComplex l E f).obj ((onComplex l E g).obj Q))).X k).val.map
      ρ.op)
    (composite_tensor_unit l E f g P Q p q k h (n, U) x y)
  refine hs.trans ?_
  apply Eq.trans (generator_restrict.{u + 1, u, u}
    (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)
    ((onComplex l E f).obj ((onComplex l E g).obj P))
    ((onComplex l E f).obj ((onComplex l E g).obj Q)) p q k h
    ρ.op _ _)
  have hr := congrArg
    ((((total l E X).map (Prod.mkHom
      ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app P)
      ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app Q))).f k).val.app
        (op (n, (proEtaleBaseChange (f ≫ g)).obj U)))
    (cochain_formula l E (f ≫ g) P Q p q k h (n, U) x y)
  have ht := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
    (J := coefficientSequenceTopology (ProEt.topology X))
    (R := coefficientSequenceCommRingSheaf l E X)
    ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app P)
    ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app Q)
    p q k h (op (n, (proEtaleBaseChange (f ≫ g)).obj U))
    (((pullbackTensorSequenceAdjunction l E (f ≫ g)).unit.app (P.X p)).val.app _ x)
    (((pullbackTensorSequenceAdjunction l E (f ≫ g)).unit.app (Q.X q)).val.app _ y)
  have hr' := hr.trans ht
  have hp := compositor_unit_sections l E o c f g (P.X p) n U x
  have hq := compositor_unit_sections l E o c f g (Q.X q) n U y
  exact (congrArg₂ (fun x' y' ↦ generator l E X
    ((onComplex l E f).obj ((onComplex l E g).obj P))
    ((onComplex l E f).obj ((onComplex l E g).obj Q)) p q k h
    (op (n, (proEtaleBaseChange (f ≫ g)).obj U)) x' y') hp hq).symm.trans hr'.symm

/-- The unit-normalized tensor maps on coefficient-system cochains commute with
composition of inverse images.
Source: Stacks 03EL and 07A4; the pure-generator step in the strict-system
realization of fix-prop-coherence
(blueprint: lem-sf-integral-system-tensor-cochain-composition).

Proof: transpose under the inverse-image adjunction for the composite. The unit
conjugation equation and the section normalization of the direct compositor
express this transpose by restriction along pullbackComp. The two successive
tensor comparisons take unit-inserted generators to the tensors of the two
successive unit images. Naturality of tensor generators under restriction and
the ordinary compositor's unit equation identify these with the composite unit
images. Total-summand pure generators detect equality of the transposes. -/
theorem integralSystemTensorCochainComposition (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P Q : CochainComplex (coefficientSequenceModules l E Z) ℤ) :
    (NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology Z))
          (coefficientSequenceCommRingSheaf l E Z)).obj (P, Q)) ≫
        ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).map
          ((pullbackTensorSequenceCochain l E g).hom.app (P, Q)) ≫
        (pullbackTensorSequenceCochain l E f).hom.app
          (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj P,
            ((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj Q) =
      (pullbackTensorSequenceCochain l E (f ≫ g)).hom.app (P, Q) ≫
        (coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)).map (Prod.mkHom
          ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app P)
          ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app Q)) := by
  let u := (onComplex l E f).map
      ((pullbackTensorSequenceCochain l E g).hom.app (P, Q)) ≫
    (pullbackTensorSequenceCochain l E f).hom.app
      ((onComplex l E g).obj P, (onComplex l E g).obj Q)
  let v := (pullbackTensorSequenceCochain l E (f ≫ g)).hom.app (P, Q) ≫
    (total l E X).map (Prod.mkHom
      ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app P)
      ((NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app Q))
  change (NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app _ ≫ u = v
  apply HomologicalComplex.hom_ext
  intro k
  apply ((pullbackTensorSequenceAdjunction l E (f ≫ g)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (pullbackTensorSequenceAdjunction l E (f ≫ g)).unit.app _ ≫
      (pullbackTensorSequenceDirect l E (f ≫ g)).map
        ((c.ordinaryPull f g).hom.app _ ≫ u.f k) = _
  have he : (pullbackTensorSequenceAdjunction l E (f ≫ g)).unit.app _ ≫
      (pullbackTensorSequenceDirect l E (f ≫ g)).map
        ((c.ordinaryPull f g).hom.app _ ≫ u.f k) =
      ((pullbackTensorSequenceAdjunction l E g).comp
        (pullbackTensorSequenceAdjunction l E f)).unit.app _ ≫
        ((pullbackTensorSequenceDirect l E f).comp
          (pullbackTensorSequenceDirect l E g)).map (u.f k) ≫
        (c.ordinaryDirect f g).hom.app _ := by
    exact transpose_paste
      (pullbackTensorSequenceDirect l E (f ≫ g))
      ((pullbackTensorSequenceDirect l E f).comp (pullbackTensorSequenceDirect l E g))
      (c.ordinaryDirect f g).hom _ _ _
      (compositor_unit l E o c f g (((total l E Z).obj (P, Q)).X k)) (u.f k)
  apply Eq.trans he
  simp only [Adjunction.comp_unit_app]
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u}
    (J := coefficientSequenceTopology (ProEt.topology Z))
    (R := coefficientSequenceCommRingSheaf l E Z) P Q k _
  intro p q h V x y
  let n := V.unop.1
  let U := V.unop.2
  change ((c.ordinaryDirect f g).hom.app _).val.app (op (n, U))
      ((u.f k).val.app _
        (((pullbackTensorSequenceAdjunction l E f).unit.app _).val.app _
          (((pullbackTensorSequenceAdjunction l E g).unit.app _).val.app _
            (generator l E Z P Q p q k h (op (n, U)) x y)))) =
    (v.f k).val.app _
      (((pullbackTensorSequenceAdjunction l E (f ≫ g)).unit.app _).val.app _
        (generator l E Z P Q p q k h (op (n, U)) x y))
  exact cochain_pure l E o c f g P Q p q k h n U x y

end WeilConjectures.IntegralSystemRealization
