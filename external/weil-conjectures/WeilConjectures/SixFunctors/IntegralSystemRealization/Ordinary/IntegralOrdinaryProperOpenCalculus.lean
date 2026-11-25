/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExpressionReduction
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryCanonicalIsoSquare
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity

/-! # Categorical calculus for ordinary proper/open coefficient squares

Source: blueprint fix-prop-coherence, the coefficient comparisons of individual maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleCanonicalTensorComparison ringedPullComp
  ringedRestrictFactor restrictFactor properOpenLambda ringedProperOpenLambda
  ringedOpenComp Compositors.openComp openCongr ringedOpenCongr ordinaryPushReduction

/-- Conjugation by adjunction preserves a commuting coefficient square.
Source: blueprint fix-prop-coherence, coherence of adjunction units and counits.
(blueprint: lem-sf-integral-ordinary-proper-open-conjugate-square).

Proof: apply the mate equivalence to the equality of the two whiskered squares.
The two vertical-composition identities for conjugate equivalences identify its
sides. Evaluate the resulting natural-transformation equality at the object X;
associator and identity components disappear. -/
theorem ordinaryProperOpenConjugateSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P P' : A ⥤ B} {Q Q' : B ⥤ A} {F F' : C ⥤ D} {G G' : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D}
    (a : P ⊣ Q) (a' : P' ⊣ Q') (b : F ⊣ G) (b' : F' ⊣ G')
    (χ : R ⋙ F ⟶ P ⋙ T) (χ' : R ⋙ F' ⟶ P' ⋙ T)
    (α : P' ⟶ P) (β : F' ⟶ F)
    (h : (TwoSquare.mk _ _ _ _ χ).whiskerRight β =
      (TwoSquare.mk _ _ _ _ χ').whiskerLeft α) (X : B) :
    (mateEquiv a b χ).app X ≫
        (conjugateEquiv b b' β).app (T.obj X) =
      R.map ((conjugateEquiv a a' α).app X) ≫
        (mateEquiv a' b' χ').app X := by
  have hh := congrArg (mateEquiv a b') h
  rw [mateEquiv_conjugateEquiv_vcomp a b b',
    conjugateEquiv_mateEquiv_vcomp a a' b'] at hh
  have hx := congrArg (fun t ↦ t.app X) hh
  simpa only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Functor.comp_obj] using hx

private theorem composite_mate_app
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {P : A ⥤ B} {Q : B ⥤ A} {P' : B ⥤ C} {Q' : C ⥤ B}
    {L : D ⥤ E} {R : E ⥤ D} {L' : E ⥤ F} {R' : F ⥤ E}
    {U : A ⥤ D} {V : B ⥤ E} {W : C ⥤ F}
    (a : P ⊣ Q) (a' : P' ⊣ Q') (b : L ⊣ R) (b' : L' ⊣ R')
    (χ : U ⋙ L ⟶ P ⋙ V) (χ' : V ⋙ L' ⟶ P' ⋙ W) (X : C) :
    (mateEquiv (a.comp a') (b.comp b') (TwoSquare.vComp χ χ')).app X =
      (mateEquiv a b χ).app (Q'.obj X) ≫
        R.map ((mateEquiv a' b' χ').app X) := by
  rw [mateEquiv_hcomp]
  simp only [TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

private theorem map_coefficient_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {R : A ⥤ B} {T : C ⥤ D} {F : A ⥤ C} {G : B ⥤ D}
    (δ : F ⋙ T ⟶ R ⋙ G) {L L' : A} {M M' : B}
    (q : R.obj L ⟶ M) (q' : R.obj L' ⟶ M')
    (α : L ⟶ L') (β : M ⟶ M') (h : q ≫ β = R.map α ≫ q') :
    δ.app L ≫ G.map q ≫ G.map β =
      T.map (F.map α) ≫ δ.app L' ≫ G.map q' := by
  have hn := δ.naturality α
  dsimp only [Functor.comp_map] at hn
  rw [← G.map_comp, h, G.map_comp, ← Category.assoc, ← hn]
  exact Category.assoc _ _ _

private theorem paste_five {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A₀ A₁ A₂ A₃ A₄ A₅ : C} {B₀ B₁ B₂ B₃ B₄ B₅ : D}
    (q₀ : R.obj A₀ ⟶ B₀) (q₁ : R.obj A₁ ⟶ B₁)
    (q₂ : R.obj A₂ ⟶ B₂) (q₃ : R.obj A₃ ⟶ B₃)
    (q₄ : R.obj A₄ ⟶ B₄) (q₅ : R.obj A₅ ⟶ B₅)
    (r₀ : A₀ ⟶ A₁) (r₁ : A₁ ⟶ A₂) (r₂ : A₂ ⟶ A₃)
    (r₃ : A₃ ⟶ A₄) (r₄ : A₄ ⟶ A₅)
    (s₀ : B₀ ⟶ B₁) (s₁ : B₁ ⟶ B₂) (s₂ : B₂ ⟶ B₃)
    (s₃ : B₃ ⟶ B₄) (s₄ : B₄ ⟶ B₅)
    (h₀ : q₀ ≫ s₀ = R.map r₀ ≫ q₁) (h₁ : q₁ ≫ s₁ = R.map r₁ ≫ q₂)
    (h₂ : q₂ ≫ s₂ = R.map r₂ ≫ q₃) (h₃ : q₃ ≫ s₃ = R.map r₃ ≫ q₄)
    (h₄ : q₄ ≫ s₄ = R.map r₄ ≫ q₅) :
    q₀ ≫ s₀ ≫ s₁ ≫ s₂ ≫ s₃ ≫ s₄ = R.map (r₀ ≫ r₁ ≫ r₂ ≫ r₃ ≫ r₄) ≫ q₅ := by
  rw [reassoc_of% h₀, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [R.map_comp, Category.assoc]

@[irreducible] private def restrictionIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {J : B ⥤ C} {K : A ⥤ C} (P : C ⥤ B)
    (cr : F ⋙ J ≅ K) (ur : 𝟭 B ≅ J ⋙ P) : K ⋙ P ≅ F :=
  Functor.isoWhiskerRight cr.symm P ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F ur.symm ≪≫ Functor.rightUnitor _

private theorem inverse_unit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasZeroMorphisms D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : Q ⋙ R ⟶ T ⋙ G) (ur : 𝟭 A ≅ P ⋙ Q) (us : 𝟭 C ≅ F ⋙ G)
    (X : A) (δ : T.obj (P.obj X) ⟶ F.obj (R.obj X))
    [IsIso (((mateEquiv a b).symm χ).app X)]
    (hur : ur.hom.app X = a.unit.app X)
    (hus : us.hom.app (R.obj X) = b.unit.app (R.obj X))
    (hδ : δ = GeneratorReduction.inverseOrZero
      (((mateEquiv a b).symm χ).app X)) :
    χ.app (P.obj X) ≫ G.map δ ≫ us.inv.app (R.obj X) = R.map (ur.inv.app X) := by
  have hu := GeneratorReduction.inverse_mate_unit_square a b χ (𝟙 (R.obj X))
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hu
  have hx := inverse_square R (ur.app X) (us.app (R.obj X)) (𝟙 _)
    (χ.app (P.obj X) ≫ G.map δ) (by
      simp only [Iso.app_hom, Category.id_comp, hur, hus, hδ]
      exact hu)
  simpa only [Iso.app_inv, Category.comp_id, Category.assoc] using hx

private theorem trans_iso_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ⥤ B) (T : C ⥤ D)
    {F₀ F₁ F₂ : C ⥤ A} {G₀ G₁ G₂ : D ⥤ B}
    (r : F₀ ≅ F₁) (r' : F₁ ≅ F₂) (s : G₀ ≅ G₁) (s' : G₁ ≅ G₂)
    (L : C) (q₀ : R.obj (F₀.obj L) ⟶ G₀.obj (T.obj L))
    (q₁ : R.obj (F₁.obj L) ⟶ G₁.obj (T.obj L))
    (q₂ : R.obj (F₂.obj L) ⟶ G₂.obj (T.obj L))
    (h : q₀ ≫ s.hom.app (T.obj L) = R.map (r.hom.app L) ≫ q₁)
    (h' : q₁ ≫ s'.hom.app (T.obj L) = R.map (r'.hom.app L) ≫ q₂) :
    q₀ ≫ (s ≪≫ s').hom.app (T.obj L) = R.map ((r ≪≫ r').hom.app L) ≫ q₂ := by
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [reassoc_of% h, h', ← R.map_comp_assoc]

attribute [local implicit_reducible] PurCompactSupport.completed
  coefficientSequenceHasDerived scalarReductionSourceDerived integralTowerHasDerivedCategory
  integralCompletedRingHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

@[irreducible] private def openR (o : Operations l E) (m : RealizationModel l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    ringedOpen l E j ⋙ (calculus l E V).reduction ⟶
      (calculus l E U).reduction ⋙ Operations.shriek l E o j :=
  (NatIso.ofComponents (fun L ↦
    @asIso _ _ _ _ ((m.openReduction l E j).app L)
      (GeneratorReduction.fixedOpenReduction_isIso l E o m j L))
    (fun f ↦ (m.openReduction l E j).naturality f)).inv

private theorem openR_app (o : Operations l E) (m : RealizationModel l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] (L : Integral l E U) :
    (openR l E o m j).app L =
      GeneratorReduction.inverseOrZero ((m.openReduction l E j).app L) := by
  have := GeneratorReduction.fixedOpenReduction_isIso l E o m j L
  rw [GeneratorReduction.inverseOrZero_eq_inv, openR]
  rfl

private theorem open_comp_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ W)
    [IsOpenImmersion j] [IsOpenImmersion k] (L : Integral l E U) :
    (openR l E o a.realizationModel k).app ((ringedOpen l E j).obj L) ≫
        (Operations.shriek l E o k).map ((openR l E o a.realizationModel j).app L) ≫
        (a.compositors.openComp l E j k).hom.app ((calculus l E U).reduction.obj L) =
      (calculus l E W).reduction.map ((ringedOpenComp l E j k).hom.app L) ≫
        (openR l E o a.realizationModel (j ≫ k)).app L := by
  have hh := left_mate_compositor_square
    (ringedOpenAdj l E j) (ringedOpenAdj l E k) (ringedOpenAdj l E (j ≫ k))
    (o.extension j).adj (o.extension k).adj (o.extension (j ≫ k)).adj
    (a.realizationModel.openReduction l E j) (a.realizationModel.openReduction l E k)
    (a.realizationModel.openReduction l E (j ≫ k))
    (ringedOpenComp l E j k).inv (a.compositors.openComp l E j k).inv (by
      intro M
      simp only [RealizationModel.openReduction, ringedOpenAdj, ringedOpenComp,
        Compositors.openComp, Equiv.apply_symm_apply,
        Adjunction.conjugateEquiv_leftAdjointCompIso_inv, Iso.symm_hom]
      simpa only [] using!
        pull_comp_inverse l E o a.realizationModel a.compositors j k M)
  have hx := congrArg (fun v ↦ v.app L) hh
  dsimp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app] at hx
  simp only [Category.id_comp, Category.comp_id, Functor.comp_obj] at hx
  have hj : ∀ M, IsIso ((a.realizationModel.openReduction l E j).app M) :=
    fun M ↦ GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j M
  have hk : ∀ M, IsIso ((a.realizationModel.openReduction l E k).app M) :=
    fun M ↦ GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel k M
  have hjk : ∀ M, IsIso ((a.realizationModel.openReduction l E (j ≫ k)).app M) :=
    fun M ↦ GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel _ M
  have hi := congrArg (fun f ↦ GeneratorReduction.inverseOrZero f) hx
  simp only [GeneratorReduction.inverseOrZero_eq_inv, IsIso.inv_comp,
    ← CategoryTheory.Functor.map_inv, NatIso.inv_inv_app, Category.assoc] at hi
  simpa only [openR_app, GeneratorReduction.inverseOrZero_eq_inv, Category.assoc] using! hi

private theorem open_congr_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} {j k : U ⟶ V} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) (L : Integral l E U) :
    (openR l E o a.realizationModel j).app L ≫
        (openCongr l E o h).hom.app ((calculus l E U).reduction.obj L) =
      (calculus l E V).reduction.map ((ringedOpenCongr l E h).hom.app L) ≫
        (openR l E o a.realizationModel k).app L := by
  subst k
  have hr : ringedOpenCongr l E (rfl : j = j) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ((ringedOpenAdj l E j).homEquiv _ _).injective
    simp [ringedOpenCongr, Adjunction.leftAdjointUniq,
      conjugateIsoEquiv, Adjunction.homEquiv_unit]
  have hs : openCongr l E o (rfl : j = j) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ((o.extension j).adj.homEquiv _ _).injective
    simp [openCongr, Adjunction.leftAdjointUniq,
      conjugateIsoEquiv, Adjunction.homEquiv_unit]
  rw [hr, hs]
  simp only [Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id _

private theorem clopen_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] [IsClosedImmersion j]
    (L : Integral l E U) :
    (openR l E o a.realizationModel j).app L ≫
        (a.openComparisons.clopen j).hom.app ((calculus l E U).reduction.obj L) =
      (calculus l E V).reduction.map ((a.ringedOpenComparisons.clopen j).hom.app L) ≫
        (ordinaryPushReduction l E o a.realizationModel j).app L := by
  let U' : Over V := Over.mk j
  let V' : Over V := Over.mk (𝟙 V)
  let f : U' ⟶ V' := Over.homMk j (Category.comp_id j)
  let X : PUnit.{u+1} → Over V := fun _ ↦ U'
  have : IsOpenImmersion f.left := ‹IsOpenImmersion j›
  have : IsClosedImmersion f.left := ‹IsClosedImmersion j›
  have h := clopen_square l E o a (X := X) (fun _ ↦ L) f
    (inferInstance : QuasiCompact j) (inferInstance : IsProper j) (.var PUnit.unit)
  change (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app L) ≫
      (Operations.shriek l E o j).map (𝟙 _)) ≫
      (a.openComparisons.clopen j).hom.app ((calculus l E U).reduction.obj L) =
    (calculus l E V).reduction.map ((a.ringedOpenComparisons.clopen j).hom.app L) ≫
      (ordinaryPushReduction l E o a.realizationModel j).app L ≫
      (Operations.push l E o j).map (𝟙 _) at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  simpa only [openR_app] using! h

private theorem push_comp_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    [IsProper f] [IsProper g] (L : Integral l E U) :
    (ordinaryPushReduction l E o a.realizationModel g).app ((ringedPush l E f).obj L) ≫
        (Operations.push l E o g).map
          ((ordinaryPushReduction l E o a.realizationModel f).app L) ≫
        (a.compositors.pushComp l E f g).hom.app ((calculus l E U).reduction.obj L) =
      (calculus l E W).reduction.map ((ringedPushComp l E f g).hom.app L) ≫
        (ordinaryPushReduction l E o a.realizationModel (f ≫ g)).app L := by
  let U' : Over W := Over.mk (f ≫ g)
  let V' : Over W := Over.mk g
  let W' : Over W := Over.mk (𝟙 W)
  let f' : U' ⟶ V' := Over.homMk f rfl
  let g' : V' ⟶ W' := Over.homMk g (Category.comp_id g)
  let X : PUnit.{u+1} → Over W := fun _ ↦ U'
  have h := pushComp_square l E o a (X := X) (fun _ ↦ L) f' g'
    (inferInstance : IsProper f) (inferInstance : IsProper g)
    (inferInstance : IsProper (f ≫ g)) (.var PUnit.unit)
  change ((ordinaryPushReduction l E o a.realizationModel g).app ((ringedPush l E f).obj L) ≫
      (Operations.push l E o g).map
        ((ordinaryPushReduction l E o a.realizationModel f).app L ≫
          (Operations.push l E o f).map (𝟙 _))) ≫
      (a.compositors.pushComp l E f g).hom.app ((calculus l E U).reduction.obj L) =
    (calculus l E W).reduction.map ((ringedPushComp l E f g).hom.app L) ≫
      (ordinaryPushReduction l E o a.realizationModel (f ≫ g)).app L ≫
      (Operations.push l E o (f ≫ g)).map (𝟙 _) at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  simpa only [Category.assoc] using! h

private theorem push_congr_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} {f g : U ⟶ V} (h : f = g) (L : Integral l E U) :
    (ordinaryPushReduction l E o a.realizationModel f).app L ≫
        (eqToIso (congrArg (Operations.push l E o) h)).hom.app
          ((calculus l E U).reduction.obj L) =
      (calculus l E V).reduction.map
          ((eqToIso (congrArg (ringedPush l E) h)).hom.app L) ≫
        (ordinaryPushReduction l E o a.realizationModel g).app L := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id _

private theorem unit_inverse_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] (L : Integral l E U) :
    (a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E j).map ((openR l E o a.realizationModel j).app L) ≫
        (a.openComparisons.unit l E o a.compositors j).inv.app
          ((calculus l E U).reduction.obj L) =
      (calculus l E U).reduction.map
        ((a.ringedOpenComparisons.unit l E a.ringedModels j).inv.app L) := by
  have hi : IsIso (((mateEquiv (ringedOpenAdj l E j) (o.extension j).adj).symm
    (a.realizationModel.reductionPull j).hom).app L) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j L
  exact inverse_unit_square (ringedOpenAdj l E j) (o.extension j).adj
    (a.realizationModel.reductionPull j).hom
    (a.ringedOpenComparisons.unit l E a.ringedModels j)
    (a.openComparisons.unit l E o a.compositors j) L
    ((openR l E o a.realizationModel j).app L) (by rfl) (by rfl)
    (by rw [openR_app]; rfl)

attribute [local irreducible] RingedOpenComparisons.unit OpenComparisons.unit

private theorem open_restriction_coefficient_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U P V : Scheme.{u}} (s : U ⟶ P) (b : P ⟶ V) (k : U ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (h : s ≫ b = k) (L : Integral l E U) :
    (a.realizationModel.reductionPull b).hom.app ((ringedOpen l E k).obj L) ≫
        (pull l E b).map ((openR l E o a.realizationModel k).app L) ≫
        (restrictionIso (F := Operations.shriek l E o s)
          (J := Operations.shriek l E o b) (K := Operations.shriek l E o k)
          (pull l E b) (a.compositors.openComp l E s b ≪≫ openCongr l E o h)
          (a.openComparisons.unit l E o a.compositors b)).hom.app
            ((calculus l E U).reduction.obj L) =
      (calculus l E P).reduction.map
          ((restrictionIso (F := ringedOpen l E s) (J := ringedOpen l E b)
            (K := ringedOpen l E k) (ringedPull l E b)
            (ringedOpenComp l E s b ≪≫ ringedOpenCongr l E h)
            (a.ringedOpenComparisons.unit l E a.ringedModels b)).hom.app L) ≫
        (openR l E o a.realizationModel s).app L := by
  let cr := ringedOpenComp l E s b ≪≫ ringedOpenCongr l E h
  let cs := a.compositors.openComp l E s b ≪≫ openCongr l E o h
  let δ := (openR l E o a.realizationModel b).app ((ringedOpen l E s).obj L) ≫
    (Operations.shriek l E o b).map ((openR l E o a.realizationModel s).app L)
  have hc := trans_iso_square (calculus l E V).reduction (calculus l E U).reduction
    (ringedOpenComp l E s b) (ringedOpenCongr l E h)
    (a.compositors.openComp l E s b) (openCongr l E o h)
    L δ ((openR l E o a.realizationModel (s ≫ b)).app L)
    ((openR l E o a.realizationModel k).app L)
    ((Category.assoc _ _ _).trans (open_comp_coefficient_square l E o a s b L))
    (open_congr_coefficient_square l E o a h L)
  have hc' := inverse_square (calculus l E V).reduction (cr.app L)
    (cs.app ((calculus l E U).reduction.obj L)) δ
    ((openR l E o a.realizationModel k).app L) hc
  have hn := (a.realizationModel.reductionPull b).hom.naturality (cr.inv.app L)
  have hn' := (a.openComparisons.unit l E o a.compositors b).inv.naturality
    ((openR l E o a.realizationModel s).app L)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hn hn'
  simp only [restrictionIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Iso.symm_hom, Functor.map_comp, Category.id_comp,
    Category.comp_id, Functor.comp_obj, Functor.id_obj, Category.assoc]
  rw [← (pull l E b).map_comp_assoc]
  rw [show (openR l E o a.realizationModel k).app L ≫
      cs.inv.app ((calculus l E U).reduction.obj L) =
      (calculus l E V).reduction.map (cr.inv.app L) ≫
        (openR l E o a.realizationModel b).app ((ringedOpen l E s).obj L) ≫
        (Operations.shriek l E o b).map ((openR l E o a.realizationModel s).app L) by
    simpa only [Iso.app_inv, δ, Category.assoc] using hc']
  simp only [(pull l E b).map_comp, Category.assoc]
  rw [← reassoc_of% hn, hn',
    reassoc_of% (unit_inverse_coefficient_square l E o a b ((ringedOpen l E s).obj L))]

end WeilConjectures.IntegralSystemRealization
