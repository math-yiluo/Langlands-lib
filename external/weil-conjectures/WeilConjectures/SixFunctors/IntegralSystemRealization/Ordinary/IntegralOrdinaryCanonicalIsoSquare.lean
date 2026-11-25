/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExpressionReduction
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.CanonicalReductionTensorPull
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity

/-! # Ordinary coefficient squares for canonical isomorphisms

Source: blueprint fix-prop-coherence, the coefficient comparisons of individual maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
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
private theorem inverse_square {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {K H : C} {M N : D} (r : K ≅ H) (s : M ≅ N)
    (q : R.obj K ⟶ M) (t : R.obj H ⟶ N)
    (h : q ≫ s.hom = R.map r.hom ≫ t) :
    t ≫ s.inv = R.map r.inv ≫ q := by
  apply (cancel_epi (R.map r.hom)).1
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]

private theorem inverse_mate_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (δ : Q ⋙ R ⟶ T ⋙ G) {X : A} {Y : B} {M : C} {N : D}
    [IsIso (((mateEquiv a b).symm δ).app X)]
    (q : R.obj X ⟶ M) (t : T.obj Y ⟶ N)
    (α : P.obj X ⟶ Y) (β : F.obj M ⟶ N)
    (h : q ≫ (b.homEquiv _ _) β =
      R.map ((a.homEquiv _ _) α) ≫ δ.app Y ≫ G.map t) :
    inv (((mateEquiv a b).symm δ).app X) ≫ F.map q ≫ β = T.map α ≫ t := by
  apply (cancel_epi (((mateEquiv a b).symm δ).app X)).1
  simp only [IsIso.hom_inv_id_assoc]
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  change q ≫ (b.homEquiv _ _) β =
    b.unit.app (R.obj X) ≫ G.map
      (((mateEquiv a b).symm δ).app X ≫ T.map α ≫ t)
  rw [G.map_comp, G.map_comp]
  rw [← reassoc_of% (unit_mateEquiv_symm a b δ X)]
  have hn := δ.naturality α
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← R.map_comp_assoc]
  exact h

private theorem left_mate_compositor_square
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
    (h : ∀ X : A₂,
      (mateEquiv a b χ).app (Q'.obj X) ≫
          G.map ((mateEquiv a' b' χ').app X) ≫
          (conjugateEquiv (b.comp b') b'' β).app (R₂.obj X) =
        R₀.map ((conjugateEquiv (a.comp a') a'' α).app X) ≫
          (mateEquiv a'' b'' χ'').app X) :
    (TwoSquare.vComp χ χ').whiskerRight β =
      (TwoSquare.mk _ _ _ _ χ'').whiskerLeft α := by
  apply (mateEquiv (a.comp a') b'').injective
  rw [mateEquiv_conjugateEquiv_vcomp (a.comp a') (b.comp b') b'',
    conjugateEquiv_mateEquiv_vcomp (a.comp a') a'' b'', mateEquiv_hcomp a b a' b']
  apply NatTrans.ext
  funext X
  simpa only [TwoSquare.hComp, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Functor.comp_obj, Category.assoc] using h X

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem pull_comp_inverse (o : Operations l E) (m : RealizationModel l E o)
    (c : Compositors l E o) {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    (L : Integral l E W) :
    (m.reductionPull f).hom.app ((ringedPull l E g).obj L) ≫
        (pull l E f).map ((m.reductionPull g).hom.app L) ≫
        (c.pullComp f g).inv.app ((calculus l E W).reduction.obj L) =
      (calculus l E U).reduction.map ((ringedPullComp l E f g).inv.app L) ≫
        (m.reductionPull (f ≫ g)).hom.app L := by
  apply (cancel_epi ((calculus l E U).reduction.map
    ((ringedPullComp l E f g).hom.app L))).1
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [reassoc_of% (GeneratorReduction.canonicalReductionPullComposition l E o m c f g L)]
  simp only [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

private theorem pull_congr_nat (o : Operations l E) (m : RealizationModel l E o)
    {U V : Scheme.{u}} {f g : U ⟶ V} (w : f = g) :
    (m.reductionPull f).hom ≫ Functor.whiskerLeft (calculus l E V).reduction
        (eqToIso (congrArg (pull l E) w.symm)).inv =
      Functor.whiskerRight (eqToIso (congrArg (ringedPull l E) w.symm)).inv
        (calculus l E U).reduction ≫ (m.reductionPull g).hom := by
  subst g
  simp only [eqToIso_refl, Iso.refl_inv, Functor.whiskerLeft_id', Functor.whiskerRight_id',
    Category.comp_id, Category.id_comp]

private theorem paste_three {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A₀ A₁ A₂ A₃ : C} {B₀ B₁ B₂ B₃ : D}
    (q₀ : R.obj A₀ ⟶ B₀) (q₁ : R.obj A₁ ⟶ B₁)
    (q₂ : R.obj A₂ ⟶ B₂) (q₃ : R.obj A₃ ⟶ B₃)
    (r₀ : A₀ ⟶ A₁) (r₁ : A₁ ⟶ A₂) (r₂ : A₂ ⟶ A₃)
    (s₀ : B₀ ⟶ B₁) (s₁ : B₁ ⟶ B₂) (s₂ : B₂ ⟶ B₃)
    (h₀ : q₀ ≫ s₀ = R.map r₀ ≫ q₁)
    (h₁ : q₁ ≫ s₁ = R.map r₁ ≫ q₂)
    (h₂ : q₂ ≫ s₂ = R.map r₂ ≫ q₃) :
    q₀ ≫ s₀ ≫ s₁ ≫ s₂ = R.map (r₀ ≫ r₁ ≫ r₂) ≫ q₃ := by
  rw [reassoc_of% h₀, reassoc_of% h₁, h₂]
  simp only [R.map_comp, Category.assoc]

private theorem paste_iso_square
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    (R : C ⥤ D) (S : C' ⥤ D)
    {A₀ A₁ A₂ A₃ : C} {B₀ B₁ B₂ B₃ : C'}
    (q₀ : R.obj A₀ ⟶ S.obj B₀) (q₁ : R.obj A₁ ⟶ S.obj B₁)
    (q₂ : R.obj A₂ ⟶ S.obj B₂) (q₃ : R.obj A₃ ⟶ S.obj B₃)
    (r₀ : A₁ ≅ A₀) (r₁ : A₂ ≅ A₁) (r₂ : A₂ ≅ A₃)
    (s₀ : B₁ ≅ B₀) (s₁ : B₂ ≅ B₁) (s₂ : B₂ ≅ B₃)
    (h₀ : q₀ ≫ S.map s₀.inv = R.map r₀.inv ≫ q₁)
    (h₁ : q₁ ≫ S.map s₁.inv = R.map r₁.inv ≫ q₂)
    (h₂ : q₂ ≫ S.map s₂.hom = R.map r₂.hom ≫ q₃) :
    q₀ ≫ S.map (s₂.symm ≪≫ s₁ ≪≫ s₀).inv =
      R.map (r₂.symm ≪≫ r₁ ≪≫ r₀).inv ≫ q₃ := by
  simpa only [Iso.trans_inv, Iso.symm_inv, S.map_comp, Category.assoc] using
    paste_three R q₀ q₁ q₂ q₃ r₀.inv r₁.inv r₂.hom
      (S.map s₀.inv) (S.map s₁.inv) (S.map s₂.hom) h₀ h₁ h₂

private theorem pull_comp_nat (o : Operations l E) (m : RealizationModel l E o)
    (c : Compositors l E o) {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) :
    (Functor.whiskerLeft (ringedPull l E g) (m.reductionPull f).hom ≫
        Functor.whiskerRight (m.reductionPull g).hom (pull l E f)) ≫
        Functor.whiskerLeft (calculus l E W).reduction (c.pullComp f g).inv =
      Functor.whiskerRight (ringedPullComp l E f g).inv (calculus l E U).reduction ≫
        (m.reductionPull (f ≫ g)).hom := by
  apply NatTrans.ext
  funext A
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Category.assoc] using! pull_comp_inverse l E o m c f g A

private theorem pull_comp_nat_forward (o : Operations l E) (m : RealizationModel l E o)
    (c : Compositors l E o) {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) :
    (m.reductionPull (f ≫ g)).hom ≫
        Functor.whiskerLeft (calculus l E W).reduction (c.pullComp f g).hom =
      Functor.whiskerRight (ringedPullComp l E f g).hom (calculus l E U).reduction ≫
        Functor.whiskerLeft (ringedPull l E g) (m.reductionPull f).hom ≫
        Functor.whiskerRight (m.reductionPull g).hom (pull l E f) := by
  apply NatTrans.ext
  funext A
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Category.assoc] using!
      (GeneratorReduction.canonicalReductionPullComposition l E o m c f g A).symm

private theorem pull_square_nat (o : Operations l E) (m : RealizationModel l E o)
    (c : Compositors l E o) {U' U V' V : Scheme.{u}}
    (v : U' ⟶ U) (j' : U' ⟶ V') (j : U ⟶ V) (g : V' ⟶ V)
    (w : v ≫ j = j' ≫ g) :
    (Functor.whiskerLeft (ringedPull l E j) (m.reductionPull v).hom ≫
        Functor.whiskerRight (m.reductionPull j).hom (pull l E v)) ≫
        Functor.whiskerLeft (calculus l E V).reduction (c.square l E v j' j g w).inv =
      Functor.whiskerRight (ringedSquare l E v j' j g w).inv (calculus l E U').reduction ≫
        (Functor.whiskerLeft (ringedPull l E g) (m.reductionPull j').hom ≫
          Functor.whiskerRight (m.reductionPull g).hom (pull l E j')) := by
  let R := (Functor.whiskeringRight (Integral l E V) (Integral l E U')
    (System l E U')).obj (calculus l E U').reduction
  let S := (Functor.whiskeringLeft (Integral l E V) (System l E V)
    (System l E U')).obj (calculus l E V).reduction
  let q₀ : (ringedPull l E j ⋙ ringedPull l E v) ⋙ (calculus l E U').reduction ⟶
      (calculus l E V).reduction ⋙ (pull l E j ⋙ pull l E v) :=
    Functor.whiskerLeft (ringedPull l E j) (m.reductionPull v).hom ≫
      Functor.whiskerRight (m.reductionPull j).hom (pull l E v)
  let q₃ : (ringedPull l E g ⋙ ringedPull l E j') ⋙ (calculus l E U').reduction ⟶
      (calculus l E V).reduction ⋙ (pull l E g ⋙ pull l E j') :=
    Functor.whiskerLeft (ringedPull l E g) (m.reductionPull j').hom ≫
      Functor.whiskerRight (m.reductionPull g).hom (pull l E j')
  have h := paste_iso_square R S q₀ (m.reductionPull (v ≫ j)).hom
    (m.reductionPull (j' ≫ g)).hom q₃
    (ringedPullComp l E v j)
    (eqToIso (congrArg (ringedPull l E) w.symm))
    (ringedPullComp l E j' g)
    (c.pullComp v j)
    (eqToIso (congrArg (pull l E) w.symm))
    (c.pullComp j' g)
    (by
      dsimp only [R, S, q₀, Functor.whiskeringRight_obj_map, Functor.whiskeringLeft_obj_map]
      exact pull_comp_nat l E o m c v j)
    (by
      dsimp only [R, S, Functor.whiskeringRight_obj_map, Functor.whiskeringLeft_obj_map]
      exact pull_congr_nat l E o m w)
    (by
      dsimp only [R, S, q₃, Functor.whiskeringRight_obj_map, Functor.whiskeringLeft_obj_map]
      exact pull_comp_nat_forward l E o m c j' g)
  simpa only [Compositors.square, ringedSquare, R, S, q₀, q₃,
    Functor.whiskeringRight_obj_map, Functor.whiskeringLeft_obj_map] using! h

attribute [local irreducible] ringedSquare Compositors.square

private theorem whisker_square_app
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category B₀] [Category B₁] [Category B₂] [Category B₃]
    {R₀ : A₀ ⥤ B₀} {R₁ : A₁ ⥤ B₁} {R₂ : A₂ ⥤ B₂} {R₃ : A₃ ⥤ B₃}
    {Pj : A₀ ⥤ A₁} {Pv : A₁ ⥤ A₃} {Pg : A₀ ⥤ A₂} {Pj' : A₂ ⥤ A₃}
    {Sj : B₀ ⥤ B₁} {Sv : B₁ ⥤ B₃} {Sg : B₀ ⥤ B₂} {Sj' : B₂ ⥤ B₃}
    (δj : Pj ⋙ R₁ ⟶ R₀ ⋙ Sj) (δv : Pv ⋙ R₃ ⟶ R₁ ⋙ Sv)
    (δg : Pg ⋙ R₂ ⟶ R₀ ⋙ Sg) (δj' : Pj' ⋙ R₃ ⟶ R₂ ⋙ Sj')
    (r : Pj ⋙ Pv ⟶ Pg ⋙ Pj') (s : Sj ⋙ Sv ⟶ Sg ⋙ Sj')
    (h : (Functor.whiskerLeft Pj δv ≫ Functor.whiskerRight δj Sv) ≫
        Functor.whiskerLeft R₀ s = Functor.whiskerRight r R₃ ≫
          (Functor.whiskerLeft Pg δj' ≫ Functor.whiskerRight δg Sj')) (L : A₀) :
    δv.app (Pj.obj L) ≫ Sv.map (δj.app L) ≫ s.app (R₀.obj L) =
      R₃.map (r.app L) ≫ δj'.app (Pg.obj L) ≫ Sj'.map (δg.app L) := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using congrArg (fun τ ↦ τ.app L) h

private theorem beta_mate_square
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {RA : A ⥤ A'} {RB : B ⥤ B'} {RC : C ⥤ C'} {RD : D ⥤ D'}
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    {F : A' ⥤ B'} {G : B' ⥤ A'} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    {V : A ⥤ C} {W : B ⥤ D} {V' : A' ⥤ C'} {W' : B' ⥤ D'}
    (a : J ⊣ P) (a' : J' ⊣ P') (b : F ⊣ G) (b' : F' ⊣ G')
    (δj : P ⋙ RA ⟶ RB ⋙ G) (δj' : P' ⋙ RC ⟶ RD ⋙ G')
    (δv : V ⋙ RC ⟶ RA ⋙ V') (δg : W ⋙ RD ⟶ RB ⋙ W')
    (r : W ⋙ P' ≅ P ⋙ V) (s : W' ⋙ G' ≅ G ⋙ V')
    (α : J ⋙ W ≅ V ⋙ J') (β : F ⋙ W' ≅ V' ⋙ F')
    (hr : ∀ L, (a'.homEquiv _ _) (α.inv.app L) =
      V.map (a.unit.app L) ≫ r.inv.app (J.obj L))
    (hs : ∀ M, (b'.homEquiv _ _) (β.inv.app M) =
      V'.map (b.unit.app M) ≫ s.inv.app (F.obj M))
    (h : (Functor.whiskerLeft P δv ≫ Functor.whiskerRight δj V') ≫
        Functor.whiskerLeft RB s.inv = Functor.whiskerRight r.inv RC ≫
          (Functor.whiskerLeft W δj' ≫ Functor.whiskerRight δg G'))
    {L : A} {M : A'} (q : RA.obj L ⟶ M) (qJ : RB.obj (J.obj L) ⟶ F.obj M)
    [IsIso (((mateEquiv a' b').symm δj').app (V.obj L))]
    (hu : q ≫ b.unit.app M = RA.map (a.unit.app L) ≫
      δj.app (J.obj L) ≫ G.map qJ) :
    inv (((mateEquiv a' b').symm δj').app (V.obj L)) ≫
        F'.map (δv.app L ≫ V'.map q) ≫ β.inv.app M =
      RD.map (α.inv.app L) ≫ δg.app (J.obj L) ≫ W'.map qJ := by
  apply inverse_mate_square a' b' δj'
  rw [hr, hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [← V'.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  have hn := δv.naturality (a.unit.app L)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have hn' := s.inv.naturality qJ
  dsimp only [Functor.comp_map] at hn'
  rw [hn', reassoc_of% (whisker_square_app δj δv δg δj' r.inv s.inv h (J.obj L))]
  rfl

private theorem open_beta_inverse_square_of_data
    (o : Operations l E) (a : AmbientModels l E o)
    {U' U V' V : Scheme.{u}} (v : U' ⟶ U) (j' : U' ⟶ V') (j : U ⟶ V) (g : V' ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (r : ringedPull l E g ⋙ ringedPull l E j' ≅ ringedPull l E j ⋙ ringedPull l E v)
    (s : pull l E g ⋙ pull l E j' ≅ pull l E j ⋙ pull l E v)
    (α : ringedOpen l E j ⋙ ringedPull l E g ≅ ringedPull l E v ⋙ ringedOpen l E j')
    (β : Operations.shriek l E o j ⋙ pull l E g ≅
      pull l E v ⋙ Operations.shriek l E o j')
    (hr : ∀ L : Integral l E U,
      ((ringedOpenAdj l E j').homEquiv _ _) (α.inv.app L) =
        (ringedPull l E v).map ((ringedOpenAdj l E j).unit.app L) ≫
          r.inv.app ((ringedOpen l E j).obj L))
    (hs : ∀ M : System l E U,
      ((o.extension j').adj.homEquiv _ _) (β.inv.app M) =
        (pull l E v).map ((o.extension j).adj.unit.app M) ≫
          s.inv.app ((Operations.shriek l E o j).obj M))
    (hn : (Functor.whiskerLeft (ringedPull l E j)
        (a.realizationModel.reductionPull v).hom ≫
        Functor.whiskerRight (a.realizationModel.reductionPull j).hom (pull l E v)) ≫
        Functor.whiskerLeft (calculus l E V).reduction s.inv =
      Functor.whiskerRight r.inv (calculus l E U').reduction ≫
        (Functor.whiskerLeft (ringedPull l E g) (a.realizationModel.reductionPull j').hom ≫
          Functor.whiskerRight (a.realizationModel.reductionPull g).hom (pull l E j')))
    (L : Integral l E U) (M : System l E U)
    (q : (calculus l E U).reduction.obj L ⟶ M)
    (qJ : (calculus l E V).reduction.obj ((ringedOpen l E j).obj L) ⟶
      (Operations.shriek l E o j).obj M)
    [IsIso (((mateEquiv (ringedOpenAdj l E j') (o.extension j').adj).symm
      (a.realizationModel.reductionPull j').hom).app ((ringedPull l E v).obj L))]
    (hu : q ≫ (o.extension j).adj.unit.app M =
      (calculus l E U).reduction.map ((ringedOpenAdj l E j).unit.app L) ≫
        (a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E j).map qJ) :
    inv (((mateEquiv (ringedOpenAdj l E j') (o.extension j').adj).symm
        (a.realizationModel.reductionPull j').hom).app
          ((ringedPull l E v).obj L)) ≫
      (Operations.shriek l E o j').map
        ((a.realizationModel.reductionPull v).hom.app L ≫ (pull l E v).map q) ≫
      β.inv.app M =
    (calculus l E V').reduction.map (α.inv.app L) ≫
      (a.realizationModel.reductionPull g).hom.app ((ringedOpen l E j).obj L) ≫
      (pull l E g).map qJ := by
  exact beta_mate_square
    (A := Integral l E U) (B := Integral l E V)
    (C := Integral l E U') (D := Integral l E V')
    (A' := System l E U) (B' := System l E V)
    (C' := System l E U') (D' := System l E V')
    (RA := (calculus l E U).reduction) (RB := (calculus l E V).reduction)
    (RC := (calculus l E U').reduction) (RD := (calculus l E V').reduction)
    (J := ringedOpen l E j) (P := ringedPull l E j)
    (J' := ringedOpen l E j') (P' := ringedPull l E j')
    (F := Operations.shriek l E o j) (G := pull l E j)
    (F' := Operations.shriek l E o j') (G' := pull l E j')
    (V := ringedPull l E v) (W := ringedPull l E g)
    (V' := pull l E v) (W' := pull l E g)
    (ringedOpenAdj l E j) (ringedOpenAdj l E j') (o.extension j).adj (o.extension j').adj
    (a.realizationModel.reductionPull j).hom (a.realizationModel.reductionPull j').hom
    (a.realizationModel.reductionPull v).hom (a.realizationModel.reductionPull g).hom
    r s α β hr hs hn q qJ hu

private theorem open_beta_inverse_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U' U V' V : Scheme.{u}} (v : U' ⟶ U) (j' : U' ⟶ V') (j : U ⟶ V) (g : V' ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (w : v ≫ j = j' ≫ g) (sq : IsPullback v j' j g)
    (L : Integral l E U) (M : System l E U)
    (q : (calculus l E U).reduction.obj L ⟶ M)
    (qJ : (calculus l E V).reduction.obj ((ringedOpen l E j).obj L) ⟶
      (Operations.shriek l E o j).obj M)
    [IsIso (((mateEquiv (ringedOpenAdj l E j') (o.extension j').adj).symm
      (a.realizationModel.reductionPull j').hom).app ((ringedPull l E v).obj L))]
    (hu : q ≫ (o.extension j).adj.unit.app M =
      (calculus l E U).reduction.map ((ringedOpenAdj l E j).unit.app L) ≫
        (a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E j).map qJ) :
    inv (((mateEquiv (ringedOpenAdj l E j') (o.extension j').adj).symm
        (a.realizationModel.reductionPull j').hom).app
          ((ringedPull l E v).obj L)) ≫
      (Operations.shriek l E o j').map
        ((a.realizationModel.reductionPull v).hom.app L ≫ (pull l E v).map q) ≫
      (a.openComparisons.beta v j' j g w sq).inv.app M =
    (calculus l E V').reduction.map ((a.ringedOpenComparisons.beta v j' j g w sq).inv.app L) ≫
      (a.realizationModel.reductionPull g).hom.app ((ringedOpen l E j).obj L) ≫
      (pull l E g).map qJ := by
  exact open_beta_inverse_square_of_data l E o a
    (U' := U') (U := U) (V' := V') (V := V) v j' j g
    (ringedSquare l E v j' j g w) (a.compositors.square l E v j' j g w)
    (a.ringedOpenComparisons.beta v j' j g w sq)
    (a.openComparisons.beta v j' j g w sq)
    (a.ringedOpenComparisons.beta_transpose v j' j g w sq)
    (a.openComparisons.beta_transpose v j' j g w sq)
    (pull_square_nat l E o a.realizationModel a.compositors v j' j g w) L M q qJ hu

private theorem tensor_pull
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (m : RealizationModel l E o) (d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (K H : Integral l E V) :
    (m.reductionPull f).hom.app ((d.tensor V).ordinary.tensor.obj (K, H)) ≫
        (pull l E f).map ((ordinaryTensorReduction l E d V).app (K, H)) ≫
        (pullbackTensorSystemComparison l E f).hom.app
          ((calculus l E V).reduction.obj K, (calculus l E V).reduction.obj H) =
      (calculus l E U).reduction.map ((ringedTensorPull l E d f).hom.app (K, H)) ≫
        (ordinaryTensorReduction l E d U).app
          ((ringedPull l E f).obj K, (ringedPull l E f).obj H) ≫
        (calculus l E U).systemClosed.tensor.map
          (Prod.mkHom ((m.reductionPull f).hom.app K) ((m.reductionPull f).hom.app H)) := by
  simpa only [ordinaryTensorReduction] using!
    canonicalReductionTensorPull l E o m d f K H

private theorem open_projection_inverse_square
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (L : Integral l E U) (H : Integral l E V) (M : System l E U) (N : System l E V)
    (q : (calculus l E U).reduction.obj L ⟶ M)
    (r : (calculus l E V).reduction.obj H ⟶ N) :
    GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app
        ((a.ringedModels.tensor U).ordinary.tensor.obj (L, (ringedPull l E j).obj H))) ≫
      (Operations.shriek l E o j).map
        ((ordinaryTensorReduction l E a.ringedModels U).app (L, (ringedPull l E j).obj H) ≫
          (calculus l E U).systemClosed.tensor.map
            (Prod.mkHom q ((a.realizationModel.reductionPull j).hom.app H ≫
              (pull l E j).map r))) ≫
      (a.openComparisons.projection j).inv.app (M, N) =
    (calculus l E V).reduction.map ((a.ringedOpenComparisons.projection j).inv.app (L, H)) ≫
      (ordinaryTensorReduction l E a.ringedModels V).app ((ringedOpen l E j).obj L, H) ≫
      (calculus l E V).systemClosed.tensor.map
        (Prod.mkHom
          (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app L) ≫
            (Operations.shriek l E o j).map q) r) := by
  let qJ := GeneratorReduction.inverseOrZero
    ((a.realizationModel.openReduction l E j).app L) ≫
    (Operations.shriek l E o j).map q
  have hj : ∀ L, IsIso ((a.realizationModel.openReduction l E j).app L) :=
    fun L ↦ GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j L
  have hi : IsIso (((mateEquiv (ringedOpenAdj l E j) (o.extension j).adj).symm
    (a.realizationModel.reductionPull j).hom).app
      ((a.ringedModels.tensor _).ordinary.tensor.obj
        (L, (ringedPull l E j).obj H))) := by
    exact hj _
  have hiL : IsIso (((mateEquiv (ringedOpenAdj l E j) (o.extension j).adj).symm
    (a.realizationModel.reductionPull j).hom).app L) := by
    exact hj L
  have hu : q ≫ (o.extension j).adj.unit.app M =
      (calculus l E _).reduction.map ((ringedOpenAdj l E j).unit.app L) ≫
        (a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E j).map qJ := by
    simpa only [qJ, RealizationModel.openReduction, ringedOpenAdj, Operations.shriek] using!
      GeneratorReduction.inverse_mate_unit_square (ringedOpenAdj l E j)
        (o.extension j).adj (a.realizationModel.reductionPull j).hom q
  have htp := inverse_square (calculus l E _).reduction
    ((ringedTensorPull l E a.ringedModels j).app ((ringedOpen l E j).obj L, H))
    ((pullbackTensorSystemComparison l E j).app
      ((calculus l E _).reduction.obj ((ringedOpen l E j).obj L),
        (calculus l E _).reduction.obj H))
    ((a.realizationModel.reductionPull j).hom.app
        ((a.ringedModels.tensor _).ordinary.tensor.obj ((ringedOpen l E j).obj L, H)) ≫
      (pull l E j).map ((ordinaryTensorReduction l E a.ringedModels _).app
        ((ringedOpen l E j).obj L, H)))
    ((ordinaryTensorReduction l E a.ringedModels _).app
        ((ringedPull l E j).obj ((ringedOpen l E j).obj L),
          (ringedPull l E j).obj H) ≫
      (calculus l E _).systemClosed.tensor.map
        (Prod.mkHom
          ((a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L))
          ((a.realizationModel.reductionPull j).hom.app H)))
    (by
      simpa only [Iso.app_hom, Category.assoc] using!
        tensor_pull l E o a.realizationModel a.ringedModels j
          ((ringedOpen l E j).obj L) H)
  have hs := inverse_mate_square (ringedOpenAdj l E j) (o.extension j).adj
    (a.realizationModel.reductionPull j).hom
    ((ordinaryTensorReduction l E a.ringedModels _).app
        (L, (ringedPull l E j).obj H) ≫
      (calculus l E _).systemClosed.tensor.map
        (Prod.mkHom q ((a.realizationModel.reductionPull j).hom.app H ≫
          (pull l E j).map r)))
    ((ordinaryTensorReduction l E a.ringedModels _).app
        ((ringedOpen l E j).obj L, H) ≫
      (calculus l E _).systemClosed.tensor.map (Prod.mkHom qJ r))
    ((a.ringedOpenComparisons.projection j).inv.app (L, H))
    ((a.openComparisons.projection j).inv.app (M, N)) (by
      erw [a.ringedOpenComparisons.projection_transpose j L H,
        a.openComparisons.projection_transpose j M N]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      erw [← CategoryTheory.Functor.map_comp_assoc]
      simp only [prod_comp]
      erw [Category.comp_id, hu]
      let T := (calculus l E U).systemClosed.tensor
      have hf : T.map (Prod.mkHom
          ((calculus l E _).reduction.map ((ringedOpenAdj l E j).unit.app L) ≫
            (a.realizationModel.reductionPull j).hom.app
              ((ringedOpen l E j).obj L) ≫ (pull l E j).map qJ)
          ((a.realizationModel.reductionPull j).hom.app H ≫
            (pull l E j).map r)) =
          T.map (Prod.mkHom
            ((calculus l E _).reduction.map ((ringedOpenAdj l E j).unit.app L))
            (𝟙 _)) ≫
          T.map (Prod.mkHom
            ((a.realizationModel.reductionPull j).hom.app
              ((ringedOpen l E j).obj L))
            ((a.realizationModel.reductionPull j).hom.app H)) ≫
          T.map (Prod.mkHom ((pull l E j).map qJ) ((pull l E j).map r)) := by
        simp only [← T.map_comp, prod_comp, Category.id_comp]
      erw [hf]
      simp only [Category.assoc]
      have hn := (ordinaryTensorReduction l E a.ringedModels _).naturality
        (Prod.mkHom ((ringedOpenAdj l E j).unit.app L)
          (𝟙 ((ringedPull l E j).obj H)))
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.id_obj] at hn
      simp only [CategoryTheory.Functor.map_id] at hn
      erw [← reassoc_of% hn]
      have hn' := (pullbackTensorSystemComparison l E j).inv.naturality
        (Prod.mkHom qJ r)
      dsimp only [Functor.comp_map, Functor.prod_map] at hn'
      erw [hn', reassoc_of% htp]
      rfl)
  simp only [qJ, GeneratorReduction.inverseOrZero_eq_inv] at hs
  simp only [GeneratorReduction.inverseOrZero_eq_inv]
  simpa only [RealizationModel.openReduction, ringedOpenAdj, Operations.shriek,
    Category.assoc] using! hs

private abbrev OrdinarySquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {W : Over B} (e t : Expression B I X W)
    (s : e.systemObj l E o ((inputReduction l E X).obj K) ≅
      t.systemObj l E o ((inputReduction l E X).obj K))
    (r : e.ringedObj l E a.ringedModels K ≅ t.ringedObj l E a.ringedModels K) : Prop :=
  e.ordinaryReduction l E o a K ≫ s.hom =
    (calculus l E W.left).reduction.map r.hom ≫ t.ordinaryReduction l E o a K

private theorem pullComp_square
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V W : Over B} (f : U ⟶ V) (g : V ⟶ W)
      (e : Expression B I X W) :
    OrdinarySquare l E o a K (.pull (f ≫ g) e) (.pull f (.pull g e))
      ((a.compositors.pullComp f.left g.left).app (e.systemObj l E o ((inputReduction l E X).obj
      K)))
      ((ringedPullComp l E f.left g.left).app (e.ringedObj l E a.ringedModels K)) := by
  dsimp only [OrdinarySquare]
  have he := GeneratorReduction.canonicalReductionPullComposition l E o
    a.realizationModel a.compositors f.left g.left (e.ringedObj l E a.ringedModels K)
  have hn := (a.compositors.pullComp f.left g.left).hom.naturality
    (e.ordinaryReduction l E o a K)
  dsimp only [Functor.comp_map] at hn
  simp only [Expression.ordinaryReduction, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [hn, ← reassoc_of% he]
  rfl

private theorem pushComp_square
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V W : Over B} (f : U ⟶ V) (g : V ⟶ W)
      (hf : IsProper f.left) (hg : IsProper g.left) (hfg : IsProper (f ≫ g).left)
      (e : Expression B I X U) :
    OrdinarySquare l E o a K (.push g hg (.push f hf e)) (.push (f ≫ g) hfg e)
      ((a.compositors.pushComp l E f.left g.left).app (e.systemObj l E o ((inputReduction l E
      X).obj K)))
      ((ringedPushComp l E f.left g.left).app (e.ringedObj l E a.ringedModels K)) := by
  dsimp only [OrdinarySquare]
  have h :
      (TwoSquare.vComp (a.realizationModel.reductionPull g.left).inv
        (a.realizationModel.reductionPull f.left).inv).whiskerRight
          (a.compositors.pullComp f.left g.left).hom =
      (TwoSquare.mk _ _ _ _ (a.realizationModel.reductionPull (f.left ≫ g.left)).inv).whiskerLeft
        (ringedPullComp l E f.left g.left).hom := by
    apply NatTrans.ext
    funext L
    dsimp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id, Functor.comp_obj]
    apply (cancel_epi ((a.realizationModel.reductionPull
      (f.left ≫ g.left)).hom.app L)).1
    simp only [Iso.hom_inv_id_app_assoc]
    erw [← reassoc_of% (GeneratorReduction.canonicalReductionPullComposition l E
      o a.realizationModel a.compositors f.left g.left L)]
    simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    exact Category.comp_id _
  have hm := GeneratorReduction.mate_compositor_square
    (ringedAdj l E g.left) (ringedAdj l E f.left)
    (ringedAdj l E (f.left ≫ g.left))
    (o.direct g.left).adj (o.direct f.left).adj (o.direct (f.left ≫ g.left)).adj
    (a.realizationModel.reductionPull g.left).inv
    (a.realizationModel.reductionPull f.left).inv
    (a.realizationModel.reductionPull (f.left ≫ g.left)).inv
    (ringedPullComp l E f.left g.left).hom
    (a.compositors.pullComp f.left g.left).hom h (e.ringedObj l E a.ringedModels K)
  have hn := (a.compositors.pushComp l E f.left g.left).hom.naturality
    (e.ordinaryReduction l E o a K)
  dsimp only [Functor.comp_map] at hn
  simp only [Expression.ordinaryReduction, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [hn, reassoc_of% hm]
  rfl

private theorem tensorAssoc_square
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {W : Over B} (e f g : Expression B I X W) :
    OrdinarySquare l E o a K (.tensor (.tensor e f) g) (.tensor e (.tensor f g))
      ((calculus l E W.left).systemClosed.monoidal.associator
        (e.systemObj l E o ((inputReduction l E X).obj K)) (f.systemObj l E o ((inputReduction l E
      X).obj K)) (g.systemObj l E o ((inputReduction l E X).obj K)))
      (ringedAssociator l E a.ringedModels W.left
        (e.ringedObj l E a.ringedModels K) (f.ringedObj l E a.ringedModels K) (g.ringedObj l E
      a.ringedModels K)) := by
  dsimp only [OrdinarySquare]
  simpa only [Expression.ordinaryReduction, ordinaryTensorReduction, ringedAssociator,
    Iso.trans_hom, Category.assoc] using!
    GeneratorReduction.comparison_associator
      (calculus l E _).integralClosed (calculus l E _).systemClosed
      (calculus l E _).reduction (calculus l E _).reductionTensor
      (calculus l E _).reduction_compatible
      (a.ringedModels.tensor _).ordinary.tensor (a.ringedModels.tensorClosed _)
      (e.ringedObj l E a.ringedModels K) (f.ringedObj l E a.ringedModels K)
      (g.ringedObj l E a.ringedModels K) _ _ _
      (e.ordinaryReduction l E o a K) (f.ordinaryReduction l E o a K)
      (g.ordinaryReduction l E o a K)

private theorem supportExpansion_square
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      (qj : QuasiCompact cf.i) (e : Expression B I X U) :
    OrdinarySquare l E o a K (.compactSupport f cf e)
      (.push (compactProper (f := f) cf) (inferInstance : IsProper cf.g)
        (.shriek (compactOpen (f := f) cf) (inferInstance : IsOpenImmersion cf.i) qj e))
      (Iso.refl _) (Iso.refl _) := by
  dsimp only [OrdinarySquare]
  simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.id_comp]
  rfl

private theorem openComp_square
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V W : Over B} (j : U ⟶ V) (k : V ⟶ W)
      [hj : IsOpenImmersion j.left] [hk : IsOpenImmersion k.left]
      (qj : QuasiCompact j.left) (qk : QuasiCompact k.left)
      (qjk : QuasiCompact (j ≫ k).left) (e : Expression B I X U) :
    OrdinarySquare l E o a K (.shriek k hk qk (.shriek j hj qj e))
      (.shriek (j ≫ k) (inferInstance : IsOpenImmersion (j.left ≫ k.left)) qjk e)
      ((a.compositors.openComp l E j.left k.left).app (e.systemObj l E o ((inputReduction l E
      X).obj K)))
      ((ringedOpenComp l E j.left k.left).app (e.ringedObj l E a.ringedModels K)) := by
  dsimp only [OrdinarySquare]
  have hh := left_mate_compositor_square
    (ringedOpenAdj l E j.left) (ringedOpenAdj l E k.left)
    (ringedOpenAdj l E (j.left ≫ k.left))
    (o.extension j.left).adj (o.extension k.left).adj
    (o.extension (j.left ≫ k.left)).adj
    (a.realizationModel.openReduction l E j.left)
    (a.realizationModel.openReduction l E k.left)
    (a.realizationModel.openReduction l E (j.left ≫ k.left))
    (ringedOpenComp l E j.left k.left).inv
    (a.compositors.openComp l E j.left k.left).inv (by
      intro L
      simp only [RealizationModel.openReduction, ringedOpenAdj, ringedOpenComp,
        Compositors.openComp,
        Equiv.apply_symm_apply, Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
        Iso.symm_hom]
      simpa only [] using!
        pull_comp_inverse l E o a.realizationModel a.compositors j.left k.left L)
  have hx := congrArg (fun v ↦ v.app
    (e.ringedObj l E a.ringedModels K)) hh
  dsimp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app] at hx
  simp only [Category.id_comp, Category.comp_id, Functor.comp_obj] at hx
  have hj : ∀ L, IsIso ((a.realizationModel.openReduction l E j.left).app L) :=
    fun L ↦ GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j.left L
  have hk : ∀ L, IsIso ((a.realizationModel.openReduction l E k.left).app L) :=
    fun L ↦ GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel k.left L
  have hjk : ∀ L, IsIso ((a.realizationModel.openReduction l E
    (j.left ≫ k.left)).app L) := fun L ↦
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel _ L
  have hi := congrArg (fun f ↦ GeneratorReduction.inverseOrZero f) hx
  simp only [GeneratorReduction.inverseOrZero_eq_inv, IsIso.inv_comp,
    ← CategoryTheory.Functor.map_inv, NatIso.inv_inv_app, Category.assoc] at hi
  have hn := (a.compositors.openComp l E j.left k.left).hom.naturality
    (e.ordinaryReduction l E o a K)
  dsimp only [Functor.comp_map] at hn
  simp only [Expression.ordinaryReduction, GeneratorReduction.inverseOrZero_eq_inv,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.app_hom]
  erw [hn, reassoc_of% hi]
  rfl

private theorem tensorPull_square
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V : Over B} (f : U ⟶ V) (e t : Expression B I X V) :
    OrdinarySquare l E o a K (.pull f (.tensor e t)) (.tensor (.pull f e) (.pull f t))
      ((pullbackTensorSystemComparison l E f.left).app
        (e.systemObj l E o ((inputReduction l E X).obj K), t.systemObj l E o ((inputReduction l E
      X).obj K)))
      ((ringedTensorPull l E a.ringedModels f.left).app (e.ringedObj l E a.ringedModels K,
      t.ringedObj l E a.ringedModels K)) := by
  dsimp only [OrdinarySquare]
  have he := tensor_pull l E o a.realizationModel a.ringedModels f.left
    (e.ringedObj l E a.ringedModels K) (t.ringedObj l E a.ringedModels K)
  have hn := (pullbackTensorSystemComparison l E f.left).hom.naturality
    (Prod.mkHom (e.ordinaryReduction l E o a K) (t.ordinaryReduction l E o a K))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [Expression.ordinaryReduction, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.app_hom]
  erw [hn, reassoc_of% he]
  simp only [← CategoryTheory.Functor.map_comp, prod_comp]
  rfl

private theorem beta_square
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U' U V' V : Over B} (v : U' ⟶ U) (j' : U' ⟶ V')
      (j : U ⟶ V) (g : V' ⟶ V)
      [hj : IsOpenImmersion j.left] [hj' : IsOpenImmersion j'.left]
      (qj : QuasiCompact j.left) (qj' : QuasiCompact j'.left)
      (w : v.left ≫ j.left = j'.left ≫ g.left)
      (sq : IsPullback v.left j'.left j.left g.left) (e : Expression B I X U) :
    OrdinarySquare l E o a K (.pull g (.shriek j hj qj e))
      (.shriek j' hj' qj' (.pull v e))
      ((a.openComparisons.beta v.left j'.left j.left g.left w sq).app (e.systemObj l E o
      ((inputReduction l E X).obj K)))
      ((a.ringedOpenComparisons.beta v.left j'.left j.left g.left w sq).app (e.ringedObj l E
      a.ringedModels K)) := by
  dsimp only [OrdinarySquare]
  let L := e.ringedObj l E a.ringedModels K
  let M := e.systemObj l E o ((inputReduction l E X).obj K)
  let q := e.ordinaryReduction l E o a K
  let qJ := GeneratorReduction.inverseOrZero
    ((a.realizationModel.openReduction l E j.left).app L) ≫
    (Operations.shriek l E o j.left).map q
  have hj : IsIso ((a.realizationModel.openReduction l E j.left).app L) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j.left L
  have hj' : IsIso ((a.realizationModel.openReduction l E j'.left).app
    ((ringedPull l E v.left).obj L)) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j'.left _
  have hj₀ := hj
  have hj'₀ := hj'
  change IsIso (((mateEquiv (ringedOpenAdj l E j.left) (o.extension j.left).adj).symm
    (a.realizationModel.reductionPull j.left).hom).app L) at hj
  change IsIso (((mateEquiv (ringedOpenAdj l E j'.left) (o.extension j'.left).adj).symm
    (a.realizationModel.reductionPull j'.left).hom).app
      ((ringedPull l E v.left).obj L)) at hj'
  have hu : q ≫ (o.extension j.left).adj.unit.app M =
      (calculus l E _).reduction.map ((ringedOpenAdj l E j.left).unit.app L) ≫
        (a.realizationModel.reductionPull j.left).hom.app ((ringedOpen l E j.left).obj L) ≫
        (pull l E j.left).map qJ := by
    simpa only [qJ, RealizationModel.openReduction, ringedOpenAdj, Operations.shriek] using!
      GeneratorReduction.inverse_mate_unit_square (ringedOpenAdj l E j.left)
        (o.extension j.left).adj (a.realizationModel.reductionPull j.left).hom q
  have hs := open_beta_inverse_square l E o a
    v.left j'.left j.left g.left w sq L M q qJ hu
  have hsrc :
      (Expression.shriek j' inferInstance qj' (.pull v e)).ordinaryReduction l E o a K =
      GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j'.left).app
        ((ringedPull l E v.left).obj L)) ≫
      (Operations.shriek l E o j'.left).map
        ((a.realizationModel.reductionPull v.left).hom.app L ≫ (pull l E v.left).map q) := rfl
  have htgt :
      (Expression.pull g (.shriek j inferInstance qj e)).ordinaryReduction l E o a K =
      (a.realizationModel.reductionPull g.left).hom.app ((ringedOpen l E j.left).obj L) ≫
        (pull l E g.left).map qJ := rfl
  have hi := inverse_square (calculus l E _).reduction
    ((a.ringedOpenComparisons.beta v.left j'.left j.left g.left w sq).app L).symm
    ((a.openComparisons.beta v.left j'.left j.left g.left w sq).app M).symm
    ((Expression.shriek j' inferInstance qj' (.pull v e)).ordinaryReduction l E o a K)
    ((Expression.pull g (.shriek j inferInstance qj e)).ordinaryReduction l E o a K)
    (by
      rw [hsrc, htgt]
      simp only [Iso.symm_hom, Iso.app_inv,
        GeneratorReduction.inverseOrZero_eq_inv, Category.assoc]
      simpa only [RealizationModel.openReduction, ringedOpenAdj, Operations.shriek,
        Category.assoc] using! hs)
  exact hi

private theorem clopen_square
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V : Over B} (j : U ⟶ V)
      [hj : IsOpenImmersion j.left] [IsClosedImmersion j.left]
      (qj : QuasiCompact j.left) (hp : IsProper j.left) (e : Expression B I X U) :
    OrdinarySquare l E o a K (.shriek j hj qj e) (.push j hp e)
      ((a.openComparisons.clopen j.left).app (e.systemObj l E o ((inputReduction l E X).obj K)))
      ((a.ringedOpenComparisons.clopen j.left).app (e.ringedObj l E a.ringedModels K)) := by
  dsimp only [OrdinarySquare]
  let L := e.ringedObj l E a.ringedModels K
  let M := e.systemObj l E o ((inputReduction l E X).obj K)
  let q := e.ordinaryReduction l E o a K
  have : IsIso ((ringedOpenAdj l E j.left).unit.app L) :=
    a.ringedOpenComparisons.unitIso j.left L
  have : IsIso ((o.extension j.left).adj.unit.app M) :=
    a.openComparisons.unitIso j.left M
  have hi : IsIso ((a.realizationModel.openReduction l E j.left).app L) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j.left L
  change IsIso (((mateEquiv (ringedOpenAdj l E j.left) (o.extension j.left).adj).symm
    (a.realizationModel.reductionPull j.left).hom).app L) at hi
  have hu := GeneratorReduction.inverse_mate_unit_square (ringedOpenAdj l E j.left)
    (o.extension j.left).adj (a.realizationModel.reductionPull j.left).hom q
  have hc := GeneratorReduction.mate_counit_square (ringedAdj l E j.left)
    (o.direct j.left).adj (a.realizationModel.reductionPull j.left).symm q
  simp only [Expression.ordinaryReduction, Iso.app_hom]
  apply ((o.direct j.left).adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  erw [a.openComparisons.clopen_transpose j.left M,
    Equiv.symm_apply_apply]
  change (pull l E j.left).map
      (GeneratorReduction.inverseOrZero
        ((a.realizationModel.openReduction l E j.left).app L) ≫
        (Operations.shriek l E o j.left).map q) ≫
      inv ((o.extension j.left).adj.unit.app M) = _
  apply (cancel_epi ((calculus l E _).reduction.map
    ((ringedOpenAdj l E j.left).unit.app L) ≫
      (a.realizationModel.reductionPull j.left).hom.app ((ringedOpen l E j.left).obj L))).1
  simp only [Category.assoc]
  erw [← reassoc_of% hu]
  erw [IsIso.hom_inv_id, Category.comp_id]
  rw [Adjunction.homEquiv_counit]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (a.realizationModel.reductionPull j.left).hom.naturality
    ((a.ringedOpenComparisons.clopen j.left).hom.app L)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  have hc' :
      (a.realizationModel.reductionPull j.left).hom.app ((ringedPush l E j.left).obj L) ≫
        (pull l E j.left).map ((ordinaryPushReduction l E o a.realizationModel j.left).app L) ≫
        (pull l E j.left).map ((Operations.push l E o j.left).map q) ≫
        (o.direct j.left).adj.counit.app M =
      (calculus l E _).reduction.map ((ringedAdj l E j.left).counit.app L) ≫ q := by
    simpa only [ordinaryPushReduction, Iso.symm_inv, Iso.symm_hom,
      CategoryTheory.Functor.map_comp, Category.assoc] using! hc
  erw [hc']
  have hr := ((ringedAdj l E j.left).homEquiv _ _).symm_apply_apply
    (inv ((ringedOpenAdj l E j.left).unit.app L))
  rw [← a.ringedOpenComparisons.clopen_transpose j.left L] at hr
  change (ringedPull l E j.left).map
    ((a.ringedOpenComparisons.clopen j.left).hom.app L) ≫
      (ringedAdj l E j.left).counit.app L = _ at hr
  simp only [← CategoryTheory.Functor.map_comp_assoc, hr,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem openProjection_square
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V : Over B} (j : U ⟶ V)
      [hj : IsOpenImmersion j.left] (qj : QuasiCompact j.left)
      (e : Expression B I X U) (t : Expression B I X V) :
    OrdinarySquare l E o a K (.tensor (.shriek j hj qj e) t)
      (.shriek j hj qj (.tensor e (.pull j t)))
      ((a.openComparisons.projection j.left).app (e.systemObj l E o ((inputReduction l E X).obj
      K), t.systemObj l E o ((inputReduction l E X).obj K)))
      ((a.ringedOpenComparisons.projection j.left).app (e.ringedObj l E a.ringedModels K,
      t.ringedObj l E a.ringedModels K)) := by
  dsimp only [OrdinarySquare]
  let L := e.ringedObj l E a.ringedModels K
  let H := t.ringedObj l E a.ringedModels K
  let M := e.systemObj l E o ((inputReduction l E X).obj K)
  let N := t.systemObj l E o ((inputReduction l E X).obj K)
  let q := e.ordinaryReduction l E o a K
  let r := t.ordinaryReduction l E o a K
  let qJ := GeneratorReduction.inverseOrZero
    ((a.realizationModel.openReduction l E j.left).app L) ≫
    (Operations.shriek l E o j.left).map q
  have hs := open_projection_inverse_square l E o a j.left L H M N q r
  have hsrc :
      (Expression.shriek j inferInstance qj (.tensor e (.pull j t))).ordinaryReduction l E o a K =
      GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j.left).app
        ((a.ringedModels.tensor _).ordinary.tensor.obj
          (L, (ringedPull l E j.left).obj H))) ≫
      (Operations.shriek l E o j.left).map
        ((ordinaryTensorReduction l E a.ringedModels _).app
            (L, (ringedPull l E j.left).obj H) ≫
          (calculus l E _).systemClosed.tensor.map
            (Prod.mkHom q ((a.realizationModel.reductionPull j.left).hom.app H ≫
              (pull l E j.left).map r))) := rfl
  have htgt :
      (Expression.tensor (.shriek j inferInstance qj e) t).ordinaryReduction l E o a K =
      (ordinaryTensorReduction l E a.ringedModels _).app ((ringedOpen l E j.left).obj L, H) ≫
        (calculus l E _).systemClosed.tensor.map (Prod.mkHom qJ r) := rfl
  have hs' :
      (Expression.shriek j inferInstance qj (.tensor e (.pull j t))).ordinaryReduction l E o a K ≫
      (a.openComparisons.projection j.left).inv.app (M, N) =
    (calculus l E _).reduction.map
        ((a.ringedOpenComparisons.projection j.left).inv.app (L, H)) ≫
      (Expression.tensor (.shriek j inferInstance qj e) t).ordinaryReduction l E o a K := by
    rw [hsrc, htgt]
    simpa only [qJ, Category.assoc] using! hs
  have hi := inverse_square (calculus l E _).reduction
    ((a.ringedOpenComparisons.projection j.left).app (L, H)).symm
    ((a.openComparisons.projection j.left).app (M, N)).symm
    ((Expression.shriek j inferInstance qj (.tensor e (.pull j t))).ordinaryReduction l E o a K)
    ((Expression.tensor (.shriek j inferInstance qj e) t).ordinaryReduction l E o a K)
    (by simpa only [Iso.symm_hom, Iso.app_inv] using! hs')
  exact hi

/-- Forward squares for the listed ordinary structural isomorphisms.
Source: blueprint fix-prop-coherence, tensor reassociation and geometric/open compositors.
(blueprint: lem-sf-integral-ordinary-canonical-iso-square).

Proof: substitute the independently constructed child coefficient maps into the
primitive coefficient diagrams. Tensor reassociation uses reduction_compatible
and tensorClosed; pull composition uses canonicalReductionPullComposition, and
proper composition is its adjoint mate. Open composition, base change and projection
are the specified open-adjunction mates, so their squares follow by pasting the
pullback, tensor, unit and counit squares. The clopen comparison is the inverse
open unit transposed by the direct-image adjunction. Compactification expansion
is definitionally the same open/proper recursion on both sides. Naturality inserts every child
coefficient map, including repeated inputs. No completion or chosen expression
realization occurs, and inverse structural arrows are not asserted here. -/
theorem ordinaryCanonicalIsoSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {W : Over B} (e t : Expression B I X W)
    (s : e.systemObj l E o ((inputReduction l E X).obj K) ≅
      t.systemObj l E o ((inputReduction l E X).obj K))
    (r : e.ringedObj l E a.ringedModels K ≅ t.ringedObj l E a.ringedModels K)
    (h : CanonicalIsoPair l E o a.compositors a.openComparisons a.ringedModels
      a.ringedOpenComparisons ((inputReduction l E X).obj K) K e t s r) :
    e.ordinaryReduction l E o a K ≫ s.hom =
      (calculus l E W.left).reduction.map r.hom ≫ t.ordinaryReduction l E o a K  := by
  cases h with
  | pullComp f g e =>
    exact pullComp_square l E o a K f g e
  | pushComp f g hf hg hfg e =>
    exact pushComp_square l E o a K f g hf hg hfg e
  | tensorAssoc e f g =>
    exact tensorAssoc_square l E o a K e f g
  | supportExpansion f cf qj e =>
    exact supportExpansion_square l E o a K f cf qj e
  | openComp j k qj qk qjk e =>
    exact openComp_square l E o a K j k qj qk qjk e
  | tensorPull f e t =>
    exact tensorPull_square l E o a K f e t
  | beta v j' j g qj qj' w sq e =>
    exact beta_square l E o a K v j' j g qj qj' w sq e
  | clopen j qj hp e =>
    exact clopen_square l E o a K j qj hp e
  | openProjection j qj e t =>
    exact openProjection_square l E o a K j qj e t

end WeilConjectures.IntegralSystemRealization
