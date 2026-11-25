/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # Generic transition calculus for tensor presentations of strict systems

Source: Stacks 03CZ, 03EK, 07A4 and 0941.

Given two levels of a strict coefficient system, presentations of two system complexes
by scalar extensions of completed-coefficient complexes, and the ordinary evaluation and
scalar tensor comparisons, the induced presentation of the system tensor product is again
compatible with the strict transition maps. Everything here is stated for arbitrary ring
sheaves, so that kernel checking never compares the concrete coefficient rings.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures
namespace OrdinaryReductionTensor

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}

/-- Forgetting a restriction of scalars on sections is injective.
Source: Stacks 03CZ. -/
theorem restrictionSection_injective {A B : Sheaf J RingCat.{r}} (φ : A ⟶ B)
    (N : SheafOfModules.{r} B) (U : Cᵒᵖ) :
    Function.Injective (coefficientRestrictionSection φ N U) := fun _ _ h ↦ h

/-- Sections of a map out of an adjunction unit.
Source: Stacks 03CZ. -/
theorem unit_comp_section {A B : Sheaf J RingCat.{r}} (p : A ⟶ B)
    {F : SheafOfModules.{r} A ⥤ SheafOfModules.{r} B}
    (a : F ⊣ SheafOfModules.restrictScalars p) {X : SheafOfModules.{r} A}
    {Y : SheafOfModules.{r} B} (φ : F.obj X ⟶ Y) (U : Cᵒᵖ) (x : X.val.obj U) :
    coefficientRestrictionSection p Y U
      ((a.unit.app X ≫ (SheafOfModules.restrictScalars p).map φ).val.app U x) =
      φ.val.app U (coefficientRestrictionSection p (F.obj X) U ((a.unit.app X).val.app U x)) :=
  rfl

/-- Restriction of scalars does not change the section map.
Source: Stacks 03CZ. -/
theorem restrict_map_section {A B : Sheaf J RingCat.{r}} (q : A ⟶ B)
    {M N : SheafOfModules.{r} B} (g : M ⟶ N) (U : Cᵒᵖ)
    (w : ((SheafOfModules.restrictScalars q).obj M).val.obj U) :
    coefficientRestrictionSection q N U (((SheafOfModules.restrictScalars q).map g).val.app U w) =
      g.val.app U (coefficientRestrictionSection q M U w) :=
  rfl

/-- Sections of a composite of module-sheaf maps.
Source: Stacks 03CZ. -/
theorem comp_section {R : Sheaf J RingCat.{r}} {M N P : SheafOfModules.{r} R}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) (x : M.val.obj U) :
    (f ≫ g).val.app U x = g.val.app U (f.val.app U x) := rfl

/-- The inverse of an isomorphism of complexes undoes it on sections.
Source: Stacks 03CZ. -/
theorem iso_inv_hom_section {R : Sheaf J RingCat.{r}}
    {P Q : CochainComplex (SheafOfModules.{r} R) ℤ} (e : P ≅ Q)
    (k : ℤ) (U : Cᵒᵖ) (x : (Q.X k).val.obj U) :
    (e.hom.f k).val.app U ((e.inv.f k).val.app U x) = x :=
  congrArg (fun (f : Q ⟶ Q) ↦ (f.f k).val.app U x) e.inv_hom_id

/-- The inverse of an isomorphism of complexes undoes it on sections.
Source: Stacks 03CZ. -/
theorem iso_hom_inv_section {R : Sheaf J RingCat.{r}}
    {P Q : CochainComplex (SheafOfModules.{r} R) ℤ} (e : P ≅ Q)
    (k : ℤ) (U : Cᵒᵖ) (x : (P.X k).val.obj U) :
    (e.inv.f k).val.app U ((e.hom.f k).val.app U x) = x :=
  congrArg (fun (f : P ⟶ P) ↦ (f.f k).val.app U x) e.hom_inv_id

/-- Maps out of a left adjoint are determined by their composites with the unit.
Source: Stacks 03CZ. -/
theorem hom_ext_of_unit {X' Y' : Type*} [Category X'] [Category Y'] {F : X' ⥤ Y'}
    {G : Y' ⥤ X'} (a : F ⊣ G) {X : X'} {Y : Y'} {f g : F.obj X ⟶ Y}
    (h : a.unit.app X ≫ G.map f = a.unit.app X ≫ G.map g) : f = g := by
  apply (a.homEquiv X Y).injective
  rw [a.homEquiv_unit, a.homEquiv_unit]
  exact h

/-- Sections of the inverse of a threefold composite isomorphism ending in a symmetric one.
Source: Stacks 03CZ. -/
theorem trans_symm_inv_section {R : Sheaf J RingCat.{r}}
    {X Y Z W : CochainComplex (SheafOfModules.{r} R) ℤ} (e₁ : X ≅ Y) (e₂ : Y ≅ Z) (s : W ≅ Z)
    (k : ℤ) (U : Cᵒᵖ) (z : (W.X k).val.obj U) :
    ((e₁ ≪≫ e₂ ≪≫ s.symm).inv.f k).val.app U z =
      (e₁.inv.f k).val.app U ((e₂.inv.f k).val.app U ((s.hom.f k).val.app U z)) := rfl

/-- Sections of a threefold composite isomorphism ending in a symmetric one.
Source: Stacks 03CZ. -/
theorem trans_symm_hom_section {R : Sheaf J RingCat.{r}}
    {X Y Z W : CochainComplex (SheafOfModules.{r} R) ℤ} (e₁ : X ≅ Y) (e₂ : Y ≅ Z) (s : W ≅ Z)
    (k : ℤ) (U : Cᵒᵖ) (z : (X.X k).val.obj U) :
    ((e₁ ≪≫ e₂ ≪≫ s.symm).hom.f k).val.app U z =
      (s.inv.f k).val.app U ((e₂.hom.f k).val.app U ((e₁.hom.f k).val.app U z)) := rfl

/-- A composite through a restriction of scalars, computed one map at a time on sections.
Source: Stacks 03CZ. -/
theorem comp_restrict_section {Bm Bn : Sheaf J RingCat.{r}} (q : Bm ⟶ Bn)
    {X Y : SheafOfModules.{r} Bm} {Z W : SheafOfModules.{r} Bn}
    (a : X ⟶ Y) (b : Y ⟶ (SheafOfModules.restrictScalars q).obj Z) (g : Z ⟶ W) (U : Cᵒᵖ)
    (z : X.val.obj U) (z₁ : Y.val.obj U) (z₂ : Z.val.obj U) (z₃ : W.val.obj U)
    (h₁ : a.val.app U z = z₁) (h₂ : coefficientRestrictionSection q Z U (b.val.app U z₁) = z₂)
    (h₃ : g.val.app U z₂ = z₃) :
    coefficientRestrictionSection q W U
      ((a ≫ b ≫ (SheafOfModules.restrictScalars q).map g).val.app U z) = z₃ := by
  subst h₁ h₂ h₃
  rfl

/-- An eqToHom of abelian groups is surjective.
Source: Stacks 0941. -/
theorem eqToHom_surjective {A B : AddCommGrpCat.{r}} (h : A = B) :
    Function.Surjective (eqToHom h) := by
  subst B
  exact fun x ↦ ⟨x, rfl⟩

/-- Transport of a commuting square along identifications of abelian groups.
Source: Stacks 0941. -/
theorem transport_square {A B A' B' : AddCommGrpCat.{r}}
    (hA : A' = A) (hB : B' = B) {f : A' ⟶ B'} {g : A ⟶ B}
    (h : eqToHom hA.symm ≫ f ≫ eqToHom hB = g) (x : A) :
    f (eqToHom hA.symm x) = eqToHom hB.symm (g x) := by
  subst A
  subst B
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    ConcreteCategory.id_apply] using congrArg (fun f ↦ f x) h

/-- A section formula for a transformation, transported along identifications of the
underlying abelian groups. Source: Stacks 0941. -/
theorem transported_transition_section {D : Type*} [Category D]
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    (Fm : D ⥤ SheafOfModules.{r} R) (Fn : D ⥤ SheafOfModules.{r} S)
    (τ : Fm ⟶ Fn ⋙ SheafOfModules.restrictScalars φ) (M : D) (U : Cᵒᵖ)
    {G H : AddCommGrpCat.{r}}
    (ha : (Fm.obj M).val.presheaf.obj U = G) (hb : (Fn.obj M).val.presheaf.obj U = H)
    (g : G ⟶ H)
    (h : eqToHom ha.symm ≫
      (forget₂ (ModuleCat.{r} (R.obj.obj U)) AddCommGrpCat.{r}).map
        ((τ.app M).val.app U) ≫ eqToHom hb = g) (x : G) :
    coefficientRestrictionSection φ (Fn.obj M) U ((τ.app M).val.app U (eqToHom ha.symm x)) =
      eqToHom hb.symm (g x) := by
  exact transport_square ha hb h x

/-- A strict quotient transformation sends adjunction unit sections to adjunction unit
sections. Packaging this as a structure keeps kernel checking at the level of its arguments.
Source: Stacks 03CZ, 03D7. -/
structure QuotientUnitLaw {R S T : Sheaf J RingCat.{r}} (pm : R ⟶ S) (pn : R ⟶ T)
    {Em : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    {En : SheafOfModules.{r} R ⥤ SheafOfModules.{r} T}
    {Tf : SheafOfModules.{r} T ⥤ SheafOfModules.{r} S}
    (quot : Em ⟶ En ⋙ Tf) (am : Em ⊣ SheafOfModules.restrictScalars pm)
    (an : En ⊣ SheafOfModules.restrictScalars pn) : Prop where
  unit : ∀ (X : SheafOfModules.{r} R) (U : Cᵒᵖ) (x : X.val.obj U),
    HEq ((quot.app X).val.app U
      (coefficientRestrictionSection pm (Em.obj X) U ((am.unit.app X).val.app U x)))
      (coefficientRestrictionSection pn (En.obj X) U ((an.unit.app X).val.app U x))

/-- A transformation agreeing with the mate of a composite of restrictions.
Source: Stacks 03D7. -/
structure QuotientMateLaw {A₀ : Type*} {B₀ : Type*} {C₀ : Type*} [Category A₀] [Category B₀]
    [Category C₀] {Em : A₀ ⥤ B₀} {En : A₀ ⥤ C₀} {Gm : B₀ ⥤ A₀} {Gn : C₀ ⥤ A₀} {Tf : C₀ ⥤ B₀}
    (am : Em ⊣ Gm) (an : En ⊣ Gn) (e : Tf ⋙ Gm ≅ Gn) (quot : Em ⟶ En ⋙ Tf) : Prop where
  app_eq : ∀ X, quot.app X = (coefficientQuotientNatTrans am an Tf e).app X

/-- The inverse of an equality of functors into module sheaves is the identity on sections.
Source: Stacks 03CZ. -/
theorem eqToIso_inv_section_heq {R : Sheaf J RingCat.{r}} {X : Type*} [Category X]
    {F G : X ⥤ SheafOfModules.{r} R} (h : F = G) (N : X) (U : Cᵒᵖ)
    (y : (G.obj N).val.obj U) : HEq (((eqToIso h).inv.app N).val.app U y) y := by
  cases h
  rfl

/-- The mate of an equality of composite restrictions sends unit sections to unit sections.
Source: Stacks 03CZ, 03D7. -/
theorem quotientUnitLaw_of_mateLaw {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : S ⟶ T)
    (h : R ⟶ T)
    (he : SheafOfModules.restrictScalars.{r} g ⋙ SheafOfModules.restrictScalars f =
      SheafOfModules.restrictScalars h)
    {F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    (adj : F ⊣ SheafOfModules.restrictScalars f)
    {F' : SheafOfModules.{r} R ⥤ SheafOfModules.{r} T}
    (adj' : F' ⊣ SheafOfModules.restrictScalars h)
    (quot : F ⟶ F' ⋙ SheafOfModules.restrictScalars g)
    (hq : QuotientMateLaw adj adj' (eqToIso he) quot) : QuotientUnitLaw f h quot adj adj' := by
  constructor
  intro M U x
  have hu : adj.unit.app M ≫ (SheafOfModules.restrictScalars f).map (quot.app M) =
      adj'.unit.app M ≫ (eqToIso he).inv.app (F'.obj M) := by
    rw [hq.app_eq M]
    exact (adj.homEquiv _ _).apply_symm_apply _
  exact (heq_of_eq (congrArg (fun k ↦ k.val.app U x) hu)).trans
    (eqToIso_inv_section_heq he (F'.obj M) U _)

section Generators

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The total tensor of a product isomorphism acts factorwise on pure generators.
Source: Stacks 03EK, 07A4. -/
theorem mapIso_prod_hom_generator {R : Sheaf J CommRingCat.{max c v r}}
    {P P' Q Q' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (a : P ≅ P') (b : Q ≅ Q') (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((coefficientTotalTensor.{r, c, v} J R).mapIso (a.prod b)).hom.f k).val.app U
        (coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x y)) =
      coefficientTensorGenerator.{r, c, v} J R P' Q' p q k h U
        ((a.hom.f p).val.app U x) ((b.hom.f q).val.app U y) :=
  CategoryTheory.ScalarHomTensor.tensor_generator_map.{c, v, r} a.hom b.hom p q k h U x y

/-- The total tensor of a product isomorphism acts factorwise on pure generators.
Source: Stacks 03EK, 07A4. -/
theorem mapIso_prod_inv_generator {R : Sheaf J CommRingCat.{max c v r}}
    {P P' Q Q' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (a : P ≅ P') (b : Q ≅ Q') (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P'.X p).val.obj U) (y : (Q'.X q).val.obj U) :
    ((((coefficientTotalTensor.{r, c, v} J R).mapIso (a.prod b)).inv.f k).val.app U
        (coefficientTensorGenerator.{r, c, v} J R P' Q' p q k h U x y)) =
      coefficientTensorGenerator.{r, c, v} J R P Q p q k h U
        ((a.inv.f p).val.app U x) ((b.inv.f q).val.app U y) :=
  CategoryTheory.ScalarHomTensor.tensor_generator_map.{c, v, r} a.inv b.inv p q k h U x y

/-- Pure tensor generators are compatible with restriction along the site.
Source: Stacks 03EK. -/
theorem generator_presheaf_restrict (R : Sheaf J CommRingCat.{max c v r})
    (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (p q k : ℤ) (h : p + q = k) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X k).val.presheaf.map f
      (coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x y) =
    coefficientTensorGenerator.{r, c, v} J R P Q p q k h V
      ((P.X p).val.presheaf.map f x) ((Q.X q).val.presheaf.map f y) :=
  CategoryTheory.ringedSiteTensorGenerator_restrict.{c, v, r} J R P Q p q k h f x y

end Generators

/-- Scalar extension of a map sends unit sections to unit sections.
Source: Stacks 03CZ. -/
theorem unit_map_section {A B : Sheaf J RingCat.{r}} (π : A ⟶ B)
    {F : SheafOfModules.{r} A ⥤ SheafOfModules.{r} B}
    (a : F ⊣ SheafOfModules.restrictScalars π) {X X' : SheafOfModules.{r} A} (φ : X ⟶ X')
    (U : Cᵒᵖ) (x : X.val.obj U) :
    (F.map φ).val.app U (coefficientRestrictionSection π (F.obj X) U ((a.unit.app X).val.app U x)) =
      coefficientRestrictionSection π (F.obj X') U ((a.unit.app X').val.app U (φ.val.app U x)) :=
  (congrArg (fun k ↦ k.val.app U x) (a.unit.naturality φ)).symm

section ScalarNaturality

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

-- The section calculation passes through total tensor complexes and scalar restriction.
/-- Scalar tensor comparisons characterized by the unit-section generator formula are
natural in both complexes. Source: Stacks 03EK, 07A4. -/
theorem scalarTensor_naturality {A B : Sheaf J CommRingCat.{max c v r}}
    (π : (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A ⟶
      (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj B)
    {F : SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) ⥤
      SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj B)}
    [hF : F.Additive] (a : F ⊣ SheafOfModules.restrictScalars π)
    {P P' Q Q' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q')
    (s : (F.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J B).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P, (F.mapHomologicalComplex (.up ℤ)).obj Q))
    (s' : (F.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} J A).obj (P', Q')) ≅
      (coefficientTotalTensor.{r, c, v} J B).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P', (F.mapHomologicalComplex (.up ℤ)).obj Q'))
    (hs : CoefficientScalarTensorGenerators.{r, c, v} J A B F
      (fun X U x ↦ coefficientRestrictionSection π (F.obj X) U ((a.unit.app X).val.app U x))
      P Q s)
    (hs' : CoefficientScalarTensorGenerators.{r, c, v} J A B F
      (fun X U x ↦ coefficientRestrictionSection π (F.obj X) U ((a.unit.app X).val.app U x))
      P' Q' s') :
    (F.mapHomologicalComplex (.up ℤ)).map
        ((coefficientTotalTensor.{r, c, v} J A).map (Prod.mkHom f g)) ≫ s'.hom =
      s.hom ≫ (coefficientTotalTensor.{r, c, v} J B).map
        (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f)
          ((F.mapHomologicalComplex (.up ℤ)).map g)) := by
  have key (k : ℤ) : F.map (((coefficientTotalTensor.{r, c, v} J A).map (Prod.mkHom f g)).f k) ≫
      s'.hom.f k = s.hom.f k ≫ ((coefficientTotalTensor.{r, c, v} J B).map
        (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f)
          ((F.mapHomologicalComplex (.up ℤ)).map g))).f k := by
    apply hom_ext_of_unit a
    apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{c, v, r} P Q k
    intro p p' hpq V x y
    apply restrictionSection_injective π _ V
    change (s'.hom.f k).val.app V
        ((F.map (((coefficientTotalTensor.{r, c, v} J A).map (Prod.mkHom f g)).f k)).val.app V
          (coefficientRestrictionSection π _ V ((a.unit.app _).val.app V
            (coefficientTensorGenerator.{r, c, v} J A P Q p p' k hpq V x y)))) =
      (((coefficientTotalTensor.{r, c, v} J B).map
        (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f)
          ((F.mapHomologicalComplex (.up ℤ)).map g))).f k).val.app V
        ((s.hom.f k).val.app V (coefficientRestrictionSection π _ V
          ((a.unit.app _).val.app V
            (coefficientTensorGenerator.{r, c, v} J A P Q p p' k hpq V x y))))
    -- Apply the generator formulas under fixed section maps, avoiding rewrite search
    -- through the scalar restrictions and total tensor complexes.
    have hleft := (congrArg ((s'.hom.f k).val.app V)
      (unit_map_section π a
        (((coefficientTotalTensor.{r, c, v} J A).map (Prod.mkHom f g)).f k) V
        (coefficientTensorGenerator.{r, c, v} J A P Q p p' k hpq V x y))).trans
      ((congrArg (fun z ↦ (s'.hom.f k).val.app V
        (coefficientRestrictionSection π _ V ((a.unit.app _).val.app V z)))
        (CategoryTheory.ScalarHomTensor.tensor_generator_map.{c, v, r}
          f g p p' k hpq V x y)).trans
        (hs' p p' k hpq V ((f.f p).val.app V x) ((g.f p').val.app V y)))
    have hright := (congrArg
      ((((coefficientTotalTensor.{r, c, v} J B).map
        (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f)
          ((F.mapHomologicalComplex (.up ℤ)).map g))).f k).val.app V)
      (hs p p' k hpq V x y)).trans
      ((CategoryTheory.ScalarHomTensor.tensor_generator_map.{c, v, r}
        ((F.mapHomologicalComplex (.up ℤ)).map f)
        ((F.mapHomologicalComplex (.up ℤ)).map g) p p' k hpq V _ _).trans
        (congrArg₂ (coefficientTensorGenerator.{r, c, v} J B
          ((F.mapHomologicalComplex (.up ℤ)).obj P')
          ((F.mapHomologicalComplex (.up ℤ)).obj Q') p p' k hpq V)
          (unit_map_section π a (f.f p) V x) (unit_map_section π a (g.f p') V y)))
    exact hleft.trans hright.symm
  apply HomologicalComplex.Hom.ext
  funext k
  exact key k

end ScalarNaturality

section TensorTransition

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify (coefficientSequenceTopology J) AddCommGrpCat.{max c v r}]
  [(coefficientSequenceTopology J).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

-- The section calculation passes through several levels of composite functors.
/-- The tensor product of two presentations of strict system complexes is again a
presentation: its finite comparison commutes with the strict transitions.
Source: Stacks 03EK, 07A4 and 0941. -/
theorem tensorPresentation_transition
    {A Bm Bn : Sheaf J CommRingCat.{max c v r}}
    {R : Sheaf (coefficientSequenceTopology J) CommRingCat.{max c v r}}
    (pm : (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A ⟶
      (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bm)
    (pn : (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A ⟶
      (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bn)
    (q : (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bm ⟶
      (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bn)
    {Em : SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) ⥤
      SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bm)}
    {En : SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) ⥤
      SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bn)}
    [hEm : Em.Additive] [hEn : En.Additive]
    (am : Em ⊣ SheafOfModules.restrictScalars pm) (an : En ⊣ SheafOfModules.restrictScalars pn)
    (quot : Em ⟶ En ⋙ SheafOfModules.restrictScalars q)
    (hquot : QuotientUnitLaw pm pn quot am an)
    {evm : SheafOfModules.{max c v r} ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⥤
      SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bm)}
    {evn : SheafOfModules.{max c v r} ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⥤
      SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bn)}
    [hevm : evm.Additive] [hevn : evn.Additive]
    (τ : evm ⟶ evn ⋙ SheafOfModules.restrictScalars q)
    {m n : ℕ} (hmn : n ≤ m)
    (σm : ∀ (M : SheafOfModules.{max c v r} ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) (U : Cᵒᵖ),
      M.val.obj (op (m, U.unop)) → (evm.obj M).val.obj U)
    (σn : ∀ (M : SheafOfModules.{max c v r} ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) (U : Cᵒᵖ),
      M.val.obj (op (n, U.unop)) → (evn.obj M).val.obj U)
    (hσm : ∀ M U, Function.Surjective (σm M U))
    (hτ : ∀ M U x, coefficientRestrictionSection q (evn.obj M) U
      ((τ.app M).val.app U (σm M U x)) =
        σn M U (M.val.presheaf.map (Prod.mkHom (homOfLE hmn) (𝟙 U.unop)).op x))
    (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ)
    (CP CQ : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (κPm : (evm.mapHomologicalComplex (.up ℤ)).obj CP ≅ (Em.mapHomologicalComplex (.up ℤ)).obj P)
    (κPn : (evn.mapHomologicalComplex (.up ℤ)).obj CP ≅ (En.mapHomologicalComplex (.up ℤ)).obj P)
    (κQm : (evm.mapHomologicalComplex (.up ℤ)).obj CQ ≅ (Em.mapHomologicalComplex (.up ℤ)).obj Q)
    (κQn : (evn.mapHomologicalComplex (.up ℤ)).obj CQ ≅ (En.mapHomologicalComplex (.up ℤ)).obj Q)
    (hP : ∀ p, τ.app (CP.X p) ≫ (SheafOfModules.restrictScalars q).map (κPn.hom.f p) =
      κPm.hom.f p ≫ quot.app (P.X p))
    (hQ : ∀ p, τ.app (CQ.X p) ≫ (SheafOfModules.restrictScalars q).map (κQn.hom.f p) =
      κQm.hom.f p ≫ quot.app (Q.X p))
    (evTm : (evm.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} (coefficientSequenceTopology J) R).obj (CP, CQ)) ≅
      (coefficientTotalTensor.{r, c, v} J Bm).obj
        ((evm.mapHomologicalComplex (.up ℤ)).obj CP, (evm.mapHomologicalComplex (.up ℤ)).obj CQ))
    (hevTm : ∀ (p q k : ℤ) (hpq : p + q = k) (U : Cᵒᵖ)
      (x : (CP.X p).val.obj (op (m, U.unop))) (y : (CQ.X q).val.obj (op (m, U.unop))),
      (evTm.hom.f k).val.app U (σm _ U
        (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J) R CP CQ p q k hpq
          (op (m, U.unop)) x y)) =
        coefficientTensorGenerator.{r, c, v} J Bm ((evm.mapHomologicalComplex (.up ℤ)).obj CP)
          ((evm.mapHomologicalComplex (.up ℤ)).obj CQ) p q k hpq U (σm _ U x) (σm _ U y))
    (evTn : (evn.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} (coefficientSequenceTopology J) R).obj (CP, CQ)) ≅
      (coefficientTotalTensor.{r, c, v} J Bn).obj
        ((evn.mapHomologicalComplex (.up ℤ)).obj CP, (evn.mapHomologicalComplex (.up ℤ)).obj CQ))
    (hevTn : ∀ (p q k : ℤ) (hpq : p + q = k) (U : Cᵒᵖ)
      (x : (CP.X p).val.obj (op (n, U.unop))) (y : (CQ.X q).val.obj (op (n, U.unop))),
      (evTn.hom.f k).val.app U (σn _ U
        (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J) R CP CQ p q k hpq
          (op (n, U.unop)) x y)) =
        coefficientTensorGenerator.{r, c, v} J Bn ((evn.mapHomologicalComplex (.up ℤ)).obj CP)
          ((evn.mapHomologicalComplex (.up ℤ)).obj CQ) p q k hpq U (σn _ U x) (σn _ U y))
    (sm : (Em.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J Bm).obj
        ((Em.mapHomologicalComplex (.up ℤ)).obj P, (Em.mapHomologicalComplex (.up ℤ)).obj Q))
    (hsm : CoefficientScalarTensorGenerators.{r, c, v} J A Bm Em
      (fun X U x ↦ coefficientRestrictionSection pm (Em.obj X) U ((am.unit.app X).val.app U x))
      P Q sm)
    (sn : (En.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J Bn).obj
        ((En.mapHomologicalComplex (.up ℤ)).obj P, (En.mapHomologicalComplex (.up ℤ)).obj Q))
    (hsn : CoefficientScalarTensorGenerators.{r, c, v} J A Bn En
      (fun X U x ↦ coefficientRestrictionSection pn (En.obj X) U ((an.unit.app X).val.app U x))
      P Q sn) :
    (NatTrans.mapHomologicalComplex τ (.up ℤ)).app
        ((coefficientTotalTensor.{r, c, v} (coefficientSequenceTopology J) R).obj (CP, CQ)) ≫
      ((SheafOfModules.restrictScalars q).mapHomologicalComplex (.up ℤ)).map
        (evTn ≪≫ (coefficientTotalTensor.{r, c, v} J Bn).mapIso (κPn.prod κQn) ≪≫ sn.symm).hom =
    (evTm ≪≫ (coefficientTotalTensor.{r, c, v} J Bm).mapIso (κPm.prod κQm) ≪≫ sm.symm).hom ≫
      (NatTrans.mapHomologicalComplex quot (.up ℤ)).app
        ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) := by
  have hq (X : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))
      (U : Cᵒᵖ) (x : X.val.obj U) :
      coefficientRestrictionSection q (En.obj X) U ((quot.app X).val.app U
        (coefficientRestrictionSection pm (Em.obj X) U ((am.unit.app X).val.app U x))) =
      coefficientRestrictionSection pn (En.obj X) U ((an.unit.app X).val.app U x) :=
    eq_of_heq (hquot.unit X U x)
  have key (k : ℤ) :
      (evTm ≪≫ (coefficientTotalTensor.{r, c, v} J Bm).mapIso (κPm.prod κQm) ≪≫ sm.symm).inv.f k ≫
        τ.app (((coefficientTotalTensor.{r, c, v} (coefficientSequenceTopology J) R).obj
          (CP, CQ)).X k) ≫ (SheafOfModules.restrictScalars q).map
          ((evTn ≪≫ (coefficientTotalTensor.{r, c, v} J Bn).mapIso (κPn.prod κQn) ≪≫
            sn.symm).hom.f k) =
      quot.app (((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)).X k) := by
    apply hom_ext_of_unit am
    apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{c, v, r} P Q k
    intro p p' hpq V x y
    apply restrictionSection_injective pm _ V
    change
      (((evTm ≪≫ (coefficientTotalTensor.{r, c, v} J Bm).mapIso (κPm.prod κQm) ≪≫
          sm.symm).inv.f k) ≫
        τ.app (((coefficientTotalTensor.{r, c, v} (coefficientSequenceTopology J) R).obj
          (CP, CQ)).X k) ≫ (SheafOfModules.restrictScalars q).map
          ((evTn ≪≫ (coefficientTotalTensor.{r, c, v} J Bn).mapIso (κPn.prod κQn) ≪≫
            sn.symm).hom.f k)).val.app V
        (coefficientRestrictionSection pm _ V ((am.unit.app _).val.app V
          (coefficientTensorGenerator.{r, c, v} J A P Q p p' k hpq V x y))) =
      (quot.app _).val.app V
        (coefficientRestrictionSection pm _ V ((am.unit.app _).val.app V
          (coefficientTensorGenerator.{r, c, v} J A P Q p p' k hpq V x y)))
    apply restrictionSection_injective q _ V
    refine Eq.trans ?_ (hq
      (((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)).X k) V
      (coefficientTensorGenerator.{r, c, v} J A P Q p p' k hpq V x y)).symm
    have hx := hσm (CP.X p) V ((κPm.inv.f p).val.app V
      (coefficientRestrictionSection pm (Em.obj (P.X p)) V ((am.unit.app (P.X p)).val.app V x)))
    have hy := hσm (CQ.X p') V ((κQm.inv.f p').val.app V
      (coefficientRestrictionSection pm (Em.obj (Q.X p')) V ((am.unit.app (Q.X p')).val.app V y)))
    -- Select the lifts without eliminating existentials in the large section equality.
    let x0 := hx.choose
    let y0 := hy.choose
    have hx0 : σm (CP.X p) V x0 = _ := hx.choose_spec
    have hy0 : σm (CQ.X p') V y0 = _ := hy.choose_spec
    refine comp_restrict_section q _ _ _ V _
      (σm _ V (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J) R CP CQ
        p p' k hpq (op (m, V.unop)) x0 y0))
      (σn _ V (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J) R CP CQ
        p p' k hpq (op (n, V.unop))
        ((CP.X p).val.presheaf.map (Prod.mkHom (homOfLE hmn) (𝟙 V.unop)).op x0)
        ((CQ.X p').val.presheaf.map (Prod.mkHom (homOfLE hmn) (𝟙 V.unop)).op y0))) _
      ?_ ?_ ?_
    · refine (congrArg ((evTm.inv.f k).val.app V) ?_).trans
        (iso_hom_inv_section evTm k V _)
      refine (congrArg
        ((((coefficientTotalTensor.{r, c, v} J Bm).mapIso (κPm.prod κQm)).inv.f k).val.app V)
        (hsm p p' k hpq V x y)).trans ?_
      refine (mapIso_prod_inv_generator κPm κQm p p' k hpq V _ _).trans ?_
      exact (congrArg₂ (coefficientTensorGenerator.{r, c, v} J Bm
        ((evm.mapHomologicalComplex (.up ℤ)).obj CP)
        ((evm.mapHomologicalComplex (.up ℤ)).obj CQ) p p' k hpq V)
        hx0.symm hy0.symm).trans (hevTm p p' k hpq V x0 y0).symm
    · exact (hτ _ V _).trans (congrArg (σn _ V)
        (generator_presheaf_restrict R CP CQ p p' k hpq
          (Prod.mkHom (homOfLE hmn) (𝟙 V.unop)).op x0 y0))
    · have hxn : (κPn.hom.f p).val.app V (σn (CP.X p) V ((CP.X p).val.presheaf.map
          (Prod.mkHom (homOfLE hmn) (𝟙 V.unop)).op x0)) =
          coefficientRestrictionSection pn (En.obj (P.X p)) V
            ((an.unit.app (P.X p)).val.app V x) := by
        have hcomp := congrArg (fun f ↦ coefficientRestrictionSection q _ V
          (f.val.app V (σm (CP.X p) V x0))) (hP p)
        have hx := (congrArg ((κPm.hom.f p).val.app V) hx0).trans
          (iso_inv_hom_section κPm p V _)
        exact (congrArg ((κPn.hom.f p).val.app V) (hτ (CP.X p) V x0).symm).trans
          (hcomp.trans ((congrArg (fun z ↦ coefficientRestrictionSection q _ V
            ((quot.app (P.X p)).val.app V z)) hx).trans (hq (P.X p) V x)))
      have hyn : (κQn.hom.f p').val.app V (σn (CQ.X p') V ((CQ.X p').val.presheaf.map
          (Prod.mkHom (homOfLE hmn) (𝟙 V.unop)).op y0)) =
          coefficientRestrictionSection pn (En.obj (Q.X p')) V
            ((an.unit.app (Q.X p')).val.app V y) := by
        have hcomp := congrArg (fun f ↦ coefficientRestrictionSection q _ V
          (f.val.app V (σm (CQ.X p') V y0))) (hQ p')
        have hy := (congrArg ((κQm.hom.f p').val.app V) hy0).trans
          (iso_inv_hom_section κQm p' V _)
        exact (congrArg ((κQn.hom.f p').val.app V) (hτ (CQ.X p') V y0).symm).trans
          (hcomp.trans ((congrArg (fun z ↦ coefficientRestrictionSection q _ V
            ((quot.app (Q.X p')).val.app V z)) hy).trans (hq (Q.X p') V y)))
      refine (congrArg ((sn.inv.f k).val.app V) ?_).trans (iso_hom_inv_section sn k V _)
      refine (congrArg
        ((((coefficientTotalTensor.{r, c, v} J Bn).mapIso (κPn.prod κQn)).hom.f k).val.app V)
        (hevTn p p' k hpq V _ _)).trans ?_
      refine (mapIso_prod_hom_generator κPn κQn p p' k hpq V _ _).trans ?_
      exact (congrArg₂ (coefficientTensorGenerator.{r, c, v} J Bn
        ((En.mapHomologicalComplex (.up ℤ)).obj P)
        ((En.mapHomologicalComplex (.up ℤ)).obj Q) p p' k hpq V)
        hxn hyn).trans (hsn p p' k hpq V x y).symm
  refine (Iso.inv_comp_eq _).1 ?_
  apply HomologicalComplex.Hom.ext
  funext k
  exact key k

end TensorTransition

end OrdinaryReductionTensor
end WeilConjectures
