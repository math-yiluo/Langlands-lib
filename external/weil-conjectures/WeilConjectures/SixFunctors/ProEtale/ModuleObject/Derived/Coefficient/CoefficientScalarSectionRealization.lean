/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentative
import all Mathlib.Algebra.Homology.Localization

/-! # Section realization of coefficient scalar extension

Source: Stacks Project, Tags 03EK, 03EL, 06YY, 07A4 and 07A6;
steps 1--3 of `lem-sfb-coefficient-scalar-tensor-realization`.
(blueprint: lem-sfb-coefficient-scalar-section-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u d₁ d₂ r m c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap
  coefficientInternalScalarComplex coefficientSectionScalarPure coefficientSectionScalarTotal
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.ordinaryTensorComparison derivedTensor
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  internalScalarTensorIso internalScalarTensorComparison
  SheafOfModules.changeOfRingsHom
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor
  Adjunction.derivedAdjunction Mod.derivedExtendMapDerivedCategoryAdjunction
  Mod.derivedExtendRestrictAdjunction Mod.extendRestrictAdjunction
  Adjunction.mapHomotopyCategory Adjunction.mapHomologicalComplex Functor.preimageIso
  Functor.leftDerivedFunctorIsoMapDerivedCategory
  Functor.rightDerivedFunctorIsoMapDerivedCategory
set_option allowUnsafeReducibility true in
attribute [local reducible] internalScalarExtension
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]
private theorem adjoint_compute {C D : Type*} [Category C] [Category D]
    {L F : C ⥤ D} {U : D ⥤ C} (n : L ⊣ U) (f : F ⊣ U)
    {X : C} {Y : D} (ε : F.obj X ⟶ Y) (c : L.obj X ⟶ Y)
    (h : f.unit.app X ≫ U.map ε = n.unit.app X ≫ U.map c) :
    (Adjunction.leftAdjointUniq n f).hom.app X ≫ ε = c := by
  apply (n.homEquiv X Y).injective
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  exact h

private theorem adjoint_hom {C D : Type*} [Category C] [Category D]
    {L F : C ⥤ D} {U : D ⥤ C} (n : L ⊣ U) (f : F ⊣ U)
    {X : C} {Y : D} (g : L.obj X ⟶ Y) :
    f.homEquiv X Y ((Adjunction.leftAdjointUniq n f).inv.app X ≫ g) =
      n.homEquiv X Y g := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

private theorem adj_comparison {C D : Type*} [Category C] [Category D]
    {L F : C ⥤ D} {U : D ⥤ C} (n : L ⊣ U) (f : F ⊣ U) :
    ∃ e : L ≅ F,
      (∀ (X : C) (Y : D) (ε : F.obj X ⟶ Y) (c : L.obj X ⟶ Y),
        f.unit.app X ≫ U.map ε = n.unit.app X ≫ U.map c → e.hom.app X ≫ ε = c) ∧
      (∀ (X : C) (Y : D) (g : L.obj X ⟶ Y),
        f.homEquiv X Y (e.inv.app X ≫ g) = n.homEquiv X Y g) := by
  refine ⟨Adjunction.leftAdjointUniq n f, ?_, ?_⟩
  · intro X Y ε c h
    exact adjoint_compute n f ε c h
  · intro X Y g
    exact adjoint_hom n f g

private theorem transport_iso {C D E : Type*}
    [Category C] [Category D] [Category E]
    {L F : C ⥤ D} {G : C ⥤ E} (e : L ≅ F) (H : D ⥤ E) (p : F ⋙ H ≅ G) :
    ∃ p' : L ⋙ H ≅ G,
      (∀ X : C, p'.hom.app X = H.map (e.hom.app X) ≫ p.hom.app X) ∧
      (∀ X : C, p'.inv.app X = p.inv.app X ≫ H.map (e.inv.app X)) := by
  exact ⟨Functor.isoWhiskerRight e H ≪≫ p, fun _ ↦ rfl, fun _ ↦ rfl⟩

private theorem transport_hom {C D E F : Type*}
    [Category C] [Category D] [Category E] [Category F]
    {L L' : C ⥤ D} {U : D ⥤ C} {T : E ⥤ F} {V : F ⥤ E}
    (n : L ⊣ U) (f : L' ⊣ U) (d : T ⊣ V) (H : C ⥤ E) (G : D ⥤ F)
    (e : L ≅ L') (p : L' ⋙ G ≅ H ⋙ T) (p' : L ⋙ G ≅ H ⋙ T)
    (q : U ⋙ H ≅ G ⋙ V)
    (he : ∀ (X : C) (Y : D) (g : L.obj X ⟶ Y),
      f.homEquiv X Y (e.inv.app X ≫ g) = n.homEquiv X Y g)
    (hp : ∀ X : C, p'.inv.app X = p.inv.app X ≫ G.map (e.inv.app X))
    (ha : ∀ (X : C) (Y : D) (g : L'.obj X ⟶ Y),
      H.map (f.homEquiv X Y g) ≫ q.hom.app Y =
        d.homEquiv _ _ (p.inv.app X ≫ G.map g)) :
    ∀ (X : C) (Y : D) (g : L.obj X ⟶ Y),
      H.map (n.homEquiv X Y g) ≫ q.hom.app Y =
        d.homEquiv _ _ (p'.inv.app X ≫ G.map g) := by
  intro X Y g
  rw [← he X Y g, ha]
  rw [hp, G.map_comp, Category.assoc]

private theorem cast_section_eq {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A : Sheaf J RingCat.{r}}
    {M N : SheafOfModules.{m} A} (h : M = N) (V : Cᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V)
    (hh : (eqToHom h).val.app V x = y) :
    x = (eqToHom h.symm).val.app V y := by
  subst N
  exact hh

private theorem map_computation {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B C' : C} {D' E' : D}
    (e : A ⟶ B) (f : B ⟶ C') (g : A ⟶ C') (h : e ≫ f = g)
    (j : H.obj C' ⟶ D') (k : D' ⟶ E') (x : H.obj B ⟶ E')
    (hh : H.map f ≫ j ≫ k = x) : H.map g ≫ j ≫ k = H.map e ≫ x := by
  rw [← h, H.map_comp, Category.assoc, hh]

private theorem factor_on_complex {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{d₁} C] [HasDerivedCategory.{d₂} D]
    (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (P : CochainComplex C ℤ) :
    H.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      H.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.comp_obj, Quotient.lift.isLift_hom]
  erw [H.mapDerivedCategory.map_id, Category.id_comp, DerivedCategory.Qh.map_id,
    Category.comp_id, Category.comp_id]

private theorem factor_on_mapped_complex {C D E : Type*}
    [Category C] [Category D] [Category E] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{d₁} D] [HasDerivedCategory.{d₂} E]
    (F : C ⥤ D) [F.Additive] (H : D ⥤ E) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (P : CochainComplex C ℤ) :
    H.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  change H.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)) = _
  exact factor_on_complex H _

private def uncurry_comparison {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) (B : C ⥤ C ⥤ C) (B' : D ⥤ D ⥤ D)
    (e : (Functor.postcompose₂.obj T).obj B ≅
      (((Functor.whiskeringLeft₂ _).obj T).obj T).obj B') :
    Functor.uncurry.obj B ⋙ T ≅ T.prod T ⋙ Functor.uncurry.obj B' := by
  refine NatIso.ofComponents (fun MN ↦ (e.app MN.1).app MN.2) ?_
  intro X Y f
  have hl := NatTrans.congr_app (e.hom.naturality f.1) X.2
  have hr := (e.hom.app Y.1).naturality f.2
  change T.map ((B.map f.1).app X.2) ≫ ((e.app Y.1).app X.2).hom =
    ((e.app X.1).app X.2).hom ≫ (B'.map (T.map f.1)).app (T.obj X.2) at hl
  change T.map ((B.obj Y.1).map f.2) ≫ ((e.app Y.1).app Y.2).hom =
    ((e.app Y.1).app X.2).hom ≫ (B'.obj (T.obj Y.1)).map (T.map f.2) at hr
  change T.map ((B.map f.1).app X.2 ≫ (B.obj Y.1).map f.2) ≫
      ((e.app Y.1).app Y.2).hom =
    ((e.app X.1).app X.2).hom ≫ (B'.map (T.map f.1)).app (T.obj X.2) ≫
      (B'.obj (T.obj Y.1)).map (T.map f.2)
  rw [T.map_comp, Category.assoc, hr, ← Category.assoc, hl, Category.assoc]

private theorem cancel_pair {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} {A B : D} (c : X ≅ Y) (p : A ≅ F.obj X)
    (g : A ⟶ B) :
    p.hom ≫ F.map c.hom ≫ F.map c.inv ≫ p.inv ≫ g = g := by
  rw [← F.map_comp_assoc, c.hom_inv_id, F.map_id, Category.id_comp, p.hom_inv_id_assoc]

private theorem monoidal_constraints {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (unitIso : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (tensorIso : ∀ M N : C, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (natural : ∀ (M N M' N' : C) (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (tensorIso M' N').hom =
        (tensorIso M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (assoc : ∀ M N K : C,
      F.map (α_ M N K).hom ≫ (tensorIso M (N ⊗ K)).hom ≫
          (F.obj M ◁ (tensorIso N K).hom) =
        (tensorIso (M ⊗ N) K).hom ≫ ((tensorIso M N).hom ▷ F.obj K) ≫
          (α_ (F.obj M) (F.obj N) (F.obj K)).hom)
    (leftUnit : ∀ M : C, (tensorIso (𝟙_ C) M).hom ≫
        (unitIso.hom ▷ F.obj M) ≫ (λ_ (F.obj M)).hom = F.map (λ_ M).hom)
    (rightUnit : ∀ M : C, (tensorIso M (𝟙_ C)).hom ≫
        (F.obj M ◁ unitIso.hom) ≫ (ρ_ (F.obj M)).hom = F.map (ρ_ M).hom) :
    ∃ m : F.Monoidal, ∀ M N : C, m.toOplaxMonoidal.δ M N = (tensorIso M N).hom := by
  let core : F.CoreMonoidal :=
    Functor.CoreMonoidal.mk' unitIso.symm (fun M N ↦ (tensorIso M N).symm)
      (by
        intro M N f K
        have h := (natural M K N K f (𝟙 K)).symm
        rw [F.map_id, tensorHom_id] at h
        simpa only [Iso.symm_inv, tensorHom_id] using h)
      (by
        intro M N K f
        have h := (natural K M K N (𝟙 K) f).symm
        rw [F.map_id, id_tensorHom] at h
        simpa only [Iso.symm_inv, id_tensorHom] using h)
      (by intro M N K; exact (assoc M N K).symm)
      (by
        intro M
        apply (cancel_mono (λ_ (F.obj M)).hom).mp
        simp only [Category.assoc, Iso.inv_hom_id, Iso.symm_inv]
        rw [leftUnit, ← F.map_comp, Iso.inv_hom_id, F.map_id])
      (by
        intro M
        apply (cancel_mono (ρ_ (F.obj M)).hom).mp
        simp only [Category.assoc, Iso.inv_hom_id, Iso.symm_inv]
        rw [rightUnit, ← F.map_comp, Iso.inv_hom_id, F.map_id])
  exact ⟨core.toMonoidal, fun _ _ ↦ rfl⟩

private theorem descend_iso {C D E : Type*}
    [Category C] [Category D] [Category E] (e : C ≌ D)
    (F G : D ⥤ E) (k : e.functor ⋙ F ≅ e.functor ⋙ G) :
    ∃ t : F ≅ G, ∀ X : C, t.hom.app (e.functor.obj X) = k.hom.app X := by
  let W := (e.congrLeft (E := E)).inverse
  refine ⟨W.preimageIso k, ?_⟩
  intro X
  have h := NatTrans.congr_app (W.map_preimage k.hom) X
  change (W.preimage k.hom).app (e.functor.obj X) = k.hom.app X at h
  simpa only [Functor.preimageIso_hom] using h

open PresheafOfModules in
omit [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))] in
private theorem coefficient_pure_eq (Z : Scheme.{u})
    (b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z))
    (M : ModuleRingedComparison.modules R Z) (V : Z.ProEtᵒᵖ)
    (s : (ModuleRingedComparison.ring S Z).obj.obj V) (x : M.val.obj V) :
    coefficientSectionScalarPure a Z b M V s x =
      (eqToHom (b.extension_obj M).symm).val.app V
        (SheafOfModules.scalarExtensionConstraintTmul
          (coefficientSectionScalarMap a Z) M V x s) := by
  unfold coefficientSectionScalarPure
  apply congrArg ((eqToHom (b.extension_obj M).symm).val.app V)
  symm
  unfold SheafOfModules.scalarExtensionConstraintTmul
  let RS : Sheaf (Scheme.ProEt.topology Z) RingCat.{u + 1} :=
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (ModuleRingedComparison.ring S Z)
  have hs := toPresheaf_map_sheafificationAdjunction_unit_app.{u + 1, u, u + 1, u + 1}
    (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := RS) (𝟙 RS.obj)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (coefficientSectionScalarMap a Z) M)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hs V) _

attribute [local irreducible] SheafOfModules.changeOfRings in
private theorem site_ordinary_monoidal
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (A B : Sheaf J CommRingCat.{w}) (α : A ⟶ B)
    (E : SheafOfModules.ScalarExtensionConstraintModules A ⥤
      SheafOfModules.ScalarExtensionConstraintModules B)
    (hobj : ∀ M, E.obj M = SheafOfModules.changeOfRings.{v, c, w} α M)
    (hE_map : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom α M f ≫ eqToHom (hobj N).symm) :
    ∃ m : E.Monoidal,
      ∀ (M N : SheafOfModules.ScalarExtensionConstraintModules A) (V : Cᵒᵖ)
        (s : B.obj.obj V) (x : M.val.obj V) (y : N.val.obj V),
      (m.toOplaxMonoidal.δ M N).val.app V
          ((eqToHom (hobj (M ⊗ N)).symm).val.app V
            (SheafOfModules.scalarExtensionConstraintTmul α (M ⊗ N) V
              (SheafOfModules.scalarExtensionConstraintPureTensor A M N V x y) s)) =
        SheafOfModules.scalarExtensionConstraintPureTensor B (E.obj M) (E.obj N) V
          ((eqToHom (hobj M).symm).val.app V
            (SheafOfModules.scalarExtensionConstraintTmul α M V x s))
          ((eqToHom (hobj N).symm).val.app V
            (SheafOfModules.scalarExtensionConstraintTmul α N V y 1)) := by
  classical
  obtain ⟨d⟩ := SheafOfModules.scalarExtension_constraint_coherence
    A B α
  let obj : SheafOfModules.ScalarExtensionConstraintModules A →
      SheafOfModules.ScalarExtensionConstraintModules B :=
    fun M ↦ SheafOfModules.changeOfRings.{v, c, w} α M
  let F : SheafOfModules.ScalarExtensionConstraintModules A ⥤
      SheafOfModules.ScalarExtensionConstraintModules B :=
    { obj := obj
      map {M N} f := eqToHom (hobj M).symm ≫ E.map f ≫
        eqToHom (hobj N)
      map_id M := by simp
      map_comp f g := by simp }
  have hmap {M N : SheafOfModules.ScalarExtensionConstraintModules A} (f : M ⟶ N) :
      F.map f = SheafOfModules.changeOfRingsHom α M f := by
    dsimp only [F]
    rw [hE_map]
    simp
  obtain ⟨mF, hδ⟩ := monoidal_constraints F d.unitIso d.tensorIso
    (by intro M N M' N' f g; simpa only [hmap] using d.natural M N M' N' f g)
    (by intro M N K; simpa only [hmap] using d.oplax_associativity M N K)
    (by intro M; simpa only [hmap] using d.oplax_left_unit M)
    (by intro M; simpa only [hmap] using d.oplax_right_unit M)
  let := mF
  let e : F ≅ E := NatIso.ofComponents
    (fun M ↦ (eqToIso (hobj M)).symm) (by intro M N f; simp [F])
  refine ⟨Functor.Monoidal.transport e, ?_⟩
  intro M N V s x y
  rw [Functor.Monoidal.transport_δ, hδ]
  simp only [e, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Iso.symm_hom, Iso.symm_inv, eqToIso.hom, eqToIso.inv]
  have hcancel : ∀ (H : SheafOfModules.ScalarExtensionConstraintModules A)
      (z : (SheafOfModules.changeOfRings α H).val.obj V),
      (eqToHom (hobj H)).val.app V
        ((eqToHom (hobj H).symm).val.app V z) = z := by
    intro H z
    change ((eqToHom (hobj H).symm ≫ eqToHom (hobj H)).val.app V) z = z
    simp
  have hpure {T U T' U' : SheafOfModules.ScalarExtensionConstraintModules B}
      (hT : T = T') (hU : U = U') (z : T.val.obj V) (w : U.val.obj V) :
      ((eqToHom hT ⊗ₘ eqToHom hU).val.app V)
          (SheafOfModules.scalarExtensionConstraintPureTensor B T U V z w) =
        SheafOfModules.scalarExtensionConstraintPureTensor B T' U' V
          ((eqToHom hT).val.app V z) ((eqToHom hU).val.app V w) := by
    subst T' U'
    simp
  change ((eqToHom (hobj M).symm ⊗ₘ
    eqToHom (hobj N).symm).val.app V)
      ((d.tensorIso M N).hom.val.app V
        ((eqToHom (hobj (M ⊗ N))).val.app V
          ((eqToHom (hobj (M ⊗ N)).symm).val.app V _))) = _
  rw [hcancel]
  rw [d.tensor_hom]
  exact hpure (hobj M).symm (hobj N).symm _ _

private theorem coefficient_tensor_pure_eq
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (Z : Scheme.{u}) (M N : ModuleRingedComparison.modules A Z) (V : Z.ProEtᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V) :
    ModuleRingedComparison.sectionPureTensor A Z M N V x y =
      SheafOfModules.scalarExtensionConstraintPureTensor
        (ModuleRingedComparison.ring A Z) M N V x y := rfl

omit [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))] in
private theorem ordinary_monoidal (Z : Scheme.{u})
    (b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z)) :
    ∃ m : b.extension.Monoidal,
      ∀ (M N : ModuleRingedComparison.modules R Z) (V : Z.ProEtᵒᵖ)
        (s : (ModuleRingedComparison.ring S Z).obj.obj V)
        (x : M.val.obj V) (y : N.val.obj V),
      (m.toOplaxMonoidal.δ M N).val.app V
          (coefficientSectionScalarPure a Z b (M ⊗ N) V s
            (ModuleRingedComparison.sectionPureTensor R Z M N V x y)) =
        ModuleRingedComparison.sectionPureTensor S Z (b.extension.obj M) (b.extension.obj N) V
          (coefficientSectionScalarPure a Z b M V s x)
          (coefficientSectionScalarPure a Z b N V 1 y) := by
  obtain ⟨m, h⟩ := site_ordinary_monoidal
    (ModuleRingedComparison.ring R Z) (ModuleRingedComparison.ring S Z)
    (coefficientSectionScalarMap a Z) b.extension b.extension_obj b.extension_map
  refine ⟨m, ?_⟩
  intro M N V s x y
  simpa only [coefficient_pure_eq, coefficient_tensor_pure_eq] using h M N V s x y

private def native_adj (Z : Scheme.{u}) : internalScalarExtension a Z ⊣
    (Mod.comap (coefficientMap a Z)).mapDerivedCategory :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Z)

omit [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)] in
private theorem native_unit (Z : Scheme.{u})
    (P : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
    (native_adj a Z).unit.app
        (DerivedCategory.Q.obj P) ≫
      (Mod.comap (coefficientMap a Z)).mapDerivedCategory.map
        (coefficientInternalScalarComplex a Z P) ≫
      (Mod.comap (coefficientMap a Z)).mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map
      (((Mod.extendRestrictAdjunction (coefficientMap a Z)).mapHomologicalComplex
        (.up ℤ)).unit.app P) := by
  unfold native_adj coefficientInternalScalarComplex
  have h := Adjunction.mapDerivedCategoryAdjunction_unit_app_fac
    (Mod.extendRestrictAdjunction (coefficientMap a Z))
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  simp only [Adjunction.mapDerivedCategoryAdjunction, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] at h
  rw [NatTrans.naturality_assoc
    (Mod.comap (coefficientMap a Z)).rightDerivedFunctorIsoMapDerivedCategory.hom] at h
  have hfacE := factor_on_complex (Mod.extendScalars (coefficientMap a Z)) P
  have hfacU := factor_on_mapped_complex (Mod.extendScalars (coefficientMap a Z))
    (Mod.comap (coefficientMap a Z)) P
  conv at h =>
    lhs
    rhs
    rhs
    rhs
    lhs
    rw [hfacE]
  conv at h =>
    lhs
    rhs
    rhs
    rhs
    rhs
    rw [hfacU]
  conv at h =>
    rhs
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [Mod.derivedExtendMapDerivedCategoryAdjunction,
    Mod.derivedExtendRestrictAdjunction, Mod.rightDerivedComapIsoMapDerivedCategory,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc]
  exact h

omit [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))] in
private theorem tensor_transport (Z : Scheme.{u})
    (b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z))
    (p : internalScalarExtension a Z ⋙
        (ModuleRingedComparison.derivedEquivalence S Z).functor ≅
      (ModuleRingedComparison.derivedEquivalence R Z).functor ⋙ b.derived) :
    ∃ t : ModuleRingedComparison.tensor R Z ⋙ b.derived ≅
        b.derived.prod b.derived ⋙ ModuleRingedComparison.tensor S Z,
      ∀ M N : DerivedCategory (ModuleRingedComparison.internalModules R Z),
      (ModuleRingedComparison.derivedEquivalence S Z).functor.map
          (((internalScalarTensorComparison a Z).app M).app N) ≫
        (ModuleRingedComparison.tensorComparison S Z).hom.app
          ((internalScalarExtension a Z).obj M, (internalScalarExtension a Z).obj N) ≫
        (ModuleRingedComparison.tensor S Z).map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (((derivedTensor R Z).obj M).obj N) ≫
        b.derived.map ((ModuleRingedComparison.tensorComparison R Z).hom.app (M, N)) ≫
        t.hom.app ((ModuleRingedComparison.derivedEquivalence R Z).functor.obj M,
          (ModuleRingedComparison.derivedEquivalence R Z).functor.obj N) := by
  let ER := (ModuleRingedComparison.derivedEquivalence R Z).functor
  let ES := (ModuleRingedComparison.derivedEquivalence S Z).functor
  let T := internalScalarExtension a Z
  let B := Functor.uncurry.obj (derivedTensor R Z)
  let it := uncurry_comparison T (derivedTensor R Z) (derivedTensor S Z)
    (internalScalarTensorIso a Z)
  let k : ER.prod ER ⋙ (ModuleRingedComparison.tensor R Z ⋙ b.derived) ≅
      ER.prod ER ⋙ (b.derived.prod b.derived ⋙ ModuleRingedComparison.tensor S Z) :=
    Functor.isoWhiskerRight (ModuleRingedComparison.tensorComparison R Z).symm b.derived ≪≫
      Functor.isoWhiskerLeft B p.symm ≪≫
      Functor.isoWhiskerRight it ES ≪≫
      Functor.isoWhiskerLeft (T.prod T) (ModuleRingedComparison.tensorComparison S Z) ≪≫
      Functor.isoWhiskerRight (NatIso.prod p p) (ModuleRingedComparison.tensor S Z)
  let eprod := (ModuleRingedComparison.derivedEquivalence R Z).prod
    (ModuleRingedComparison.derivedEquivalence R Z)
  obtain ⟨t, ht⟩ := descend_iso eprod
    (ModuleRingedComparison.tensor R Z ⋙ b.derived)
    (b.derived.prod b.derived ⋙ ModuleRingedComparison.tensor S Z) k
  refine ⟨t, ?_⟩
  intro M N
  unfold internalScalarTensorComparison
  have h := ht (M, N)
  change t.hom.app (ER.obj M, ER.obj N) = k.hom.app (M, N) at h
  rw [h]
  dsimp only [k, it, uncurry_comparison, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact (cancel_pair b.derived ((ModuleRingedComparison.tensorComparison R Z).app (M, N))
    (p.app (((derivedTensor R Z).obj M).obj N)) _).symm

/-- Scalar extension, its adjunction and its tensorator realize the normalized section
operations, including the signed flat-term K-flat representative square.

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL; Cohomology on Sites,
Tags 06YY, 07A4 and 07A6; steps 1--3 of
`lem-sfb-coefficient-scalar-tensor-realization`.
(blueprint: lem-sfb-coefficient-scalar-section-realization).

Proof: apply internal_section_scalar_adjunction to the actual coefficient map.
Its ordinary generator and Hom formulas give the recorded extension and restriction
isomorphisms. Compare its universal internal derived functor with
internalScalarExtension by uniqueness of left adjoints. The exact computation
counit is leftDerivedFunctorIsoMapDerivedCategory followed by mapDerivedCategoryFactors.
The normalization of the unit identifies the transported adjunction with
Mod.derivedExtendMapDerivedCategoryAdjunction, and naturality transports the Hom formula.
Construct the section scalar monoidal structure from scalarExtension_constraint_coherence
on changeOfRings. Transport it through the object equalities of the normalized scalar
pair; on generators its oplax map sends s tensor (x tensor y) to
(s tensor x) tensor (1 tensor y). Transport the fixed internal derived tensor isomorphism
through the product of the section equivalences to obtain t. Its identification equation
is the defining transport square. For representative normalization, precompose both
ordinary comparisons with the balanced tensor coprojection and scalar unit. The internal
normalization and the preceding generator formula give equal maps on every generalized
pure tensor. Totalization applies this equation in each bidegree with the same signs.
Scalar extension preserves the direct sums, so the two total arrows agree. On internal
flat-term K-flat representatives the fixed derived tensorator is the localization of
this arrow. Substitute the scalar and tensor computation comparisons and cancel the
adjacent isomorphisms. Section reconstruction preserves flatness and K-flatness; its
inverse and the equivalence counit transport this equality to every section pair. These
are precisely all clauses of the realization predicate. No boundedness is used. -/
theorem coefficientScalarSectionRealization (Z : Scheme.{u}) :
    CoefficientScalarSectionRealization a Z := by
  obtain ⟨b, r, hr, o, ho, hh, F, ε, _, _, adj, hu, q, hq, p, hp, ha⟩ :=
    InternalAbelianSheafModule.internal_section_scalar_adjunction.{u + 1, u + 1, u, u + 1}
      (Scheme.ProEt.topology Z) (coefficientMap a Z)
  let native := native_adj a Z
  obtain ⟨e, he_compute, he_hom⟩ := adj_comparison native adj
  have he (P : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P =
        coefficientInternalScalarComplex a Z P := by
    apply he_compute
    apply (cancel_mono ((Mod.comap (coefficientMap a Z)).mapDerivedCategoryFactors.hom.app
      (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj P))).mp
    simpa only [Category.assoc] using (hu P).trans (native_unit a Z P).symm
  obtain ⟨p', hp'_hom, hp'_inv⟩ :=
    transport_iso e (ModuleRingedComparison.derivedEquivalence S Z).functor p
  have hgen : ∀ (M : ModuleRingedComparison.internalModules R Z) (V : Z.ProEtᵒᵖ)
      (s : (condensedRingObj S Z).obj.obj V) (x : M.X.obj.obj V),
      (o.hom.app M).val.app V
        (InternalAbelianSheafModule.internalScalarGenerator.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Z) (coefficientMap a Z) M V s x) =
      coefficientSectionScalarPure a Z b
        ((ModuleRingedComparison.equivalence R Z).functor.obj M) V s x := by
    intro M V s x
    unfold coefficientSectionScalarPure
    exact cast_section_eq (b.extension_obj _) V _ _ (ho M V s x)
  have hrep : ∀ (P : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z)
        (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
          (.up ℤ)).obj P) →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z)
        ((ModuleRingedComparison.equivalence R Z).functor.obj (P.X n))) →
      (ModuleRingedComparison.derivedEquivalence S Z).functor.map
          (coefficientInternalScalarComplex a Z P) ≫
        (ModuleRingedComparison.equivalence S Z).functor.mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) =
      p'.hom.app (DerivedCategory.Q.obj P) ≫
        b.derived.map
          ((ModuleRingedComparison.equivalence R Z).functor.mapDerivedCategoryFactors.hom.app P) ≫
        SheafOfModules.scalarPairComplexComparison
          (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
          (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
          b.extension b.extension_additive b.derived b.counit
          (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
            (.up ℤ)).obj P) := by
    intro P hP hflat
    have h := map_computation
      (ModuleRingedComparison.derivedEquivalence S Z).functor
      (e.hom.app (DerivedCategory.Q.obj P)) (ε.app P)
      (coefficientInternalScalarComplex a Z P) (he P) _ _ _ (hp P hP hflat)
    simpa only [hp'_hom, Category.assoc] using h
  obtain ⟨m, hm⟩ := ordinary_monoidal a Z b
  obtain ⟨t, ht⟩ := tensor_transport a Z b p'
  refine ⟨b, o, r, hgen, hr, hh, p', q, hq, hrep, ?_, m, hm, t, ?_, ht⟩
  · exact transport_hom native adj b.adjunction
      (ModuleRingedComparison.derivedEquivalence R Z).functor
      (ModuleRingedComparison.derivedEquivalence S Z).functor e p p' q
      he_hom hp'_inv ha
  · exact coefficientScalarTensorRepresentative a Z b o p' m t hgen hrep hm ht

end AlgebraicGeometry.ProEtale.CondensedRing
