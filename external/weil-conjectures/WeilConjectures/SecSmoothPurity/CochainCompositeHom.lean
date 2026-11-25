/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all WeilConjectures.SecSmoothPurity.CochainInverseComparison
import all WeilConjectures.SecSmoothPurity.CochainModuleAdjunction
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
/-! # Normalized scalar-extension comparison for a composite

Source: Stacks Project, Modules on Sites, Tags 03EL and 0D6D.
(auxiliary; not a blueprint node).

The comparison is recovered from the two explicit Hom adjunctions. Its value on
scalar-insertion generators determines it and gives its naturality.
-/

@[expose] public section
universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings TensorProduct
namespace CategoryTheory.CochainCompositeHom
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
/-- Module sheaves, using Mathlib's category verbatim.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
private abbrev Modules {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- Underlying sheaves of sets of module sheaves.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
private noncomputable abbrev underlying {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) : Modules R ⥤ Sheaf J (Type w) :=
  SheafOfModules.toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

private structure RingedPullback (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w}) where
  uInv : Sheaf J (Type w) ⥤ Sheaf K (Type w)
  uPush : Sheaf K (Type w) ⥤ Sheaf J (Type w)
  adj : uInv ⊣ uPush
  finiteLimits : PreservesFiniteLimits uInv
  RI : Sheaf K CommRingCat.{w}
  I : SheafOfModules.AlgebraicInverseImage uInv R RI
  coefficient : RI ⟶ S
  L : Modules R ⥤ Modules S
  hobj : ∀ M, L.obj M = SheafOfModules.changeOfRings coefficient (I.modules.obj M)
  hmap : ∀ {M N} (f : M ⟶ N), L.map f = eqToHom (hobj M) ≫
    SheafOfModules.changeOfRingsHom coefficient (I.modules.obj M) (I.modules.map f) ≫
      eqToHom (hobj N).symm

variable {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
private noncomputable abbrev extensionFunctor {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  SheafOfModules.CochainScalarConstruction.tensorFunctor a
private noncomputable abbrev restrictionFunctor {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  SheafOfModules.CochainScalarConstruction.restriction a
private noncomputable abbrev extensionAdjunction {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  SheafOfModules.CochainScalarConstruction.tensorAdjunction a
private noncomputable abbrev insertion {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M : Modules A) := SheafOfModules.CochainScalarConstruction.tensorUnit a M
private structure Comparison (f : RingedPullback R S) where
  q : ∀ M : Modules R, (underlying f.RI).obj (f.I.modules.obj M) ⟶
    (underlying S).obj (f.L.obj M)
  q_one : ∀ (M : Modules R) (U : Dᵒᵖ) (x : (f.I.modules.obj M).val.obj U),
    (q M).hom.app U x = (eqToHom (f.hobj M).symm).val.app U
      ((insertion f.coefficient (f.I.modules.obj M)).hom.app U x)
set_option backward.isDefEq.respectTransparency false
private noncomputable def generator (f : RingedPullback R S) (k : Comparison f)
    {M : Modules R} {Z : Sheaf J (Type w)} (x : Z ⟶ (underlying R).obj M) :
    f.uInv.obj Z ⟶ (underlying S).obj (f.L.obj M) :=
  f.uInv.map x ≫ f.I.moduleUnderlying.inv.app M ≫ k.q M

private theorem insertion_naturality {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {M N : Modules A} (b : M ⟶ N) :
    (underlying A).map b ≫ insertion a N =
      insertion a M ≫ (underlying B).map ((extensionFunctor a).map b) := by
  ext U x
  exact congrArg (fun z ↦ z.val.app U x) ((extensionAdjunction a).unit.naturality b)

private noncomputable def presentationIso (f : RingedPullback R S) :
    f.L ≅ f.I.modules ⋙ extensionFunctor f.coefficient :=
  NatIso.ofComponents (fun M ↦ eqToIso (f.hobj M)) (by
    intro M N b
    change f.L.map b ≫ eqToHom (f.hobj N) =
      eqToHom (f.hobj M) ≫
        SheafOfModules.changeOfRingsHom f.coefficient _ (f.I.modules.map b)
    rw [f.hmap]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

private theorem q_eq (f : RingedPullback R S) (k : Comparison f) (M : Modules R) :
    k.q M = insertion f.coefficient (f.I.modules.obj M) ≫
      (underlying S).map ((presentationIso f).inv.app M)  := by
  ext U x
  exact k.q_one M U x

private theorem q_naturality (f : RingedPullback R S) (k : Comparison f)
    {M N : Modules R} (b : M ⟶ N) :
    (underlying f.RI).map (f.I.modules.map b) ≫ k.q N =
      k.q M ≫ (underlying S).map (f.L.map b) := by
  have h := (presentationIso f).inv.naturality b
  change (extensionFunctor f.coefficient).map (f.I.modules.map b) ≫
    (presentationIso f).inv.app N = (presentationIso f).inv.app M ≫ f.L.map b at h
  rw [q_eq f k M, q_eq f k N, ← Category.assoc,
    insertion_naturality, Category.assoc, ← Functor.map_comp,
    h, Functor.map_comp, Category.assoc]

private theorem generator_naturality (f : RingedPullback R S) (k : Comparison f)
    {M N : Modules R} (b : M ⟶ N) {Z : Sheaf J (Type w)}
    (x : Z ⟶ (underlying R).obj M) :
    generator f k (x ≫ (underlying R).map b) =
      generator f k x ≫ (underlying S).map (f.L.map b) := by
  have h := f.I.moduleUnderlying.inv.naturality b
  change f.uInv.map ((underlying R).map b) ≫ f.I.moduleUnderlying.inv.app N =
    f.I.moduleUnderlying.inv.app M ≫ (underlying f.RI).map (f.I.modules.map b) at h
  simp only [generator, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (f.uInv.map ((underlying R).map b)), h]
  simp only [Category.assoc]
  rw [q_naturality]

private theorem generator_precomp (f : RingedPullback R S) (k : Comparison f)
    {M : Modules R} {Z Z' : Sheaf J (Type w)}
    (x : Z ⟶ (underlying R).obj M) (z : Z' ⟶ Z) :
    generator f k (z ≫ x) = f.uInv.map z ≫ generator f k x := by
  simp only [generator, Functor.map_comp, Category.assoc]

open SheafOfModules SheafOfModules.GeometricConstruction

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private noncomputable abbrev moduleAddMap
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) (M : Modules R) :=
  fromProd ((underlying R).obj M) ((underlying R).obj M) ≫ addition R M

private noncomputable abbrev moduleSMulMap
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) (M : Modules R) :=
  fromProd (rset R) ((underlying R).obj M) ≫ action R M

private theorem binary_of_graph
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {X Y Z : Sheaf J (Type w)} {A B E : Sheaf K (Type w)}
    (dX : F.obj X ⟶ A) (dY : F.obj Y ⟶ B) (dZ : F.obj Z ⟶ E)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ V, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ V p, b.hom.app V p =
      op' V ((prod.fst : A ⨯ B ⟶ A).hom.app V p)
        ((prod.snd : A ⨯ B ⟶ B).hom.app V p))
    (hgraph : ∀ (T : Sheaf J (Type w)) (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z),
      (∀ U p, z.hom.app U p = op U (x.hom.app U p) (y.hom.app U p)) →
      ∀ V p, (F.map z ≫ dZ).hom.app V p =
        op' V ((F.map x ≫ dX).hom.app V p) ((F.map y ≫ dY).hom.app V p)) :
    F.map a ≫ dZ = prodComparison F X Y ≫ prod.map dX dY ≫ b := by
  have h₁ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.fst =
      F.map prod.fst ≫ dX := by simp only [prod.map_fst, prodComparison_fst_assoc]
  have h₂ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.snd =
      F.map prod.snd ≫ dY := by simp only [prod.map_snd, prodComparison_snd_assoc]
  ext V p
  have h := hgraph (X ⨯ Y) prod.fst prod.snd a hs V p
  change (F.map a ≫ dZ).hom.app V p = b.hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p)
  rw [ht]
  have hh₁ := congrArg (fun k ↦ k.hom.app V p) h₁
  have hh₂ := congrArg (fun k ↦ k.hom.app V p) h₂
  change (prod.fst : A ⨯ B ⟶ A).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₁
  change (prod.snd : A ⨯ B ⟶ B).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₂
  rw [hh₁, hh₂]
  exact h

private noncomputable abbrev structureMap (f : RingedPullback R S) :=
  f.I.ringUnderlying.hom ≫
    (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map f.coefficient

private noncomputable instance pushPreservesLimits (f : RingedPullback R S) :
    PreservesLimits f.uPush := f.adj.rightAdjoint_preservesLimits

private theorem linearMate_exists (f : RingedPullback R S)
    (H : Modules S) (P : Modules R)
    (e : (underlying R).obj P ≅ f.uPush.obj ((underlying S).obj H))
    (ha : moduleAddMap R P ≫ e.hom = prod.map e.hom e.hom ≫
      inv (prodComparison f.uPush ((underlying S).obj H) ((underlying S).obj H)) ≫
        f.uPush.map (moduleAddMap S H))
    (hs : moduleSMulMap R P ≫ e.hom =
      prod.map (f.adj.homEquiv _ _ (structureMap f)) e.hom ≫
        inv (prodComparison f.uPush (rset S) ((underlying S).obj H)) ≫
          f.uPush.map (moduleSMulMap S H)) (M : Modules R) :
    ∃ E : (f.I.modules.obj M ⟶ (restrictionFunctor f.coefficient).obj H) ≃ (M ⟶ P),
      ∀ a, (underlying R).map (E a) ≫ e.hom =
        f.adj.homEquiv _ _
          (f.I.moduleUnderlying.inv.app M ≫ (underlying f.RI).map a) := by
  let _ : PreservesFiniteLimits f.uInv := f.finiteLimits
  let _ : PreservesLimits f.uPush := f.adj.rightAdjoint_preservesLimits
  let eR := f.I.ringUnderlying.symm
  let eI := f.I.moduleUnderlying.app M
  let E := mateIsoEquiv f.adj eI e
  have hLA : f.uInv.map (moduleAddMap R M) =
      prodComparison f.uInv ((underlying R).obj M) ((underlying R).obj M) ≫
        prod.map eI.inv eI.inv ≫ moduleAddMap f.RI (f.I.modules.obj M) ≫ eI.hom := by
    apply (cancel_mono eI.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact binary_of_graph f.uInv eI.inv eI.inv eI.inv
      (moduleAddMap R M) (moduleAddMap f.RI (f.I.modules.obj M))
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add ((f.I.modules.obj M).val.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ f.I.moduleAdd M T x y z hz U t)
  have hLS : f.uInv.map (moduleSMulMap R M) =
      prodComparison f.uInv (rset R) ((underlying R).obj M) ≫
        prod.map eR.inv eI.inv ≫ moduleSMulMap f.RI (f.I.modules.obj M) ≫ eI.hom := by
    apply (cancel_mono eI.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact binary_of_graph f.uInv eR.inv eI.inv eI.inv
      (moduleSMulMap R M) (moduleSMulMap f.RI (f.I.modules.obj M))
      (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @SMul.smul (f.RI.obj.obj U)
        ((f.I.modules.obj M).val.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T a x z hz U t ↦ f.I.moduleSMul M T a x z hz U t)
  have hImage (α : (underlying f.RI).obj (f.I.modules.obj M) ⟶ (underlying S).obj H) :
      (∃ a : f.I.modules.obj M ⟶ (restrictionFunctor f.coefficient).obj H,
        (underlying f.RI).map a = α) ↔
      ∃ b : M ⟶ P, (underlying R).map b = E α := by
    have hm := mateIsoEquiv_equation f.adj eI e α
    have hAdd := binary_mate_iso_iff f.adj eI eI eI e.hom e.hom e
      (moduleAddMap R M) (moduleAddMap f.RI (f.I.modules.obj M))
      (moduleAddMap S H) (moduleAddMap R P) hLA ha
      α α α (E α) (E α) (E α) hm hm hm
    have hSmul := binary_mate_iso_iff f.adj eR eI eI
      (f.adj.homEquiv _ _ (structureMap f)) e.hom e
      (moduleSMulMap R M) (moduleSMulMap f.RI (f.I.modules.obj M))
      (moduleSMulMap S H) (moduleSMulMap R P) hLS hs
      ((sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map f.coefficient) α α
      (𝟙 (rset R)) (E α) (E α) (by exact (Category.id_comp _).symm) hm hm
    exact (linear_iff f.coefficient (f.I.modules.obj M) H
      (moduleAddMap f.RI _) (moduleAddMap S _) (moduleSMulMap f.RI _)
      (moduleSMulMap S _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) α).trans
      ((and_congr hAdd hSmul).trans
        (linear_iff (𝟙 R) M P (moduleAddMap R _) (moduleAddMap R _)
          (moduleSMulMap R _) (moduleSMulMap R _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
          (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (E α)).symm)
  refine ⟨restrictHomEquiv (underlying f.RI) (underlying R) E hImage, ?_⟩
  intro a
  rw [restrictHomEquiv_map]
  exact (mateIsoEquiv_equation f.adj eI e _).symm

private theorem directModule_exists (f : RingedPullback R S) (H : Modules S) :
    ∃ (P : Modules R) (e : (underlying R).obj P ≅ f.uPush.obj ((underlying S).obj H)),
      moduleAddMap R P ≫ e.hom = prod.map e.hom e.hom ≫
        inv (prodComparison f.uPush ((underlying S).obj H) ((underlying S).obj H)) ≫
          f.uPush.map (moduleAddMap S H) ∧
      moduleSMulMap R P ≫ e.hom =
        prod.map (f.adj.homEquiv _ _ (structureMap f)) e.hom ≫
          inv (prodComparison f.uPush (rset S) ((underlying S).obj H)) ≫
            f.uPush.map (moduleSMulMap S H) := by
  let _ : PreservesFiniteLimits f.uInv := f.finiteLimits
  let _ : PreservesLimits f.uPush := f.adj.rightAdjoint_preservesLimits
  let _ : f.uInv.Braided := Functor.Braided.ofChosenFiniteProducts f.uInv
  let _ : f.uPush.Braided := Functor.Braided.ofChosenFiniteProducts f.uPush
  let d := f.adj.homEquiv (rset R) (rset S) (structureMap f)
  have hb (a : rset R ⊗ rset R ⟶ rset R) (b : rset S ⊗ rset S ⟶ rset S)
      (h : f.uInv.map a ≫ structureMap f =
        CartesianMonoidalCategory.prodComparison f.uInv _ _ ≫
          (structureMap f ⊗ₘ structureMap f) ≫ b) :
      a ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ f.uPush _ _ ≫ f.uPush.map b :=
    adjunct_binary f.uInv f.uPush f.adj _ _ a b (structureMap f) h
  have ha : ringAdd R ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ f.uPush _ _ ≫
      f.uPush.map (ringAdd S) := by
    apply hb
    ext U t
    have h := f.I.ringAdd (rset R ⊗ rset R)
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (ringAdd R) (fun _ _ ↦ rfl) U t
    exact (congrArg (f.coefficient.hom.app U).hom h).trans
      ((f.coefficient.hom.app U).hom.map_add _ _)
  have hm : letI := ringMonoid S
            letI := ringMonoid R
            letI := f.uPush.monObjObj (rset S)
            IsMonHom d := by
    let := ringMonoid S
    let := ringMonoid R
    let := f.uPush.monObjObj (rset S)
    refine ⟨?_, ?_⟩
    · apply adjunct_constant f.uInv f.uPush f.adj _ _ (ringOne R) (ringOne S)
        (structureMap f)
      ext U t
      have h := f.I.ringOne (𝟙_ (Sheaf J (Type w))) (ringOne R) (fun _ _ ↦ rfl) U t
      exact (congrArg (f.coefficient.hom.app U).hom h).trans
        (f.coefficient.hom.app U).hom.map_one
    · apply hb
      ext U t
      have h := f.I.ringMul (rset R ⊗ rset R)
        (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
        (ringMul R) (fun _ _ ↦ rfl) U t
      exact (congrArg (f.coefficient.hom.app U).hom h).trans
        ((f.coefficient.hom.app U).hom.map_mul _ _)
  let P := imageModule f.uPush S R d ha hm H
  refine ⟨P, Iso.refl _, ?_, ?_⟩
  · have h := imageModule_addition_comparison f.uPush S R d ha hm H
    apply (cancel_epi (prodComparison f.uPush _ _)).mp
    dsimp only [P, moduleAddMap, Iso.refl_hom]
    simp only [Category.comp_id, prod.map_id_id, Category.id_comp,
      IsIso.hom_inv_id_assoc]
    exact h.symm
  · exact imageModule_action_comparison_right f.uPush S R d ha hm H

private theorem extensionHomEquiv_formula {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (M : Modules A) (H : Modules B)
    (b : (extensionFunctor a).obj M ⟶ H) :
    (underlying A).map ((extensionAdjunction a).homEquiv M H b) =
      insertion a M ≫ (underlying B).map b := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem pullHomEquiv_exists (f : RingedPullback R S) (k : Comparison f)
    (H : Modules S) (P : Modules R)
    (e : (underlying R).obj P ≅ f.uPush.obj ((underlying S).obj H))
    (ha : moduleAddMap R P ≫ e.hom = prod.map e.hom e.hom ≫
      inv (prodComparison f.uPush ((underlying S).obj H) ((underlying S).obj H)) ≫
        f.uPush.map (moduleAddMap S H))
    (hs : moduleSMulMap R P ≫ e.hom =
      prod.map (f.adj.homEquiv _ _ (structureMap f)) e.hom ≫
        inv (prodComparison f.uPush (rset S) ((underlying S).obj H)) ≫
          f.uPush.map (moduleSMulMap S H)) (M : Modules R) :
    ∃ E : (f.L.obj M ⟶ H) ≃ (M ⟶ P),
      ∀ b, (underlying R).map (E b) ≫ e.hom =
        f.adj.homEquiv _ _ (generator f k (𝟙 ((underlying R).obj M)) ≫
          (underlying S).map b) := by
  obtain ⟨E, hE⟩ := linearMate_exists f H P e ha hs M
  let T := ((presentationIso f).app M).homCongr (Iso.refl H)
  refine ⟨(T.trans ((extensionAdjunction f.coefficient).homEquiv _ _)).trans E, ?_⟩
  intro b
  rw [Equiv.trans_apply, Equiv.trans_apply, hE]
  congr 1
  erw [extensionHomEquiv_formula]
  change f.I.moduleUnderlying.inv.app M ≫
      (insertion f.coefficient (f.I.modules.obj M) ≫
        (underlying S).map ((presentationIso f).inv.app M ≫ b)) = _
  rw [Functor.map_comp, ← Category.assoc (insertion _ _), ← q_eq f k M]
  simp only [generator, Functor.map_id, Category.id_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency true in
private theorem transport_binary_comp
    {A : Type uC} [Category.{vC} A] [HasBinaryProducts A]
    {B : Type uD} [Category.{vD} B] [HasBinaryProducts B]
    {E : Type uE} [Category.{vE} E] [HasBinaryProducts E]
    (V : B ⥤ A) (W : E ⥤ B)
    [PreservesFiniteLimits V] [PreservesFiniteLimits W]
    {X Y Z : A} {X' Y' Z' : B} {X'' Y'' Z'' : E}
    (a : X ⨯ Y ⟶ Z) (b : X' ⨯ Y' ⟶ Z') (c : X'' ⨯ Y'' ⟶ Z'')
    (x : X ⟶ V.obj X') (y : Y ⟶ V.obj Y') (z : Z ⟶ V.obj Z')
    (x' : X' ⟶ W.obj X'') (y' : Y' ⟶ W.obj Y'') (z' : Z' ⟶ W.obj Z'')
    (ha : a ≫ z = prod.map x y ≫ inv (prodComparison V X' Y') ≫ V.map b)
    (hb : b ≫ z' = prod.map x' y' ≫ inv (prodComparison W X'' Y'') ≫ W.map c) :
    a ≫ (z ≫ V.map z') =
      prod.map (x ≫ V.map x') (y ≫ V.map y') ≫
        inv (prodComparison (W ⋙ V) X'' Y'') ≫ (W ⋙ V).map c := by
  rw [← Category.assoc, ha]
  simp only [Category.assoc]
  rw [← V.map_comp, hb]
  simp only [Functor.map_comp]
  rw [← Category.assoc (inv (prodComparison V X' Y')),
    prodComparison_inv_natural]
  simp only [Category.assoc]
  rw [← Category.assoc (prod.map x y), prod.map_map]
  have hi : inv (prodComparison (W ⋙ V) X'' Y'') =
      inv (prodComparison V (W.obj X'') (W.obj Y'')) ≫
        V.map (inv (prodComparison W X'' Y'')) := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [prodComparison_comp]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← V.map_comp,
      IsIso.hom_inv_id, Functor.map_id, Functor.comp_obj]
  rw [hi]
  simp only [Functor.comp_map, Category.assoc]

variable {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {H : GrothendieckTopology E}
  [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {T : Sheaf H CommRingCat.{w}}

set_option backward.isDefEq.respectTransparency true in
private theorem composite_directModule (f : RingedPullback R S) (g : RingedPullback S T)
    (N : Modules T) (Q : Modules S) (P : Modules R)
    (eg : (underlying S).obj Q ≅ g.uPush.obj ((underlying T).obj N))
    (ef : (underlying R).obj P ≅ f.uPush.obj ((underlying S).obj Q))
    (hag : moduleAddMap S Q ≫ eg.hom = prod.map eg.hom eg.hom ≫
      inv (prodComparison g.uPush _ _) ≫ g.uPush.map (moduleAddMap T N))
    (hsg : moduleSMulMap S Q ≫ eg.hom =
      prod.map (g.adj.homEquiv _ _ (structureMap g)) eg.hom ≫
        inv (prodComparison g.uPush _ _) ≫ g.uPush.map (moduleSMulMap T N))
    (haf : moduleAddMap R P ≫ ef.hom = prod.map ef.hom ef.hom ≫
      inv (prodComparison f.uPush _ _) ≫ f.uPush.map (moduleAddMap S Q))
    (hsf : moduleSMulMap R P ≫ ef.hom =
      prod.map (f.adj.homEquiv _ _ (structureMap f)) ef.hom ≫
        inv (prodComparison f.uPush _ _) ≫ f.uPush.map (moduleSMulMap S Q)) :
    let e := ef ≪≫ f.uPush.mapIso eg
    moduleAddMap R P ≫ e.hom = prod.map e.hom e.hom ≫
      inv (prodComparison (g.uPush ⋙ f.uPush) _ _) ≫
        (g.uPush ⋙ f.uPush).map (moduleAddMap T N) ∧
    moduleSMulMap R P ≫ e.hom =
      prod.map ((f.adj.comp g.adj).homEquiv _ _
        (g.uInv.map (structureMap f) ≫ structureMap g)) e.hom ≫
        inv (prodComparison (g.uPush ⋙ f.uPush) _ _) ≫
          (g.uPush ⋙ f.uPush).map (moduleSMulMap T N) := by
  let _ : PreservesLimits f.uPush := f.adj.rightAdjoint_preservesLimits
  let _ : PreservesLimits g.uPush := g.adj.rightAdjoint_preservesLimits
  constructor
  · exact transport_binary_comp f.uPush g.uPush _ _ _ _ _ _ _ _ _ haf hag
  · have hd : (f.adj.comp g.adj).homEquiv _ _
        (g.uInv.map (structureMap f) ≫ structureMap g) =
        f.adj.homEquiv _ _ (structureMap f) ≫
          f.uPush.map (g.adj.homEquiv _ _ (structureMap g)) := by
      rw [Adjunction.comp_homEquiv]
      change f.adj.homEquiv _ _ (g.adj.homEquiv _ _ _) = _
      rw [g.adj.homEquiv_naturality_left, f.adj.homEquiv_naturality_right]
    rw [hd]
    exact transport_binary_comp f.uPush g.uPush _ _ _ _ _ _ _ _ _ hsf hsg

private noncomputable abbrev compositeLift (f : RingedPullback R S) (g : RingedPullback S T)
    (RI : Sheaf H CommRingCat.{w})
    (I : AlgebraicInverseImage (f.uInv ⋙ g.uInv) R RI) (c : RI ⟶ T)
    (L : Modules R ⥤ Modules T)
    (hobj : ∀ M, L.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N} (b : M ⟶ N), L.map b = eqToHom (hobj M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map b) ≫ eqToHom (hobj N).symm) :
    RingedPullback R T where
  uInv := f.uInv ⋙ g.uInv
  uPush := g.uPush ⋙ f.uPush
  adj := f.adj.comp g.adj
  finiteLimits := by
    let _ := f.finiteLimits
    let _ := g.finiteLimits
    exact comp_preservesFiniteLimits f.uInv g.uInv
  RI := RI
  I := I
  coefficient := c
  L := L
  hobj := hobj
  hmap := hmap

private noncomputable def twoGenerator (f : RingedPullback R S) (g : RingedPullback S T)
    (kf : Comparison f) (kg : Comparison g) {M : Modules R}
    {Z : Sheaf J (Type w)} (x : Z ⟶ (underlying R).obj M) :=
  generator g kg (generator f kf x)

private theorem compositeHomEquiv_exists (f : RingedPullback R S)
    (g : RingedPullback S T) (kf : Comparison f) (kg : Comparison g)
    (RI : Sheaf H CommRingCat.{w})
    (I : AlgebraicInverseImage (f.uInv ⋙ g.uInv) R RI) (c : RI ⟶ T)
    (L : Modules R ⥤ Modules T)
    (hobj : ∀ M, L.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N} (b : M ⟶ N), L.map b = eqToHom (hobj M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map b) ≫ eqToHom (hobj N).symm)
    (kh : Comparison (compositeLift f g RI I c L hobj hmap))
    (hφ : I.ringUnderlying.hom ≫
      (sheafCompose H (CategoryTheory.forget CommRingCat.{w})).map c =
        g.uInv.map (structureMap f) ≫ structureMap g)
    (M : Modules R) (N : Modules T) :
    ∃ E : (L.obj M ⟶ N) ≃ (g.L.obj (f.L.obj M) ⟶ N),
      ∀ b d, E b = d ↔
        generator (compositeLift f g RI I c L hobj hmap) kh (𝟙 _) ≫
          (underlying T).map b = twoGenerator f g kf kg (𝟙 _) ≫ (underlying T).map d := by
  let h := compositeLift f g RI I c L hobj hmap
  obtain ⟨Q, eg, hag, hsg⟩ := directModule_exists g N
  obtain ⟨P, ef, haf, hsf⟩ := directModule_exists f Q
  let e := ef ≪≫ f.uPush.mapIso eg
  obtain ⟨ha, hs⟩ := composite_directModule f g N Q P eg ef hag hsg haf hsf
  have hh : structureMap h = g.uInv.map (structureMap f) ≫ structureMap g := hφ
  have hs' : moduleSMulMap R P ≫ e.hom =
      prod.map (h.adj.homEquiv _ _ (structureMap h)) e.hom ≫
        inv (prodComparison h.uPush _ _) ≫ h.uPush.map (moduleSMulMap T N) := by
    rw [hh]
    exact hs
  obtain ⟨Eh, hEh⟩ := pullHomEquiv_exists h kh N P e ha hs' M
  obtain ⟨Eg, hEg⟩ := pullHomEquiv_exists g kg N Q eg hag hsg (f.L.obj M)
  obtain ⟨Ef, hEf⟩ := pullHomEquiv_exists f kf Q P ef haf hsf M
  let Efg := Eg.trans Ef
  have hEfg (d : g.L.obj (f.L.obj M) ⟶ N) :
      (underlying R).map (Efg d) ≫ e.hom =
        h.adj.homEquiv _ _ (twoGenerator f g kf kg (𝟙 _) ≫ (underlying T).map d) := by
    change (underlying R).map (Ef (Eg d)) ≫ ef.hom ≫ f.uPush.map eg.hom = _
    rw [← Category.assoc, hEf, ← f.adj.homEquiv_naturality_right,
      Category.assoc, hEg, ← g.adj.homEquiv_naturality_left]
    rw [Adjunction.comp_homEquiv]
    dsimp only [Equiv.trans, Equiv.coe_fn_mk]
    simp only [twoGenerator, generator, Functor.map_id, Category.id_comp,
      Category.assoc]
    rfl
  refine ⟨Eh.trans Efg.symm, ?_⟩
  intro b d
  change Efg.symm (Eh b) = d ↔ _
  rw [Equiv.symm_apply_eq]
  constructor
  · intro hd
    apply h.adj.homEquiv _ _ |>.injective
    rw [← hEh, ← hEfg, hd]
  · intro hd
    apply (underlying R).map_injective
    apply (cancel_mono e.hom).mp
    rw [hEh, hEfg, hd]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 40000 in
-- Keep generic functor elaboration from unfolding the module constructions.
private theorem isoOfGenerators
    {A : Type uC} [Category.{vC} A] {B : Type uD} [Category.{vD} B]
    {D' : Type uE} [Category.{vE} D'] (U : B ⥤ D')
    (L P : A ⥤ B) (Q : A ⥤ D') (i : Q ⟶ L ⋙ U) (j : Q ⟶ P ⋙ U)
    (E : ∀ M N, (L.obj M ⟶ N) ≃ (P.obj M ⟶ N))
    (hE : ∀ M N b d, E M N b = d ↔ i.app M ≫ U.map b = j.app M ≫ U.map d) :
    ∃ a : L ≅ P, ∀ M, i.app M ≫ U.map (a.hom.app M) = j.app M := by
  classical
  have hi (M : A) (N : B) (b d : L.obj M ⟶ N)
      (hb : i.app M ≫ U.map b = i.app M ≫ U.map d) : b = d := by
    apply (E M N).injective
    apply (hE M N b (E M N d)).mpr
    exact hb.trans ((hE M N d (E M N d)).mp rfl)
  have hj (M : A) (N : B) (b d : P.obj M ⟶ N)
      (hb : j.app M ≫ U.map b = j.app M ≫ U.map d) : b = d := by
    apply (E M N).symm.injective
    apply hi
    exact ((hE M N ((E M N).symm b) b).mp ((E M N).apply_symm_apply b)).trans
      (hb.trans (((hE M N ((E M N).symm d) d).mp
        ((E M N).apply_symm_apply d)).symm))
  let a (M : A) := (E M (P.obj M)).symm (𝟙 _)
  let b (M : A) := E M (L.obj M) (𝟙 _)
  have ha (M : A) : i.app M ≫ U.map (a M) = j.app M := by
    have he := (hE M _ (a M) (𝟙 _)).mp ((E M _).apply_symm_apply (𝟙 _))
    simpa only [Functor.map_id, Functor.comp_obj, Category.comp_id] using he
  have hb (M : A) : j.app M ≫ U.map (b M) = i.app M := by
    have he := (hE M _ (𝟙 _) (b M)).mp rfl
    simpa only [Functor.map_id, Functor.comp_obj, Category.comp_id] using he.symm
  have hab (M : A) : a M ≫ b M = 𝟙 _ := by
    apply hi
    rw [Functor.map_comp, ← Category.assoc, ha, hb, Functor.map_id]
    exact (Category.comp_id _).symm
  have hba (M : A) : b M ≫ a M = 𝟙 _ := by
    apply hj
    rw [Functor.map_comp, ← Category.assoc, hb, ha, Functor.map_id]
    exact (Category.comp_id _).symm
  have hn {M N : A} (m : M ⟶ N) : L.map m ≫ a N = a M ≫ P.map m := by
    apply hi
    simp only [Functor.map_comp, ← Category.assoc]
    have hi := i.naturality m
    have hj := j.naturality m
    change Q.map m ≫ i.app N = i.app M ≫ U.map (L.map m) at hi
    change Q.map m ≫ j.app N = j.app M ≫ U.map (P.map m) at hj
    rw [← hi, Category.assoc, ha, hj, ha]
  exact ⟨NatIso.ofComponents (fun M ↦ ⟨a M, b M, hab M, hba M⟩)
    (fun {M N} m ↦ hn m), ha⟩
set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 40000 in
-- Keep generic functor elaboration from unfolding the module constructions.
private theorem normalizedComposite_exists (f : RingedPullback R S)
    (g : RingedPullback S T) (kf : Comparison f) (kg : Comparison g)
    (RI : Sheaf H CommRingCat.{w})
    (I : AlgebraicInverseImage (f.uInv ⋙ g.uInv) R RI) (c : RI ⟶ T)
    (L : Modules R ⥤ Modules T)
    (hobj : ∀ M, L.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N} (b : M ⟶ N), L.map b = eqToHom (hobj M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map b) ≫ eqToHom (hobj N).symm)
    (kh : Comparison (compositeLift f g RI I c L hobj hmap))
    (hφ : I.ringUnderlying.hom ≫
      (sheafCompose H (CategoryTheory.forget CommRingCat.{w})).map c =
        g.uInv.map (structureMap f) ≫ structureMap g) :
    ∃ a : L ≅ f.L ⋙ g.L, ∀ (M : Modules R) (Z : Sheaf J (Type w))
      (x : Z ⟶ (underlying R).obj M),
      generator (compositeLift f g RI I c L hobj hmap) kh x ≫
        (underlying T).map (a.hom.app M) = twoGenerator f g kf kg x := by
  classical
  let h := compositeLift f g RI I c L hobj hmap
  let Q := underlying R ⋙ f.uInv ⋙ g.uInv
  let i : Q ⟶ L ⋙ underlying T := {
    app M := generator h kh (𝟙 _)
    naturality {M N} m := by
      have h₁ := generator_precomp h kh (𝟙 ((underlying R).obj N)) ((underlying R).map m)
      have h₂ := generator_naturality h kh m (𝟙 ((underlying R).obj M))
      simpa only [Q, h, compositeLift, Functor.comp_map, Functor.comp_obj,
        Category.comp_id, Category.id_comp] using h₁.symm.trans h₂ }
  let j : Q ⟶ (f.L ⋙ g.L) ⋙ underlying T := {
    app M := twoGenerator f g kf kg (𝟙 _)
    naturality {M N} m := by
      have h₁ := generator_precomp f kf (𝟙 ((underlying R).obj N)) ((underlying R).map m)
      have h₂ := generator_naturality f kf m (𝟙 ((underlying R).obj M))
      rw [Category.comp_id] at h₁
      rw [Category.id_comp] at h₂
      have h₃ := generator_precomp g kg (generator f kf (𝟙 ((underlying R).obj N)))
        (f.uInv.map ((underlying R).map m))
      have h₄ := generator_naturality g kg (f.L.map m)
        (generator f kf (𝟙 ((underlying R).obj M)))
      change g.uInv.map (f.uInv.map ((underlying R).map m)) ≫
        generator g kg (generator f kf (𝟙 ((underlying R).obj N))) =
          generator g kg (generator f kf (𝟙 ((underlying R).obj M))) ≫
            (underlying T).map (g.L.map (f.L.map m))
      rw [← h₃, ← h₁, h₂, h₄] }
  choose E hE using fun M N ↦ compositeHomEquiv_exists f g kf kg RI I c L hobj hmap
    kh hφ M N
  obtain ⟨a, ha⟩ := isoOfGenerators (underlying T) L (f.L ⋙ g.L) Q i j E hE
  refine ⟨a, ?_⟩
  intro M Z x
  have he := congrArg (fun z ↦ h.uInv.map x ≫ z) (ha M)
  dsimp only [i, j, h, compositeLift] at he ⊢
  simp only [twoGenerator, generator, Functor.comp_map, Functor.map_comp,
    Functor.comp_obj, Functor.map_id, Category.id_comp,
    Category.assoc] at he ⊢
  exact he

set_option backward.isDefEq.respectTransparency true in
/-- Scalar extension commutes with composition of geometric inverse images,
with the isomorphism fixed on the scalar-insertion generators.
Source: Stacks Project, Modules on Sites, Tags 03EL and 0D6D.
(auxiliary; not a blueprint node).
Proof: transpose linear maps through each underlying adjunction and through
scalar extension. The composed Hom equivalence agrees with that of the composite
on insertion generators, because the direct-image addition and scalar-action
formulas compose. Apply the equivalence and its inverse to identities. Their
composites fix generators, hence are identities; the same calculation proves
naturality and the displayed normalization. -/
theorem normalizedScalarComposition_exists
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (aF : F ⊣ V)
    [PreservesFiniteLimits F]
    (RIf : Sheaf K CommRingCat.{w})
    (If : AlgebraicInverseImage F R RIf) (cf : RIf ⟶ S)
    (Lf : ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{w} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (hof : ∀ M, Lf.obj M = changeOfRings cf (If.modules.obj M))
    (hmf : ∀ {M N} (b : M ⟶ N), Lf.map b = eqToHom (hof M) ≫
      changeOfRingsHom cf (If.modules.obj M) (If.modules.map b) ≫
        eqToHom (hof N).symm)
    (G : Sheaf K (Type w) ⥤ Sheaf H (Type w))
    (W : Sheaf H (Type w) ⥤ Sheaf K (Type w)) (aG : G ⊣ W)
    [PreservesFiniteLimits G]
    (RIg : Sheaf H CommRingCat.{w})
    (Ig : AlgebraicInverseImage G S RIg) (cg : RIg ⟶ T)
    (Lg : ringedSiteModules.{w} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) ⥤
      ringedSiteModules.{w} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj T))
    (hog : ∀ M, Lg.obj M = changeOfRings cg (Ig.modules.obj M))
    (hmg : ∀ {M N} (b : M ⟶ N), Lg.map b = eqToHom (hog M) ≫
      changeOfRingsHom cg (Ig.modules.obj M) (Ig.modules.map b) ≫
        eqToHom (hog N).symm)
    (RIh : Sheaf H CommRingCat.{w})
    (Ih : AlgebraicInverseImage (F ⋙ G) R RIh) (ch : RIh ⟶ T)
    (Lh : ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{w} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj T))
    (hoh : ∀ M, Lh.obj M = changeOfRings ch (Ih.modules.obj M))
    (hmh : ∀ {M N} (b : M ⟶ N), Lh.map b = eqToHom (hoh M) ≫
      changeOfRingsHom ch (Ih.modules.obj M) (Ih.modules.map b) ≫
        eqToHom (hoh N).symm)
    (qf : ∀ M, (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RIf) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).obj (If.modules.obj M) ⟶
      (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).obj (Lf.obj M))
    (hqf : ∀ M (U) (x : (If.modules.obj M).val.obj U),
      (qf M).hom.app U x = (eqToHom (hof M).symm).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
            (changeOfRingsPresheaf cf (If.modules.obj M))).app U
              ((1 : S.obj.obj U) ⊗ₜ[RIf.obj.obj U,(cf.hom.app U).hom] x)))
    (qg : ∀ M, (SheafOfModules.toSheaf ((sheafCompose H (forget₂ CommRingCat RingCat)).obj RIg) ⋙
        sheafCompose H (CategoryTheory.forget AddCommGrpCat.{w})).obj (Ig.modules.obj M) ⟶
      (SheafOfModules.toSheaf ((sheafCompose H (forget₂ CommRingCat RingCat)).obj T) ⋙
        sheafCompose H (CategoryTheory.forget AddCommGrpCat.{w})).obj (Lg.obj M))
    (hqg : ∀ M (U) (x : (Ig.modules.obj M).val.obj U),
      (qg M).hom.app U x = (eqToHom (hog M).symm).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose H (forget₂ CommRingCat RingCat)).obj T).obj)).unit.app
            (changeOfRingsPresheaf cg (Ig.modules.obj M))).app U
              ((1 : T.obj.obj U) ⊗ₜ[RIg.obj.obj U,(cg.hom.app U).hom] x)))
    (qh : ∀ M, (SheafOfModules.toSheaf ((sheafCompose H (forget₂ CommRingCat RingCat)).obj RIh) ⋙
        sheafCompose H (CategoryTheory.forget AddCommGrpCat.{w})).obj (Ih.modules.obj M) ⟶
      (SheafOfModules.toSheaf ((sheafCompose H (forget₂ CommRingCat RingCat)).obj T) ⋙
        sheafCompose H (CategoryTheory.forget AddCommGrpCat.{w})).obj (Lh.obj M))
    (hqh : ∀ M (U) (x : (Ih.modules.obj M).val.obj U),
      (qh M).hom.app U x = (eqToHom (hoh M).symm).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose H (forget₂ CommRingCat RingCat)).obj T).obj)).unit.app
            (changeOfRingsPresheaf ch (Ih.modules.obj M))).app U
              ((1 : T.obj.obj U) ⊗ₜ[RIh.obj.obj U,(ch.hom.app U).hom] x)))
    (hφ : Ih.ringUnderlying.hom ≫
      (sheafCompose H (CategoryTheory.forget CommRingCat.{w})).map ch =
      G.map (If.ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map cf) ≫
        Ig.ringUnderlying.hom ≫
          (sheafCompose H (CategoryTheory.forget CommRingCat.{w})).map cg) :
    ∃ a : Lh ≅ Lf ⋙ Lg, ∀ M (Z : Sheaf J (Type w))
      (x : Z ⟶ (SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj M),
      (F ⋙ G).map x ≫ Ih.moduleUnderlying.inv.app M ≫
        qh M ≫
        (SheafOfModules.toSheaf ((sheafCompose H (forget₂ CommRingCat RingCat)).obj T) ⋙
        sheafCompose H (CategoryTheory.forget AddCommGrpCat.{w})).map (a.hom.app M) =
      G.map (F.map x ≫ If.moduleUnderlying.inv.app M ≫
        qf M) ≫
          Ig.moduleUnderlying.inv.app (Lf.obj M) ≫
            qg (Lf.obj M) := by
  let f : RingedPullback R S := ⟨F, V, aF, inferInstance, RIf, If, cf, Lf, hof, hmf⟩
  let g : RingedPullback S T := ⟨G, W, aG, inferInstance, RIg, Ig, cg, Lg, hog, hmg⟩
  let kf : Comparison f := {
    q := qf
    q_one := by
      intro M U x
      rw [SheafOfModules.CochainScalarConstruction.tensorUnit_apply]
      exact hqf M U x }
  let kg : Comparison g := {
    q := qg
    q_one := by
      intro M U x
      rw [SheafOfModules.CochainScalarConstruction.tensorUnit_apply]
      exact hqg M U x }
  let kh : Comparison (compositeLift f g RIh Ih ch Lh hoh hmh) := {
    q := qh
    q_one := by
      intro M U x
      rw [SheafOfModules.CochainScalarConstruction.tensorUnit_apply]
      exact hqh M U x }
  obtain ⟨a, ha⟩ := normalizedComposite_exists f g kf kg RIh Ih ch Lh hoh hmh kh hφ
  exact ⟨a, ha⟩

end CategoryTheory.CochainCompositeHom
