/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrows

/-! # Signed tensor comparison and coherence on cochain sheaves

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and sites-modules.tex,
Tag 03EL (blueprint: def-pur-cochain-coefficient-arrows).

The tensor, associator, Koszul symmetry and action unitors below are the existing
homological-complex constructions. Coefficient arrows are characterized on
scalar-extension generators, and composition uses the adjunction conjugate.
-/

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
namespace CategoryTheory.CochainPullback
set_option autoImplicit false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

variable {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

/-- The canonical scalar-association map epsilon, with its actual tensor source and target.
Source: Stacks 03EL and 07A4
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def epsilon {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (P Q : Complex A) : (extend a).obj (P ⊗ Q) ≅
      (extend a).obj P ⊗ (extend a).obj Q :=
  comparison (extensionPullback a) (extensionComparison a) P Q

attribute [instance] CoefficientSquare.additive'

/-- Change coefficients while keeping the original inverse-image adjunction.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def changed (f : RingedPullback R S) (d : CoefficientSquare f) :
    RingedPullback d.R' d.S' where
  uInv := f.uInv
  uPush := f.uPush
  adj := f.adj
  finiteLimits := f.finiteLimits
  RI := d.RI'
  I := d.I'
  coefficient := d.coefficient'
  L := d.L'
  hobj := d.hobj'
  hmap := d.hmap'
  V := d.V'
  moduleAdj := d.moduleAdj'

/-- Scalar association is normalized on every generalized inverse-image generator.
Together with S'-linearity and balancing this specifies exactly
`s' ⊗ (x ⊗ r) ↦ (1 ⊗ x) ⊗ s' phi'(r)`.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
def IsScalarAssociation (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d))
    (b : extensionFunctor d.sourceMap ⋙ (changed f d).L ≅
      f.L ⋙ extensionFunctor d.targetMap) : Prop :=
  ∀ (M : Modules R) (Z : Sheaf J (Type w)) (x : Z ⟶ (underlying R).obj M),
    generator (changed f d) k' (x ≫ insertion d.sourceMap M) ≫
        (underlying d.S').map (b.hom.app M) =
      generator f k x ≫ insertion d.targetMap (f.L.obj M)

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
      (underlying S).map ((presentationIso f).inv.app M) := by
  ext U x
  change (k.q M).hom.app U x = _
  rw [k.q_one M U x]
  change _ = (eqToHom (f.hobj M).symm).val.app U
    (((extensionAdjunction f.coefficient).unit.app (f.I.modules.obj M)).val.app U x)
  apply congrArg ((eqToHom (f.hobj M).symm).val.app U)
  exact ((Classical.choose_spec (extensionAdjunction_existsUnique f.coefficient)).1
    (f.I.modules.obj M) U x).symm

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

set_option backward.isDefEq.respectTransparency false
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

/-- Original inverse-image generators detect maps after source coefficient extension.
Source: Stacks Project, Modules on Sites, Tags 03CY and 03EL
(blueprint: def-pur-cochain-coefficient-arrows).
Proof: maps out of sheafified scalar extension are determined by their composites with
its unit. The source extension is generated as an R'-module by those inserted original
sections. Inverse image preserves this generating presentation: it is left adjoint and
preserves finite products, and the algebraic inverse-image graph laws preserve addition
and scalar multiplication. Thus the inverse images of inserted original sections generate
after extending scalars to S'. Equality on every generalized original section therefore
implies equality of module maps. The argument is by universal properties of module
presentations and sheafification and requires neither points nor a nonzero coefficient. -/
private theorem coefficientGenerator_hom_ext {A : Sheaf J CommRingCat.{w}} (a : A ⟶ R)
    (f : RingedPullback R S) (k : Comparison f) (M : Modules A) (H : Modules S)
    (b c : f.L.obj ((extensionFunctor a).obj M) ⟶ H)
    (h : ∀ (Z : Sheaf J (Type w)) (x : Z ⟶ (underlying A).obj M),
      generator f k (x ≫ insertion a M) ≫ (underlying S).map b =
        generator f k (x ≫ insertion a M) ≫ (underlying S).map c) : b = c := by
  obtain ⟨P, e, ha, hs⟩ := directModule_exists f H
  obtain ⟨E, hE⟩ := pullHomEquiv_exists f k H P e ha hs ((extensionFunctor a).obj M)
  apply E.injective
  apply ((extensionAdjunction a).homEquiv M P).injective
  apply (underlying A).map_injective
  apply (cancel_mono e.hom).mp
  rw [extensionHomEquiv_formula, extensionHomEquiv_formula]
  change (insertion a M ≫ (underlying R).map (E b)) ≫ e.hom =
    (insertion a M ≫ (underlying R).map (E c)) ≫ e.hom
  rw [Category.assoc, hE, Category.assoc, hE,
    ← f.adj.homEquiv_naturality_left, ← f.adj.homEquiv_naturality_left]
  congr 1
  have h₀ := h ((underlying A).obj M) (𝟙 _)
  simpa only [generator, Functor.map_comp, Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc] using h₀

private theorem structureMap_square (f : RingedPullback R S) (d : CoefficientSquare f) :
    f.uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map d.sourceMap) ≫
        structureMap (changed f d) =
      structureMap f ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map d.targetMap := by
  change _ ≫ (d.I'.ringUnderlying.hom ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map d.coefficient') = _
  rw [← Category.assoc, d.inverseImageMap_graph, Category.assoc,
    ← Functor.map_comp, d.square, Functor.map_comp]
  rfl

private theorem restricted_directModule (f : RingedPullback R S) (d : CoefficientSquare f)
    (H : Modules d.S') (P : Modules d.R')
    (e : (underlying d.R').obj P ≅ f.uPush.obj ((underlying d.S').obj H))
    (ha : moduleAddMap d.R' P ≫ e.hom = prod.map e.hom e.hom ≫
      inv (prodComparison f.uPush ((underlying d.S').obj H) ((underlying d.S').obj H)) ≫
        f.uPush.map (moduleAddMap d.S' H))
    (hs : moduleSMulMap d.R' P ≫ e.hom =
      prod.map (f.adj.homEquiv _ _ (structureMap (changed f d))) e.hom ≫
        inv (prodComparison f.uPush (rset d.S') ((underlying d.S').obj H)) ≫
          f.uPush.map (moduleSMulMap d.S' H)) :
    moduleAddMap R ((restrictionFunctor d.sourceMap).obj P) ≫ e.hom =
      prod.map e.hom e.hom ≫
        inv (prodComparison f.uPush ((underlying S).obj
          ((restrictionFunctor d.targetMap).obj H)) ((underlying S).obj
          ((restrictionFunctor d.targetMap).obj H))) ≫
          f.uPush.map (moduleAddMap S ((restrictionFunctor d.targetMap).obj H)) ∧
    moduleSMulMap R ((restrictionFunctor d.sourceMap).obj P) ≫ e.hom =
      prod.map (f.adj.homEquiv _ _ (structureMap f)) e.hom ≫
        inv (prodComparison f.uPush (rset S) ((underlying S).obj
          ((restrictionFunctor d.targetMap).obj H))) ≫
          f.uPush.map (moduleSMulMap S ((restrictionFunctor d.targetMap).obj H)) := by
  let _ : PreservesLimits f.uPush := f.adj.rightAdjoint_preservesLimits
  refine ⟨ha, ?_⟩
  let a := (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map d.sourceMap
  let b := (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map d.targetMap
  have hc : a ≫ f.adj.homEquiv _ _ (structureMap (changed f d)) =
      f.adj.homEquiv _ _ (structureMap f) ≫ f.uPush.map b := by
    rw [← f.adj.homEquiv_naturality_left, structureMap_square,
      f.adj.homEquiv_naturality_right]
  have hP : moduleSMulMap R ((restrictionFunctor d.sourceMap).obj P) =
      prod.map a (𝟙 _) ≫ moduleSMulMap d.R' P := by
    have hact : action R ((restrictionFunctor d.sourceMap).obj P) =
        (a ⊗ₘ 𝟙 _) ≫ action d.R' P := by
      ext U t
      rfl
    dsimp only [moduleSMulMap]
    rw [fromProd_map_assoc, hact]
    rfl
  have hH : moduleSMulMap S ((restrictionFunctor d.targetMap).obj H) =
      prod.map b (𝟙 _) ≫ moduleSMulMap d.S' H := by
    have hact : action S ((restrictionFunctor d.targetMap).obj H) =
        (b ⊗ₘ 𝟙 _) ≫ action d.S' H := by
      ext U t
      rfl
    dsimp only [moduleSMulMap]
    rw [fromProd_map_assoc, hact]
    rfl
  rw [hP, Category.assoc, hs, prod.map_map_assoc]
  simp only [Category.id_comp]
  rw [hc]
  have hn := Limits.prodComparison_inv_natural f.uPush b
    (𝟙 ((underlying d.S').obj H))
  rw [Functor.map_id] at hn
  have hh := congrArg (fun t ↦
    prod.map (f.adj.homEquiv _ _ (structureMap f)) e.hom ≫
      t ≫ f.uPush.map (moduleSMulMap d.S' H)) hn
  simp only [← Category.assoc, prod.map_map, Category.comp_id] at hh
  change prod.map
      (f.adj.homEquiv _ _ (structureMap f) ≫ f.uPush.map b) e.hom ≫
        inv (prodComparison f.uPush (rset d.S') ((underlying d.S').obj H)) ≫
          f.uPush.map (moduleSMulMap d.S' H) = _
  calc
    _ = prod.map (f.adj.homEquiv _ _ (structureMap f)) e.hom ≫
        inv (prodComparison f.uPush (rset S) ((underlying d.S').obj H)) ≫
          f.uPush.map (prod.map b (𝟙 _) ≫ moduleSMulMap d.S' H) := by
      simpa only [Functor.map_comp, Category.assoc] using hh.symm
    _ = _ := by
      rw [← hH]
      rfl

private theorem coefficientHomEquiv_exists (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d))
    (M : Modules R) (H : Modules d.S') :
    ∃ E : ((changed f d).L.obj ((extensionFunctor d.sourceMap).obj M) ⟶ H) ≃
        ((extensionFunctor d.targetMap).obj (f.L.obj M) ⟶ H),
      ∀ b, generator (changed f d) k' (insertion d.sourceMap M) ≫
          (underlying d.S').map b =
        generator f k (𝟙 ((underlying R).obj M)) ≫ insertion d.targetMap (f.L.obj M) ≫
          (underlying d.S').map (E b) := by
  obtain ⟨P, e, ha, hs⟩ := directModule_exists (changed f d) H
  obtain ⟨E₁, hE₁⟩ := pullHomEquiv_exists (changed f d) k' H P e ha hs
    ((extensionFunctor d.sourceMap).obj M)
  obtain ⟨ha₀, hs₀⟩ := restricted_directModule f d H P e ha hs
  obtain ⟨E₂, hE₂⟩ := pullHomEquiv_exists f k
    ((restrictionFunctor d.targetMap).obj H) ((restrictionFunctor d.sourceMap).obj P)
    e ha₀ hs₀ M
  let T₁ := E₁.trans ((extensionAdjunction d.sourceMap).homEquiv M P)
  let T₂ := ((extensionAdjunction d.targetMap).homEquiv (f.L.obj M) H).trans E₂
  refine ⟨T₁.trans T₂.symm, ?_⟩
  intro b
  have ht : T₁ b = T₂ ((T₁.trans T₂.symm) b) := (T₂.apply_symm_apply _).symm
  have hh := congrArg (fun z ↦ (underlying R).map z ≫ e.hom) ht
  dsimp only [T₁, T₂, Equiv.trans_apply] at hh
  rw [extensionHomEquiv_formula] at hh
  change (insertion d.sourceMap M ≫ (underlying d.R').map (E₁ b)) ≫ e.hom = _ at hh
  rw [Category.assoc, hE₁] at hh
  change insertion d.sourceMap M ≫ f.adj.homEquiv _ _
      (generator (changed f d) k' (𝟙 _) ≫ (underlying d.S').map b) = _ at hh
  rw [← f.adj.homEquiv_naturality_left, hE₂] at hh
  apply (f.adj.homEquiv _ _).injective
  change f.adj.homEquiv _ _
      (f.uInv.map (insertion d.sourceMap M) ≫
        generator (changed f d) k' (𝟙 _) ≫ (underlying d.S').map b) =
    f.adj.homEquiv _ _
      (generator f k (𝟙 _) ≫ (underlying S).map
        ((extensionAdjunction d.targetMap).homEquiv _ _ ((T₁.trans T₂.symm) b))) at hh
  rw [extensionHomEquiv_formula] at hh
  simp only [generator, changed, Functor.map_id, Category.id_comp, Category.assoc] at hh ⊢
  exact hh

/-- The balanced scalar-association map for one module is invertible.
Source: Stacks Project, Modules on Sites, Tag 03EL
(blueprint: def-pur-cochain-coefficient-arrows).
Proof: inverse image preserves the colimit presentation of a module tensor product.
Apply it to R' tensor_R M, then extend scalars to S'. The coefficient square identifies
both scalar actions of R on S'. The balanced tensor map sends s' tensor (r' tensor m)
to s' times the image of r' tensor (1 tensor m). Its inverse inserts the R' unit.
The balancing relations make both maps well-defined; their composites fix pure tensors.
Sheafification extends these mutually inverse maps. On generalized sections their unit
formula is exactly the displayed equation. This argument includes zero rings and modules;
no flatness or injectivity of any coefficient map is used. -/
private theorem coefficientAssociation_component (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) (M : Modules R) :
    ∃ b : (changed f d).L.obj ((extensionFunctor d.sourceMap).obj M) ≅
      (extensionFunctor d.targetMap).obj (f.L.obj M),
      ∀ (Z : Sheaf J (Type w)) (x : Z ⟶ (underlying R).obj M),
        generator (changed f d) k' (x ≫ insertion d.sourceMap M) ≫
          (underlying d.S').map b.hom =
        generator f k x ≫ insertion d.targetMap (f.L.obj M) := by
  classical
  let X := (changed f d).L.obj ((extensionFunctor d.sourceMap).obj M)
  let Y := (extensionFunctor d.targetMap).obj (f.L.obj M)
  let gx := generator (changed f d) k' (insertion d.sourceMap M)
  let gy := generator f k (𝟙 ((underlying R).obj M)) ≫
    insertion d.targetMap (f.L.obj M)
  have hX {H : Modules d.S'} (a b : X ⟶ H)
      (h : gx ≫ (underlying d.S').map a = gx ≫ (underlying d.S').map b) : a = b := by
    apply coefficientGenerator_hom_ext d.sourceMap (changed f d) k' M
    intro Z x
    rw [generator_precomp (changed f d) k' (insertion d.sourceMap M) x]
    simpa only [gx, changed, Category.assoc] using
      congrArg (fun t ↦ f.uInv.map x ≫ t) h
  choose E hE using coefficientHomEquiv_exists f k d k' M
  have hY {H : Modules d.S'} (a b : Y ⟶ H)
      (h : gy ≫ (underlying d.S').map a = gy ≫ (underlying d.S').map b) : a = b := by
    apply (E H).symm.injective
    apply hX
    rw [hE H, hE H, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h
  let hom : X ⟶ Y := (E Y).symm (𝟙 Y)
  let inv : Y ⟶ X := E X (𝟙 X)
  have hhom : gx ≫ (underlying d.S').map hom = gy := by
    have h := hE Y hom
    change gx ≫ (underlying d.S').map hom = gy ≫
      (underlying d.S').map ((E Y) ((E Y).symm (𝟙 Y))) at h
    rw [Equiv.apply_symm_apply] at h
    exact h.trans (by erw [Functor.map_id, Category.comp_id])
  have hinv : gy ≫ (underlying d.S').map inv = gx := by
    have h := (hE X (𝟙 X)).symm
    change gy ≫ (underlying d.S').map inv = gx ≫ (underlying d.S').map (𝟙 X) at h
    exact h.trans (by erw [Functor.map_id, Category.comp_id])
  let e : X ≅ Y :=
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply hX
        rw [Functor.map_comp, ← Category.assoc, hhom, hinv,
          Functor.map_id, Category.comp_id]
      inv_hom_id := by
        apply hY
        rw [Functor.map_comp, ← Category.assoc, hinv, hhom,
          Functor.map_id, Category.comp_id] }
  refine ⟨e, ?_⟩
  intro Z x
  rw [generator_precomp (changed f d) k' (insertion d.sourceMap M) x]
  change (f.uInv.map x ≫ gx) ≫ (underlying d.S').map hom = _
  rw [Category.assoc, hhom]
  simp only [gy, generator, Functor.map_id, Category.id_comp, Category.assoc]

/-- The compatible coefficient square gives a unique normalized scalar association.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows).
Proof: on generalized pure tensors use the coefficient square to move the R'
scalar across the tensor relation. Multiplication of S' scalars gives the forward
map; insertion of the two units gives its inverse. The bilinear universal property,
then sheafification, extend the maps. The two composites are identities on pure
tensors. Those generators also give naturality and uniqueness. -/
theorem scalarAssociation_existsUnique (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) :
    ∃! b : extensionFunctor d.sourceMap ⋙ (changed f d).L ≅
      f.L ⋙ extensionFunctor d.targetMap, IsScalarAssociation f k d k' b := by
  classical
  let b := fun M ↦ Classical.choose (coefficientAssociation_component f k d k' M)
  have hb (M : Modules R) :=
    Classical.choose_spec (coefficientAssociation_component f k d k' M)
  let e : extensionFunctor d.sourceMap ⋙ (changed f d).L ≅
      f.L ⋙ extensionFunctor d.targetMap := NatIso.ofComponents b (by
    intro M N a
    apply coefficientGenerator_hom_ext d.sourceMap (changed f d) k' M
    intro Z x
    change generator (changed f d) k' (x ≫ insertion d.sourceMap M) ≫
        (underlying d.S').map
          ((changed f d).L.map ((extensionFunctor d.sourceMap).map a) ≫ (b N).hom) =
      generator (changed f d) k' (x ≫ insertion d.sourceMap M) ≫
        (underlying d.S').map
          ((b M).hom ≫ (extensionFunctor d.targetMap).map (f.L.map a))
    simp only [Functor.map_comp, ← Category.assoc]
    rw [← generator_naturality]
    rw [Category.assoc x, ← insertion_naturality]
    rw [← Category.assoc x, hb N, generator_naturality]
    rw [Category.assoc, hb M, insertion_naturality]
    simp only [Category.assoc])
  refine ⟨e, ?_, ?_⟩
  · exact hb
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply coefficientGenerator_hom_ext d.sourceMap (changed f d) k' M
    intro Z x
    exact (he' M Z x).trans (hb M Z x).symm

/-- The unique canonical module scalar-association isomorphism.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def scalarAssociation (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) :=
  Classical.choose (scalarAssociation_existsUnique f k d k')

/-- Kappa is the termwise lift of the normalized scalar-association map.
Source: Stacks 03EL and 07A4
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def kappa (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) (P : Complex R) :
    (pull (changed f d)).obj ((extend d.sourceMap).obj P) ≅
      (extend d.targetMap).obj ((pull f).obj P) :=
  (NatIso.mapHomologicalComplex (scalarAssociation f k d k') (.up ℤ)).app P

/-- Tau is the extension unit followed by the inverse scalar association, with
restriction of scalars making the semilinear map an S-linear map.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def transitionModule (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) :
    f.L ⟶ extensionFunctor d.sourceMap ⋙ (changed f d).L ⋙
      restrictionFunctor d.targetMap :=
  Functor.whiskerLeft f.L (extensionAdjunction d.targetMap).unit ≫
    Functor.whiskerRight (scalarAssociation f k d k').inv (restrictionFunctor d.targetMap)

/-- The canonical transition chain map, rather than an inverse to coefficient change.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def tau (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) (P : Complex R) :
    (pull f).obj P ⟶ (restrictComplex d.targetMap).obj
      ((pull (changed f d)).obj ((extend d.sourceMap).obj P)) :=
  (NatTrans.mapHomologicalComplex (transitionModule f k d k') (.up ℤ)).app P

/-- The canonical lax tensor map for restriction of scalars, obtained by adjunction.
Source: Stacks 03CY and 03EK
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def restrictionTensorModule {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M N : Modules B) :
    (restrictionFunctor a).obj M ⊗ (restrictionFunctor a).obj N ⟶
      (restrictionFunctor a).obj (M ⊗ N) :=
  (extensionAdjunction a).homEquiv _ _
    (((extensionComparison a).mu
      ((restrictionFunctor a).obj M) ((restrictionFunctor a).obj N)).hom ≫
        ((extensionAdjunction a).counit.app M ⊗ₘ
          (extensionAdjunction a).counit.app N))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionTensorModule_naturality
    {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {M M' N N' : Modules B} (f : M ⟶ M') (g : N ⟶ N') :
    ((restrictionFunctor a).map f ⊗ₘ (restrictionFunctor a).map g) ≫
        restrictionTensorModule a M' N' =
      restrictionTensorModule a M N ≫ (restrictionFunctor a).map (f ⊗ₘ g) := by
  unfold restrictionTensorModule
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  apply congrArg ((extensionAdjunction a).homEquiv _ _)
  have h := (extensionComparison a).naturality
    ((restrictionFunctor a).map f) ((restrictionFunctor a).map g)
  dsimp only [extensionPullback] at h
  rw [← Category.assoc, h, Category.assoc, Category.assoc]
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  have hf : (extensionFunctor a).map ((restrictionFunctor a).map f) ≫
      (extensionAdjunction a).counit.app M' =
        (extensionAdjunction a).counit.app M ≫ f :=
    (extensionAdjunction a).counit.naturality f
  have hg : (extensionFunctor a).map ((restrictionFunctor a).map g) ≫
      (extensionAdjunction a).counit.app N' =
        (extensionAdjunction a).counit.app N ≫ g :=
    (extensionAdjunction a).counit.naturality g
  rw [hf, hg]

universe uA vA uB vB

section

variable {A : Type uA} [Category.{vA} A] [Abelian A] [MonoidalCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) [L.Additive]
  (e : ∀ X Y : A, L.obj X ⊗ L.obj Y ⟶ L.obj (X ⊗ Y))

private noncomputable def laxTotalComponent (P Q : CochainComplex A ℤ) (n : ℤ) :
    (CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B)).X n ⟶
        L.obj ((CochainComplex.mapBifunctor P Q (curriedTensor A)).X n) :=
  HomologicalComplex.mapBifunctorDesc (fun a b h ↦
    e (P.X a) (Q.X b) ≫
      L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n h))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem laxTotalComponent_comm
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      e X Y ≫ L.map (f ⊗ₘ g) = (L.map f ⊗ₘ L.map g) ≫ e X' Y')
    (P Q : CochainComplex A ℤ) (n m : ℤ) :
    laxTotalComponent L e P Q n ≫
        L.map ((CochainComplex.mapBifunctor P Q (curriedTensor A)).d n m) =
      (CochainComplex.mapBifunctor
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B)).d n m ≫
          laxTotalComponent L e P Q m := by
  by_cases hnm : (ComplexShape.up ℤ).Rel n m
  · change n + 1 = m at hnm
    subst m
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    change a + b = n at hab
    simp only [laxTotalComponent,
      HomologicalComplex.ι_mapBifunctorDesc_assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      Preadditive.add_comp, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    simp only [L.map_add, Preadditive.comp_add, Category.assoc]
    rw [← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₁,
      ← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₂]
    rw [HomologicalComplex.mapBifunctor.d₁_eq P Q _ _
        (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl) b (n + 1)
        (by change a + 1 + b = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq P Q _ _ a
        (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl) (n + 1)
        (by change a + (b + 1) = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₁_eq
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) _ _
        (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl) b (n + 1)
        (by change a + 1 + b = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) _ _ a
        (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl) (n + 1)
        (by change a + (b + 1) = n + 1; omega)]
    simp only [
      ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ,
      one_smul, Functor.map_units_smul, Functor.map_comp,
      Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    simp only [curriedTensor_map_app, curriedTensor_obj_map,
      Functor.mapHomologicalComplex_obj_d, ← tensorHom_id, ← id_tensorHom]
    dsimp only [Functor.mapHomologicalComplex, curriedTensor_obj_obj]
    apply congrArg₂ (· + ·)
    · simpa only [L.map_id, Category.assoc] using
        congrArg (fun f ↦ f ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A)
            (a + 1) b (n + 1) (by omega))) (he (P.d a (a + 1)) (𝟙 (Q.X b)))
    · simpa only [L.map_id, Category.assoc, Linear.units_smul_comp,
        Linear.comp_units_smul] using
        congrArg (fun f ↦ a.negOnePow • (f ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A)
            a (b + 1) (n + 1) (by omega)))) (he (𝟙 (P.X a)) (Q.d b (b + 1)))
  · rw [HomologicalComplex.shape _ n m hnm, HomologicalComplex.shape _ n m hnm,
      L.map_zero, comp_zero, zero_comp]

end

/-- Sum of the canonical restriction tensor maps over a total degree.
Source: Stacks 03EK and 07A4
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def restrictionTensorComponent {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (P Q : Complex B) (n : ℤ) :
    ((restrictComplex a).obj P ⊗ (restrictComplex a).obj Q).X n ⟶
      (restrictionFunctor a).obj ((P ⊗ Q).X n) :=
  HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦
    restrictionTensorModule a (P.X p) (Q.X q) ≫
      (restrictionFunctor a).map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules B)) p q n hpq))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction's tensor comparison commutes with the signed total differential.
Source: Stacks 03EK and 07A4
(blueprint: def-pur-cochain-coefficient-arrows).
Proof: on each summand, naturality of the adjunction's unit and counit and of
scalar extension's tensor comparison commutes with each differential. Restriction
is additive, so it preserves the factor (-1)^p. Sum the two equations. -/
theorem restrictionTensorComponent_comm {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (P Q : Complex B) (n m : ℤ) :
    restrictionTensorComponent a P Q n ≫
        (restrictionFunctor a).map ((P ⊗ Q).d n m) =
      ((restrictComplex a).obj P ⊗ (restrictComplex a).obj Q).d n m ≫
        restrictionTensorComponent a P Q m := by
  exact laxTotalComponent_comm (restrictionFunctor a) (restrictionTensorModule a)
    (fun f g ↦ (restrictionTensorModule_naturality a f g).symm) P Q n m

/-- The usual restriction-of-scalars tensor map on total complexes.
It sends a homogeneous pure tensor `x ⊗ y` to `x ⊗ y` and is not asserted invertible.
Source: Stacks 03EK and 07A4
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def restrictionTensor {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (P Q : Complex B) :
    (restrictComplex a).obj P ⊗ (restrictComplex a).obj Q ⟶
      (restrictComplex a).obj (P ⊗ Q) where
  f := restrictionTensorComponent a P Q
  comm' n m _ := restrictionTensorComponent_comm a P Q n m

end CategoryTheory.CochainPullback
