/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport

/-! # Signed tensor comparison and coherence on cochain sheaves

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and sites-modules.tex,
Tag 03EL (auxiliary; not a blueprint node).

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

/-- Identity inverse image, transporting every operation by the identity.
Source: Stacks 03D2 (auxiliary; not a blueprint node). -/
noncomputable def identityAlgebraicInverseImage (A : Sheaf J CommRingCat.{w}) :
    SheafOfModules.AlgebraicInverseImage (𝟭 (Sheaf J (Type w))) A A where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 (Modules A)
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

/-- Functor laws for the existing sheafified scalar extension.
Source: Stacks 03CY (auxiliary; not a blueprint node).
Proof: on a pure tensor the maps are `s ⊗ x ↦ s ⊗ h(x)`.
Identity and composition hold on these tensors; sheafification is functorial. -/
theorem extensionFunctor_laws {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    (∀ M : Modules A, SheafOfModules.changeOfRingsHom a M (𝟙 M) = 𝟙 _) ∧
      (∀ (M N H : Modules A) (b : M ⟶ N) (c : N ⟶ H),
        SheafOfModules.changeOfRingsHom a M (b ≫ c) =
          SheafOfModules.changeOfRingsHom a M b ≫
            SheafOfModules.changeOfRingsHom a N c) := by
  constructor
  · intro M
    unfold SheafOfModules.changeOfRingsHom
    have h : (show SheafOfModules.changeOfRingsPresheaf a M ⟶
        SheafOfModules.changeOfRingsPresheaf a M from
      { app := fun U ↦ (ModuleCat.extendScalars (a.hom.app U).hom).map
          ((show M ⟶ M from 𝟙 M).val.app U)
        naturality := SheafOfModules.changeOfRingsHom_naturality a M (𝟙 M) }) =
          𝟙 _ := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendScalars (a.hom.app U).hom).map_id _
    exact (congrArg (fun b ↦ (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).map b) h).trans
        (Functor.map_id _ _)
  · intro M N H b c
    unfold SheafOfModules.changeOfRingsHom
    rw [← Functor.map_comp]
    congr 1
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (a.hom.app U).hom).map_comp _ _

/-- Actual scalar extension, with the scalar placed first by the existing API.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
noncomputable def extensionFunctor {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    Modules A ⥤ Modules B where
  obj M := SheafOfModules.changeOfRings a M
  map b := SheafOfModules.changeOfRingsHom a _ b
  map_id := (extensionFunctor_laws a).1
  map_comp := (extensionFunctor_laws a).2 _ _ _

/-- Actual restriction of scalars; this keeps the underlying abelian sheaf.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
noncomputable abbrev restrictionFunctor {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)

/-- The sheafification-unit image of `s ⊗ x` in scalar extension.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
noncomputable def extensionTmul {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M : Modules A) (U : Cᵒᵖ) (s : B.obj.obj U) (x : M.val.obj U) :
    ((extensionFunctor a).obj M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf a M)).app U)
        (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)

private local instance {A : Sheaf J CommRingCat.{w}} (M : Modules A)
    {X Y : Cᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.map i).hom).obj
          (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

set_option backward.isDefEq.respectTransparency false in
open SheafOfModules in
private theorem tensorRestriction_tmul
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S) (M : Modules A)
    {X Y : Cᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap c M i) s m

open SheafOfModules in
private noncomputable def tensorToRestriction
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    (M : Modules A) (H : Modules S)
    (f : changeOfRingsPresheaf c M ⟶ H.val) : M ⟶ (restrictionFunctor c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

open SheafOfModules in
private noncomputable def restrictionToTensor
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    (M : Modules A) (H : Modules S)
    (g : M ⟶ (restrictionFunctor c).obj H) : changeOfRingsPresheaf c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Cᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

open SheafOfModules in
private noncomputable def tensorPresheafHomEquiv
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    (M : Modules A) (H : Modules S) :
    (changeOfRingsPresheaf c M ⟶ H.val) ≃ (M ⟶ (restrictionFunctor c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

open SheafOfModules in
private noncomputable def tensorHomEquiv
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    (M : Modules A) (H : Modules S) :
    ((extensionFunctor c).obj M ⟶ H) ≃ (M ⟶ (restrictionFunctor c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

open SheafOfModules in
private theorem tensorHomEquiv_naturality_left
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    {M N : Modules A} (a : M ⟶ N)
    (H : Modules S) (f : (extensionFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((extensionFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).map
          ((show SheafOfModules.changeOfRingsPresheaf c M ⟶
          SheafOfModules.changeOfRingsPresheaf c N from
        { app := fun U ↦ (ModuleCat.extendScalars (c.hom.app U).hom).map (a.val.app U)
          naturality := SheafOfModules.changeOfRingsHom_naturality c M a })) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv
    (changeOfRingsPresheaf c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

open SheafOfModules in
private theorem tensorHomEquiv_naturality_right
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    (M : Modules A)
    {H H' : Modules S}
    (f : (extensionFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restrictionFunctor c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

open SheafOfModules in
private noncomputable def tensorAdjunction
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S) : extensionFunctor c ⊣ restrictionFunctor c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

/-- The scalar-extension adjunction normalized by `x ↦ 1 ⊗ x`.
Source: Stacks 03CY and 03D7
(auxiliary; not a blueprint node).
Proof: compose the sectionwise balanced tensor hom correspondence with the
module sheafification adjunction. The resulting unit has the displayed formula.
The unit determines the counit, so an adjunction with this formula is unique. -/
theorem extensionAdjunction_existsUnique {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    ∃! adj : extensionFunctor a ⊣ restrictionFunctor a,
      ∀ (M : Modules A) (U : Cᵒᵖ) (x : M.val.obj U),
        (adj.unit.app M).val.app U x = extensionTmul a M U 1 x := by
  have hunit : ∀ (M : Modules A) (U : Cᵒᵖ) (x : M.val.obj U),
      ((tensorAdjunction a).unit.app M).val.app U x = extensionTmul a M U 1 x := by
    intro M U x
    rw [← Adjunction.homEquiv_id, tensorAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  refine ⟨tensorAdjunction a, hunit, ?_⟩
  intro adj hadj
  apply Adjunction.ext
  ext M U x
  exact (hadj M U x).trans (hunit M U x).symm

/-- The unique normalized scalar-extension adjunction.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
noncomputable def extensionAdjunction {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  Classical.choose (extensionAdjunction_existsUnique a)

/-- Scalar extension is additive because it is a left adjoint between abelian categories.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
noncomputable instance extensionFunctorAdditive {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) : (extensionFunctor a).Additive :=
  (extensionAdjunction a).left_adjoint_additive

/-- The object/map presentation of scalar extension with identity inverse image.
Source: Stacks 03CY (auxiliary; not a blueprint node).
Proof: expand the functor map; the two transport maps are identities. -/
theorem extensionFunctor_mapPresentation {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {M N : Modules A} (b : M ⟶ N) :
    (extensionFunctor a).map b = eqToHom (rfl :
      (extensionFunctor a).obj M = SheafOfModules.changeOfRings a M) ≫
        SheafOfModules.changeOfRingsHom a M b ≫ eqToHom rfl := by
  simp [extensionFunctor]

/-- Scalar extension as the actual ringed identity-topos pullback.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
noncomputable def extensionPullback {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    RingedPullback A B where
  uInv := 𝟭 _
  uPush := 𝟭 _
  adj := Adjunction.id
  finiteLimits := inferInstance
  RI := A
  I := identityAlgebraicInverseImage A
  coefficient := a
  L := extensionFunctor a
  hobj _ := rfl
  hmap := extensionFunctor_mapPresentation a
  V := restrictionFunctor a
  moduleAdj := extensionAdjunction a

/-- The normalized comparison for scalar extension, uniquely fixed by pure tensors.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
noncomputable def extensionComparison {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    Comparison (extensionPullback a) :=
  Classical.choice
    (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_existsUnique
    A B A (𝟭 _) (identityAlgebraicInverseImage A) a (extensionFunctor a)
    (fun _ ↦ rfl) (𝟭 _) Adjunction.id (extensionFunctor_mapPresentation a)).1

/-- Termwise scalar extension on unbounded cochain complexes.
Source: Stacks 03CY and 07A4
(auxiliary; not a blueprint node). -/
noncomputable abbrev extend {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  pull (extensionPullback a)

/-- Insertion of the scalar unit, as a morphism of underlying sheaves.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
noncomputable def insertion {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) (M : Modules A) :
    (underlying A).obj M ⟶ (underlying B).obj ((extensionFunctor a).obj M) :=
  (underlying A).map ((extensionAdjunction a).unit.app M)

/-- The compatible coefficient square over the same geometric inverse image.
In particular the equality of the two coefficient maps is part of the input.
The module functor is required to be the actual scalar-extension presentation.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
structure CoefficientSquare (f : RingedPullback R S) where
  R' : Sheaf J CommRingCat.{w}
  S' : Sheaf K CommRingCat.{w}
  sourceMap : R ⟶ R'
  targetMap : S ⟶ S'
  RI' : Sheaf K CommRingCat.{w}
  I' : SheafOfModules.AlgebraicInverseImage f.uInv R' RI'
  coefficient' : RI' ⟶ S'
  inverseImageMap : f.RI ⟶ RI'
  inverseImageMap_graph :
    f.uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map sourceMap) ≫
        I'.ringUnderlying.hom =
      f.I.ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map inverseImageMap
  square : inverseImageMap ≫ coefficient' = f.coefficient ≫ targetMap
  L' : Modules R' ⥤ Modules S'
  hobj' : ∀ M, L'.obj M = SheafOfModules.changeOfRings coefficient' (I'.modules.obj M)
  hmap' : ∀ {M N} (b : M ⟶ N), L'.map b = eqToHom (hobj' M) ≫
    SheafOfModules.changeOfRingsHom coefficient' (I'.modules.obj M) (I'.modules.map b) ≫
      eqToHom (hobj' N).symm
  V' : Modules S' ⥤ Modules R'
  moduleAdj' : L' ⊣ V'
  [additive' : L'.Additive]

attribute [instance] CoefficientSquare.additive'

/-- A generalized inverse-image generator, followed by scalar-unit insertion.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
noncomputable def generator (f : RingedPullback R S) (k : Comparison f)
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

open SheafOfModules SheafOfModules.GeometricConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private noncomputable instance pushPreservesLimits (f : RingedPullback R S) :
    PreservesLimits f.uPush := f.adj.rightAdjoint_preservesLimits

/-- The restriction of scalars on complexes, applied termwise.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
noncomputable abbrev restrictComplex {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  (restrictionFunctor a).mapHomologicalComplex (.up ℤ)

universe uA vA uB vB

section

variable {A : Type uA} [Category.{vA} A] [Abelian A] [MonoidalCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) [L.Additive]
  (e : ∀ X Y : A, L.obj X ⊗ L.obj Y ⟶ L.obj (X ⊗ Y))

end

end CategoryTheory.CochainPullback
