/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # The finite ordinary restriction mate

Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
universe t u a b c d av bv cv dv
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

private theorem mate_word
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{av} A] [Category.{bv} B] [Category.{cv} C] [Category.{dv} D]
    {L : A ⥤ B} {R : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    (adj : L ⊣ R) (level : F ⊣ G) {S : A ⥤ C} {T : B ⥤ D}
    (α : TwoSquare S L F T) (N : B) :
    (mateEquiv adj level α).app N = level.unit.app (S.obj (R.obj N)) ≫
      G.map (α.app (R.obj N)) ≫ G.map (T.map (adj.counit.app N)) := by
  simp [mateEquiv]

private theorem equivalence_comp_unit_isIso
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{av} A] [Category.{bv} B] [Category.{cv} C]
    (e : A ≌ B) {L : B ⥤ C} {R : C ⥤ B} (adj : L ⊣ R) (M : A)
    (h : IsIso (adj.unit.app (e.functor.obj M))) :
    IsIso ((e.toAdjunction.comp adj).unit.app M) := by
  rw [Adjunction.comp_unit_app]
  change IsIso (e.unitIso.hom.app M ≫ e.inverse.map (adj.unit.app (e.functor.obj M)))
  infer_instance

private theorem mapped_conjugate_isIso
    {A : Type a} {B : Type b} [Category.{av} A] [Category.{bv} B]
    (T : A ⥤ B) {X X' Y Y' : A} {a : X = X'} {b : Y' = Y}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : f = eqToHom a ≫ g ≫ eqToHom b)
    (hg : IsIso (T.map g)) : IsIso (T.map f) := by
  rw [h, Functor.map_comp, Functor.map_comp]
  infer_instance

section SliceHelpers
set_option backward.isDefEq.respectTransparency.types false

open SheafOfModules in
set_option backward.isDefEq.respectTransparency false in
private def summandIso
    {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c d u}) (V W : C) [Subsingleton (W ⟶ V)]
    (a : W ⟶ V) (M : SheafOfModules.{max c d u} (R.over V)) :
    M.val.obj (op (Over.mk a)) ≅ ((extensionByZeroPresheaf R V).obj M).obj (op W) := by
  classical
  letI : DecidableEq (W ⟶ V) := Classical.typeDecidableEq _
  exact LinearEquiv.toModuleIso
    { toLinearMap := DirectSum.lof (R.obj.obj (op W)) (W ⟶ V)
        (fun b ↦ M.val.obj (op (Over.mk b))) a
      invFun := DirectSum.component (R.obj.obj (op W)) (W ⟶ V)
        (fun b ↦ M.val.obj (op (Over.mk b))) a
      left_inv := fun x ↦ DirectSum.component.lof_self
        (M := fun b ↦ M.val.obj (op (Over.mk b))) (R.obj.obj (op W)) a x
      right_inv := by
        intro x
        induction x using DirectSum.induction_on with
        | zero => simp
        | of b x =>
          have : b = a := Subsingleton.elim _ _
          subst b
          change DirectSum.lof _ _ _ a (DirectSum.component _ _ _ a
            (DirectSum.lof (R.obj.obj (op W)) _
              (fun b ↦ M.val.obj (op (Over.mk b))) a x)) = _
          rw [DirectSum.component.lof_self]
          rfl
        | add x y hx hy =>
          change DirectSum.of _ a (x a + y a) = x + y
          rw [map_add]
          exact congrArg₂ (· + ·) hx hy }

open SheafOfModules in
set_option backward.isDefEq.respectTransparency false in
open Classical in
private theorem restrict_summand
    {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c d u}) (V : C)
    (M : SheafOfModules.{max c d u} (R.over V)) {W Z : Cᵒᵖ} (f : W ⟶ Z)
    (a : W.unop ⟶ V) (b : Z.unop ⟶ V) (h : f.unop ≫ a = b)
    (x : M.val.obj (op (Over.mk a))) :
    extensionByZeroPresheafRestrictAdd R V M f
        (DirectSum.of (fun z : W.unop ⟶ V ↦ M.val.obj (op (Over.mk z))) a x) =
      DirectSum.of (fun z : Z.unop ⟶ V ↦ M.val.obj (op (Over.mk z))) b
        (M.val.map (op (Over.homMk f.unop h : Over.mk b ⟶ Over.mk a)) x) := by
  classical
  subst b
  change (DirectSum.toAddMonoid _)
    (DirectSum.of (fun z : W.unop ⟶ V ↦ M.val.obj (op (Over.mk z))) a x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

open SheafOfModules in
set_option backward.isDefEq.respectTransparency false in
private def restrictedExtensionIso
    {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c d u}) (V : C)
    (hV : ∀ W : C, Subsingleton (W ⟶ V))
    (M : SheafOfModules.{max c d u} (R.over V)) :
    M.val.presheaf ≅
      (Over.forget V).op ⋙ ((extensionByZeroPresheaf R V).obj M).presheaf := by
  classical
  refine NatIso.ofComponents (fun W ↦ ?_) ?_
  · let := hV W.unop.left
    exact (forget₂ (ModuleCat (R.obj.obj (op W.unop.left))) AddCommGrpCat).mapIso
      (summandIso R V W.unop.left W.unop.hom M)
  · intro W Z a
    let : DecidableEq (W.unop.left ⟶ V) := Classical.typeDecidableEq _
    let : DecidableEq (Z.unop.left ⟶ V) := Classical.typeDecidableEq _
    ext x
    change DirectSum.of _ Z.unop.hom (M.val.map a x) =
      extensionByZeroPresheafRestrictAdd R V M
        ((Over.forget V).op.map a) (DirectSum.of _ W.unop.hom x)
    exact (restrict_summand R V M ((Over.forget V).op.map a)
      W.unop.hom Z.unop.hom (Over.w a.unop) x).symm

open SheafOfModules in
set_option backward.isDefEq.respectTransparency false in
private theorem sliceUnit_isIso
    {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c d u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c d u}]
    (B : Sheaf J CommRingCat.{max c d u}) (V : C)
    (hV : ∀ W : C, Subsingleton (W ⟶ V))
    (M : SheafOfModules.{max c d u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).over V)) :
    IsIso ((localizedSystemAdjunction.{c, d, u} B V).unit.app M) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B
  let P := ((extensionByZeroPresheaf R V).obj M).presheaf
  let T := (Over.forget V).op ⋙ P
  let e := restrictedExtensionIso R V hV M
  have hT : Presheaf.IsSheaf (J.over V) T :=
    (Presheaf.isSheaf_of_iso_iff e).mp M.isSheaf
  have : IsIso (toSheafify (J.over V) T) := isIso_toSheafify _ hT
  have hh := (Over.forget V).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat.{max c d u} (J.over V) J P
  have : IsIso (Functor.whiskerLeft (Over.forget V).op (toSheafify J P)) := by
    rw [← hh]
    infer_instance
  let η := (localizedSystemAdjunction.{c, d, u} B V).unit.app M
  have hη : ((toSheaf _).map η).hom =
      e.hom ≫ Functor.whiskerLeft (Over.forget V).op (toSheafify J P) := by
    ext W x
    convert! (localizedSystemAdjunction_existsUnique.{c, d, u} B V).exists.choose_spec
      M W x using 1
  have : IsIso ((sheafToPresheaf (J.over V) AddCommGrpCat.{max c d u}).map
      ((toSheaf _).map η)) := by
    change IsIso (((toSheaf _).map η).hom)
    rw [hη]
    infer_instance
  have : IsIso ((toSheaf _).map η) :=
    isIso_of_reflects_iso _ (sheafToPresheaf (J.over V) AddCommGrpCat.{max c d u})
  exact isIso_of_reflects_iso η (toSheaf _)

open SheafOfModules in
set_option backward.isDefEq.respectTransparency false in
private theorem changeOfRings_over_isIso
    {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c d u} RingCat.{max c d u})]
    [HasSheafify J AddCommGrpCat.{max c d u}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c d u}]
    (V : C)
    [HasSheafify (J.over V) AddCommGrpCat.{max c d u}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c d u}]
    {A B : Sheaf J CommRingCat.{max c d u}} (φ : A ⟶ B)
    {M N : SheafOfModules.{max c d u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)}
    (f : M ⟶ N) [IsIso (f.over V)] :
    IsIso ((changeOfRingsHom φ M f).over V) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B
  let p : changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N :=
    { app := fun W ↦ (ModuleCat.extendScalars (φ.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality φ M f }
  let Q := PresheafOfModules.pushforward (F := Over.forget V) (𝟙 (R.over V).obj)
  have hcomp (W : (Over V)ᵒᵖ) : IsIso ((Q.map p).app W) := by
    have : IsIso (f.val.app (op W.unop.left)) :=
      inferInstanceAs (IsIso ((evaluation _ W).map (f.over V)))
    exact inferInstanceAs
      (IsIso ((ModuleCat.extendScalars (φ.hom.app (op W.unop.left)).hom).map
        (f.val.app (op W.unop.left))))
  let e := PresheafOfModules.isoMk (fun W ↦
    letI := hcomp W
    asIso ((Q.map p).app W))
    (fun {_ _} a ↦ (Q.map p).naturality a)
  have : IsIso (Q.map p) := by
    change IsIso e.hom
    infer_instance
  let qAb := (PresheafOfModules.toPresheaf (R.over V).obj).map (Q.map p)
  have : IsIso qAb := inferInstance
  let pAb := (PresheafOfModules.toPresheaf R.obj).map p
  let c := (Over.forget V).pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{max c d u} (J.over V) J
  have hq : IsIso ((presheafToSheaf (J.over V) AddCommGrpCat.{max c d u}).map qAb) :=
    inferInstance
  have ht := (NatIso.isIso_map_iff c pAb).mp hq
  have : IsIso ((toSheaf (R.over V)).map ((changeOfRingsHom φ M f).over V)) := ht
  exact isIso_of_reflects_iso _ (toSheaf (R.over V))

end SliceHelpers

attribute [local irreducible] scalarReductionExistence scalarReductionExtension
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] (o : Operations l E j)

/-- The finite open adjunction, retaining both coefficient-equivalence transformations.
Source: Stacks 03DJ (blueprint: lem-sf-ordinary-open-finite-restriction-mate-invertible). -/
abbrev finiteOpenAdjunction (n : ℕ) := (o.finite n).toAdjunction.comp
  (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
    (rings l E X n) (openObject j))

/-- The actual mate of inverse extension tensor comparison.
Source: Stacks 0E8I (blueprint: lem-sf-ordinary-open-finite-restriction-mate-invertible). -/
def finiteRestrictionMate (tensor : TensorComparison l E j o) (n : ℕ) :
    restriction l E j o ⋙ scalarReductionExtension l E U n ⟶
      scalarReductionExtension l E X n ⋙ finiteRestriction l E j o n :=
  (mateEquiv (ordinaryAdjunction l E j o) (finiteOpenAdjunction l E j o n)
    (TwoSquare.mk _ _ _ _ (tensor.ordinary n).inv))

/-- The mate has the prescribed unit, inverse-tensor, counit word.
Source: Stacks 0E8I (blueprint: lem-sf-ordinary-open-finite-restriction-mate-invertible). -/
theorem finiteRestrictionMate_app (tensor : TensorComparison l E j o) (n : ℕ)
    (N : scalarReductionSource l E X) :
    (finiteRestrictionMate l E j o tensor n).app N =
      (finiteOpenAdjunction l E j o n).unit.app _ ≫
        (finiteRestriction l E j o n).map
          ((tensor.ordinary n).inv.app ((restriction l E j o).obj N)) ≫
        (finiteRestriction l E j o n).map
          ((scalarReductionExtension l E X n).map
            ((ordinaryAdjunction l E j o).counit.app N)) := by
  exact mate_word (ordinaryAdjunction l E j o) (finiteOpenAdjunction l E j o n)
    (TwoSquare.mk _ _ _ _ (tensor.ordinary n).inv) N

/-- The generator-normalized finite restriction mate is invertible.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I,
lemma-j-shriek-and-tensor; finite part of the ordinary quotient argument.
(blueprint: lem-sf-ordinary-open-finite-restriction-mate-invertible).

Proof: the open object is subterminal because j is a monomorphism. On its
slice the extension presheaf has precisely one summand at each object, naturally
identified with the original module. Slice restriction commutes with sheafification
by the cocontinuity of Over.forget. Thus the section-normalized localized unit
is invertible. Composing with the coefficient equivalences gives invertible
units for both ordinary open adjunctions.

Let epsilon be the integral counit at N. Its restriction is invertible by the
right triangle identity and the integral unit. The inverse coefficient equivalence
reflects isomorphisms, so epsilon is already invertible on the actual slice.
Sectionwise extension of scalars preserves these slice isomorphisms; the natural
slice sheafification comparison shows the same after sheafification. Transport
through the fixed object and map identifications of scalarReductionExtension.
Consequently finiteRestriction sends scalarReductionExtension(epsilon) to an
isomorphism. In finiteRestrictionMate_app, the other two factors are the finite
open unit and the image of tensor.ordinary.inv. Hence every factor is invertible.
Componentwise invertibility proves the assertion. This uses only the ordinary
isomorphism of TensorComparison; its generator equation is not needed for
invertibility. The argument includes n = 0, zero modules and the empty open. -/
theorem finiteRestrictionMate_isIso (tensor : TensorComparison l E j o) (n : ℕ) :
    IsIso (finiteRestrictionMate l E j o tensor n) := by
  have hV (W : X.ProEt) : Subsingleton (W ⟶ openObject j) := by
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).mp
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  have hu (M : scalarReductionSource l E U) :
      IsIso ((ordinaryAdjunction l E j o).unit.app M) :=
    equivalence_comp_unit_isIso o.integral _ M
      (sliceUnit_isIso.{max u (t+1), t+1, t}
        (completedIntegralCommRingSheafUnrestricted l E X)
        (openObject j) hV (o.integral.functor.obj M))
  have hv (M : normalizedDVRModules l E U n) :
      IsIso ((finiteOpenAdjunction l E j o n).unit.app M) :=
    equivalence_comp_unit_isIso (o.finite n) _ M
      (sliceUnit_isIso.{max u (t+1), t+1, t} (rings l E X n) (openObject j) hV
        ((o.finite n).functor.obj M))
  have (N : scalarReductionSource l E X) :
      IsIso ((finiteRestrictionMate l E j o tensor n).app N) := by
    rw [finiteRestrictionMate_app]
    have := hv ((scalarReductionExtension l E U n).obj ((restriction l E j o).obj N))
    let ε := (ordinaryAdjunction l E j o).counit.app N
    have hε : IsIso ((restriction l E j o).map ε) := by
      have := hu ((restriction l E j o).obj N)
      exact IsIso.of_isIso_fac_left
        ((ordinaryAdjunction l E j o).right_triangle_components N)
    have : IsIso (o.integral.inverse.map (ε.over (openObject j))) := hε
    have : IsIso (ε.over (openObject j)) :=
      o.integral.fullyFaithfulInverse.isIso_of_isIso_map _
    have hchange := changeOfRings_over_isIso.{max u (t+1), t+1, t} (openObject j)
      (completedIntegralCommRingProjectionUnrestricted l E X n) ε
    have hm := (scalarReductionExistence l E X n).choose_spec.choose_spec.choose ε
    have hscalar : IsIso
        (((scalarReductionExtension l E X n).map ε).over (openObject j)) := by
      unfold scalarReductionExtension
      exact mapped_conjugate_isIso
        (SheafOfModules.overFunctor (integralCoefficientSheaf l E X n) (openObject j))
        hm hchange
    have : IsIso ((finiteRestriction l E j o n).map
        ((scalarReductionExtension l E X n).map ε)) :=
      inferInstanceAs (IsIso ((o.finite n).inverse.map
        (((scalarReductionExtension l E X n).map ε).over (openObject j))))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end WeilConjectures.CanonicalOpenRestriction
