/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Supporting.PbcWeilCategory
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.Algebra.Homology.SixFunctors.WeilSiteDerivedTensorDescent
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.CategoryTheory.Localization.Linear
import WeilConjectures.Algebra.Homology.BifunctorLinear
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-!
# Linearity and K-flat descent for Weil tensors

The localization and scalar-localization helpers used by `WeilTensorProduct`.
This module keeps the descent construction independently compilable.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

attribute [local irreducible] ScalarLocalization.composition
namespace WfTensorLinearity
universe x
variable {C : Type u} [Category C] {D : Type v} [Category D]
  {E : Type w} [Category E] {E' : Type x} [Category E']

set_option backward.isDefEq.respectTransparency false in
private def fixedLeftIso (L : C ⥤ D) (B : D × D ⥤ E') (F : C ⥤ C ⥤ E) (Q : E ⥤ E')
    (c : (L.prod L) ⋙ B ≅ Functor.uncurry.obj F ⋙ Q) (P : C) :
    L ⋙ (Functor.curry.obj B).obj (L.obj P) ≅ F.obj P ⋙ Q :=
  NatIso.ofComponents (fun Q ↦ c.app (P, Q)) (by
    intro Q Q' f
    have h := c.hom.naturality (Prod.mkHom (𝟙 P) f)
    simpa using h)

set_option backward.isDefEq.respectTransparency false in
private def fixedRightIso (L : C ⥤ D) (B : D × D ⥤ E') (F : C ⥤ C ⥤ E) (Q : E ⥤ E')
    (c : (L.prod L) ⋙ B ≅ Functor.uncurry.obj F ⋙ Q) (P : C) :
    L ⋙ (Functor.curry.obj B).flip.obj (L.obj P) ≅ F.flip.obj P ⋙ Q :=
  NatIso.ofComponents (fun Q ↦ c.app (Q, P)) (by
    intro Q Q' f
    have h := c.hom.naturality (Prod.mkHom f (𝟙 P))
    simpa using h)

set_option backward.isDefEq.respectTransparency false in
theorem homotopyBilinear
    (R : Type*) [CommRing R] [Preadditive C] [Preadditive D]
    [Preadditive E] [Preadditive E']
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    [CategoryTheory.Linear R E] [CategoryTheory.Linear R E']
    (L : C ⥤ D) [L.Full] [L.EssSurj] [L.Additive] [L.Linear R]
    (B : D × D ⥤ E') (F : C ⥤ C ⥤ E) (Q : E ⥤ E')
    [Q.Additive] [Q.Linear R]
    [∀ P, (F.obj P).Additive] [∀ P, (F.flip.obj P).Additive]
    [∀ P, (F.obj P).Linear R] [∀ P, (F.flip.obj P).Linear R]
    (c : (L.prod L) ⋙ B ≅ Functor.uncurry.obj F ⋙ Q) :
    (∀ P, ((Functor.curry.obj B).obj P).Additive ∧
      ((Functor.curry.obj B).obj P).Linear R) ∧
    (∀ P, ((Functor.curry.obj B).flip.obj P).Additive ∧
      ((Functor.curry.obj B).flip.obj P).Linear R) := by
  constructor
  · intro P
    let e := L.objObjPreimageIso P
    let i := fixedLeftIso L B F Q c (L.objPreimage P)
    have : (L ⋙ (Functor.curry.obj B).obj (L.obj (L.objPreimage P))).Additive :=
      Functor.additive_of_iso i.symm
    have : (L ⋙ (Functor.curry.obj B).obj (L.obj (L.objPreimage P))).Linear R :=
      Functor.linear_of_iso R i.symm
    have := Functor.additive_of_full_essSurj_comp L
      ((Functor.curry.obj B).obj (L.obj (L.objPreimage P)))
    have := Functor.linear_of_full_essSurj_comp (R := R) L
      ((Functor.curry.obj B).obj (L.obj (L.objPreimage P)))
    exact ⟨Functor.additive_of_iso ((Functor.curry.obj B).mapIso e),
      Functor.linear_of_iso R ((Functor.curry.obj B).mapIso e)⟩
  · intro P
    let e := L.objObjPreimageIso P
    let i := fixedRightIso L B F Q c (L.objPreimage P)
    have : (L ⋙ (Functor.curry.obj B).flip.obj (L.obj (L.objPreimage P))).Additive :=
      Functor.additive_of_iso i.symm
    have : (L ⋙ (Functor.curry.obj B).flip.obj (L.obj (L.objPreimage P))).Linear R :=
      Functor.linear_of_iso R i.symm
    have := Functor.additive_of_full_essSurj_comp L
      ((Functor.curry.obj B).flip.obj (L.obj (L.objPreimage P)))
    have := Functor.linear_of_full_essSurj_comp (R := R) L
      ((Functor.curry.obj B).flip.obj (L.obj (L.objPreimage P)))
    exact ⟨Functor.additive_of_iso ((Functor.curry.obj B).flip.mapIso e),
      Functor.linear_of_iso R ((Functor.curry.obj B).flip.mapIso e)⟩

set_option backward.isDefEq.respectTransparency false in
theorem resolvingFractions (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] (P : ObjectProperty C)
    (res : ∀ X : C, ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    (W.inverseImage P.ι).HasRightCalculusOfFractions := by
  let V := W.inverseImage P.ι
  exact
    { exists_rightFraction := by
        intro X Y φ
        obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk φ.f.hom φ.s.hom φ.hs
          : W.LeftFraction X.obj Y.obj).exists_rightFraction
        obtain ⟨Z, r, hr⟩ := res ψ.X'
        refine ⟨MorphismProperty.RightFraction.mk
          (ObjectProperty.homMk (r ≫ ψ.s)) (W.comp_mem _ _ hr ψ.hs)
          (ObjectProperty.homMk (r ≫ ψ.f)), ?_⟩
        apply ObjectProperty.hom_ext
        exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hψ).trans
          (Category.assoc _ _ _).symm)
      ext := by
        intro X Y Y' f g s hs h
        obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
          f.hom g.hom s.hom hs (congrArg (fun k ↦ k.hom) h)
        obtain ⟨T, r, hr⟩ := res Z
        refine ⟨T, ObjectProperty.homMk (r ≫ t), W.comp_mem _ _ hr ht, ?_⟩
        apply ObjectProperty.hom_ext
        exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) heq).trans
          (Category.assoc _ _ _).symm) }

set_option backward.isDefEq.respectTransparency false in
private theorem additive_of_localization
    [Preadditive C] [Preadditive D] [Preadditive E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasRightCalculusOfFractions] [L.Additive]
    (G : D ⥤ E) [(L ⋙ G).Additive] : G.Additive := by
  have : (L.op ⋙ G.op).Additive := by
    exact inferInstanceAs ((L ⋙ G).op.Additive)
  have hop : G.op.Additive :=
    (Localization.functor_additive_iff L.op W.op G.op).2 inferInstance
  constructor
  intro X Y f g
  exact Quiver.Hom.op_inj (G.op.map_add (f := f.op) (g := g.op))

set_option backward.isDefEq.respectTransparency false in
theorem localizedBilinear
    (R : Type*) [CommRing R] [Preadditive C] [Preadditive D]
    [Preadditive E] [Preadditive E']
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    [CategoryTheory.Linear R E] [CategoryTheory.Linear R E']
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasRightCalculusOfFractions] [L.Additive] [L.Linear R]
    (H : C ⥤ E) [H.Additive] [H.Linear R]
    (B : E × E ⥤ E) (Q : E ⥤ E') [Q.Additive] [Q.Linear R]
    [∀ P, ((Functor.curry.obj B).obj P).Additive]
    [∀ P, ((Functor.curry.obj B).flip.obj P).Additive]
    [∀ P, ((Functor.curry.obj B).obj P).Linear R]
    [∀ P, ((Functor.curry.obj B).flip.obj P).Linear R]
    (T : D × D ⥤ E')
    (t : (H.prod H) ⋙ B ⋙ Q ≅ (L.prod L) ⋙ T) :
    (∀ P, ((Functor.curry.obj T).obj P).Additive ∧
      ((Functor.curry.obj T).obj P).Linear R) ∧
    (∀ P, ((Functor.curry.obj T).flip.obj P).Additive ∧
      ((Functor.curry.obj T).flip.obj P).Linear R) := by
  have := Localization.essSurj L W
  constructor
  · intro P
    let c := L.objPreimage P
    let F := H ⋙ (Functor.curry.obj B).obj (H.obj c) ⋙ Q
    let G := (Functor.curry.obj T).obj (L.obj c)
    let i : F ≅ L ⋙ G := NatIso.ofComponents (fun Y ↦ t.app (c, Y)) (by
      intro Y Z f
      have h := t.hom.naturality (Prod.mkHom (𝟙 c) f)
      simpa [F, G] using h)
    have : (L ⋙ G).Additive := Functor.additive_of_iso i
    have : (L ⋙ G).Linear R := Functor.linear_of_iso R i
    have : G.Additive := additive_of_localization L W G
    let : Localization.Lifting L W (L ⋙ G) G := ⟨Iso.refl _⟩
    have : G.Linear R := (Localization.functor_linear_iff L W R (L ⋙ G) G).1
      inferInstance
    let j := (Functor.curry.obj T).mapIso (L.objObjPreimageIso P)
    exact ⟨Functor.additive_of_iso j, Functor.linear_of_iso R j⟩
  · intro P
    let c := L.objPreimage P
    let F := H ⋙ (Functor.curry.obj B).flip.obj (H.obj c) ⋙ Q
    let G := (Functor.curry.obj T).flip.obj (L.obj c)
    let i : F ≅ L ⋙ G := NatIso.ofComponents (fun Y ↦ t.app (Y, c)) (by
      intro Y Z f
      have h := t.hom.naturality (Prod.mkHom f (𝟙 c))
      simpa [F, G] using h)
    have : (L ⋙ G).Additive := Functor.additive_of_iso i
    have : (L ⋙ G).Linear R := Functor.linear_of_iso R i
    have : G.Additive := additive_of_localization L W G
    let : Localization.Lifting L W (L ⋙ G) G := ⟨Iso.refl _⟩
    have : G.Linear R := (Localization.functor_linear_iff L W R (L ⋙ G) G).1
      inferInstance
    let j := (Functor.curry.obj T).flip.mapIso (L.objObjPreimageIso P)
    exact ⟨Functor.additive_of_iso j, Functor.linear_of_iso R j⟩

private def mapBilinear
    (R : Type*) [CommRing R] [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (T : C × C ⥤ D) (M M' N N' : C)
    [((Functor.curry.obj T).flip.obj N).Additive]
    [((Functor.curry.obj T).flip.obj N).Linear R]
    [((Functor.curry.obj T).obj M').Additive]
    [((Functor.curry.obj T).obj M').Linear R] :
    (M ⟶ M') →ₗ[R] (N ⟶ N') →ₗ[R] (T.obj (M, N) ⟶ T.obj (M', N')) :=
  ((Linear.comp (S := R) (T.obj (M, N)) (T.obj (M', N)) (T.obj (M', N'))).compl₂
    (((Functor.curry.obj T).obj M').mapLinearMap R)).comp
      (((Functor.curry.obj T).flip.obj N).mapLinearMap R)

private theorem mapBilinear_apply
    (R : Type*) [CommRing R] [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (T : C × C ⥤ D) (M M' N N' : C)
    [((Functor.curry.obj T).flip.obj N).Additive]
    [((Functor.curry.obj T).flip.obj N).Linear R]
    [((Functor.curry.obj T).obj M').Additive]
    [((Functor.curry.obj T).obj M').Linear R] (f : M ⟶ M') (g : N ⟶ N') :
    mapBilinear R T M M' N N' f g = T.map (Prod.mkHom f g) := by
  change T.map (Prod.mkHom f (𝟙 N)) ≫ T.map (Prod.mkHom (𝟙 M') g) = _
  rw [← T.map_comp]
  simp

theorem rationalTensorHom_exists
    (R : Type*) [CommRing R] [Preadditive C] [CategoryTheory.Linear R C]
    (T : C × C ⥤ C)
    [∀ P, ((Functor.curry.obj T).obj P).Additive]
    [∀ P, ((Functor.curry.obj T).obj P).Linear R]
    [∀ P, ((Functor.curry.obj T).flip.obj P).Additive]
    [∀ P, ((Functor.curry.obj T).flip.obj P).Linear R]
    (p : R) (M M' N N' : ScalarLocalization R C p) :
    ∃! b : (M ⟶ M') →ₗ[Localization.Away p] (N ⟶ N') →ₗ[Localization.Away p]
        ((⟨T.obj (M.obj, N.obj)⟩ : ScalarLocalization R C p) ⟶
          (⟨T.obj (M'.obj, N'.obj)⟩ : ScalarLocalization R C p)),
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (s t : Localization.Away p),
        b (s ⊗ₜ[R] f) (t ⊗ₜ[R] g) = (s * t) ⊗ₜ[R] T.map (Prod.mkHom f g) := by
  let b := mapBilinear R T M.obj M'.obj N.obj N'.obj
  let β := TensorProduct.curry
    (((TensorProduct.lift b).baseChange (Localization.Away p)).comp
      (AlgebraTensorModule.distribBaseChange R (Localization.Away p)
        (M.obj ⟶ M'.obj) (N.obj ⟶ N'.obj)).symm.toLinearMap)
  have hβ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj)
      (s t : Localization.Away p) :
      β (s ⊗ₜ[R] f) (t ⊗ₜ[R] g) = (s * t) ⊗ₜ[R] T.map (Prod.mkHom f g) := by
    simp [β, TensorProduct.curry_apply, b, mapBilinear_apply]
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul s f =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t g => exact (hγ f g s t).trans (hβ f g s t).symm

theorem reflectsComplete
    (F G : C ⥤ C) (η : 𝟭 C ⟶ F) [G.ReflectsIsomorphisms]
    (c : G ⋙ F ≅ F ⋙ G)
    (hc : ∀ M, η.app (G.obj M) ≫ c.hom.app M = G.map (η.app M)) (M : C) :
    IsIso (η.app (G.obj M)) ↔ IsIso (η.app M) := by
  constructor
  · intro hM
    have : IsIso (η.app (G.obj M)) := hM
    have : IsIso (G.map (η.app M)) := by
      rw [← hc M]
      infer_instance
    exact isIso_of_reflects_iso _ G
  · intro hM
    have : IsIso (η.app M) := hM
    have : IsIso (η.app (G.obj M) ≫ c.hom.app M) := by
      rw [hc M]
      exact Functor.map_isIso G (η.app M)
    exact IsIso.of_isIso_comp_right _ (c.hom.app M)

def representativeComparison
    {C₁ C₂ C₃ P S : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* P] [Category* S]
    (ι : P ⥤ C₁) (J : P ⥤ S) (κ : S ⥤ C₂)
    (L : C₁ ⥤ C₂) (Qh : C₂ ⥤ C₃) (Q : C₁ ⥤ C₃)
    (B : C₂ × C₂ ⥤ C₂) (T : C₃ × C₃ ⥤ C₃) (F : C₁ × C₁ ⥤ C₁)
    (c : (L.prod L) ⋙ B ≅ F ⋙ L)
    (t : (κ.prod κ) ⋙ B ⋙ Qh ≅ ((κ ⋙ Qh).prod (κ ⋙ Qh)) ⋙ T)
    (hj : (ι.prod ι) ⋙ (L.prod L) = (J.prod J) ⋙ (κ.prod κ))
    (hjQ : (J.prod J) ⋙ ((κ ⋙ Qh).prod (κ ⋙ Qh)) =
      ((ι ⋙ L ⋙ Qh).prod (ι ⋙ L ⋙ Qh))) (q : L ⋙ Qh ≅ Q) :
    (ι.prod ι) ⋙ F ⋙ Q ≅ ((ι ⋙ Q).prod (ι ⋙ Q)) ⋙ T :=
  Functor.isoWhiskerLeft ((ι.prod ι) ⋙ F) q.symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (ι.prod ι) c.symm) Qh ≪≫
    Functor.isoWhiskerRight (eqToIso hj) (B ⋙ Qh) ≪≫
    Functor.isoWhiskerLeft (J.prod J) t ≪≫
    Functor.isoWhiskerRight (eqToIso hjQ) T ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (Functor.isoWhiskerLeft ι q) (Functor.isoWhiskerLeft ι q)) T

theorem uniqueComparison (F : C ⥤ D) (ff : F.FullyFaithful)
    {M N : C} {P : D} (i : P ≅ F.obj M) (j : P ≅ F.obj N) :
    ∃! e : M ≅ N, i.hom ≫ F.map e.hom = j.hom := by
  let e := ff.preimageIso (i.symm ≪≫ j)
  have he : F.map e.hom = (i.symm ≪≫ j).hom := ff.map_preimage _
  refine ⟨e, ?_, ?_⟩
  · change i.hom ≫ F.map e.hom = j.hom
    rw [he]
    exact i.hom_inv_id_assoc _
  · intro e' he'
    apply Iso.ext
    apply ff.map_injective
    apply (cancel_epi i.hom).1
    rw [he', he]
    exact (i.hom_inv_id_assoc _).symm

end WfTensorLinearity

namespace SheafOfModules

/-- The derived tensor supplied by localization of the flat-term K-flat subcategory.
The representative comparison in site_derived_tensor_descent determines this functor
up to the unique compatible natural isomorphism; no functorial representatives are chosen.
Source: Stacks 06YS and 06YT (blueprint: prose-03-02). -/
def wfSiteDerivedTensor {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))] :
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ×
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ⥤
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :=
  (wf_site_derived_tensor_descent.{u, v, w, 0, 0} J R).choose_spec.2.2.1.choose_spec.2.choose

end SheafOfModules
