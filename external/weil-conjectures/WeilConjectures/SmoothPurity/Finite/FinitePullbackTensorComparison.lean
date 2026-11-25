/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorAssociativityRepresentatives
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorUnitRepresentatives
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorCompositionRepresentatives
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorSignedRepresentatives
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Coherence of the canonical finite tensor/pullback comparison

Source: Stacks 07A4, lemma-pullback-tensor-product, with the prescribed
coefficient conventions (blueprint: def-pur-finite-pullback-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped MonoidalCategory
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField
attribute [local irreducible] finiteIntrinsicClosed finiteIntrinsicTensorModels

private theorem tensorNatTrans_ext_resolving
    {B : Type*} [Category* B] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (q : B ⥤ D) (P : ObjectProperty B)
    (res : ∀ X : D, ∃ Y : B, P Y ∧ Nonempty (q.obj Y ≅ X))
    {F G : D × D ⥤ E} (a b : F ⟶ G)
    (h : ∀ Y Z : B, P Y → P Z → a.app (q.obj Y, q.obj Z) =
      b.app (q.obj Y, q.obj Z)) : a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨Y, hY, ⟨eY⟩⟩ := res X.1
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := res X.2
  let e := Iso.prod eY eZ
  apply (cancel_epi (F.map e.hom)).1
  rw [a.naturality, b.naturality, h Y Z hY hZ]

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
private theorem finiteTensor_flat_representatives (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) (n : ℕ)
    (M : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    ∃ P : CochainComplex (normalizedDVRModules l E Y n) ℤ,
      proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  let q := DerivedCategory.Q (C := normalizedDVRModules l E Y n)
  let K := q.objPreimage M
  obtain ⟨P, a, hP, hflat, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  let : QuasiIso a := ha
  refine ⟨P, ⟨hP, ?_⟩, ⟨asIso (q.map a) ≪≫ q.objObjPreimageIso M⟩⟩
  intro i
  exact (CategoryTheory.exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso
      (integralCoefficientCommRingSheaf l E Y n) (P.X i)).symm (hflat i)

section CoherenceHelpers
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open MonoidalCategory

private theorem natTrans_ext_resolving
    {B : Type u₁} [Category.{v₁} B] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (q : B ⥤ D) (P : ObjectProperty B)
    (res : ∀ X : D, ∃ Y : B, P Y ∧ Nonempty (q.obj Y ≅ X))
    {F G : D ⥤ E} (a b : F ⟶ G)
    (h : ∀ Y : B, P Y → a.app (q.obj Y) = b.app (q.obj Y)) : a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨Y, hY, ⟨eY⟩⟩ := res X
  apply (cancel_epi (F.map eY.hom)).1
  rw [a.naturality, b.naturality, h Y hY]

private theorem tripleNatTrans_ext_resolving
    {B : Type u₁} [Category.{v₁} B] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (q : B ⥤ D) (P : ObjectProperty B)
    (res : ∀ X : D, ∃ Y : B, P Y ∧ Nonempty (q.obj Y ≅ X))
    {F G : D × D × D ⥤ E} (a b : F ⟶ G)
    (h : ∀ U V W : B, P U → P V → P W →
      a.app (q.obj U, q.obj V, q.obj W) = b.app (q.obj U, q.obj V, q.obj W)) :
    a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨U, hU, ⟨eU⟩⟩ := res X.1
  obtain ⟨V, hV, ⟨eV⟩⟩ := res X.2.1
  obtain ⟨W, hW, ⟨eW⟩⟩ := res X.2.2
  let e := Iso.prod eU (Iso.prod eV eW)
  apply (cancel_epi (F.map e.hom)).1
  rw [a.naturality, b.naturality, h U V W hU hV hW]

section Paths
variable {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalCategory E]
  (F : D ⥤ E) (μ : tensor D ⋙ F ≅ (F.prod F) ⋙ tensor E)

private def assocLeftPath :
    leftAssocTensor D ⋙ F ⟶ (F.prod (F.prod F)) ⋙ rightAssocTensor E :=
  Functor.whiskerRight (associatorNatIso D).hom F ≫
    Functor.whiskerLeft ((𝟭 D).prod (tensor D)) μ.hom ≫
      Functor.whiskerRight (NatTrans.prod (𝟙 F) μ.hom) (tensor E)

private def assocRightPath :
    leftAssocTensor D ⋙ F ⟶ (F.prod (F.prod F)) ⋙ rightAssocTensor E := by
  let p₁ := CategoryTheory.Prod.fst D (D × D)
  let p₂ := CategoryTheory.Prod.snd D (D × D) ⋙ CategoryTheory.Prod.fst D D
  let p₃ := CategoryTheory.Prod.snd D (D × D) ⋙ CategoryTheory.Prod.snd D D
  let p₁₂ := p₁.prod' p₂
  exact Functor.whiskerLeft ((p₁₂ ⋙ tensor D).prod' p₃) μ.hom ≫
    Functor.whiskerRight
      (NatTrans.prod' (Functor.whiskerLeft p₁₂ μ.hom) (𝟙 (p₃ ⋙ F))) (tensor E) ≫
    Functor.whiskerLeft (F.prod (F.prod F)) (associatorNatIso E).hom

private def unitLeftPath (ε : F.obj (𝟙_ D) ≅ 𝟙_ E) :
    tensorUnitLeft D ⋙ F ⟶ F where
  app M := (μ.app (𝟙_ D, M)).hom ≫ (ε.hom ⊗ₘ 𝟙 (F.obj M)) ≫
    (λ_ (F.obj M)).hom
  naturality {M N} g := by
    have hn := μ.hom.naturality (Prod.mkHom (𝟙 (𝟙_ D)) g)
    change F.map (𝟙 (𝟙_ D) ⊗ₘ g) ≫ μ.hom.app (𝟙_ D, N) =
      μ.hom.app (𝟙_ D, M) ≫ (F.map (𝟙 (𝟙_ D)) ⊗ₘ F.map g) at hn
    rw [F.map_id] at hn
    dsimp only [tensorUnitLeft, tensorLeft, curriedTensor, Functor.comp_map]
    simp only [Iso.app_hom]
    rw [← id_tensorHom, ← Category.assoc, hn]
    simp only [Category.assoc]
    rw [id_tensorHom (F.obj (𝟙_ D)) (F.map g),
      tensorHom_id ε.hom (F.obj N), tensorHom_id ε.hom (F.obj M),
      whisker_exchange_assoc ε.hom (F.map g), leftUnitor_naturality]

private def unitRightPath (ε : F.obj (𝟙_ D) ≅ 𝟙_ E) :
    tensorUnitRight D ⋙ F ⟶ F where
  app M := (μ.app (M, 𝟙_ D)).hom ≫ (𝟙 (F.obj M) ⊗ₘ ε.hom) ≫
    (ρ_ (F.obj M)).hom
  naturality {M N} g := by
    have hn := μ.hom.naturality (Prod.mkHom g (𝟙 (𝟙_ D)))
    change F.map (g ⊗ₘ 𝟙 (𝟙_ D)) ≫ μ.hom.app (N, 𝟙_ D) =
      μ.hom.app (M, 𝟙_ D) ≫ (F.map g ⊗ₘ F.map (𝟙 (𝟙_ D))) at hn
    rw [F.map_id] at hn
    dsimp only [tensorUnitRight, tensorRight, curriedTensor, Functor.flip,
      Functor.comp_map]
    simp only [Iso.app_hom]
    rw [← tensorHom_id, ← Category.assoc, hn]
    simp only [Category.assoc]
    rw [tensorHom_id (F.map g) (F.obj (𝟙_ D)),
      id_tensorHom (F.obj N) ε.hom, id_tensorHom (F.obj M) ε.hom,
      ← whisker_exchange_assoc (F.map g) ε.hom, rightUnitor_naturality]

private theorem unitMap_unique
    (j j' : F.obj (𝟙_ D) ≅ 𝟙_ E)
    (hj : ∀ X, (μ.app (X, 𝟙_ D)).hom ≫ (𝟙 (F.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom)
    (hj' : ∀ X, (μ.app (X, 𝟙_ D)).hom ≫ (𝟙 (F.obj X) ⊗ₘ j'.hom) ≫
      (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom) : j = j' := by
  have h := (hj (𝟙_ D)).trans (hj' (𝟙_ D)).symm
  have ht : (𝟙 (F.obj (𝟙_ D)) ⊗ₘ j.hom) =
      (𝟙 (F.obj (𝟙_ D)) ⊗ₘ j'.hom) := by
    apply (cancel_mono (ρ_ (F.obj (𝟙_ D))).hom).mp
    apply (cancel_epi (μ.app (𝟙_ D, 𝟙_ D)).hom).mp
    simpa only [Category.assoc] using h
  have ht' := congrArg (fun f ↦ (j.inv ⊗ₘ 𝟙 (F.obj (𝟙_ D))) ≫ f ≫
    (j.hom ⊗ₘ 𝟙 (𝟙_ E))) ht
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id] at ht'
  have he := congrArg (fun f ↦ f ≫ (λ_ (𝟙_ E)).hom) ht'
  simp only [id_tensorHom, leftUnitor_naturality] at he
  apply Iso.ext
  exact (cancel_epi (λ_ (F.obj (𝟙_ D))).hom).mp he
end Paths

end CoherenceHelpers

section FiniteCanonical
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical finite tensor comparison, using the small-site specialization of
ringedTopoiCanonicalDerivedTensorComparison and the prescribed unit-normalized
realization. Its K-flat square is proEtaleCanonicalTensorPullback; the tensor
representative comparisons are exactly finiteIntrinsicTensorModels.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def canonicalFinitePullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@FinitePullbackTensorComparison l _ E _ _ _ X Y f n hX hY) :=
  finitePullbackTensorConstruction l E f n

-- Keep the constructed comparison sealed while elaborating its coherence equations.
attribute [local irreducible] canonicalFinitePullbackTensor

/-- Associativity is the tensor-functor square for the actual comparison μ.
Source: Stacks 07A4, signed-total proof (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: choose simultaneous flat K-flat representatives for the three inputs.
Both routes carry the pullback of (x tensor y) tensor z to
f*x tensor (f*y tensor f*z), with the same total differential. Localize the
strict equality and use the recorded representative comparisons. -/
theorem canonicalFinitePullbackTensor_associativity {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N P : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finiteDerivedPullback l E n f).map
      ((finiteIntrinsicClosed l E Y n).monoidal.associator M N P).hom ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M
        ((finiteIntrinsicDerivedTensor l E Y n).obj (N,P))).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (𝟙 _) ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) N P).hom) =
    ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
      ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) P).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom (𝟙 _)) ≫
      ((finiteIntrinsicClosed l E X n).monoidal.associator
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)
        ((finiteDerivedPullback l E n f).obj P)).hom := by
  let monoidalY : MonoidalCategory
      (proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :=
    (finiteIntrinsicClosed l E Y n).monoidal
  let monoidalX : MonoidalCategory
      (proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))) :=
    (finiteIntrinsicClosed l E X n).monoidal
  let F := finiteDerivedPullback l E n f
  let μ := finitePullbackTensorConstructionIso l E f n
  let a := assocLeftPath F μ
  let b := assocRightPath F μ
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  have hab : a = b := tripleNatTrans_ext_resolving DerivedCategory.Q
    (proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n))
    (finiteTensor_flat_representatives l E Y n) a b (by
      intro A B C hA hB hC
      exact finitePullbackTensor_associativity_representatives l E f n A B C hA hB hC)
  unfold canonicalFinitePullbackTensor
  exact NatTrans.congr_app hab (M, N, P)

/-- The unit comparison is uniquely determined by the two unit squares on μ.
Source: Stacks 03EL and 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: on module representatives the unit map identifies f*O_Y with O_X by
sending the inverse-image unit to 1. The two squares hold on pure tensors;
localization gives the displayed squares. For uniqueness, take M to be the
unit, and cancel the unitors and the invertible tensor comparison. -/
theorem canonicalFinitePullbackTensor_unit {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! ε : (finiteDerivedPullback l E n f).obj
        (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit ≅
      (finiteIntrinsicClosed l E X n).monoidal.tensorUnit,
      ∀ M : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)),
        (((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
          (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit M).hom ≫
          (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((finiteIntrinsicClosed l E X n).monoidal.leftUnitor
            ((finiteDerivedPullback l E n f).obj M)).hom =
          (finiteDerivedPullback l E n f).map
            ((finiteIntrinsicClosed l E Y n).monoidal.leftUnitor M).hom) ∧
        (((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M
          (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit).hom ≫
          (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((finiteIntrinsicClosed l E X n).monoidal.rightUnitor
            ((finiteDerivedPullback l E n f).obj M)).hom =
          (finiteDerivedPullback l E n f).map
            ((finiteIntrinsicClosed l E Y n).monoidal.rightUnitor M).hom) := by
  let monoidalY : MonoidalCategory
      (proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :=
    (finiteIntrinsicClosed l E Y n).monoidal
  let monoidalX : MonoidalCategory
      (proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))) :=
    (finiteIntrinsicClosed l E X n).monoidal
  let D := proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))
  let F := finiteDerivedPullback l E n f
  let μ := finitePullbackTensorConstructionIso l E f n
  obtain ⟨ε, hε⟩ := finitePullbackTensor_unit_representatives_exists l E f n
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  have hL : unitLeftPath F μ ε =
      Functor.whiskerRight (MonoidalCategory.leftUnitorNatIso D).hom F :=
    natTrans_ext_resolving DerivedCategory.Q
      (proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n))
      (finiteTensor_flat_representatives l E Y n) _ _ (by
        intro P hP
        exact (hε P hP).1)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  have hR : unitRightPath F μ ε =
      Functor.whiskerRight (MonoidalCategory.rightUnitorNatIso D).hom F :=
    natTrans_ext_resolving DerivedCategory.Q
      (proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n))
      (finiteTensor_flat_representatives l E Y n) _ _ (by
        intro P hP
        exact (hε P hP).2)
  unfold canonicalFinitePullbackTensor
  refine ⟨ε, ?_, ?_⟩
  · intro M
    exact ⟨NatTrans.congr_app hL M, NatTrans.congr_app hR M⟩
  · intro ε' hε'
    exact unitMap_unique F μ ε' ε (fun M ↦ (hε' M).2)
      (fun M ↦ NatTrans.congr_app hR M)

/-- Composition of pullbacks acts on the same canonical tensor comparison.
Source: Stacks 07A4 and 00YV (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: on flat K-flat representatives both sides are the sheaf pullback tensor
map for h followed by that for f, with the canonical adjunction composition
inserted. The unit formulas for the inverse images agree on every local
section. Totalize and localize this equality. -/
theorem canonicalFinitePullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    ((@canonicalFinitePullbackTensor l _ E _ _ _ Z Y (h ≫ f) n hZ hY) M N).hom ≫
      (finiteIntrinsicDerivedTensor l E Z n).map
        (Prod.mkHom
          ((sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app M)
          ((sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app N)) =
    (sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app
        ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) ≫
      (finiteDerivedPullback l E n h).map
        ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ Z X h n hZ hX)
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)).hom := by
  let F := finiteDerivedPullback l E n f
  let H := finiteDerivedPullback l E n h
  let K := finiteDerivedPullback l E n (h ≫ f)
  let TY := finiteIntrinsicDerivedTensor l E Y n
  let TZ := finiteIntrinsicDerivedTensor l E Z n
  let c := sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f
  let μf := finitePullbackTensorConstructionIso l E f n
  let μh := finitePullbackTensorConstructionIso l E h n
  let μhf := finitePullbackTensorConstructionIso l E (h ≫ f) n
  let a : TY ⋙ K ⟶ ((F ⋙ H).prod (F ⋙ H)) ⋙ TZ :=
    μhf.hom ≫ Functor.whiskerRight (NatTrans.prod c.hom c.hom) TZ
  let b : TY ⋙ K ⟶ ((F ⋙ H).prod (F ⋙ H)) ⋙ TZ :=
    Functor.whiskerLeft TY c.hom ≫ Functor.whiskerRight μf.hom H ≫
      Functor.whiskerLeft (F.prod F) μh.hom
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  have hab : a = b := tensorNatTrans_ext_resolving DerivedCategory.Q
    (proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n))
    (finiteTensor_flat_representatives l E Y n) a b (by
      intro P Q hP hQ
      exact finitePullbackTensor_composition_representatives l E f h n P Q hP hQ)
  unfold canonicalFinitePullbackTensor
  exact NatTrans.congr_app hab (M, N)

/-- Proposition form of the finite associativity equation, for use by the main statement.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def canonicalFinitePullbackTensor_associativity_condition
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
    (finiteDerivedPullback l E n f).map
      ((finiteIntrinsicClosed l E Y n).monoidal.associator M N P).hom ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M
        ((finiteIntrinsicDerivedTensor l E Y n).obj (N,P))).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (𝟙 _) ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
          N P).hom) =
    ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
      ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) P).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
          M N).hom (𝟙 _)) ≫
      ((finiteIntrinsicClosed l E X n).monoidal.associator
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)
        ((finiteDerivedPullback l E n f).obj P)).hom

/-- Proposition form of the finite unit equation, for use by the main statement.
Source: Stacks 03EL, 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def canonicalFinitePullbackTensor_unit_condition
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : (finiteDerivedPullback l E n f).obj
      (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit ≅
      (finiteIntrinsicClosed l E X n).monoidal.tensorUnit,
    ∀ M : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)),
      (((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
        (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit M).hom ≫
        (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((finiteIntrinsicClosed l E X n).monoidal.leftUnitor
          ((finiteDerivedPullback l E n f).obj M)).hom =
      (finiteDerivedPullback l E n f).map
        ((finiteIntrinsicClosed l E Y n).monoidal.leftUnitor M).hom) ∧
      (((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M
        (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit).hom ≫
        (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((finiteIntrinsicClosed l E X n).monoidal.rightUnitor
          ((finiteDerivedPullback l E n f).obj M)).hom =
      (finiteDerivedPullback l E n f).map
        ((finiteIntrinsicClosed l E Y n).monoidal.rightUnitor M).hom)

/-- Proposition form of finite pullback composition, for use by the main statement.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def canonicalFinitePullbackTensor_composition_condition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] : Prop :=
  ∀ (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
    ((@canonicalFinitePullbackTensor l _ E _ _ _ Z Y (h ≫ f) n hZ hY) M N).hom ≫
      (finiteIntrinsicDerivedTensor l E Z n).map
        (Prod.mkHom
          ((sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app M)
          ((sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app N)) =
    (sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app
        ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) ≫
      (finiteDerivedPullback l E n h).map
        ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ Z X h n hZ hX)
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)).hom

end FiniteCanonical

attribute [local irreducible] canonicalFinitePullbackTensor

section FiniteSymmetry
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical finite comparison commutes with the signed derived braiding.
Source: Stacks 07A4 and 06YS (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: on homogeneous generators of degrees p,q both composites send the
pullback of x tensor y to (-1)^(pq) f*y tensor f*x. The representative
normalizations and K-flat descent give the displayed equation for all inputs. -/
theorem canonicalFinitePullbackTensor_braiding {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finiteDerivedPullback l E n f).map
      ((pullbackTensorBraiding (ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)
        (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)).hom.app (M,N)) ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) N M).hom =
    ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom ≫
      (pullbackTensorBraiding (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
        (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)).hom.app
          ((finiteDerivedPullback l E n f).obj M,(finiteDerivedPullback l E n f).obj N) := by
  let F := finiteDerivedPullback l E n f
  let TY := finiteIntrinsicDerivedTensor l E Y n
  let TX := finiteIntrinsicDerivedTensor l E X n
  let μ := finitePullbackTensorConstructionIso l E f n
  let σY := pullbackTensorBraiding (ProEt.topology Y)
    (integralCoefficientCommRingSheaf l E Y n)
    (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)
  let σX := pullbackTensorBraiding (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n)
    (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)
  let a : TY ⋙ F ⟶ pullbackTensorSwap _ ⋙ (F.prod F) ⋙ TX :=
    Functor.whiskerRight σY.hom F ≫
      Functor.whiskerLeft (pullbackTensorSwap _) μ.hom
  let b : TY ⋙ F ⟶ pullbackTensorSwap _ ⋙ (F.prod F) ⋙ TX :=
    μ.hom ≫ Functor.whiskerLeft (F.prod F) σX.hom
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  have hab : a = b := tensorNatTrans_ext_resolving DerivedCategory.Q
    (proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n))
    (finiteTensor_flat_representatives l E Y n) a b (by
      intro P Q hP hQ
      exact finitePullbackTensor_signed_representatives l E f n P Q hP hQ)
  unfold canonicalFinitePullbackTensor
  exact NatTrans.congr_app hab (M,N)
end FiniteSymmetry

/-- Proposition form of finite signed braiding, for use by the main statement.
Source: Stacks 06YS, 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def canonicalFinitePullbackTensor_braiding_condition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
    (finiteDerivedPullback l E n f).map
      ((pullbackTensorBraiding (ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)
        (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)).hom.app (M,N)) ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) N M).hom =
    ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom ≫
      (pullbackTensorBraiding (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
        (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)).hom.app
          ((finiteDerivedPullback l E n f).obj M,(finiteDerivedPullback l E n f).obj N)

end WeilConjectures
