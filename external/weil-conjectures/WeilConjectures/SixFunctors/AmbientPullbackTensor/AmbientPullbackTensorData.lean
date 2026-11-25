/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData
import WeilConjectures.AlgebraicGeometry.SixFunctors.SitePullbackTensorGenerators
import WeilConjectures.SixFunctors.IndependentTensorModel.ExactTensorModelConstructionIndependent
import all WeilConjectures.SixFunctors.TensorModelUniqueness.TensorComparisonModelUniqueness
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-! # Components of ambient pullback coherence

Source: Stacks 03CB, 03D3, 03EL, 07A4 and 04VG.
(blueprint: lem-sf-ambient-tensor-data-exists-unique).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
private theorem normalizedTensorBundle.{c, v, r}
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (U : C ⥤ D) [U.IsContinuous J K] [RepresentablyFlat U]
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf K CommRingCat.{max c v r})
    (phi : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{max c v r} J K).obj S)
    (F : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
      SemilinearSections.Mod.{c, v, max c v r} K S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ SheafOfModules.pushforward.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map phi))
    (A : SemilinearSections.Closed.{c, v, r} J R)
    (B : SemilinearSections.Closed.{c, v, r} K S)
    (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} K S B) :
    ∃! data : BundledTensorComparison.{c, v, r} J K R S F A B TA TB,
      OrdinaryTensorNormalized J K U R S phi F adj data.model.ordinary ∧
      (∀ P Q, IsIso (data.model.chain P Q)) ∧
      ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
        P.IsKFlatIndependentCoefficients → flatTerms.{c, v, r} J R P →
        CochainComplex.IsKFlatIndependentCoefficients
            ((F.mapHomologicalComplex (.up ℤ)).obj P) ∧
          flatTerms.{c, v, r} K S ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨od, _, hod⟩ := sitePullbackTensorGenerators.{c, v, max c v r} J K U R S phi F adj
  obtain ⟨mu, model, ho, hc⟩ := IndependentTensorModel.modelOfOrdinary.{c, v, r}
    J K R S F _ adj A B TA TB od.ordinary
    (fun a b ↦ od.normalized.2 _ _ _ _ a b) (fun P hp hf ↦ (od.flat P hp hf).1)
  let data : BundledTensorComparison.{c, v, r} J K R S F A B TA TB := ⟨mu, model⟩
  have hn : OrdinaryTensorNormalized J K U R S phi F adj model.ordinary := by
    rw [ho]
    exact od.normalized
  refine ⟨data, ⟨hn, hc, od.flat⟩, ?_⟩
  intro other hother
  have he : other.model.ordinary = model.ordinary := by
    rw [ho]
    exact congrArg (fun z ↦ z.ordinary)
      (hod ⟨other.model.ordinary, hother.1, od.flat⟩ trivial)
  exact TensorModelUniqueness.bundled_unique.{c, v, r} J K R S F A B TA TB other data he

/-- Tensor operations use the existing ordinary, K-flat and closed derived models.
Source: Stacks 03EL and 07A4 (blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
abbrev Tensor (X : Scheme.{t}) (s : Option ℕ) :=
  WeilConjectures.SemilinearSections.Closed.{t + 1, t, u} (topology X s) (coefficients ell E X s)

/-- The representative model fixes the meaning of derived tensor, rather than its coordinates.
Source: Stacks 07A4 (blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
abbrev TensorModels (X : Scheme.{t}) (s : Option ℕ) (A : Tensor ell E X s) :=
  WeilConjectures.SemilinearSections.Models.{t + 1, t, u} (topology X s) (coefficients ell E X s) A

/-- Ordinary sheaf tensor, reusing the dependency's monoidal structure.
Source: Stacks 03EK (blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
abbrev tensor (X : Scheme.{t}) (s : Option ℕ) :=
  ordinaryTensor.{t + 1, t, u} (topology X s) (coefficients ell E X s)

/-- Tensor of module morphisms in the same ordinary tensor.
Source: Stacks 03EK (blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
abbrev tensorHom (X : Scheme.{t}) (s : Option ℕ) :=
  @ordinaryTensorHom.{t + 1, t, u} _ _ (topology X s) _ (coefficients ell E X s)

/-- Actual sheafified pure tensor section. Source: Stacks 03EK
(blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
abbrev pure (X : Scheme.{t}) (s : Option ℕ) :=
  fun (M N : Modules ell E X s) (U : (Site X s)ᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) ↦
    (tensorSectionAtSize.{t + 1, t, max u (t + 1)}
      (topology X s) (coefficients ell E X s) M N U x y :
        (tensor ell E X s M N).val.obj U)

/-- Unbounded total tensor; the second differential has sign (-1)^p.
Source: Stacks 06YN (blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
abbrev total (X : Scheme.{t}) (s : Option ℕ) :=
  totalTensor.{t + 1, t, u} (topology X s) (coefficients ell E X s)

/-- K-flat flat-term representative class, with no condition on coefficient transitions.
Source: Stacks 06YS and 0G7E (blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
def FlatRepresentative (X : Scheme.{t}) (s : Option ℕ)
    (P : CochainComplex (Modules ell E X s) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
      (J := topology X s) (R := coefficients ell E X s) P ∧
    flatTerms.{t + 1, t, u} (topology X s) (coefficients ell E X s) P

/-- The comparison and its chain-level computation on the actual ringed site.
Source: Stacks 03EL and 07A4 (blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
abbrev TensorData {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    (A : Tensor ell E Y s) (B : Tensor ell E X s)
    (TA : TensorModels ell E Y s A) (TB : TensorModels ell E X s B) :=
  BundledTensorComparison.{t + 1, t, u} (topology Y s) (topology X s)
    (coefficients ell E Y s) (coefficients ell E X s) (pull ell E f s) A B TA TB

/-- The normalization determining both the ordinary and derived comparison.
Source: Stacks 03EL and 07A4 (blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
def TensorData.Normalized {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    (A : Tensor ell E Y s) (B : Tensor ell E X s)
    (TA : TensorModels ell E Y s A) (TB : TensorModels ell E X s B)
    (K : TensorData ell E f s A B TA TB) : Prop :=
  (∀ (M N : Modules ell E Y s) (U : Site Y s) (V : Site X s)
      (a : V ⟶ (base f s).obj U) (x : M.val.obj (op U)) (y : N.val.obj (op U))
      (r : (coefficients ell E X s).obj.obj (op V)),
    ((K.model.ordinary M N).hom.val.app (op V))
        (generator ell E f s (tensor ell E Y s M N) U V a (pure ell E Y s M N (op U) x y) r) =
      pure ell E X s ((pull ell E f s).obj M) ((pull ell E f s).obj N) (op V)
        (generator ell E f s M U V a x r) (generator ell E f s N U V a y 1)) ∧
  (∀ (M M' N N' : Modules ell E Y s) (a : M ⟶ M') (b : N ⟶ N'),
    (pull ell E f s).map (tensorHom ell E Y s a b) ≫ (K.model.ordinary M' N').hom =
      (K.model.ordinary M N).hom ≫
        tensorHom ell E X s ((pull ell E f s).map a) ((pull ell E f s).map b)) ∧
  (∀ P Q : CochainComplex (Modules ell E Y s) ℤ, IsIso (K.model.chain P Q)) ∧
  ∀ (P : CochainComplex (Modules ell E Y s) ℤ), FlatRepresentative ell E Y s P →
    FlatRepresentative ell E X s (((pull ell E f s).mapHomologicalComplex (.up ℤ)).obj P)

/-- Unique canonical tensor comparison with its full ordinary/total/derived normalization.
Source: Stacks 03EL, 07A4, 0G7E and 0G7D
(blueprint: lem-sf-ambient-tensor-data-exists-unique).
Proof: on scalar-extension generators send (x tensor y) tensor r to
(x tensor r) tensor (y tensor 1); the inverse multiplies the two scalars.
Balancing and sheafification prove uniqueness, naturality and the inverse laws.
The normalized ordinary maps on each total summand commute with the signed
 differential, so give the unique chain map in TensorComparisonModel. Pullback
preserves K-flat flat-term representatives by 0G7E. Use their tensor models to
localize the chain map, and the resolving-subcategory tensor descent theorem to
extend uniquely to every unbounded pair. Apply this on the sequence site itself,
so arbitrary transitions are included before any evaluation. -/
theorem tensorData_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    (A : Tensor ell E Y s) (B : Tensor ell E X s)
    (TA : TensorModels ell E Y s A) (TB : TensorModels ell E X s B) :
    ∃! K : TensorData ell E f s A B TA TB, K.Normalized ell E f s A B TA TB := by
  have : RepresentablyFlat (base f s) := by
    cases s with
    | some n =>
      change RepresentablyFlat (Scheme.proEtaleBaseChange f)
      exact flat_of_preservesFiniteLimits _
    | none =>
      have : RepresentablyFlat (Scheme.proEtaleBaseChange f) :=
        flat_of_preservesFiniteLimits _
      change RepresentablyFlat ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange f))
      constructor
      intro U
      exact IsCofiltered.of_equivalence
        (StructuredArrow.prodEquivalence U.1 U.2 (𝟭 ℕ)
          (Scheme.proEtaleBaseChange f)).symm
  obtain ⟨data, hd, huniq⟩ := normalizedTensorBundle.{t + 1, t, u}
    (topology Y s) (topology X s) (base f s)
    (coefficients ell E Y s) (coefficients ell E X s) (ringUnit ell E f s)
    (pull ell E f s) (adjunction ell E f s) A B TA TB
  have generator_one (N : Modules ell E Y s) (U : Site Y s) (V : Site X s)
      (a : V ⟶ (base f s).obj U) (y : N.val.obj (op U)) :
      generator ell E f s N U V a y 1 =
        ((pull ell E f s).obj N).val.map a.op
          (((adjunction ell E f s).unit.app N).val.app (op U) y) :=
    one_smul ((ring (topology X s) (coefficients ell E X s)).obj.obj (op V))
      (show ((pull ell E f s).obj N).val.obj (op V) from
        ((pull ell E f s).obj N).val.map a.op
          (((adjunction ell E f s).unit.app N).val.app (op U) y))
  have hn : TensorData.Normalized ell E f s A B TA TB data := by
    refine ⟨?_, ?_, hd.2.1, ?_⟩
    · intro M N U V a x y r
      rw [generator_one]
      dsimp only [generator, tensor, pure, Modules]
      exact hd.1.1 M N U V a x y r
    · intro M M' N N' a b
      exact hd.1.2 M M' N N' a b
    · intro P hp
      exact hd.2.2 P hp.1 hp.2
  refine ⟨data, hn, ?_⟩
  intro other ho
  apply huniq other
  refine ⟨⟨?_, ho.2.1⟩, ho.2.2.1, ?_⟩
  · intro M N U V a x y r
    have h := ho.1 M N U V a x y r
    rw [generator_one] at h
    dsimp only [generator, tensor, pure, Modules] at h
    exact h
  · intro P hp hf
    exact ho.2.2.2 P ⟨hp, hf⟩

/-- The unique representative-normalized tensor comparison, including its chain model.
Source: Stacks 07A4 (blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
def tensorData {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    (A : Tensor ell E Y s) (B : Tensor ell E X s)
    (TA : TensorModels ell E Y s A) (TB : TensorModels ell E X s B) :=
  (tensorData_existsUnique ell E f s A B TA TB).exists.choose

/-- The termwise compositor, constructed by the existing map on complexes.
Source: Stacks 015F (blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
abbrev chainComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ)
    (P : CochainComplex (Modules ell E Z s) ℤ) :=
  Functor.mapHomologicalComplexCompIsoHomOfIso (comp ell E f g s) P

/-- The ordinary and derived compositor laws, including both identity cases.
Source: Stacks 03CB and Categories 0B65
(blueprint: lem-sf-ambient-tensor-data-exists-unique). -/
def CompositionLaws (K : Scheme.{t}) (s : Option ℕ) : Prop :=
  (∀ {W X Y Z : Scheme.{t}} (w : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
      (aW : W ⟶ K) (aX : X ⟶ K) (aY : Y ⟶ K) (aZ : Z ⟶ K)
      [LocallyOfFiniteType aW] [QuasiCompact aW] [LocallyOfFiniteType aX]
      [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      [LocallyOfFiniteType aZ] [QuasiCompact aZ]
      (_hw : w ≫ aX = aW) (_hf : f ≫ aY = aX) (_hg : g ≫ aZ = aY)
      (M : Modules ell E Z s),
    (pull ell E w s).map ((comp ell E f g s).hom.app M) ≫
        (comp ell E w (f ≫ g) s).hom.app M =
      (comp ell E w f s).hom.app ((pull ell E g s).obj M) ≫
        (comp ell E (w ≫ f) g s).hom.app M ≫
        eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M) (Category.assoc w f g))) ∧
  (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX]
      [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Modules ell E Y s),
    (pull ell E f s).map ((identity ell E Y s).hom.app M) =
      (comp ell E f (𝟙 Y) s).hom.app M ≫
        eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M) (Category.comp_id f))) ∧
  (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX]
      [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Modules ell E Y s),
    (identity ell E X s).hom.app ((pull ell E f s).obj M) =
      (comp ell E (𝟙 X) f s).hom.app M ≫
        eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M) (Category.id_comp f))) ∧
  (∀ {W X Y Z : Scheme.{t}} (w : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
      (aW : W ⟶ K) (aX : X ⟶ K) (aY : Y ⟶ K) (aZ : Z ⟶ K)
      [LocallyOfFiniteType aW] [QuasiCompact aW] [LocallyOfFiniteType aX]
      [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      [LocallyOfFiniteType aZ] [QuasiCompact aZ]
      (_hw : w ≫ aX = aW) (_hf : f ≫ aY = aX) (_hg : g ≫ aZ = aY)
      (M : Derived ell E Z s),
    (derivedPull ell E w s).map ((derivedComp ell E f g s).hom.app M) ≫
        (derivedComp ell E w (f ≫ g) s).hom.app M =
      (derivedComp ell E w f s).hom.app ((derivedPull ell E g s).obj M) ≫
        (derivedComp ell E (w ≫ f) g s).hom.app M ≫
        eqToHom (congrArg (fun a ↦ (derivedPull ell E a s).obj M) (Category.assoc w f g))) ∧
  (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX]
      [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Derived ell E Y s),
    (derivedPull ell E f s).map ((derivedIdentity ell E Y s).hom.app M) =
      (derivedComp ell E f (𝟙 Y) s).hom.app M ≫
        eqToHom (congrArg (fun a ↦ (derivedPull ell E a s).obj M) (Category.comp_id f))) ∧
  ∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX]
      [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Derived ell E Y s),
    (derivedIdentity ell E X s).hom.app ((derivedPull ell E f s).obj M) =
      (derivedComp ell E (𝟙 X) f s).hom.app M ≫
        eqToHom (congrArg (fun a ↦ (derivedPull ell E a s).obj M) (Category.id_comp f))

end WeilConjectures.AmbientPullbackTensor
