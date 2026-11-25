/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.Algebra.Homology.SixFunctors.IntrinsicDerivedTensorOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.AlgebraicGeometry.Adic.ReductionDerivedChangeCoherence
import WeilConjectures.SixFunctors.Supporting.IntrinsicQbarCategory

/-! # Ordinary discrete constant-field realization

The derived-category universe parameters below are inferred where possible.

Source: Stacks Project, Tag 09C2; Bhatt--Scholze, Proposition 6.8.14(1),(2);
blueprint lem-weil-field-tor-amplitude, proof, first two sentences
(blueprint: lem-sf-field-stage-ordinary-realization).

The targets use discrete constant ring sheaves, not completed or continuous field sheaves.
The closure and the scheme have independent universes; Shrink transports coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe d u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.OrdinaryFieldRealization

/-- Discrete constant coefficients on the actual small pro-etale site.
Source: blueprint first realization formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
abbrev constantRing (Y : Scheme.{u}) (A : Type u) [CommRing A] :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} A))

/-- The ordinary ambient derived category, with no constructibility restriction.
Source: blueprint first realization formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
abbrev Ambient (Y : Scheme.{u}) (A : Type u) [CommRing A] :=
  proEtaleDerivedCategory Y A

/-- Constant sheafification of the actual lifted coefficient homomorphism.
Source: blueprint ordinary scalar extension
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def coefficientMap (Y : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : constantRing Y A ⟶ constantRing Y B :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (f.comp ULift.ringEquiv.toRingHom)))

/-- Ordinary derived tensor with the target constant coefficient ring, retaining its
new scalar action. The universal K-flat derived-change-of-rings construction is reused.
Source: Stacks Tag 06YY; blueprint scalar extension
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def extend (Y : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Ambient Y A ⥤ Ambient Y B :=
  reductionDerivedChange Y (coefficientMap Y f)

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : Scheme.{u})

/-- Restriction along the recorded constant-quotient limit lift u_E.
Source: blueprint realization formula, first proof step
(blueprint: lem-sf-field-stage-ordinary-realization). -/
abbrev integralRestriction : scalarReductionSource l E Y ⥤
    reductionModules Y (constantRing Y (Padic.coefficientExtensionIntegers l E)) :=
  SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses l E Y)

/-- Restriction along u_E preserves kernels and cokernels.
Source: blueprint realization formula, first proof step
(blueprint: lem-sf-field-stage-ordinary-realization).
Proof: underlying abelian sheaves are unchanged; kernels are sectionwise, and cokernels
are sheafified sectionwise cokernels, with only the scalar action precomposed by u_E. -/
theorem integralRestriction_exact :
    PreservesFiniteLimits (integralRestriction l E Y) ∧
      PreservesFiniteColimits (integralRestriction l E Y) := by
  let A := integralConstantRingOfUniverses l E Y
  let B := completedIntegralCoefficientSheafUnrestricted l E Y
  let U := integralRestriction l E Y
  have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf B))
  have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf B))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf A),
    preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf A)⟩

/-- Exactness supplies the required derived-restriction instance.
Source: blueprint realization formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
instance integralRestriction_limits : PreservesFiniteLimits (integralRestriction l E Y) :=
  (integralRestriction_exact l E Y).1

/-- Exactness supplies the required derived-restriction instance.
Source: blueprint realization formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
instance integralRestriction_colimits : PreservesFiniteColimits (integralRestriction l E Y) :=
  (integralRestriction_exact l E Y).2

/-- U_E is termwise restriction descended through quasi-isomorphisms.
Source: blueprint realization formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def integralDerivedRestriction : DerivedCategory (scalarReductionSource l E Y) ⥤
    Ambient Y (Padic.coefficientExtensionIntegers l E) :=
  (integralRestriction l E Y).mapDerivedCategory

/-- The prescribed integral value U_E(C) tensor^L E_Y.
Source: blueprint realization formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def integralRealization : sfIntegralConstructibleCategory l E Y ⥤ Ambient Y E :=
  (sfIntegralConstructible l E Y).ι ⋙ integralDerivedRestriction l E Y ⋙
    extend Y (algebraMap (Padic.coefficientExtensionIntegers l E) E)

private def constantSections (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    A →+* RingCat.sectionsSubring
      ((constantRing Y A).obj ⋙ forget₂ CommRingCat RingCat) where
  toFun a := ⟨fun V ↦
    ((toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app V)
        (ULift.up a), by
      intro V W f
      exact (congrArg (fun k ↦ k.hom (ULift.up a))
        ((toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} A)))).naturality f)).symm⟩
  map_one' := by
    apply Subtype.ext
    funext V
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    funext V
    exact map_mul _ _ _
  map_zero' := by
    apply Subtype.ext
    funext V
    exact map_zero _
  map_add' a b := by
    apply Subtype.ext
    funext V
    exact map_add _ _ _

@[instance_reducible]
private def constantModuleLinear (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    Linear A (reductionModules Y (constantRing Y A)) := by
  letI : Linear (RingCat.sectionsSubring
      ((constantRing Y A).obj ⋙ forget₂ CommRingCat RingCat))
      (reductionModules Y (constantRing Y A)) :=
    SheafOfModules.homLinear (constantRing Y A).obj
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (constantRing Y A)).property
  exact
    { homModule := fun M N ↦ Module.compHom (M ⟶ N) (constantSections Y A)
      smul_comp := fun M N P a f g ↦
        Linear.smul_comp M N P (constantSections Y A a) f g
      comp_smul := fun M N P f a g ↦
        Linear.comp_smul M N P f (constantSections Y A a) g }

private theorem constantLinear_ext
    {R : Type*} [Ring R] {C : Type*} [Category* C] [Preadditive C]
    (s t : Linear R C)
    (h : ∀ (M N : C) (a : R) (f : M ⟶ N),
      (letI := s; a • f) = (letI := t; a • f)) : s = t := by
  cases s with
  | mk s sm sc =>
    cases t with
    | mk t tm tc =>
      have heq : s = t := by
        funext M N
        exact Module.ext' _ _ (fun a f ↦ h M N a f)
      cases heq
      rfl

set_option linter.unusedVariables false in
/-- The standard constant-section linear structure, uniquely fixed sectionwise.
Source: blueprint E-linearity clause (blueprint: lem-sf-field-stage-ordinary-realization).
Proof: multiply each component by the image of a in the constant sheaf. Naturality
of the sheafification unit and commutativity give module maps and bilinear composition.
The displayed formula fixes every scalar action, hence every field of Linear. -/
theorem constantLinear_existsUnique (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    ∃! s : Linear A (reductionModules Y (constantRing Y A)),
      (fun [lin : Linear A (reductionModules Y (constantRing Y A))] ↦
        ∀ (M N : reductionModules Y (constantRing Y A)) (f : M ⟶ N)
          (a : A) (V : Y.ProEtᵒᵖ) (x : M.val.obj V),
          ((a • f).val.app V) x =
            ((toSheafify (ProEt.topology Y)
              ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app V)
                (ULift.up a) • f.val.app V x) (lin := s) := by
  let s := constantModuleLinear Y A
  have hs : (fun [lin : Linear A (reductionModules Y (constantRing Y A))] ↦
      ∀ (M N : reductionModules Y (constantRing Y A)) (f : M ⟶ N)
        (a : A) (V : Y.ProEtᵒᵖ) (x : M.val.obj V),
        ((a • f).val.app V) x =
          ((toSheafify (ProEt.topology Y)
            ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app V)
              (ULift.up a) • f.val.app V x) (lin := s) := by
    intro M N f a V x
    rfl
  refine ⟨s, hs, ?_⟩
  intro t ht
  have h : ∀ (M N : reductionModules Y (constantRing Y A)) (a : A) (f : M ⟶ N),
      (letI := t; a • f) = (letI := s; a • f) := by
    intro M N a f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    exact (ht M N f a V x).trans (hs M N f a V x).symm
  exact constantLinear_ext t s h

/-- Constant scalars act on module sheaves by the specified constant sections.
Source: blueprint E-linearity clause (blueprint: lem-sf-field-stage-ordinary-realization). -/
instance constantLinear (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    Linear A (reductionModules Y (constantRing Y A)) :=
  (constantLinear_existsUnique Y A).exists.choose

/-- Derived localization inherits the same constant scalar action.
Source: blueprint E-linearity clause (blueprint: lem-sf-field-stage-ordinary-realization). -/
instance ambientLinear (Y : Scheme.{u}) (A : Type u) [CommRing A] : Linear A (Ambient Y A) :=
  inferInstanceAs (Linear A (DerivedCategory (reductionModules Y (constantRing Y A))))

/-- Transport the actual localized scalar action along the recorded coefficient equivalence.
Source: blueprint raw scalar localization
(blueprint: lem-sf-field-stage-ordinary-realization). -/
instance rationalLinear : Linear E (sfRationalConstructibleCategory l E Y) :=
  Linear.ofRingMorphism
    ((Linear.toCatCenter (R := Localization.Away (Padic.coefficientExtensionUniformizer l E))
      (sfRationalConstructibleCategory l E Y)).comp
        (sfRationalCoefficientEquiv l E).symm.toRingHom)

set_option linter.defProp false in
/-- An algebraic closure of the small field Q_l has a model in every scheme universe.
This uses an existing closure equivalence only to prove size; Shrink supplies the actual
coefficient identification, so no choice of closure automorphism enters the realization.
Source: blueprint size convention
(blueprint: lem-sf-field-stage-ordinary-realization). -/
@[instance_reducible] def closureSmall (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] : Small.{u} Ω :=
  small_map (IsAlgClosure.equiv (Padic l) Ω (AlgebraicClosure (Padic l))).toEquiv

/-- The chosen closure in the site universe, identified with Ω by Shrink.algEquiv.
Source: blueprint size convention
(blueprint: lem-sf-field-stage-ordinary-realization). -/
abbrev Closure (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] : Type u :=
  @Shrink.{u} Ω (closureSmall l Ω)

/-- Transport the coefficient algebra structure along the same size equivalence.
Source: blueprint size convention
(blueprint: lem-sf-field-stage-ordinary-realization). -/
instance closureAlgebra (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] : Algebra (Padic l) (Closure.{u} l Ω) :=
  letI := closureSmall.{u} l Ω
  inferInstanceAs (Algebra (Padic l) (Shrink.{u} Ω))

/-- The actual coefficient identification; the closure itself is not replaced.
Source: blueprint size convention
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def closureEquiv (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    Closure.{u} l Ω ≃ₐ[Padic l] Ω :=
  letI := closureSmall.{u} l Ω
  Shrink.algEquiv (Padic l) Ω

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

/-- The actual inclusion of a finite coefficient model into the chosen closure model.
Source: blueprint final scalar-extension formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def closureInclusion (E : Index l Ω) : Coefficient.{u} l Ω E →ₐ[Padic l] Closure.{u} l Ω :=
  (closureEquiv l Ω).symm.toAlgHom.comp
    (E.val.val.comp (Shrink.algEquiv (Padic l) E.val).toAlgHom)

/-- Constant sheafification preserves the composition of coefficient homomorphisms.
Source: blueprint coefficient tower coherence
(blueprint: lem-sf-field-stage-ordinary-realization).
Proof: lifted homomorphisms compose on each element; apply constantSheaf.map_comp. -/
theorem coefficientMap_comp (Y : Scheme.{u}) {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    coefficientMap Y f ≫ coefficientMap Y g = coefficientMap Y (g.comp f) := by
  unfold coefficientMap
  rw [← Functor.map_comp]
  congr 1

/-- Constant sheafification sends the identity coefficient homomorphism to the identity.
Source: blueprint identity-inclusion coherence
(blueprint: lem-sf-field-stage-ordinary-realization).
Proof: the lifted identity homomorphism is the identity; apply constantSheaf.map_id. -/
theorem coefficientMap_id (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    coefficientMap Y (RingHom.id A) = 𝟙 (constantRing Y A) := by
  unfold coefficientMap
  rw [← CategoryTheory.Functor.map_id]
  congr 1

/-- The ordinary derived scalar associator is uniquely fixed by balancing on K-flat models.
Source: Stacks Tag 06YY; blueprint coefficient tower coherence
(blueprint: lem-sf-field-stage-ordinary-realization).
Proof: extension preserves K-flat complexes. The two counits compute successive tensor
products, and reductionBalance sends c tensor (b tensor x) to c*g(b) tensor x.
These maps are natural and invertible. Descend through the K-flat localization.
For an arbitrary P, use a K-flat resolution and counit naturality to obtain the same
equation. Every derived object has such a model, so this equation fixes the map. -/
theorem extendComp_existsUnique (Y : Scheme.{u}) {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    ∃! e : extend Y f ⋙ extend Y g ≅ extend Y (g.comp f),
      ∀ P : CochainComplex (reductionModules Y (constantRing Y A)) ℤ,
        e.hom.app ((DerivedCategory.Q.{u + 2, u + 1, u + 2}
          (C := reductionModules Y (constantRing Y A))).obj P) ≫
            reductionScalarComplexCounit Y (coefficientMap Y (g.comp f)) P =
          (extend Y g).map (reductionScalarComplexCounit Y (coefficientMap Y f) P) ≫
            reductionScalarComplexCounit Y (coefficientMap Y g)
              ((reductionChangeComplex Y (coefficientMap Y f)).obj P) ≫
            (DerivedCategory.Q
              (C := reductionModules Y (constantRing Y C))).map
              (reductionBalance Y (coefficientMap Y f)
              (coefficientMap Y g) (coefficientMap Y (g.comp f))
              (coefficientMap_comp Y f g) P) :=
  reductionDerivedChange_comp_existsUnique Y (coefficientMap Y f) (coefficientMap Y g)
    (coefficientMap Y (g.comp f)) (coefficientMap_comp Y f g)

/-- The counit-normalized ordinary derived tensor associator.
Source: blueprint coefficient tower coherence
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def extendComp (Y : Scheme.{u}) {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    extend Y f ⋙ extend Y g ≅ extend Y (g.comp f) :=
  (extendComp_existsUnique Y f g).exists.choose

/-- Identity scalar extension is multiplication, uniquely fixed on K-flat computations.
Source: Stacks Tag 06YY; blueprint identity-inclusion coherence
(blueprint: lem-sf-field-stage-ordinary-realization).
Proof: ordinary identity extension has the multiplication map a tensor x to a*x,
with inverse x to 1 tensor x. Local tensor generators prove the inverse equations
and naturality. Its localization composed with the universal K-flat counit is
invertible on K-flat models and descends uniquely. Counit naturality along a K-flat
resolution gives the same formula on arbitrary complexes; these also prove uniqueness. -/
theorem extendUnit_existsUnique (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    ∃! e : extend Y (RingHom.id A) ≅ 𝟭 (Ambient Y A),
      ∀ P : CochainComplex (reductionModules Y (constantRing Y A)) ℤ,
        ∃ μ : (reductionChangeComplex Y (coefficientMap Y (RingHom.id A))).obj P ⟶ P,
          (∀ (i : ℤ) (V : Y.ProEtᵒᵖ) (a : (constantRing Y A).obj.obj V)
            (x : (P.X i).val.obj V),
            (μ.f i).val.app V
              (reductionTensorSection Y (coefficientMap Y (RingHom.id A)) (P.X i) V a x) =
                a • x) ∧
          e.hom.app ((DerivedCategory.Q
          (C := reductionModules Y (constantRing Y A))).obj P) =
            reductionScalarComplexCounit Y (coefficientMap Y (RingHom.id A)) P ≫
              (DerivedCategory.Q
                (C := reductionModules Y (constantRing Y A))).map μ :=
  reductionDerivedChange_id_existsUnique Y (coefficientMap Y (RingHom.id A))
    (coefficientMap_id Y A)

/-- The multiplication-normalized identity comparison.
Source: blueprint identity-inclusion coherence
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def extendUnit (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    extend Y (RingHom.id A) ≅ 𝟭 (Ambient Y A) :=
  (extendUnit_existsUnique Y A).exists.choose

/-- The displayed coefficient inclusions compose before any scalar tensor.
Source: blueprint common-stage formula
(blueprint: lem-sf-field-stage-ordinary-realization).
Proof: substitute the Shrink algebra equivalences; inverse equivalences cancel and
subfield inclusions compose literally. This includes equal coefficient fields. -/
theorem closureInclusion_comp (E L : Index l Ω) (h : E ≤ L) :
    (closureInclusion.{u} l Ω L).comp (coefficientInclusion l Ω E L h) =
      closureInclusion l Ω E := by
  ext x
  simp [closureInclusion, coefficientInclusion]

/-- The recorded transition of the stage system is the specified rational scalar tensor.
Source: blueprint common-stage construction
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def stageIdentification (E L : Index l Ω) (h : E ≤ L) :
    GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h ≅
      GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E L h :=
  eqToIso
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω Y).exists.choose_spec.1
      E L h)

/-- The normalized identity transition, retaining the actual stage-system interface.
Source: blueprint identity-inclusion coherence
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def stageUnit (E : Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E E le_rfl ≅
      𝟭 (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :=
  stageIdentification l Y Ω E E le_rfl ≪≫
    GeneralAlgebraicallyClosedCoefficients.unitor l Ω Y E

/-- The finite stage uses exactly the field action transported from its raw localization.
Source: blueprint E-linearity clause
(blueprint: lem-sf-field-stage-ordinary-realization). -/
instance stageLinear (E : Index l Ω) : Linear (Coefficient.{u} l Ω E)
    (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :=
  rationalLinear l (Coefficient.{u} l Ω E) Y

/-- The representative Hom inherits the same finite field action, with no new choice.
Source: blueprint common-stage linearity clause
(blueprint: lem-sf-field-stage-ordinary-realization). -/
instance stageHomModule (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y)
    (L : GeneralAlgebraicallyClosedCoefficients.Common A B) :
    Module (Coefficient.{u} l Ω L.val)
      (GeneralAlgebraicallyClosedCoefficients.StageHom A B L) :=
  inferInstanceAs (Module (Coefficient.{u} l Ω L.val)
    ((GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y A.stage L.val
        L.property.1).obj A.obj ⟶
      (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y B.stage L.val
        L.property.2).obj B.obj))

/-- Scalar multiplication on a common-stage representative uses its finite-stage action.
Source: blueprint common-stage linearity clause
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def stageSmul (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y)
    (L : GeneralAlgebraicallyClosedCoefficients.Common A B)
    (a : Coefficient.{u} l Ω L.val)
    (f : GeneralAlgebraicallyClosedCoefficients.StageHom A B L) :
    GeneralAlgebraicallyClosedCoefficients.StageHom A B L :=
  letI := stageHomModule l Y Ω A B L
  a • f

set_option linter.unusedVariables false in
/-- E-linearity in the common-stage category is the scalar action on a common finite
representative. Every scalar of Ω occurs in such a finite stage. The equality displayed
here uniquely fixes the entire linear structure; it is not an arbitrary action.
Source: Bhatt--Scholze Proposition 6.8.14(2), common-stage coefficients
(blueprint: lem-sf-field-stage-ordinary-realization).
Proof: enlarge the representative field to contain the scalar. Multiply the finite
representative using its rational Hom scalar action and pass to its colimit class.
Coefficient inclusions preserve multiplication, so eventual equality makes this independent
of enlargement. Move each finite module identity and each composition to one common field.
There it is the usual field-module identity. Every scalar and morphism has a finite
representative; these formulas therefore determine the action and all linearity data. -/
theorem pairLinear_existsUnique :
    ∃! s : Linear (Closure.{u} l Ω)
        (GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y),
      (fun [lin : Linear (Closure.{u} l Ω)
          (GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y)] ↦
        ∀ (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y)
          (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
          (f : GeneralAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩)
          (a : Coefficient.{u} l Ω L),
          closureInclusion l Ω L a •
              GeneralAlgebraicallyClosedCoefficients.ofHom A B L hA hB f =
            GeneralAlgebraicallyClosedCoefficients.ofHom A B L hA hB
              (stageSmul l Y Ω A B ⟨L, hA, hB⟩ a f))
        (lin := s) := by
  classical
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y
  have hS : StageSystem.QbarScalarCompatible l Ω S := intrinsicQbarScalarCompatible l Ω Y
  -- The finite-stage action is the localized action through the field identification.
  have hstage (L : Index l Ω) (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y)
      (hA : A.stage ≤ L) (hB : B.stage ≤ L) (f : A.toStage hA ⟶ B.toStage hB)
      (a : Coefficient.{u} l Ω L) :
      stageSmul l Y Ω A B ⟨L, hA, hB⟩ a f = (Shrink.algEquiv (Padic l) L.val a) • f := by
    change (((sfRationalCoefficientEquiv l (Coefficient.{u} l Ω L)).symm a) • 𝟙 _) ≫ f =
        ((intrinsicQbarStageFieldEquiv.{u} l Ω L).symm (Shrink.algEquiv (Padic l) L.val a)) • f
    rw [Linear.smul_comp, Category.id_comp,
      show (intrinsicQbarStageFieldEquiv.{u} l Ω L).symm (Shrink.algEquiv (Padic l) L.val a) =
        (sfRationalCoefficientEquiv l (Coefficient.{u} l Ω L)).symm a by
          simp [intrinsicQbarStageFieldEquiv]]
  -- The closure action through intrinsicQbarLinear.
  let φ : Closure.{u} l Ω →+* CatCenter (GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) :=
    (Linear.toCatCenter Ω (generalAlgebraicallyClosedConstructibleCategory l Ω Y)).comp
      (closureEquiv.{u} l Ω).toRingHom
  let s : Linear (Closure.{u} l Ω) (GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) :=
    Linear.ofRingMorphism φ
  have hs (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) (c : Closure.{u} l Ω)
      (f : A ⟶ B) :
      (letI := s; c • f) = intrinsicQbarScalarAction l Ω Y (closureEquiv.{u} l Ω c) f := by
    change (closureEquiv.{u} l Ω c • 𝟙 A) ≫ f = _
    rw [Linear.smul_comp, Category.id_comp]
    exact (intrinsicQbarLinear_existsUnique l Ω Y).exists.choose_spec A B _ f
  -- The scalar formula at a stage containing the scalar.
  have hform (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y)
      (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f : GeneralAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩)
      (a : Coefficient.{u} l Ω L) :
      (letI := s; closureInclusion l Ω L a •
          GeneralAlgebraicallyClosedCoefficients.ofHom A B L hA hB f) =
        GeneralAlgebraicallyClosedCoefficients.ofHom A B L hA hB
          (stageSmul l Y Ω A B ⟨L, hA, hB⟩ a f) := by
    rw [hs]
    have hmem : closureEquiv.{u} l Ω (closureInclusion l Ω L a) ∈ L.val := by
      simp [closureInclusion]
    unfold intrinsicQbarScalarAction
    rw [StageSystem.qbarScalarHom_mkHom l Ω S hS _ L hA hB f L le_rfl hmem]
    have hself : S.tr (le_refl L) f = f :=
      (GeneralAlgebraicallyClosedCoefficients.transportSystem A B).map_self
        (i := ⟨L, hA, hB⟩) f
    rw [hself, hstage]
    congr 2
    apply Subtype.ext
    simp [closureInclusion]
  refine ⟨s, hform, ?_⟩
  intro t ht
  apply constantLinear_ext t s
  intro A B c f
  obtain ⟨L, hA, hB, u, rfl⟩ :=
    (GeneralAlgebraicallyClosedCoefficients.representatives A B).1 f
  obtain ⟨M, hM⟩ := (Padic.finiteCoefficientFields_properties l Ω).2.1
    (closureEquiv.{u} l Ω c)
  let N := Padic.finiteCoefficientCompositum l Ω L M
  have hLN : L ≤ N := ((Padic.finiteCoefficientFields_properties l Ω).1 L M).1
  have hMN : M ≤ N := ((Padic.finiteCoefficientFields_properties l Ω).1 L M).2
  let a : Coefficient.{u} l Ω N :=
    (Shrink.algEquiv (Padic l) N.val).symm ⟨closureEquiv.{u} l Ω c, hMN hM⟩
  have hc : closureInclusion l Ω N a = c := by
    apply (closureEquiv.{u} l Ω).injective
    simp [closureInclusion, a]
  have hu : GeneralAlgebraicallyClosedCoefficients.ofHom A B L hA hB u =
      GeneralAlgebraicallyClosedCoefficients.ofHom A B N (hA.trans hLN) (hB.trans hLN)
        (S.tr hLN u) :=
    (StageSystem.PairCategory.mkHom_tr hLN u).symm
  rw [hu, ← hc]
  exact (ht A B N _ _ _ a).trans (hform A B N _ _ _ a).symm

/-- The unique common-stage scalar action determined by finite representatives.
Source: blueprint Qbar-linearity clause
(blueprint: lem-sf-field-stage-ordinary-realization). -/
instance pairLinear : Linear (Closure.{u} l Ω)
    (GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) :=
  (pairLinear_existsUnique l Y Ω).exists.choose

/-- A pure tensor in the recorded finite-stage Hom coordinates.
Source: blueprint scalar-localized morphism formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def stagePureHom (E : Index l Ω)
    (C D : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E)
    (f : C.obj ⟶ D.obj) (a : Coefficient.{u} l Ω E) : C ⟶ D :=
  (sfRationalHomCoordinates l (Coefficient.{u} l Ω E) Y C D).symm
    (f ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E)] a)

/-- The required image of a pure tensor, with its ordinary target scalar action.
Source: blueprint scalar-localized morphism formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def integralScalarMap (E : Index l Ω)
    (C D : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E)
    (f : C.obj ⟶ D.obj) (a : Coefficient.{u} l Ω E) :
    (integralRealization l (Coefficient.{u} l Ω E) Y).obj C.obj ⟶
      (integralRealization l (Coefficient.{u} l Ω E) Y).obj D.obj :=
  a • (integralRealization l (Coefficient.{u} l Ω E) Y).map f

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The ordinary coefficient-composition comparison for the specified finite inclusions.
Source: blueprint composition coherence
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def fieldComp (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    extend Y (coefficientInclusion l Ω E L h).toRingHom ⋙
        extend Y (coefficientInclusion l Ω L M k).toRingHom ≅
      extend Y (coefficientInclusion l Ω E M (h.trans k)).toRingHom :=
  extendComp Y (coefficientInclusion l Ω E L h).toRingHom
      (coefficientInclusion l Ω L M k).toRingHom ≪≫
    eqToIso (congrArg (fun f ↦ extend Y f)
      (congrArg AlgHom.toRingHom
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k)))

/-- The ordinary identity comparison for the specified finite-field inclusion.
Source: blueprint identity coherence
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def fieldUnit (E : Index l Ω) :
    extend Y (coefficientInclusion l Ω E E le_rfl).toRingHom ≅
      𝟭 (Ambient Y (Coefficient.{u} l Ω E)) :=
  eqToIso (congrArg (fun f ↦ extend Y f)
    (congrArg AlgHom.toRingHom
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E))) ≪≫
    extendUnit Y (Coefficient.{u} l Ω E)

/-- Associating extension through L with direct extension to the closure.
Source: blueprint final common-stage formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def closureComp (E L : Index l Ω) (h : E ≤ L) :
    extend Y (coefficientInclusion l Ω E L h).toRingHom ⋙
        extend Y (closureInclusion.{u} l Ω L).toRingHom ≅
      extend Y (closureInclusion.{u} l Ω E).toRingHom :=
  extendComp Y (coefficientInclusion l Ω E L h).toRingHom
      (closureInclusion l Ω L).toRingHom ≪≫
    eqToIso (congrArg (fun f ↦ extend Y f)
      (congrArg AlgHom.toRingHom (closureInclusion_comp l Ω E L h)))

/-- Canonical identification of a realized pair with its realization at a larger stage.
It uses precisely the finite-stage comparison followed by ordinary tensor associativity.
Source: blueprint morphism formula over a common finite field
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def toCommon
    (J : ∀ E : Index l Ω, GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤
      Ambient Y (Coefficient.{u} l Ω E))
    (β : ∀ (E L : Index l Ω) (h : E ≤ L),
      GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h ⋙ J L ≅
        J E ⋙ extend Y (coefficientInclusion l Ω E L h).toRingHom)
    (E L : Index l Ω) (h : E ≤ L)
    (C : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    (extend Y (closureInclusion l Ω E).toRingHom).obj ((J E).obj C) ≅
      (extend Y (closureInclusion l Ω L).toRingHom).obj
        ((J L).obj ((GeneralAlgebraicallyClosedCoefficients.stageTransition
          l Ω Y E L h).obj C)) :=
  ((closureComp l Y Ω E L h).app ((J E).obj C)).symm ≪≫
    (extend Y (closureInclusion l Ω L).toRingHom).mapIso ((β E L h).app C).symm

/-- The two specified paths through a coefficient tower agree.
Source: blueprint coefficient-composition coherence
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def HasComparisonComposition
    (J : ∀ E : Index l Ω, GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤
      Ambient Y (Coefficient.{u} l Ω E))
    (β : ∀ (E L : Index l Ω) (h : E ≤ L),
      GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h ⋙ J L ≅
        J E ⋙ extend Y (coefficientInclusion l Ω E L h).toRingHom) : Prop :=
  ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (C : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E),
    (J M).map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).assoc h k).hom.app C) ≫
        (β E M (h.trans k)).hom.app C =
      (β L M k).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h).obj C) ≫
        (extend Y (coefficientInclusion l Ω L M k).toRingHom).map
          ((β E L h).hom.app C) ≫
        (fieldComp l Y Ω E L M h k).hom.app ((J E).obj C)

/-- The identity-inclusion comparison is the normalized tensor unit.
Source: blueprint identity-inclusion coherence
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def HasComparisonIdentity
    (J : ∀ E : Index l Ω, GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤
      Ambient Y (Coefficient.{u} l Ω E))
    (β : ∀ (E L : Index l Ω) (h : E ≤ L),
      GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h ⋙ J L ≅
        J E ⋙ extend Y (coefficientInclusion l Ω E L h).toRingHom) : Prop :=
  ∀ (E : Index l Ω) (C : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E),
    (β E E le_rfl).hom.app C ≫ (fieldUnit l Y Ω E).hom.app ((J E).obj C) =
      (J E).map ((stageUnit l Y Ω E).hom.app C)

/-- Each common-stage representative has the specified scalar-extended image.
Source: blueprint common-stage morphism formula
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def HasCommonMorphismFormula
    (J : ∀ E : Index l Ω, GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤
      Ambient Y (Coefficient.{u} l Ω E))
    (β : ∀ (E L : Index l Ω) (h : E ≤ L),
      GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h ⋙ J L ≅
        J E ⋙ extend Y (coefficientInclusion l Ω E L h).toRingHom)
    (JΩ : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y ⥤ Ambient Y (Closure.{u} l Ω))
    (γ : ∀ A : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y,
      JΩ.obj A ≅ (extend Y (closureInclusion l Ω A.stage).toRingHom).obj
        ((J A.stage).obj A.obj)) : Prop :=
  ∀ (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y)
    (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : GeneralAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩),
    JΩ.map (GeneralAlgebraicallyClosedCoefficients.ofHom A B L hA hB f) =
      (γ A).hom ≫ (toCommon l Y Ω J β A.stage L hA A.obj).hom ≫
        (extend Y (closureInclusion l Ω L).toRingHom).map ((J L).map f) ≫
        (toCommon l Y Ω J β B.stage L hB B.obj).inv ≫ (γ B).inv

set_option backward.isDefEq.respectTransparency false in
/-- The functors and precisely the formulas and coherence asserted by the node.
The targets are ordinary derived categories over discrete constant coefficient sheaves;
there is deliberately no constructibility predicate on their objects.
Source: Stacks Tag 09C2 and Bhatt--Scholze Proposition 6.8.14(1),(2)
(blueprint: lem-sf-field-stage-ordinary-realization). -/
structure System where
  finite : ∀ E : Index l Ω, GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤
    Ambient Y (Coefficient.{u} l Ω E)
  finite_additive : ∀ E : Index l Ω, (finite E).Additive
  finite_linear : ∀ E : Index l Ω, (finite E).Linear (Coefficient.{u} l Ω E)
  integral_objects (E : Index l Ω)
      (C : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    (finite E).obj C = (integralRealization l (Coefficient.{u} l Ω E) Y).obj C.obj
  scalar_morphisms (E : Index l Ω)
      (C D : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E)
      (f : C.obj ⟶ D.obj) (a : Coefficient.{u} l Ω E) :
    HEq ((finite E).map (stagePureHom l Y Ω E C D f a))
      (integralScalarMap l Y Ω E C D f a)
  finite_bounded (E : Index l Ω) (C : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    ∃ r s : ℤ, r ≤ s ∧ ∀ i : ℤ, i < r ∨ s < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj ((finite E).obj C))
  comparison (E L : Index l Ω) (h : E ≤ L) :
    GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h ⋙ finite L ≅
      finite E ⋙ extend Y (coefficientInclusion l Ω E L h).toRingHom
  identity : HasComparisonIdentity l Y Ω finite comparison
  composition : HasComparisonComposition l Y Ω finite comparison
  closure : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y ⥤ Ambient Y (Closure.{u} l Ω)
  closure_additive : closure.Additive
  closure_linear : closure.Linear (Closure.{u} l Ω)
  closure_objects (A : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) :
    closure.obj A ≅ (extend Y (closureInclusion l Ω A.stage).toRingHom).obj
      ((finite A.stage).obj A.obj)
  common_morphisms : HasCommonMorphismFormula l Y Ω finite comparison closure closure_objects
  closure_bounded (A : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) :
    ∃ r s : ℤ, r ≤ s ∧ ∀ i : ℤ, i < r ∨ s < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj (closure.obj A))

end WeilConjectures.OrdinaryFieldRealization
