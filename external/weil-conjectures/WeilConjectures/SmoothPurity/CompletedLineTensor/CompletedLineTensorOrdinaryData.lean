/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.Algebra.Homology.Site.SiteTensorCancellation
import WeilConjectures.Algebra.Homology.Signed.SignedLineEvaluation

/-! # Ordinary signed coefficient lines and normalized scalar comparisons

Source: Bhatt--Scholze, Definitions 3.4.10 and 3.5.2, Lemma 3.4.12,
Proposition 3.5.1; blueprint sk-def-sp-tate-twist-locally-free, Proof (3).
(blueprint: lem-pur-completed-line-ordinary-data)

The signed powers and sheaf evaluations define inverse exact tensor functors.
Their exact derived functors retain the canonical localization comparisons.
`PairData` and `IsPairNormalized` record ordinary scalar comparisons and their
pure-tensor and K-flat-counit equations. Existence of normalized scalar comparisons
and all completion constructions remain in `CompletedLineTensorCoherence`.
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

/-- The signed power of a coefficient line, using the recorded ordinary powers and Hom.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-ordinary-data). -/
def power (L : integralTowerModules l E X) : ℤ → integralTowerModules l E X
  | .ofNat n => SheafOfModules.scalarTensorPower
      (completedIntegralCommRingSheafUnrestricted l E X) L n
  | .negSucc n => SheafOfModules.homObj.{max u (t + 1), t, t + 1, max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      (SheafOfModules.scalarTensorPower
        (completedIntegralCommRingSheafUnrestricted l E X) L (n + 1))
      (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)))

/-- Ordinary tensor with the signed power, before deriving or completing.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-ordinary-data). -/
def sheaf (L : integralTowerModules l E X) (m : ℤ) :
    integralTowerModules l E X ⥤ integralTowerModules l E X :=
  SheafOfModules.siteSheafTensorRight.{t, t + 1, max u (t + 1), max u (t + 1)}
    (A := completedIntegralCommRingSheafUnrestricted l E X)
    (power l E X L m)

/-- Evaluation of signed powers on sections; negative powers are the recorded sheaf Hom.
Source: Stacks 03EO (blueprint: lem-pur-completed-line-ordinary-data). -/
def pairing (L : integralTowerModules l E X) (m : ℤ) (U : X.ProEtᵒᵖ) :
    (power l E X L m).val.obj U → (power l E X L (-m)).val.obj U →
      (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U :=
  match m with
  | .ofNat 0 => fun a b ↦
      (@id ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) a) *
        (@id ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) b)
  | .ofNat (_n + 1) => fun a b ↦ b.app (op (Over.mk (𝟙 U.unop))) a
  | .negSucc _n => fun a b ↦ a.app (op (Over.mk (𝟙 U.unop))) b

/-- Pure tensor in the exact signed-line functor, with its source and target explicit.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-ordinary-data). -/
def tmul (L : integralTowerModules l E X) (m : ℤ) (M : integralTowerModules l E X)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) (a : (power l E X L m).val.obj U) :
    ((sheaf l E X L m).obj M).val.obj U :=
  SheafOfModules.siteSheafTensorTmul
    (A := completedIntegralCommRingSheafUnrestricted l E X) M (power l E X L m) U x a

/-- The existing module action, with the completed coefficient section type explicit.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-ordinary-data). -/
def smul (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
    (x : M.val.obj U) : M.val.obj U :=
  @SMul.smul _ _ (M.val.obj U).isModule.toSMul s x

section EvaluationProof

open MonoidalCategory SheafOfModules
attribute [local instance 2000] cochainModulesMonoidal

section EvaluationLocalProofs

private theorem evaluationOverSheafify (U : X.ProEt) :
    HasSheafify ((AlgebraicGeometry.Scheme.ProEt.topology X).over U)
      AddCommGrpCat.{max u (t + 1)} := by
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  exact hasSheafifyEssentiallySmallSite _ _

private theorem evaluationOverLocallyBijective (U : X.ProEt) :
    ((AlgebraicGeometry.Scheme.ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := by
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

attribute [local instance 5000] evaluationOverSheafify evaluationOverLocallyBijective

private theorem signedEvaluation (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    ∃ e : power l E X L m ⊗ power l E X L (-m) ≅ unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
          (forget₂ CommRingCat RingCat)).obj
            (completedIntegralCommRingSheafUnrestricted l E X)),
      ∀ U a b, e.hom.val.app U
        (LineEvaluation.pureTensor.{t + 1, t, u}
          (completedIntegralCommRingSheafUnrestricted l E X) _ _ U a b) =
        pairing l E X L m U a b := by
  have h := signedLineEvaluation_exists.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E X) L m
  dsimp only [power, pairing, signedLinePower, signedLinePairing,
    derivedChangeRingIndependentCoefficients] at h ⊢
  exact h

end EvaluationLocalProofs

attribute [local irreducible] power pairing

/-- The specified evaluation isomorphism, characterized before localization.
Source: Stacks 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-ordinary-data).
Proof: sheaf Hom evaluation defines the balanced pairing. In a basis and its dual
it multiplies coefficients, hence is an isomorphism. The resulting local inverse
glues. Associativity followed by evaluation and the unitor gives the displayed
natural isomorphism. Pure tensors generate locally, proving uniqueness. -/
theorem evaluation_existsUnique (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    ∃! e : sheaf l E X L m ⋙ sheaf l E X L (-m) ≅ 𝟭 _,
      ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
        (x : M.val.obj U) (a : (power l E X L m).val.obj U)
        (b : (power l E X L (-m)).val.obj U),
        (e.hom.app M).val.app U
            (tmul l E X L (-m) ((sheaf l E X L m).obj M) U
              (tmul l E X L m M U x a) b) =
          smul l E X M U (pairing l E X L m U a b) x := by
  obtain ⟨e, he⟩ := signedEvaluation l E X L m
  obtain ⟨c, hc, hu⟩ := siteTensorCancellation.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E X)
    (power l E X L m) (power l E X L (-m)) e
  have hc₀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ) (x : M.val.obj U)
      (a : (power l E X L m).val.obj U) (b : (power l E X L (-m)).val.obj U) :
      (c.hom.app M).val.app U
        (tmul l E X L (-m) ((sheaf l E X L m).obj M) U
          (tmul l E X L m M U x a) b) =
        smul l E X M U (pairing l E X L m U a b) x := by
    exact (hc M U x a b).trans
      (congrArg (fun z ↦ smul l E X M U z x) (he U a b))
  refine ⟨c, hc₀, ?_⟩
  intro c' hc'
  apply hu c'
  intro M U x a b
  exact (hc' M U x a b).trans
    (congrArg (fun z ↦ smul l E X M U z x) (he U a b)).symm

end EvaluationProof

/-- The canonical sheaf evaluation; its full section formula determines it uniquely.
Source: Stacks 03EO (blueprint: lem-pur-completed-line-ordinary-data). -/
def evaluation (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    sheaf l E X L m ⋙ sheaf l E X L (-m) ≅ 𝟭 (integralTowerModules l E X) :=
  (evaluation_existsUnique l E X L m).exists.choose

/-- Signed powers are lines, so their ordinary tensor functors are exact and additive.
Source: Stacks 03EK, 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-ordinary-data).
Proof: trivialize L on a covering. Every tensor power and its internal dual is the
unit there, including exponent zero. Tensor is thus locally the identity. Exactness
is local, and additivity follows on the sectionwise pure tensors and sheafification. -/
theorem exact (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (sheaf l E X L m).Additive ∧ PreservesFiniteLimits (sheaf l E X L m) ∧
      PreservesFiniteColimits (sheaf l E X L m) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let T := sheaf l E X L m
    let S := sheaf l E X L (-m)
    let e : T ⋙ S ≅ 𝟭 _ := evaluation l E X L m
    let f : S ⋙ T ≅ 𝟭 _ := by
      simpa only [neg_neg] using evaluation l E X L (-m)
    let equiv : integralTowerModules l E X ≌ integralTowerModules l E X :=
      CategoryTheory.Equivalence.mk T S e.symm f
    let : T.IsEquivalence := equiv.isEquivalence_functor
    refine ⟨?_, inferInstance, inferInstance⟩
    exact Functor.additive_of_preserves_binary_products T

/-- Additivity of signed line tensor. Source: blueprint Proof (3)
(blueprint: lem-pur-completed-line-ordinary-data). -/
instance additive (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (sheaf l E X L m).Additive := (exact l E X L m).1

/-- Left exactness of signed line tensor. Source: blueprint Proof (3)
(blueprint: lem-pur-completed-line-ordinary-data). -/
instance finiteLimits (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) : PreservesFiniteLimits (sheaf l E X L m) := (exact l E X L m).2.1

/-- Right exactness of signed line tensor. Source: blueprint Proof (3)
(blueprint: lem-pur-completed-line-ordinary-data). -/
instance finiteColimits (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) : PreservesFiniteColimits (sheaf l E X L m) := (exact l E X L m).2.2

/-- Tensor on all unbounded complexes is termwise tensor by the signed line.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-data). -/
def complex (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    CochainComplex (integralTowerModules l E X) ℤ ⥤
      CochainComplex (integralTowerModules l E X) ℤ :=
  (sheaf l E X L m).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The exact derived tensor functor T, with its canonical localization comparison.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-data). -/
def tensor (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    DerivedCategory (integralTowerModules l E X) ⥤
      DerivedCategory (integralTowerModules l E X) :=
  (sheaf l E X L m).mapDerivedCategory

/-- The evaluation on the unbounded derived category, with the canonical localization units.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-data). -/
def epsilon (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    tensor l E X L m ⋙ tensor l E X L (-m) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryCompIso (sheaf l E X L m) (sheaf l E X L (-m)) ≪≫
    Functor.mapDerivedCategoryNatIso (evaluation l E X L m) ≪≫
      Functor.mapDerivedCategoryIdIso _

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

/-- The canonical binary tensor comparison; its pure-tensor formula determines it uniquely.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-ordinary-data). -/
def binary : SheafOfModules.ScalarExtensionTensorCore.{t + 1, t, max u (t + 1)}
    (completedIntegralCommRingSheafUnrestricted l E X)
    (completedIntegralCommRingSheafUnrestricted l F X) (completedCoefficientMap l E F ι X) :=
  Classical.choice (SheafOfModules.exists_scalarExtensionTensorCore.{t + 1, t, max u (t + 1)}
  (completedIntegralCommRingSheafUnrestricted l E X)
  (completedIntegralCommRingSheafUnrestricted l F X) (completedCoefficientMap l E F ι X))

/-- Canonical exact localization factor for the signed-line functor.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-data). -/
def factors (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    DerivedCategory.Q ⋙ tensor l E X L m ≅ complex l E X L m ⋙ DerivedCategory.Q :=
  (sheaf l E X L m).mapDerivedCategoryFactors

attribute [local irreducible] sheaf

/-- The ordinary sheaf comparison applied termwise, without derived choices.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-data). -/
def comparisonComplex (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1] (m : ℤ)
    (e : sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m) :
    complex l E X L m ⋙ completedOrdinaryScalarComplex l E F ι X ≅
      completedOrdinaryScalarComplex l E F ι X ⋙ complex l F X N m :=
  by
    unfold complex completedOrdinaryScalarComplex
    let lift {A B C D : Type (max (t + 2) (u + 1))}
        [Category.{max (t + 1) u} A] [Category.{max (t + 1) u} B]
        [Category.{max (t + 1) u} C] [Category.{max (t + 1) u} D]
        [HasZeroMorphisms A] [HasZeroMorphisms B]
        [HasZeroMorphisms C] [HasZeroMorphisms D]
        (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
        [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
        [H.PreservesZeroMorphisms] [I.PreservesZeroMorphisms]
        (e : F ⋙ G ≅ H ⋙ I) :
        F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
          H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
      NatIso.mapHomologicalComplex e (.up ℤ)
    exact lift _ _ _ _ e

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)

/-- Ordinary scalar associativity applied termwise, with explicit complex functors.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-data). -/
def scalarAssociatorComplex
    (e : completedOrdinaryScalarExtension l E F ι X ⋙
      completedOrdinaryScalarExtension l F G j X ≅
        completedOrdinaryScalarExtension l E G (j.comp ι) X) :
    completedOrdinaryScalarComplex l E F ι X ⋙ completedOrdinaryScalarComplex l F G j X ≅
      completedOrdinaryScalarComplex l E G (j.comp ι) X :=
  by
    unfold completedOrdinaryScalarComplex
    exact Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)

attribute [local irreducible] binary epsilon tensor complex pairing
  factors comparisonComplex scalarAssociatorComplex smul tmul
  SheafOfModules.ScalarExtensionTensorCore.power SheafOfModules.scalarExtensionSection

/-- Signed-power scalar maps and their specified ordinary derived tensor comparisons.
All normalization equations are on actual sheafified tensors and the universal counits.
Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-ordinary-data). -/
def PairData (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1] :=
  (∀ m : ℤ, SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m) ×
  (∀ m : ℤ,
    sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m) ×
  (∀ m : ℤ, tensor l E X L m ⋙ completedDerivedScalarExtension l E F ι X ≅
    completedDerivedScalarExtension l E F ι X ⋙ tensor l F X N m)

variable {l E X F ι}

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-ordinary-data). -/
def PairData.line {L : integralTowerModules l E X} [L.IsFiniteLocallyFreeOfRank 1]
    {N : integralTowerModules l F X} [N.IsFiniteLocallyFreeOfRank 1]
    (d : PairData l E X F ι L N) :
    ∀ m : ℤ, SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m := d.1

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-ordinary-data). -/
def PairData.ordinarySheaf {L : integralTowerModules l E X} [L.IsFiniteLocallyFreeOfRank 1]
    {N : integralTowerModules l F X} [N.IsFiniteLocallyFreeOfRank 1]
    (d : PairData l E X F ι L N) :
    ∀ m : ℤ,
    sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m := d.2.1

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-ordinary-data). -/
def PairData.ordinary {L : integralTowerModules l E X} [L.IsFiniteLocallyFreeOfRank 1]
    {N : integralTowerModules l F X} [N.IsFiniteLocallyFreeOfRank 1]
    (d : PairData l E X F ι L N) :
    ∀ m : ℤ, tensor l E X L m ⋙ completedDerivedScalarExtension l E F ι X ≅
    completedDerivedScalarExtension l E F ι X ⋙ tensor l F X N m := d.2.2

variable (l E X F ι)

/-- The complete pure-tensor and K-flat-counit normalization of the ordinary data.
Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-ordinary-data). -/
def IsPairNormalized (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) : Prop :=
  (∀ n : ℕ,
    (d.line (Int.ofNat n)).hom = ((binary l E X F ι).power L n).hom ≫
      SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingSheafUnrestricted l F X) b.hom n) ∧
  (∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (f : (power l E X L (-Int.ofNat (n + 1))).val.obj U)
      (x : (power l E X L (Int.ofNat (n + 1))).val.obj U),
    pairing l F X N (Int.ofNat (n + 1)) U
      ((d.line (Int.ofNat (n + 1))).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) _ U t x))
      ((d.line (-Int.ofNat (n + 1))).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) _ U s f)) =
      s * t * (completedCoefficientMap l E F ι X).hom.app U
        (pairing l E X L (Int.ofNat (n + 1)) U x f)) ∧
  (∀ (m : ℤ) (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (x : M.val.obj U) (a : (power l E X L m).val.obj U),
    ((d.ordinarySheaf m).hom.app M).val.app U
        (completedScalarTensorSection l E F ι X ((sheaf l E X L m).obj M) U s
          (tmul l E X L m M U x a)) =
      tmul l F X N m ((completedOrdinaryScalarExtension l E F ι X).obj M) U
        (completedScalarTensorSection l E F ι X M U s x)
        ((d.line m).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) (power l E X L m) U 1 a))) ∧
  (∀ (m : ℤ)
      (P : (integralOperationsGoodComplex l E X).FullSubcategory),
    HEq ((completedDerivedScalarExtension l E F ι X).map
        ((factors l E X L m).hom.app P.obj) ≫
        completedScalarCounit l E F ι X ((complex l E X L m).obj P.obj) ≫
        DerivedCategory.Q.map
          ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app P.obj))
      ((d.ordinary m).hom.app (DerivedCategory.Q.obj P.obj) ≫
        (tensor l F X N m).map (completedScalarCounit l E F ι X P.obj) ≫
        (factors l F X N m).hom.app
          ((completedOrdinaryScalarComplex l E F ι X).obj P.obj)))

end CompletedLineTensor
end WeilConjectures
