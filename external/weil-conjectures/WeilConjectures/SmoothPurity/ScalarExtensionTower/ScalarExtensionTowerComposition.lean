/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionTensorUnit

/-! # Composition of the strict scalar comparisons

Source: Stacks Tags 03EL and 07A4
(blueprint: stage3-pur-scalar-tower-composition).

The associator multiplies successive coefficients. Checking unit generators through
the two scalar adjunctions proves both the pullback and the tensor composition equations.
`WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence`
publicly re-exports this theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.coefficientTotalTensor
  SheafOfModules.monoidalCategory
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.integralComparisonSequenceScalarModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] scalar_adj comparisons
  integralComparisonSequenceTensorSection integralComparisonSequenceScalarUnit

attribute [local irreducible] integralComparisonSequenceScalarComposition

private theorem scalar_comp_section
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (c : (coefficientSequenceCommRingSheaf.{u, u} l F W).obj.obj V)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj V)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarComposition.{u, u} l E L ι F j W).hom.app M).val.app V
        (integralComparisonSequenceTensorSection l L F j W
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.obj M) V c
          (integralComparisonSequenceTensorSection l E L ι W M V b x)) =
      integralComparisonSequenceTensorSection l E F (j.comp ι) W M V
        (c * (integralComparisonSequenceScalarMap.{u, u} l L F j W).hom.app V b) x := by
  simpa only [integralComparisonSequenceScalarComposition] using
    (integralComparisonSequenceScalarComposition_existsUnique.{u, u}
      l E L ι F j W).exists.choose_spec M V c b x

private theorem scalar_transpose_twice_section
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    (M : coefficientSequenceModules.{u, u} l E W)
    (N : coefficientSequenceModules.{u, u} l F W)
    (a : (integralComparisonSequenceScalarModel.{u, u} l L F j W).E.obj
      ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.obj M) ⟶ N)
    (V : (ℕ × W.ProEt)ᵒᵖ) (x : M.val.obj V) :
    (((scalar_adj l E L ι W).homEquiv M _)
      (((scalar_adj l L F j W).homEquiv _ N) a)).val.app V x =
      a.val.app V (integralComparisonSequenceTensorSection l L F j W
        ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.obj M) V 1
        (integralComparisonSequenceTensorSection l E L ι W M V 1 x)) := by
  exact (scalar_transpose_section l E L ι W M _ _ V x).trans
    (scalar_transpose_section l L F j W _ N a V
      (integralComparisonSequenceTensorSection l E L ι W M V 1 x))

private theorem composition_pullback (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (j : L →ₐ[ℚ_[l]] F)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CompositionSquare (pull l E f) (pull l L f) (pull l F f)
      (scalar l E L ι Y) (scalar l L F j Y) (scalar l E F (j.comp ι) Y)
      (scalar l E L ι X) (scalar l L F j X) (scalar l E F (j.comp ι) X)
      (kappa l E L ι f) (kappa l L F j f) (kappa l E F (j.comp ι) f)
      (scalarComp l E L ι F j Y) (scalarComp l E L ι F j X) := by
  unfold CompositionSquare
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro n
  apply ((scalar_adj l L F j X).homEquiv _ _).injective
  apply ((scalar_adj l E L ι X).homEquiv _ _).injective
  apply pull_hom_ext l E f (P.X n)
  intro m U x
  refine (scalar_transpose_twice_section l E L ι F j X
    ((integralComparisonSequencePullback.{u, u} l E f).obj (P.X n)) _ _
    (op (m, (Scheme.proEtaleBaseChange f).obj U))
    (pullSection l E f (P.X n) m U x)).trans ?_
  refine Eq.trans ?_ (scalar_transpose_twice_section l E L ι F j X
    ((integralComparisonSequencePullback.{u, u} l E f).obj (P.X n)) _ _
    (op (m, (Scheme.proEtaleBaseChange f).obj U))
    (pullSection l E f (P.X n) m U x)).symm
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [scalar_section_naturality l L F j X
    ((integralComparisonSequenceScalarPullback.{u, u} l E L ι f).hom.app (P.X n))]
  erw [scalar_pull_section l E L ι f (P.X n) m U x]
  erw [scalar_pull_section l L F j f
    ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj (P.X n)) m U]
  erw [pull_section_naturality l F f
    ((integralComparisonSequenceScalarComposition.{u, u}
      l E L ι F j Y).hom.app (P.X n))]
  erw [scalar_comp_section l E L ι F j Y (P.X n),
    scalar_comp_section l E L ι F j X
      ((integralComparisonSequencePullback.{u, u} l E f).obj (P.X n))]
  simp only [map_one, mul_one]
  exact (scalar_pull_section l E F (j.comp ι) f (P.X n) m U x).symm

private theorem composition_tensor (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (j : L →ₐ[ℚ_[l]] F)
    (Y : Scheme.{u}) :
    TensorCompositionSquare (tensor l E Y) (tensor l L Y) (tensor l F Y)
      (scalar l E L ι Y) (scalar l L F j Y) (scalar l E F (j.comp ι) Y)
      (scalarComp l E L ι F j Y) ((comparisons l).sigma E L ι Y)
      ((comparisons l).sigma L F j Y) ((comparisons l).sigma E F (j.comp ι) Y) := by
  unfold TensorCompositionSquare
  apply Iso.ext
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ((scalar_adj l L F j Y).homEquiv _ _).injective
  apply ((scalar_adj l E L ι Y).homEquiv _ _).injective
  apply WeilConjectures.total_tensor_sections_ext l E Y P Q n
  intro p q hpq V x y
  subst n
  refine (scalar_transpose_twice_section l E L ι F j Y
    (((tensor l E Y).obj (P, Q)).X (p + q)) _ _ V
    (generator l E Y P Q p q V x y)).trans ?_
  refine Eq.trans ?_ (scalar_transpose_twice_section l E L ι F j Y
    (((tensor l E Y).obj (P, Q)).X (p + q)) _ _ V
    (generator l E Y P Q p q V x y)).symm
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [scalar_section_naturality l L F j Y
    ((((comparisons l).sigma E L ι Y).hom.app (P, Q)).f (p + q))]
  erw [(comparisons l).sigma_formula E L ι Y P Q p q V 1 x y]
  have htotal := scalar_comp_section l E L ι F j Y
    (((tensor l E Y).obj (P, Q)).X (p + q)) V 1 1
    (generator l E Y P Q p q V x y)
  simp only [map_one, mul_one] at htotal
  refine Eq.trans ?_ (congrArg
    (fun z ↦ ((((comparisons l).sigma E F (j.comp ι) Y).hom.app (P, Q)).f
      (p + q)).val.app V z) htotal).symm
  refine Eq.trans ?_
    ((comparisons l).sigma_formula E F (j.comp ι) Y P Q p q V 1 x y).symm
  refine (congrArg
    (fun z ↦ ((((tensor l F Y).map (Prod.mkHom
      ((scalarComp l E L ι F j Y).hom.app P)
      ((scalarComp l E L ι F j Y).hom.app Q))).f (p + q)).val.app V z))
    ((comparisons l).sigma_formula L F j Y
      ((scalar l E L ι Y).obj P) ((scalar l E L ι Y).obj Q) p q V 1
      (integralComparisonSequenceTensorSection l E L ι Y (P.X p) V 1 x)
      (integralComparisonSequenceTensorSection l E L ι Y (Q.X q) V 1 y))).trans ?_
  refine (WeilConjectures.generator_map l F Y
    ((scalarComp l E L ι F j Y).hom.app P)
    ((scalarComp l E L ι F j Y).hom.app Q) p q (p + q) rfl V
    (integralComparisonSequenceTensorSection l L F j Y
      ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj (P.X p)) V 1
      (integralComparisonSequenceTensorSection l E L ι Y (P.X p) V 1 x))
    (integralComparisonSequenceTensorSection l L F j Y
      ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj (Q.X q)) V 1
      (integralComparisonSequenceTensorSection l E L ι Y (Q.X q) V 1 y))).trans ?_
  have hP := scalar_comp_section l E L ι F j Y (P.X p) V 1 1 x
  have hQ := scalar_comp_section l E L ι F j Y (Q.X q) V 1 1 y
  simp only [map_one, mul_one] at hP hQ
  exact congrArg₂
    (generator l F Y ((scalar l E F (j.comp ι) Y).obj P)
      ((scalar l E F (j.comp ι) Y).obj Q) p q V) hP hQ

-- Compare successive scalar extensions on homogeneous tensor generators.
/-- Direct and successive scalar comparisons agree before passing to derived limits.
Source: node proof step 7; Stacks 03EL, 07A4
(blueprint: stage3-pur-scalar-tower-composition).
Proof: the coefficient map for E to F is the composite of those for E to L and
L to F. The scalar associator sends d tensor (b tensor x) to d*j(b) tensor x.
The two pullback routes therefore multiply exactly these coefficients. For tensor,
both routes send d tensor (b tensor (x tensor y)) to
(d*j(b) tensor x) tensor (1 tensor y). Balancing, sheafification and direct sums
extend these equations. Reductions preserve multiplication and one, so these are
identities of strict systems, including their inverses. -/
theorem composition (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (j : L →ₐ[ℚ_[l]] F)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CompositionSquare (pull l E f) (pull l L f) (pull l F f)
      (scalar l E L ι Y) (scalar l L F j Y) (scalar l E F (j.comp ι) Y)
      (scalar l E L ι X) (scalar l L F j X) (scalar l E F (j.comp ι) X)
      (kappa l E L ι f) (kappa l L F j f) (kappa l E F (j.comp ι) f)
      (scalarComp l E L ι F j Y) (scalarComp l E L ι F j X) ∧
    TensorCompositionSquare (tensor l E Y) (tensor l L Y) (tensor l F Y)
      (scalar l E L ι Y) (scalar l L F j Y) (scalar l E F (j.comp ι) Y)
      (scalarComp l E L ι F j Y) ((comparisons l).sigma E L ι Y)
      ((comparisons l).sigma L F j Y) ((comparisons l).sigma E F (j.comp ι) Y) := by
  exact ⟨composition_pullback l E L ι F j f, composition_tensor l E L ι F j Y⟩

end WeilConjectures.ScalarExtensionTower
