/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleTriangulated
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Integral constructible categories are linear over the valuation ring

Source: Weil conjectures blueprint, `def-weil-rationalization-karoubi`, its integral
linearity hypothesis (blueprint: lem-weil-integral-constructible-linear).

The section maps are specified by every finite quotient projection; their naturality
includes restriction from the terminal object, hence the map from constant global
sections. Sheaf-level scalar multiplication and linearity of the localization specify
the resulting action on derived morphisms, including morphisms created by localization.
The constructible subcategory carries precisely the inherited linear structure.
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe d u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

section CoefficientProof

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

private theorem coefficient_scalar_ext (U : Y.ProEtᵒᵖ)
    {x y : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U}
    (h : ∀ n : ℕ,
      ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E Y)
        (op n)).hom.app U) x =
      ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E Y)
        (op n)).hom.app U) y) : x = y := by
  let h₁ := CategoryTheory.Limits.isLimitOfPreserves
    (sheafToPresheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) RingCat)
    (CategoryTheory.Limits.limit.isLimit (integralCoefficientSheafSystem l E Y))
  let h₂ := CategoryTheory.Limits.isLimitOfPreserves ((evaluation _ _).obj U) h₁
  apply Concrete.isLimit_ext _ h₂
  intro n
  exact h n.unop

private theorem coefficient_scalar_naturality {U V : Y.ProEtᵒᵖ} (f : U ⟶ V)
    (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
      (integralScalarConstant l E Y U a) = integralScalarConstant l E Y V a := by
  apply coefficient_scalar_ext l E Y V
  intro n
  have hn := congrArg (fun k ↦ k.hom (integralScalarConstant l E Y U a))
    ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E Y)
      (op n)).hom.naturality f)
  change ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E Y)
      (op n)).hom.app V)
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
        (integralScalarConstant l E Y U a)) =
      (integralCoefficientSheaf l E Y n).obj.map f
        (((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E Y)
          (op n)).hom.app U) (integralScalarConstant l E Y U a)) at hn
  rw [hn]
  erw [(integralScalarConstant_existsUnique l E Y U a).exists.choose_spec n,
    (integralScalarConstant_existsUnique l E Y V a).exists.choose_spec n]
  exact (congrArg
    (fun k ↦ k.hom
      (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a)))
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).naturality f)).symm

private noncomputable abbrev coefficient_finiteConstantMap (n : ℕ) (U : Y.ProEtᵒᵖ) :=
  ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U).hom

private noncomputable def coefficient_scalarSections : Padic.coefficientExtensionIntegers l E →+*
    RingCat.sectionsSubring
      ((completedIntegralCommRingSheafUnrestricted l E Y).obj ⋙
        forget₂ CommRingCat.{max u (u + 1)} RingCat.{max u (u + 1)}) where
  toFun a := ⟨fun U ↦ integralScalarConstant l E Y U a,
    fun f ↦ coefficient_scalar_naturality l E Y f a⟩
  map_one' := by
    apply Subtype.ext
    funext U
    apply coefficient_scalar_ext l E Y U
    intro n
    erw [(integralScalarConstant_existsUnique l E Y U 1).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, OneMemClass.coe_one, Pi.one_apply, map_one]
    exact map_one (coefficient_finiteConstantMap l E Y n U)
  map_mul' a b := by
    apply Subtype.ext
    funext U
    apply coefficient_scalar_ext l E Y U
    intro n
    change _ = (CategoryTheory.Limits.limit.π
      (integralCoefficientSheafSystem l E Y) (op n)).hom.app U
        (integralScalarConstant l E Y U a * integralScalarConstant l E Y U b)
    rw [map_mul]
    erw [(integralScalarConstant_existsUnique l E Y U (a * b)).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E Y U a).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E Y U b).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, map_mul]
    exact map_mul (coefficient_finiteConstantMap l E Y n U) _ _
  map_zero' := by
    apply Subtype.ext
    funext U
    apply coefficient_scalar_ext l E Y U
    intro n
    erw [(integralScalarConstant_existsUnique l E Y U 0).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, ZeroMemClass.coe_zero, Pi.zero_apply, map_zero]
    exact map_zero (coefficient_finiteConstantMap l E Y n U)
  map_add' a b := by
    apply Subtype.ext
    funext U
    apply coefficient_scalar_ext l E Y U
    intro n
    change _ = (CategoryTheory.Limits.limit.π
      (integralCoefficientSheafSystem l E Y) (op n)).hom.app U
        (integralScalarConstant l E Y U a + integralScalarConstant l E Y U b)
    rw [map_add]
    erw [(integralScalarConstant_existsUnique l E Y U (a + b)).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E Y U a).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E Y U b).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, map_add]
    exact map_add (coefficient_finiteConstantMap l E Y n U) _ _

@[instance_reducible]
private noncomputable def coefficientModuleLinear :
    Linear (Padic.coefficientExtensionIntegers l E) (integralTowerModules l E Y) := by
  letI : Linear
      (RingCat.sectionsSubring ((completedIntegralCommRingSheafUnrestricted l E Y).obj ⋙
        forget₂ CommRingCat RingCat)) (integralTowerModules l E Y) :=
    SheafOfModules.homLinear (completedIntegralCommRingSheafUnrestricted l E Y).obj
      (completedIntegralCoefficientSheafUnrestricted l E Y).property
  exact
    { homModule := fun M N ↦ Module.compHom (M ⟶ N) (coefficient_scalarSections l E Y)
      smul_comp := fun M N P a f g ↦
        Linear.smul_comp M N P (coefficient_scalarSections l E Y a) f g
      comp_smul := fun M N P f a g ↦
        Linear.comp_smul M N P f (coefficient_scalarSections l E Y a) g }

attribute [local instance] coefficientModuleLinear

private theorem coefficientChain_eq (a : Padic.coefficientExtensionIntegers l E) :
    integralScalarChainAction l E Y a =
      (Linear.toCatCenter (Padic.coefficientExtensionIntegers l E)
        (CochainComplex (integralTowerModules l E Y) ℤ) a).asHom := by
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (integralScalarChainAction_existsUnique l E Y a).exists.choose_spec P i U x

private theorem coefficientDerived_eq (a : Padic.coefficientExtensionIntegers l E) :
    integralScalarDerivedAction l E Y a =
      (CatCenter.localization
        (Linear.toCatCenter (Padic.coefficientExtensionIntegers l E)
          (CochainComplex (integralTowerModules l E Y) ℤ) a)
        DerivedCategory.Q
        (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))).asHom := by
  unfold integralScalarDerivedAction
  rw [(existsUnique_eq (a' := _)).exists.choose_spec]
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
  intro P
  have h := NatTrans.congr_app
    ((Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
      (DerivedCategory (integralTowerModules l E Y))).map_preimage
        (X := 𝟭 _) (Y := 𝟭 _)
        (Functor.whiskerRight (integralScalarChainAction l E Y a) DerivedCategory.Q)) P
  change ((Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
      (DerivedCategory (integralTowerModules l E Y))).preimage (X := 𝟭 _) (Y := 𝟭 _)
        (Functor.whiskerRight (integralScalarChainAction l E Y a) DerivedCategory.Q)).app
      (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map ((integralScalarChainAction l E Y a).app P) at h
  change _ = (CatCenter.localization _ DerivedCategory.Q _).app (DerivedCategory.Q.obj P)
  rw [CatCenter.localization_app]
  exact h.trans (congrArg (fun k ↦ DerivedCategory.Q.map (k.app P))
    (coefficientChain_eq l E Y a))

private theorem coefficientLinear_ext
    {R : Type*} [Ring R] {C : Type*} [Category* C] [Preadditive C]
    (s t : Linear R C)
    (h : ∀ (A B : C) (a : R) (f : A ⟶ B),
      (letI := s; a • f) = (letI := t; a • f)) : s = t := by
  cases s with
  | mk s sm sc =>
    cases t with
    | mk t tm tc =>
      have heq : s = t := by
        funext A B
        exact Module.ext' _ _ (fun a f ↦ h A B a f)
      cases heq
      rfl

@[instance_reducible]
private noncomputable def coefficientDerivedLinear :=
  Localization.linear (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))

private theorem coefficientDerivedShift_linear (n : ℤ) :
    letI := coefficientDerivedLinear l E Y
    (shiftFunctor (DerivedCategory (integralTowerModules l E Y)) n).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  let := coefficientDerivedLinear l E Y
  let := Localization.functor_linear (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
  exact Shift.linear_of_localization (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)) n

end CoefficientProof

end WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

set_option linter.unusedVariables false in
/-- The coefficient action is the unique linear structure whose scalar maps are
multiplication by the actual constant sections of the completed coefficient sheaf.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear).
Proof: constant sections give a ring homomorphism to central endomorphisms of the
identity functor, characterized by their finite residues. Its ring laws can be
checked after all finite projections. Composition with these endomorphisms defines
scalar multiplication on every Hom group; centrality makes composition bilinear.
The same sectionwise action commutes with shifts on complexes. Localization at
quasi-isomorphisms preserves it by lem-weil-linear-abelian-derived-category.
The specified scalar maps determine the module structures and hence uniqueness.
Complete DAG proof plan:
1. Apply clause (2) of lem-pod-adic-limit-finite-modules to the free rank-one module $M=\mathcal
O_E$. Its finite-generation hypothesis holds because $1$ generates $M$. It identifies the
canonical reduction map $\mathcal O_E\to\varprojlim_n A_{E,n}$ with an isomorphism. This is a
ring isomorphism, since each coordinate is the quotient ring homomorphism and addition and
multiplication of compatible sequences are coordinatewise.
2. For each object $U$ of $Y_{\mathrm{proet}}$, map $a\in\mathcal O_E$ to the sequence of
constant sections $(a\bmod\varpi_E^n)_U$ in $(A_{E,n})_Y(U)$. These sections come from the
constant-presheaf-to-sheaf map in the definition of $(A_{E,n})_Y$. The reduction maps take the
$(n+1)$st coordinate to the $n$th. The sectionwise inverse-limit description therefore gives an
element $c_U(a)$ of $\widehat{\mathcal O}_{E,Y}(U)$. Coordinatewise ring operations make $c_U$ a
unital ring homomorphism, and restriction along $V\to U$ takes $c_U(a)$ to $c_V(a)$. At the
terminal object $Y$ this is precisely the stated map to global sections, using the identification
of Step 1. No equality between the constant sheaf $(\mathcal O_E)_Y$ and the completed sheaf is
asserted.
3. Put $\mathcal O=\widehat{\mathcal O}_{E,Y}$. On morphisms $f:M\to N$ of $\mathcal O$-module
sheaves set $(a f)_U(x)=c_U(a)f_U(x)$. Each $A_{E,n}$ is commutative; local representatives in
its constant sheaf therefore commute, and multiplication in their inverse limit is
coordinatewise. Hence $\mathcal O$ is commutative, so $(a f)_U$ is $\mathcal O(U)$-linear.
Semilinearity of restriction and $c_U(a)|_V=c_V(a)$ show that these components commute with
restriction. All module identities hold sectionwise: $(a+b)f=af+bf$, $a(f+g)=af+ag$,
$(ab)f=a(bf)$ and $1f=f$. For composable $f,g$, linearity of $g_U$ gives
$g_U(c_U(a)f_U(x))=c_U(a)g_U(f_U(x))$, hence $g\circ(af)=a(g\circ f)=(ag)\circ f$. Addition is
sectionwise as well. Thus the sheaf category is $\mathcal O_E$-linear; its abelian structure is
supplied by the cited module-category statement in a universe large enough for the site.
4. Apply lem-weil-linear-abelian-derived-category with $R=\mathcal O_E$ and $\mathcal
A=\Mod(\widehat{\mathcal O}_{E,Y})$, using the abelian category and scalar action of Step 3. The
derived category here is exactly $D(Y_{\mathrm{proet}},\mathcal O_E)$ by the
completed-coefficients definition. Take the localization universe from the
abstract-derived-category convention. The lemma makes this category linear, its localization
functor linear, and every integer shift linear. To identify the action, multiplication by
$c_U(a)$ on each term defines a cochain endomorphism $\mu_{a,K}$, since the differentials are
module maps; already on complexes $\mu_{a,K}=a\,\mathrm{id}_K$. Consequently
$Q(\mu_{a,K})=a\,\mathrm{id}_{QK}$. For any derived morphism $f:QK\to QL$, bilinearity now gives
$af=Q(\mu_{a,L})\circ f=f\circ Q(\mu_{a,K})$. Thus it is exactly the action through the constant
global sections constructed above, including on morphisms introduced by localization.
5. By def-weil-derived-complete-integral-detailed, $D^b_c(Y,\mathcal O_E)$ is a full subcategory
of the ambient derived category. Give each of its Hom groups exactly the ambient module
structure: sums, scalar multiples and compositions still have the same source and target, so all
module and bilinearity identities are the ambient identities. By
lem-weil-integral-constructible-triangulated it is closed under every integer shift and has the
induced triangulated structure. Its shift maps on Hom groups are therefore the ambient shift
maps, and $[m](af)=a[m](f)$ is the identity proved in Step 4. This proves the final assertion
without imposing a new boundedness, finite-Tor-dimension, or coefficient hypothesis.
-/
theorem integralCoefficientLinear_existsUnique :
    ∃! s : Linear (Padic.coefficientExtensionIntegers l E)
        (DerivedCategory (integralTowerModules l E Y)),
      (fun [linearInst : Linear (Padic.coefficientExtensionIntegers l E)
          (DerivedCategory (integralTowerModules l E Y))] ↦
        ∀ (a : Padic.coefficientExtensionIntegers l E)
          (K K' : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ K'),
          a • f = (integralScalarDerivedAction l E Y a).app K ≫ f) (linearInst := s) := by
  let s := coefficientDerivedLinear l E Y
  have hs : (fun [_linearInst : Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E Y))] ↦
      ∀ (a : Padic.coefficientExtensionIntegers l E)
        (K K' : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ K'),
        a • f = (integralScalarDerivedAction l E Y a).app K ≫ f) (_linearInst := s) := by
    intro a K K' f
    rw [coefficientDerived_eq]
    rfl
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact coefficientLinear_ext t s (fun K K' a f ↦ (ht a K K' f).trans (hs a K K' f).symm)

/-- The canonical constant-section linear structure, fixed by its scalar formula.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear). -/
noncomputable instance integralCoefficientLinear :
    Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E Y)) :=
  (integralCoefficientLinear_existsUnique l E Y).exists.choose

/-- Shift is linear for the canonical constant-section action.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear).
Proof: on complexes multiplication by a constant section commutes with translation
and its signed differential. Localization extends this equality to roofs, by
lem-weil-linear-abelian-derived-category. -/
theorem integralCoefficientShift_linear (n : ℤ) :
    (shiftFunctor (DerivedCategory (integralTowerModules l E Y)) n).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  have hs : integralCoefficientLinear l E Y = coefficientDerivedLinear l E Y := by
    apply coefficientLinear_ext
    intro K K' a f
    rw [(integralCoefficientLinear_existsUnique l E Y).exists.choose_spec]
    rw [coefficientDerived_eq]
    rfl
  rw [hs]
  exact coefficientDerivedShift_linear l E Y n

/-- Linearity of the integral constructible full subcategory is inherited by fullness.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear). -/
noncomputable instance integralConstructibleLinear (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    Linear (Padic.coefficientExtensionIntegers l E)
      (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :=
  letI : Linear (Padic.coefficientExtensionIntegers l E)
      (completedIntegralDerivedCategory l E Y D hl) := integralCoefficientLinear l E Y
  Linear.fullSubcategory (boundedConstructibleDerivedCompleteIntegral D l hl E Y)

/-- Isomorphism closure supplies the inherited integral triangulation.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear). -/
noncomputable instance integralConstructibleClosedIso (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    (boundedConstructibleDerivedCompleteIntegral D l hl E Y).IsClosedUnderIsomorphisms :=
  (boundedConstructibleDerivedCompleteIntegral_isTriangulated D l hl E Y).1

/-- Triangulated closure, specialized from the recorded integral triangulation theorem.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear). -/
noncomputable instance integralConstructibleTriangulated (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    (boundedConstructibleDerivedCompleteIntegral D l hl E Y).IsTriangulated :=
  (boundedConstructibleDerivedCompleteIntegral_isTriangulated D l hl E Y).2

/-- The inherited shift of the integral full subcategory is linear.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear).
Proof: the inherited shift acts on each underlying Hom by the ambient shift.
Use integralCoefficientShift_linear and fullness; the inherited module action is
exactly the ambient constant-section action. -/
theorem integralConstructibleShift_linear (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℤ) :
    (shiftFunctor (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) n).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  let : Linear (Padic.coefficientExtensionIntegers l E)
      (completedIntegralDerivedCategory l E Y D hl) := integralCoefficientLinear l E Y
  let P := boundedConstructibleDerivedCompleteIntegral D l hl E Y
  let R := Padic.coefficientExtensionIntegers l E
  let : (shiftFunctor (completedIntegralDerivedCategory l E Y D hl) n).Linear R :=
    integralCoefficientShift_linear l E Y n
  let : (shiftFunctor P.FullSubcategory n ⋙ P.ι).Linear R :=
    Functor.linear_of_iso R (P.ι.commShiftIso n).symm
  constructor
  intro X Z f a
  apply P.ι.map_injective
  rw [P.ι.map_smul]
  exact (shiftFunctor P.FullSubcategory n ⋙ P.ι).map_smul a f

end WeilConjectures
