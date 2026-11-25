/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCoefficientInverseImage
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeAdicForgetAbEquivalence
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeDirectImageSections
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetMonoidalAdjunction
import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
import WeilConjectures.CategoryTheory.Sites.SheafComposeBraided

/-! # Native locally finite coefficient transport

Source: Bhatt--Scholze, Section 6.8; Stacks Tags 03D6, 03D7 and 03DI.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

private theorem native_commutative (T : Scheme.{u}) : IsCommMonObj (abRing l T) := by
  haveI : IsCommMonObj (ProEtale.adicConstantSheaf l T) :=
    ProEtale.adicConstantSheaf.isCommMonObj T
  let _ : (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}).LaxBraided :=
    ModuleCat.laxBraidedForget₂Ab _
  letI : (ProEtale.weilCoefficientsForgetAb l T).LaxBraided :=
    CategoryTheory.sheafComposeLaxBraided _ _
  exact Functor.isCommMonObj_obj (F := ProEtale.weilCoefficientsForgetAb l T)

/-- The native section presentation respects pullback, direct image and open extension.
Source: Bhatt--Scholze, Section 6.8, and Stacks Tags 03D6, 03D7, 03DI.
(blueprint: lem-sf-native-compact-support-geometry).

Proof: forget the constant algebraic-closure vector-space action on a native internal
module. Restriction along constant functions recovers this action, so this is an exact
additive equivalence with modules over the underlying abelian coefficient ring.
The section-module equivalence then gives sections. Pointwise commutativity of locally
finite functions supplies the commutative ring object. Precomposition along base change
identifies the inverse-image coefficient ring with the coefficient ring on the source:
locally finite functions are the sheaf colimit of the finite-subextension-valued
continuous functions, whose inverse-image identifications are compatible with inclusions.
The structural ring map is precomposition on functions, giving pull_normalized.
Both direct images evaluate the same module on the same base-changed test object;
the comparison is identity on sections. Conjugate the native pullback adjunction through
the section equivalences and use uniqueness of left adjoints for upper. Its mate is
therefore this lower comparison. Repeat for the open-extension adjunction to obtain
extension, whose mate is upper. The equivalences preserve finite limits and colimits
and addition. These constructions give every field of NativeGeometry simultaneously,
for all schemes and morphisms; no finite-type or separatedness hypothesis is used. -/
theorem native_compact_support_geometry : Nonempty (NativeGeometry.{u} l) := by
  classical
  let commutative : ∀ T : Scheme.{u}, IsCommMonObj (abRing l T) :=
    native_commutative l
  let pull {U V : Scheme.{u}} (g : U ⟶ V) :=
    (native_coefficient_inverse_image l g).choose
  let N : NativeRings.{u} l :=
    { commutative := commutative
      pull := pull
      pull_normalized := fun g ↦ (native_coefficient_inverse_image l g).choose_spec.1 }
  have equivalence (T : Scheme.{u}) : (sections l T).IsEquivalence := by
    have := native_adic_forgetAb_isEquivalence l T
    unfold sections
    infer_instance
  have additive (T : Scheme.{u}) : (sections l T).Additive :=
    Functor.additive_of_preserves_binary_products (sections l T)
  let lower {U V : Scheme.{u}} (g : U ⟶ V) :=
    (native_direct_image_sections l g).choose
  let upperExists {U V : Scheme.{u}} (g : U ⟶ V) :=
    exists_equivalenceAdjunctionComparison
      (sections l V).asEquivalence (sections l U).asEquivalence
      (ProEtale.adicUpperStarLowerStarAdjunction l g)
      (proEtaleRingModuleAdjunction g (ringSheaf l V) (ringSheaf l U) (N.pull g))
      (lower g)
  let upper {U V : Scheme.{u}} (g : U ⟶ V) := (upperExists g).choose
  let extensionExists {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :=
    exists_equivalenceAdjunctionComparison
      (sections l U).asEquivalence (sections l V).asEquivalence
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l j)
      (PurCompactSupport.openAdjunction (nativeCoefficients l) j) (upper j)
  let extension {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :=
    (extensionExists j).choose
  exact ⟨{
    toNativeRings := N
    additive := additive
    limits := fun T ↦ inferInstance
    colimits := fun T ↦ inferInstance
    equivalence := equivalence
    lower := lower
    lower_normalized := fun g ↦ (native_direct_image_sections l g).choose_spec.1
    upper := upper
    upper_normalized := fun g ↦ (upperExists g).choose_spec.1
    extension := extension
    extension_normalized := fun j ↦ (extensionExists j).choose_spec.1 }⟩

end WeilConjectures.LocallyFiniteAdicCompactSupport
