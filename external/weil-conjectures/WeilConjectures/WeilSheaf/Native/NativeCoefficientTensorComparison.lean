/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.AlgebraicGeometry.Native.NativeModuleConstructibilityComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorIdentification
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal

/-! # Coefficient transport of the ordinary relative derived tensor

Source: the internal-Hom paragraph of `lem-fix-weil-operations.proof.md`, and
steps 2--3 of the native geometric Hom comparison.
(blueprint: lem-sf-native-coefficient-tensor-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Opposite WeilConjectures

namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The coefficient equivalence carries ordinary product-total derived tensor to
condensed-module derived tensor. The source tensor is fixed by its K-flat model,
including the reversed input convention of `ordinaryTensorBifunctor`.

Source: current blueprint, `lem-fix-weil-operations.proof.md`, internal-Hom paragraph;
`lem-sf-native-geometric-hom-comparison`, proof steps 2--3; Stacks Tags 06YS and 08J9.
(blueprint: lem-sf-native-coefficient-tensor-comparison).

Proof: The natural ordinary Hom representatives determine the right adjoint of
standard derived tensor. Uniqueness of left adjoints therefore identifies the
specified source tensor with the standard derived module tensor. To equip
ambient scalar forgetting with a monoidal structure, construct its left adjoint
as free ambient modules followed by extension along the coefficient counit.
Both factors are strong monoidal. Scalar forgetting is an equivalence, so the
inverse monoidal structure on this left adjoint transfers back to forgetting
by uniqueness of right adjoints. Restriction along the coefficient ring
isomorphism is strong monoidal and an equivalence too. Thus their composite is
an additive exact monoidal equivalence and preserves flat objects. Apply the
existing generic derived monoidal comparison, which is invertible for such a
functor and is built on K-flat resolutions. First use the native derived
braiding to change the fixed-right source convention to the fixed-left target
convention. The result applies to unbounded complexes, zero objects and the
empty scheme. No constructibility or Frobenius datum is used. -/
theorem nativeCoefficient_tensorComparison (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
        DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H)
    (β : @SymmetricCategory _ _ S.monoidal)
    (_hModels : NativeOrdinaryTensorModels l Y H R S β) :
    let F := (ProEtale.AdicSheaf.forgetAb l Y ⋙
      Mod.comap (ProEtale.nativeModuleCoefficientIso l Y).hom).mapDerivedCategory
    ∀ P : DerivedCategory (ProEtale.AdicSheaf l Y),
      Nonempty (@MonoidalCategory.tensorRight _ _ S.monoidal P ⋙ F ≅
        F ⋙ (ProEtale.CondensedRing.derivedTensor
          (Profinite.padicAlgClRingObj l) Y).obj (F.obj P)) := by
  classical
  let U := ProEtale.AdicSheaf.forgetAb l Y
  let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (ProEtale.nativeModuleCoefficientIso l Y).hom
  obtain ⟨c⟩ := ProEtale.nativeScalarForgetting_monoidal l Y
  let : U.Monoidal := c
  have : U.IsEquivalence := ProEtale.nativeScalarForgetting_isEquivalence l Y
  have : V.IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (ProEtale.nativeModuleCoefficientIso l Y).hom).isEquivalence_functor
  let E := U ⋙ V
  let : E.Monoidal := inferInstanceAs (U ⋙ V).Monoidal
  have : E.IsEquivalence := inferInstance
  have : E.PreservesFlat := Functor.preservesFlat_of_isEquivalence E
  intro _F P
  obtain ⟨e⟩ := nativeOrdinary_tensorRight_iso l Y H R S P
  let : BraidedCategory (DerivedCategory (ProEtale.AdicSheaf l Y)) :=
    (DerivedCategory.nonempty_braidedCategory (ProEtale.AdicSheaf l Y)).some
  exact ⟨Functor.isoWhiskerRight
      (e ≪≫ (BraidedCategory.tensorLeftIsoTensorRight P).symm) E.mapDerivedCategory ≪≫
    asIso (E.mapDerivedCategoryTensorComparison.app P)⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
