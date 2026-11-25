/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting

/-! # Forgetting the constant vector-space action of a native adic module

Source: Bhatt--Scholze, Section 6.8, scalar-recovery step of the native geometry argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
variable (l : ℕ) [Fact l.Prime]

/-- The action of constant coefficient functions recovers the forgotten vector-space action.
Source: Bhatt--Scholze, Section 6.8, scalar-recovery step of the native geometry argument.
(blueprint: lem-sf-native-adic-forget-ab-equivalence).

Proof: for an abelian-sheaf module over the native function ring, let a constant scalar
act on a section by the module action of the corresponding constant function. The
module axioms give a vector space over the lifted algebraic closure. Restrictions are
linear because constants restrict to constants. The original action is balanced for
these vector spaces: associativity and commutativity identify action by a scalar on
either tensor factor. Thus the abelian tensor action factors through tensor over the
constant coefficient field, and through its sheafification, defining a native adic
module. The original tensor action is recovered on pure tensors, which generate the
sheafified tensor. Conversely in an adic module, the constant function a is a times
its unit, so its action is the original scalar action. An abelian module map commutes
with constants, hence is linear for the recovered vector spaces. These constructions
are inverse on objects up to the identity underlying section maps, and inverse on
morphisms, proving full faithfulness and essential surjectivity. For the empty test
object the section group is zero; the same constructions and identities apply. -/
theorem native_adic_forgetAb_isEquivalence (T : Scheme.{u}) :
    (ProEtale.AdicSheaf.forgetAb l T).IsEquivalence := by
  exact ProEtale.nativeScalarForgetting_isEquivalence l T

end WeilConjectures.LocallyFiniteAdicCompactSupport
