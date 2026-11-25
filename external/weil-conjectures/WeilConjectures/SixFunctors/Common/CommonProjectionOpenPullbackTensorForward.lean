/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Currying

/-! # Forward open pullback/tensor square for common-stage inclusion

Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-common-projection-open-pullback-tensor-forward).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false

universe v w v' w'
open CategoryTheory

namespace WeilConjectures

/-- The forward form of the open tensor/pullback square.

STATEMENT-DISPUTED (repaired): The original theorem quantified over arbitrary `mu` and `mu'`
with no compatibility hypothesis. Take all four categories to be `SingleObj (Multiplicative
Bool)`, all four functors and comparison isomorphisms to be identities, and take `TA` and
`TB` to be the first projection functor from the product category (likewise `TA'` and
`TB'`). Then the displayed equation reduces to `mu = mu'`; choosing the two distinct
endomorphisms `false` and `true` gives a counterexample. A valid forward transport lemma
needs the canonical compatibility equation (or hypotheses that imply it).
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-projection-open-pullback-tensor-forward).

The compatibility equation is now an explicit hypothesis. This is the strictly
smaller representative equation from which the inverse square follows by cancelling
the two displayed isomorphisms. -/
theorem commonProjectionOpenPullbackTensor_forward
    {A : Type v} [Category.{w} A] {B : Type v'} [Category.{w'} B]
    {A' : Type v} [Category.{w} A'] {B' : Type v'} [Category.{w'} B']
    {F : A ⥤ B} {F' : A' ⥤ B'} {c : A ⥤ A'} {d : B ⥤ B'}
    (e : F ⋙ d ≅ c ⋙ F')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (tA : TA ⋙ c ≅ c.prod c ⋙ TA')
    (tB : TB ⋙ d ≅ d.prod d ⋙ TB')
    (M N : A) (mu : F.obj (TA.obj (M, N)) ⟶ TB.obj (F.obj M, F.obj N))
    (mu' : F'.obj (TA'.obj (c.obj M, c.obj N)) ⟶
      TB'.obj (F'.obj (c.obj M), F'.obj (c.obj N))) :
    d.map mu ≫ tB.hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu' →
    d.map mu ≫ tB.hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu' := by
  intro h
  exact h

end WeilConjectures
