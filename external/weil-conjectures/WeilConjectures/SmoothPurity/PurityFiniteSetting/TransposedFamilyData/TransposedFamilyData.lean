/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Actual data for a family of prescribed adjoint transposes -/

@[expose] public noncomputable section
set_option autoImplicit false
universe uC uD vC vD uI uA
open CategoryTheory
namespace WeilConjectures.PurityFiniteSetting

/-- An actual adjunction and prescribed values of its hom equivalences.
Source: finite reduction of purity, proof Steps 3--5; Stacks 06YY and 03EM.
(blueprint: def-pur-transposed-family-data). -/
structure TransposedFamilyData
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {ι : Type uI} (F : C ⥤ D) (G : D ⥤ C) (X : ι → C) (Y : ι → D)
    (A : Type uA) where
  adjunction : F ⊣ G
  valueType : ι → Type vC
  value : A → ∀ i, valueType i

namespace TransposedFamilyData
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {ι : Type uI} {F : C ⥤ D} {G : D ⥤ C} {X : ι → C} {Y : ι → D} {A : Type uA}

/-- The entire prescribed transpose equation for one isomorphism.
Source: Stacks 06YY and 03EM (blueprint: def-pur-transposed-family-data). -/
def Pointwise (d : TransposedFamilyData F G X Y A) (a : A) (i : ι)
    (b : F.obj (X i) ≅ Y i) : Prop :=
  HEq (d.adjunction.homEquiv _ _ b.hom) (d.value a i)

/-- All the prescribed transpose equations, without unfolding their concrete values.
Source: Stacks 06YY and 03EM (blueprint: def-pur-transposed-family-data). -/
def Normalized (d : TransposedFamilyData F G X Y A) (a : A)
    (b : ∀ i, F.obj (X i) ≅ Y i) : Prop :=
  ∀ i, d.Pointwise a i (b i)

/-- A prescribed adjoint transpose determines an isomorphism uniquely.
Source: adjunction hom bijection; Stacks 06YY
(blueprint: def-pur-transposed-family-data). -/
theorem pointwise_unique (d : TransposedFamilyData F G X Y A) (a : A) (i : ι)
    {b b' : F.obj (X i) ≅ Y i} (hb : d.Pointwise a i b) (hb' : d.Pointwise a i b') :
    b = b' := by
  apply Iso.ext
  apply (d.adjunction.homEquiv _ _).injective
  exact eq_of_heq (hb.trans hb'.symm)

end TransposedFamilyData
end WeilConjectures.PurityFiniteSetting
