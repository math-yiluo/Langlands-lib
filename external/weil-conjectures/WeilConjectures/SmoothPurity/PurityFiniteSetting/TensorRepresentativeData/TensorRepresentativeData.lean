/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Typed data for a representative tensor-counit square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w uA vA uB vB wA wB
open CategoryTheory MonoidalCategory
namespace WeilConjectures.PurityFiniteSetting

/-- Source and tail maps of a tensor-counit square, retaining their actual common target.
Source: Stacks 07A4 and 0FPT, the representative formula for derived scalar extension.
(blueprint: def-pur-tensor-representative-data). -/
structure TensorRepresentativeData
    {C D K L : Type*} [Category* C] [Category* D] [Category* K] [Category* L]
    [MonoidalCategory C] [MonoidalCategory D]
    (Q : C ⥤ D) (R : K ⥤ C) (QB : L ⥤ D) (S : K → Prop) where
  tensor : K → K → K
  tensor_closed : ∀ X Y, S X → S Y → S (tensor X Y)
  secondTarget : K → L
  target : K → K → L
  first : ∀ X Y, R.obj X ⊗ R.obj Y ⟶ R.obj (tensor X Y)
  second : ∀ X, Q.obj (R.obj X) ⟶ QB.obj (secondTarget X)
  third : ∀ X Y, secondTarget (tensor X Y) ⟶ target X Y
  tail : ∀ X Y, Q.obj (R.obj X) ⊗ Q.obj (R.obj Y) ⟶ QB.obj (target X Y)
  isIso_first : ∀ X Y, S X → S Y → IsIso (first X Y)
  isIso_second : ∀ X, S X → IsIso (second X)
  isIso_third : ∀ X Y, IsIso (third X Y)

namespace TensorRepresentativeData
variable {C D K L : Type*} [Category* C] [Category* D] [Category* K] [Category* L]
  [MonoidalCategory C] [MonoidalCategory D]
  {Q : C ⥤ D} {R : K ⥤ C} {QB : L ⥤ D} {S : K → Prop}

/-- The common target of the actual source and tail composites.
Source: Stacks 07A4 and 0FPT (blueprint: def-pur-tensor-representative-data). -/
abbrev obj (d : TensorRepresentativeData Q R QB S) (X Y : K) : D := QB.obj (d.target X Y)

/-- Compose the three recorded source factors in abstract categories.
Source: Stacks 07A4 and 0FPT (blueprint: def-pur-tensor-representative-data). -/
def source (d : TensorRepresentativeData Q R QB S) (X Y : K) :
    Q.obj (R.obj X ⊗ R.obj Y) ⟶ d.obj X Y :=
  Q.map (d.first X Y) ≫ d.second (d.tensor X Y) ≫ QB.map (d.third X Y)

/-- The entire representative equation, formed before specializing the input categories.
Source: Stacks 07A4 and 0FPT (blueprint: def-pur-tensor-representative-data). -/
def Normalized (d : TensorRepresentativeData Q R QB S) (h : Q.CoreMonoidal) : Prop :=
  ∀ X Y, S X → S Y →
    d.source X Y = (h.μIso (R.obj X) (R.obj Y)).inv ≫ d.tail X Y

end TensorRepresentativeData
end WeilConjectures.PurityFiniteSetting
