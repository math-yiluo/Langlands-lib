/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.Ideal.Defs
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-!
# Derived completeness of module complexes

Source: Stacks Project, More on Algebra, Section 15.93 (Tag 091N), notation `T(K,f)`,
and Definition 15.93.4 (Tag 091S)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- An object of `D(A)` is derived complete for `I` when every derived limit of the
constant tower with transition multiplication by `f` is zero, for every `f ∈ I`.
We quantify over product structures to express the Roos-triangle condition without
choosing one or imposing an additional product hypothesis on the object.
Source: Stacks Project, Tags 091N and 091S
(auxiliary; not a blueprint node). -/
noncomputable def IsDerivedComplete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{v} A)) : Prop :=
  ∀ (f : A), f ∈ I → ∀ [HasProduct (fun _ : ℕ ↦ K)]
    (T : DerivedCategory (ModuleCat.{v} A)),
      IsDerivedLimit (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K) T → IsZero T

end DerivedCategory

namespace ModuleCat

/-- A module is derived complete for `I` if its complex concentrated in degree zero is
derived complete. Source: Stacks Project, Definition 15.93.4 (Tag 091S)
(auxiliary; not a blueprint node). -/
noncomputable def IsDerivedComplete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)] (I : Ideal A) (M : ModuleCat.{v} A) : Prop :=
  DerivedCategory.IsDerivedComplete I ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)

end ModuleCat
