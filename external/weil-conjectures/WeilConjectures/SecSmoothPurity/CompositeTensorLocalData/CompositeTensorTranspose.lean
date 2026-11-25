/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Double transpose of composite tensor-counit maps

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/thm-pur-cohomological-smoothness.proof.md, second paragraph, sentence
on transposing the two tensor transformations; Stacks Tag 0037 for adjunction
transpose conventions (blueprint: lem-pur-composite-tensor-transpose).

The helpers construct the two maps and their proposed common inverse transpose
using the recorded projection-formula structure and Mathlib's composite adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe uX vX uY vY uZ vZ

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj

namespace SecSmoothPurity

/-! ## The calculation on full domains of definition

The local data below name just the objects and projection instances in the calculation.
`X`, `Y`, and `R` are arbitrary full domains for the two left functors and the first
pullback functor. They need not be closed under tensor products. No functor or Hom
bijection is requested at an object outside these domains. The three objects `A`,
`V`, `T` stand for `S_g K`, `G_g 𝟙`, `G_g K`; `W`, `U`, `H` stand for `G_f 𝟙`,
`G_f V`, `G_f T`. The selected tensor comparison is the inverse strong tensorator.
-/

/-- The finite diagram of functors, Hom bijections and projection isomorphisms used in
both transposes. The functors are defined only on the indicated full domains.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm, second paragraph, restricted
Hom-bijection interpretation (blueprint: lem-pur-composite-tensor-transpose). -/
structure CompositeTensorLocalData
    (C : Type uX) [Category.{vX} C] [MonoidalCategory C]
    (D : Type uY) [Category.{vY} D] [MonoidalCategory D]
    (E : Type uZ) [Category.{vZ} E] [MonoidalCategory E] where
  /-- Full domain of `P_f`. -/
  X : ObjectProperty C
  /-- Full domain of `P_g`. -/
  Y : ObjectProperty D
  /-- Full domain of `S_f`. -/
  R : ObjectProperty D
  /-- The first left functor on its domain. -/
  P : X.FullSubcategory ⥤ D
  /-- The second left functor on its domain. -/
  Q : Y.FullSubcategory ⥤ E
  /-- The first pullback functor on its domain. -/
  S : R.FullSubcategory ⥤ C
  /-- The target object. -/
  K : E
  /-- The objects `S_g K`, `G_g 𝟙`, and `G_g K`. -/
  A : R.FullSubcategory
  V : R.FullSubcategory
  T : R.FullSubcategory
  /-- The objects `G_f 𝟙`, `G_f V`, and `G_f T`. -/
  W : X.FullSubcategory
  U : X.FullSubcategory
  H : X.FullSubcategory
  /-- The coefficient tensor is in the domain of `S_f`. -/
  hAV : R (A.obj ⊗ V.obj)
  /-- The inverse tensorator of the specified strong monoidal comparison. -/
  delta : S.obj ⟨A.obj ⊗ V.obj, hAV⟩ ≅ S.obj A ⊗ S.obj V
  /-- Memberships of the five tensor sources in the domain of `P_f`. -/
  hN : X (S.obj ⟨A.obj ⊗ V.obj, hAV⟩ ⊗ W.obj)
  hVW : X (S.obj V ⊗ W.obj)
  hTW : X (S.obj T ⊗ W.obj)
  hAU : X (S.obj A ⊗ U.obj)
  hAVW : X (S.obj A ⊗ (S.obj V ⊗ W.obj))
  /-- Memberships of the seven sources in the domain of `P_g`. -/
  hPN : Y (P.obj ⟨S.obj ⟨A.obj ⊗ V.obj, hAV⟩ ⊗ W.obj, hN⟩)
  hPAU : Y (P.obj ⟨S.obj A ⊗ U.obj, hAU⟩)
  hAPU : Y (A.obj ⊗ P.obj U)
  hPU : Y (P.obj U)
  hV : Y V.obj
  hAVY : Y (A.obj ⊗ V.obj)
  hAVPW : Y ((A.obj ⊗ V.obj) ⊗ P.obj W)
  /-- The first adjunction Hom bijections, at the three target objects used. -/
  homFOne (M : X.FullSubcategory) : (P.obj M ⟶ 𝟙_ D) ≃ (M.obj ⟶ W.obj)
  homFV (M : X.FullSubcategory) : (P.obj M ⟶ V.obj) ≃ (M.obj ⟶ U.obj)
  homFT (M : X.FullSubcategory) : (P.obj M ⟶ T.obj) ≃ (M.obj ⟶ H.obj)
  /-- The second adjunction Hom bijections, at the two target objects used. -/
  homGOne (L : Y.FullSubcategory) : (Q.obj L ⟶ 𝟙_ E) ≃ (L.obj ⟶ V.obj)
  homGK (L : Y.FullSubcategory) : (Q.obj L ⟶ K) ≃ (L.obj ⟶ T.obj)
  /-- Contravariant naturality of the first Hom bijections at `V`. -/
  naturalFV {M M' : X.FullSubcategory} (a : M ⟶ M') (b : M'.obj ⟶ U.obj) :
    (homFV M).symm (a.hom ≫ b) = P.map a ≫ (homFV M').symm b
  /-- Contravariant naturality of the first Hom bijections at `G_g K`. -/
  naturalFT {M M' : X.FullSubcategory} (a : M ⟶ M') (b : M'.obj ⟶ H.obj) :
    (homFT M).symm (a.hom ≫ b) = P.map a ≫ (homFT M').symm b
  /-- Contravariant naturality of the second Hom bijections at `K`. -/
  naturalGK {L L' : Y.FullSubcategory} (a : L ⟶ L') (b : L'.obj ⟶ T.obj) :
    (homGK L).symm (a.hom ≫ b) = Q.map a ≫ (homGK L').symm b
  /-- The five instances of the first projection formula used in the calculation. -/
  pfAV : P.obj ⟨S.obj ⟨A.obj ⊗ V.obj, hAV⟩ ⊗ W.obj, hN⟩ ≅
    (A.obj ⊗ V.obj) ⊗ P.obj W
  pfT : P.obj ⟨S.obj T ⊗ W.obj, hTW⟩ ≅ T.obj ⊗ P.obj W
  pfV : P.obj ⟨S.obj V ⊗ W.obj, hVW⟩ ≅ V.obj ⊗ P.obj W
  pfAQ : P.obj ⟨S.obj A ⊗ (S.obj V ⊗ W.obj), hAVW⟩ ≅
    A.obj ⊗ P.obj ⟨S.obj V ⊗ W.obj, hVW⟩
  pfAU : P.obj ⟨S.obj A ⊗ U.obj, hAU⟩ ≅ A.obj ⊗ P.obj U
  /-- The two instances of the second projection formula used in the calculation. -/
  pgV : Q.obj ⟨A.obj ⊗ V.obj, hAVY⟩ ≅ K ⊗ Q.obj ⟨V.obj, hV⟩
  pgU : Q.obj ⟨A.obj ⊗ P.obj U, hAPU⟩ ≅ K ⊗ Q.obj ⟨P.obj U, hPU⟩

namespace CompositeTensorLocalData

variable {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
  {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
  {E : Type uZ} [Category.{vZ} E] [MonoidalCategory E]
  (d : CompositeTensorLocalData C D E)

end CompositeTensorLocalData

end SecSmoothPurity
