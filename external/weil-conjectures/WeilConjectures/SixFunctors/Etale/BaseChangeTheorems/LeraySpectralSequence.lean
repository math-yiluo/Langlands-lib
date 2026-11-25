/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical

/-!
# The Grothendieck spectral sequence of a composite of étale direct images

For morphisms of schemes `f : X ⟶ Y` and `h : Y ⟶ Z` and an étale sheaf `F` of `Λ`-modules
on `X`, there is a first quadrant spectral sequence

`E₂^{p,q} = Rᵖh_* Rᵠf_* F ⟹ Rᵖ⁺ᵠ(f_* ⋙ h_*) F`,

the Grothendieck spectral sequence of the composable pair `(f_*, h_*)`: no acyclicity
hypothesis on `F` is needed, because `f_*` is right adjoint to the exact functor `f^*` and
therefore preserves injective objects.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The Grothendieck spectral sequence of a composite of direct images.** For morphisms
`f : X ⟶ Y`, `h : Y ⟶ Z` and an étale sheaf `F` of `Λ`-modules on `X` there is a first quadrant
spectral sequence `E₂^{p,q} = Rᵖh_* Rᵠf_* F ⟹ Rᵖ⁺ᵠ(f_* ⋙ h_*) F`. The pair `(f_*, h_*)` has
the acyclicity of the Grothendieck spectral sequence theorem because `f_*` preserves injective
objects (`AlgebraicGeometry.Etale.preservesInjectiveObjects_lowerStar`). Its compatibility with
inverse image along a cartesian base change is the general
`CategoryTheory.Functor.exists_grothendieckSpectralObject_baseChange`.
(blueprint: `lemma-composition-cancellation`) -/
theorem Etale.exists_grothendieckSpectralSequence_lowerStar {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (h : Y ⟶ Z) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ E : E₂CohomologicalSpectralSequenceNat (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        ((h)_*[ModuleCat.{u + 1} Λ].rightDerived p).obj
          (((f)_*[ModuleCat.{u + 1} Λ].rightDerived q).obj F))) ∧
      E.AbutsTo (fun n ↦
        (((f)_*[ModuleCat.{u + 1} Λ] ⋙ (h)_*[ModuleCat.{u + 1} Λ]).rightDerived n).obj F) :=
  Functor.exists_grothendieckSpectralSequence _ _
    (Functor.isAcyclicComposablePair_of_preservesInjectiveObjects _ _) F

end AlgebraicGeometry
