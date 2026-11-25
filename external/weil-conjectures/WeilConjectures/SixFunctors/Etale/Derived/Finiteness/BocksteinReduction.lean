/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BocksteinLimit

/-!
# Finiteness of the limit along `Λ ⧸ ϖⁿ⁺¹` from the reduction modulo `ϖ`

Let `Λ` be a noetherian ring, complete for `I = (ϖ)` with `ϖ` a nonzerodivisor, and
`H : D(X_ét, Λ) ⥤ Mod_Λ` a `Λ`-linear homological functor. The Bockstein triangle
`Λ_X --ϖ--> Λ_X ⟶ (Λ ⧸ I)_X ⟶ Λ_X⟦1⟧` gives an exact sequence

`H(Λ_X) --ϖ--> H(Λ_X) ⟶ H((Λ ⧸ I)_X) ⟶ H(Λ_X⟦1⟧) --ϖ--> H(Λ_X⟦1⟧)`,

so `H(Λ_X) ⧸ ϖ` is a submodule and `H(Λ_X⟦1⟧)[ϖ]` a quotient of `H((Λ ⧸ I)_X)`. Hence the
hypotheses of `AlgebraicGeometry.Etale.finite_limit_quotPowTriangle` follow from the finiteness
of the single module `H((Λ ⧸ I)_X)`
(`AlgebraicGeometry.Etale.finite_limit_quotPowTriangle_of_finite`).

We also record that the transition maps of the tower are induced by the quotient maps
`Λ ⧸ Iⁿ⁺¹ ⟶ Λ ⧸ Iⁿ` (`DerivedCategory.quotPowTriangleMap_hom₃`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] {I : Ideal R} {ϖ : R}
  (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

/-- The third component of `quotPowTriangleMap` is induced by the quotient map
`R ⧸ Iⁿ⁺¹ ⟶ R ⧸ Iⁿ`. -/
lemma quotPowTriangleMap_hom₃ (n : ℕ) :
    (quotPowTriangleMap J hϖ hI n).hom₃ = (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
      ((constantSheaf J (ModuleCat.{u + 1} R)).map
        ((Ideal.quotPowFunctor I).map (homOfLE n.le_succ).op)) :=
  rfl

end DerivedCategory

namespace AlgebraicGeometry.Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_bocksteinReduction
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} {I : Ideal Λ} {ϖ : Λ}
  (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})

/-- **Finiteness of the limit along the torsion coefficients, from the reduction modulo `ϖ`.**
Let `Λ` be noetherian and complete for `I = (ϖ)`, `ϖ` a nonzerodivisor, and
`H : D(X_ét, Λ) ⥤ Mod_Λ` a `Λ`-linear homological functor. If `H((Λ ⧸ I)_X)` is a finite
`Λ`-module, then so is `lim_n H((Λ ⧸ Iⁿ⁺¹)_X)`: by the Bockstein sequence of `ϖ`, the
hypotheses of `AlgebraicGeometry.Etale.finite_limit_quotPowTriangle` are a submodule and a
quotient of `H((Λ ⧸ I)_X)`. -/
theorem finite_limit_quotPowTriangle_of_finite [IsNoetherianRing Λ]
    [IsAdicComplete (Ideal.span {ϖ}) Λ]
    (H : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ ModuleCat.{v} Λ)
    [H.IsHomological] [H.Linear Λ]
    [Module.Finite Λ (H.obj (DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ hI 1).obj₃)] :
    Module.Finite Λ ↑(limit (Functor.ofOpSequence
      (X := fun n ↦ H.obj (DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ hI (n + 1)).obj₃)
      fun n ↦ H.map
        (DerivedCategory.quotPowTriangleMap X.smallEtaleTopology hϖ hI (n + 1)).hom₃)) := by
  let T := DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ hI 1
  have hT : T ∈ distTriang _ := DerivedCategory.quotPowTriangle_distinguished _ hϖ hI 1
  have hsmul (Y) (y : H.obj Y) : H.map (ϖ • 𝟙 Y) y = ϖ • y := by
    rw [Functor.map_smul, H.map_id]
    rfl
  have hmor₁ (y : H.obj (constantUnitSingle X)) : H.map T.mor₁ y = ϖ • y := by
    rw [DerivedCategory.quotPowTriangle_mor₁, pow_one]
    exact hsmul _ y
  -- `H(Λ_X) ⧸ ϖ` embeds into `H((Λ ⧸ I)_X)`
  let f : H.obj (constantUnitSingle X) →ₗ[Λ] H.obj T.obj₃ := (H.map T.mor₂).hom
  have hker : LinearMap.ker f = (Ideal.span {ϖ} • ⊤ : Submodule Λ _) := by
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (H.map_distinguished_exact _ hT)
    ext y
    rw [LinearMap.mem_ker, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    refine (hex y).trans ⟨fun ⟨b, hb⟩ ↦ ⟨b, Submodule.mem_top, ?_⟩,
      fun ⟨b, _, hb⟩ ↦ ⟨b, ?_⟩⟩
    · rw [← hb]
      exact (hmor₁ b).symm
    · rw [← hb]
      exact hmor₁ b
  have : Module.Finite Λ (H.obj (constantUnitSingle X) ⧸
      (Ideal.span {ϖ} • ⊤ : Submodule Λ (H.obj (constantUnitSingle X)))) :=
    Module.Finite.equiv ((Submodule.quotEquivOfEq _ _ hker).symm ≪≫ₗ f.quotKerEquivRange).symm
  -- `H(Λ_X⟦1⟧)[ϖ]` is the image of `H((Λ ⧸ I)_X)`
  let g : H.obj T.obj₃ →ₗ[Λ] H.obj (T.obj₁⟦(1 : ℤ)⟧) := (H.map T.mor₃).hom
  have hrange : LinearMap.ker (ϖ • LinearMap.id :
      H.obj (T.obj₁⟦(1 : ℤ)⟧) →ₗ[Λ] _) = LinearMap.range g := by
    have hex : Function.Exact g (H.map (-T.mor₁⟦(1 : ℤ)⟧')).hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (H.map_distinguished_exact _ (rot_of_distTriang _ (rot_of_distTriang _ hT)))
    ext y
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    refine Iff.trans ?_ (hex y)
    have key := congrArg (fun φ ↦ (H.map ((shiftFunctor _ (1 : ℤ)).map φ)).hom y)
      (DerivedCategory.quotPowTriangle_mor₁ X.smallEtaleTopology hϖ hI 1)
    simp only [pow_one, Functor.map_smul] at key
    rw [Functor.map_neg, ModuleCat.hom_neg, LinearMap.neg_apply, neg_eq_zero, key,
      ModuleCat.hom_smul, LinearMap.smul_apply]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  have hB : (LinearMap.ker (ϖ • LinearMap.id : H.obj (T.obj₁⟦(1 : ℤ)⟧) →ₗ[Λ] _)).FG := by
    rw [hrange, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map g
  exact finite_limit_quotPowTriangle hϖ hI H hB

end AlgebraicGeometry.Etale
