/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
public import WeilConjectures.CategoryTheory.Triangulated.BocksteinTowerFinite
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

/-!
# Finiteness of limits along the torsion coefficients `Λ ⧸ ϖⁿ⁺¹`

Let `Λ` be a noetherian ring, complete for the adic topology of `I = (ϖ)` with `ϖ` a
nonzerodivisor (the case `Λ = 𝒪_E`), and `X` a scheme. The triangles
`Λ_X --ϖⁿ⁺¹--> Λ_X ⟶ (Λ ⧸ Iⁿ⁺¹)_X ⟶ Λ_X⟦1⟧` of `D(X_ét, Λ)`
(`DerivedCategory.quotPowTriangle`) with their transition maps
(`DerivedCategory.quotPowTriangleMap`) form a Bockstein tower. Hence for every `Λ`-linear
homological functor `H : D(X_ét, Λ) ⥤ Mod_Λ` the limit `lim_n H((Λ ⧸ Iⁿ⁺¹)_X)` is a finite
`Λ`-module as soon as `H(Λ_X) ⧸ ϖ` is finite and the `ϖ`-torsion of `H(Λ_X⟦1⟧)` is finitely
generated (`AlgebraicGeometry.Etale.finite_limit_quotPowTriangle`).

The intended functor is `H = (Hⁱ ∘ Rg_*)_ȳ`: the stalk at a geometric point `ȳ` of the `i`-th
cohomology sheaf of a derived direct image `Rg_*`, which is homological as `Rg_*` is
triangulated. The tower is then the tower of stalks `(Rⁱg_* (Λ ⧸ Iⁿ⁺¹))_ȳ` with the transition
maps induced by the quotient maps of coefficients, and the hypotheses ask that
`(Rⁱg_* Λ)_ȳ ⧸ ϖ` and `(Rⁱ⁺¹g_* Λ)_ȳ[ϖ]` are finitely generated. By the Bockstein sequence they
are a submodule and a quotient of the stalk of `Rⁱg_* (Λ ⧸ ϖ)` at `ȳ`, which is finite in the
situations of the finiteness theorem.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_bocksteinLimit
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} {I : Ideal Λ} {ϖ : Λ}
  (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})

/-- The torsion coefficients `(Λ ⧸ Iⁿ)_X` are killed by `Iⁿ`. -/
lemma smul_id_quotPowTriangle_obj₃ {n : ℕ} {r : Λ} (hr : r ∈ I ^ n) :
    r • 𝟙 (DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ hI n).obj₃ = 0 := by
  have hM : r • 𝟙 (ModuleCat.of Λ (Λ ⧸ I ^ n)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul (Ideal.Quotient.mk _),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hr
  change r • 𝟙 ((DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ (Λ ⧸ I ^ n)))) = 0
  rw [← (DerivedCategory.singleFunctor _ 0).map_id, ← Functor.map_smul,
    ← (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map_id, ← Functor.map_smul, hM,
    Functor.map_zero, Functor.map_zero]

variable (X) in
/-- The constant sheaf `Λ` placed in degree `0`: the first two vertices of the triangles
`DerivedCategory.quotPowTriangle`. It is isomorphic to the unit `constantComplex Λ X` of the
derived tensor product. -/
noncomputable abbrev constantUnitSingle :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (𝟙_ (ModuleCat.{u + 1} Λ)))

/-- **Finiteness of the limit along the torsion coefficients.** Let `Λ` be noetherian and
complete for `I = (ϖ)`, `ϖ` a nonzerodivisor, and `H : D(X_ét, Λ) ⥤ Mod_Λ` a `Λ`-linear
homological functor. If `H(Λ_X) ⧸ ϖ` is finite and the `ϖ`-torsion of `H(Λ_X⟦1⟧)` is finitely
generated, then `lim_n H((Λ ⧸ Iⁿ⁺¹)_X)`, along the maps induced by the quotient maps
`Λ ⧸ Iⁿ⁺² ⟶ Λ ⧸ Iⁿ⁺¹`, is a finite `Λ`-module. -/
theorem finite_limit_quotPowTriangle [IsNoetherianRing Λ] [IsAdicComplete (Ideal.span {ϖ}) Λ]
    (H : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ ModuleCat.{v} Λ)
    [H.IsHomological] [H.Linear Λ]
    [Module.Finite Λ (H.obj (constantUnitSingle X) ⧸
      (Ideal.span {ϖ} • ⊤ : Submodule Λ (H.obj (constantUnitSingle X))))]
    (hB : (LinearMap.ker (ϖ • LinearMap.id :
      H.obj ((constantUnitSingle X)⟦(1 : ℤ)⟧) →ₗ[Λ] _)).FG) :
    Module.Finite Λ ↑(limit (Functor.ofOpSequence
      (X := fun n ↦ H.obj (DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ hI (n + 1)).obj₃)
      fun n ↦ H.map
        (DerivedCategory.quotPowTriangleMap X.smallEtaleTopology hϖ hI (n + 1)).hom₃)) := by
  -- The vertex `Λ_X` is given explicitly: unifying the vertices of `quotPowTriangle n` for two
  -- different `n` compares the whole triangles, which is very slow.
  refine Pretriangulated.finite_limit_of_bockstein_of_map H (ϖ := ϖ) (L := constantUnitSingle X)
    (fun n ↦ (DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ hI (n + 1)).mor₂)
    (fun n ↦ (DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ hI (n + 1)).mor₃)
    (fun n ↦ (DerivedCategory.quotPowTriangleMap X.smallEtaleTopology hϖ hI (n + 1)).hom₃)
    (fun n ↦ (DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ hI (n + 1)).mor₁)
    (fun n ↦ (DerivedCategory.quotPowTriangleMap X.smallEtaleTopology hϖ hI (n + 1)).hom₁)
    (fun n y ↦ ?_) (fun n y ↦ ?_) (fun n ↦ ?_) (fun n ↦ ?_)
    (fun n ↦ (DerivedCategory.quotPowTriangleMap X.smallEtaleTopology hϖ hI (n + 1)).comm₃)
    (fun n y ↦ ?_) hB
  · rw [DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul]
    erw [CategoryTheory.Functor.map_id]
    rfl
  · rw [DerivedCategory.quotPowTriangleMap_hom₁, Functor.map_smul]
    erw [CategoryTheory.Functor.map_id]
    rw [Functor.map_smul]
    erw [CategoryTheory.Functor.map_id]
    rfl
  · exact DerivedCategory.quotPowTriangle_distinguished X.smallEtaleTopology hϖ hI (n + 1)
  · -- not via `quotPowTriangleMap_hom₂`, which makes the kernel compare two triangles
    have key := congrArg (fun f ↦ (DerivedCategory.singleFunctor _ 0).map
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map f))
      ((Ideal.quotPowCone I).w (homOfLE (Nat.le_succ (n + 1))).op)
    simp only [Functor.map_comp] at key
    exact key
  · have h := congrArg (fun f ↦ H.map f y) (smul_id_quotPowTriangle_obj₃ hϖ hI
      (Ideal.pow_mem_pow (hI ▸ Ideal.mem_span_singleton_self ϖ) (n + 1)))
    simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
    exact h

end AlgebraicGeometry.Etale
