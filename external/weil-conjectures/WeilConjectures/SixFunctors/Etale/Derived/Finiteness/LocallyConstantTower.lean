/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Finite local constancy of higher direct images along towers of coefficients

Finite locally constant étale sheaves of modules over a finite ring are closed under kernels,
cokernels and extensions (`WeilConjectures.ConstructibleSheaf.KernelCokernel`). This file deduces
the closure statement needed for a *uniform* stratification of the higher direct images of the
torsion coefficients `𝒪_E ⧸ ℓⁿ` (step (6) of the comparison of `ℓ`-adic and torsion direct
images, `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`):

- `CategoryTheory.ObjectProperty.prop_of_exact_five`: for a property closed under isomorphisms,
  kernels, cokernels and extensions, the middle term of a five-term exact sequence whose outer
  terms have the property has it;
- `AlgebraicGeometry.Etale.flcProperty_rightDerived_lowerStar_X₂`: in a short exact sequence of
  étale sheaves of modules over a finite ring, if all the `Rⁱg_*` of the outer terms are finite
  locally constant, so are those of the middle term (long exact sequence of `Rⁱg_*`);
- `AlgebraicGeometry.Etale.flcProperty_rightDerived_lowerStar_of_tower`: for a tower of
  extensions `0 ⟶ F 0 ⟶ F (n + 1) ⟶ F n ⟶ 0`, finite local constancy of all `Rⁱg_* (F 0)` gives
  that of all `Rⁱg_* (F n)`. Applied on a stratum, this is the uniform stratification of the
  `Rⁱg_*(𝒪_E ⧸ ℓⁿ)` from that of `Rⁱg_*(𝒪_E ⧸ ℓ)`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C)

/-- **The middle term of a five-term exact sequence.** Let `P` be a property of objects of an
abelian category closed under isomorphisms, kernels, cokernels and extensions. For an exact
sequence `C₀ ⟶ A ⟶ B ⟶ C ⟶ A₁` (exact at `A`, `B` and `C`) whose outer four terms satisfy
`P`, the middle term `B` satisfies `P`: it is an extension of `ker(C ⟶ A₁)` by
`coker(C₀ ⟶ A)`. -/
lemma prop_of_exact_five [P.IsClosedUnderIsomorphisms]
    (hker : ∀ {X Y : C} (φ : X ⟶ Y), P X → P Y → P (kernel φ))
    (hcoker : ∀ {X Y : C} (φ : X ⟶ Y), P X → P Y → P (cokernel φ))
    (hext : ∀ {S : ShortComplex C}, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {C₀ A B C' A₁ : C} (δ₀ : C₀ ⟶ A) (f : A ⟶ B) (g : B ⟶ C') (δ : C' ⟶ A₁)
    (w₀ : δ₀ ≫ f = 0) (w₁ : f ≫ g = 0) (w₂ : g ≫ δ = 0)
    (h₀ : (ShortComplex.mk δ₀ f w₀).Exact) (h₁ : (ShortComplex.mk f g w₁).Exact)
    (h₂ : (ShortComplex.mk g δ w₂).Exact)
    (hC₀ : P C₀) (hA : P A) (hC : P C') (hA₁ : P A₁) : P B := by
  let i : cokernel δ₀ ⟶ B := cokernel.desc δ₀ f w₀
  let p : B ⟶ kernel δ := kernel.lift δ g w₂
  have hip : i ≫ p = 0 := by
    ext
    simp [i, p, w₁]
  have : Mono i := h₀.mono_cokernelDesc
  have : Epi p := h₂.epi_kernelLift
  -- `A ⟶ B ⟶ ker δ` is exact
  let S₁ := ShortComplex.mk f p (by ext; simp [p, w₁])
  have hS₁ : S₁.Exact := by
    let φ : S₁ ⟶ ShortComplex.mk f g w₁ :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι δ, comm₂₃ := by simp [S₁, p] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 h₁
  let S := ShortComplex.mk i p hip
  have hS : S.ShortExact := by
    refine ⟨?_⟩
    let φ : S₁ ⟶ S :=
      { τ₁ := cokernel.π δ₀, τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simp [S₁, S, i] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS₁
  exact hext hS (hcoker δ₀ hC₀ hA) (hker δ hC hA₁)

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Etale

open Scheme

universe u

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {T Y : Scheme.{u}}

/-- Finite local constancy, as a property of étale sheaves of `Λ`-modules. -/
abbrev flcProperty (Y : Scheme.{u}) : ObjectProperty (Sheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) :=
  fun F ↦ IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F

instance : (flcProperty (Λ := Λ) Y).IsClosedUnderIsomorphisms where
  of_iso e h := by
    have := h
    exact IsFiniteLocallyConstantSheaf.of_iso e

/-- **Finite local constancy of higher direct images in a short exact sequence.** Let `Λ` be a
finite ring and `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` a short exact sequence of étale sheaves of `Λ`-modules
on `T`. If all the `Rⁱg_* F'` and `Rⁱg_* F''` are finite locally constant, so are all the
`Rⁱg_* F`: by the long exact sequence, `Rⁱg_* F` is an extension of a kernel by a cokernel of
morphisms between finite locally constant sheaves, which form a Serre-type subcategory
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.kernel`, `.cokernel`,
`.of_shortExact`). -/
theorem flcProperty_rightDerived_lowerStar_X₂ (g : T ⟶ Y)
    {S : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (h₁ : ∀ i, flcProperty Y (((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerived i).obj S.X₁))
    (h₃ : ∀ i, flcProperty Y (((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerived i).obj S.X₃))
    (i : ℕ) :
    flcProperty Y (((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerived i).obj S.X₂) := by
  have hker {X Z : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : X ⟶ Z)
      (hX : flcProperty Y X) (hZ : flcProperty Y Z) : flcProperty Y (kernel φ) := by
    have := hX; have := hZ
    exact IsFiniteLocallyConstantSheaf.kernel φ
  have hcoker {X Z : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : X ⟶ Z)
      (hX : flcProperty Y X) (hZ : flcProperty Y Z) : flcProperty Y (cokernel φ) := by
    have := hX; have := hZ
    exact IsFiniteLocallyConstantSheaf.cokernel φ
  have hext {S' : ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (hS' : S'.ShortExact) (hX : flcProperty Y S'.X₁) (hZ : flcProperty Y S'.X₃) :
      flcProperty Y S'.X₂ := by
    have := hX; have := hZ
    exact IsFiniteLocallyConstantSheaf.of_shortExact hS'
  obtain ⟨δ, hmono, hδ⟩ := hS.exists_rightDerived_full_long_exact
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) g)
  cases i with
  | zero =>
    obtain ⟨hmid, _, _, hexg, _⟩ := hδ 0
    refine (flcProperty Y).prop_of_exact_five hker hcoker hext 0 _ _ (δ 0) (by simp)
      _ _ ?_ hmid hexg (h₁ 0) (h₁ 0) (h₃ 0) (h₁ 1)
    exact (ShortComplex.exact_iff_mono _ rfl).2 hmono
  | succ n =>
    obtain ⟨hmid, _, _, hexg, _⟩ := hδ (n + 1)
    obtain ⟨_, _, _, _, hexf'⟩ := hδ n
    exact (flcProperty Y).prop_of_exact_five hker hcoker hext (δ n) _ _ (δ (n + 1)) _
      _ _ hexf' hmid hexg (h₃ n) (h₁ (n + 1)) (h₃ (n + 1)) (h₁ (n + 2))

/-- **Uniform finite local constancy along a tower of extensions.** Let `F : ℕ → Sh(T_ét, Λ)` be
sheaves of modules over a finite ring with short exact sequences
`0 ⟶ F 0 ⟶ F (n + 1) ⟶ F n ⟶ 0` (for instance `F n = Λ ⧸ πⁿ⁺¹` for a uniformizer `π` of a
discrete valuation ring with finite residue field, viewed over `Λ ⧸ π^N`). If all the
`Rⁱg_* (F 0)` are finite locally constant, then so are all the `Rⁱg_* (F n)`. -/
theorem flcProperty_rightDerived_lowerStar_of_tower (g : T ⟶ Y)
    (F : ℕ → Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (S : ℕ → ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hS : ∀ n, (S n).ShortExact) (e₁ : ∀ n, (S n).X₁ ≅ F 0) (e₂ : ∀ n, (S n).X₂ ≅ F (n + 1))
    (e₃ : ∀ n, (S n).X₃ ≅ F n)
    (h₀ : ∀ i, flcProperty Y (((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerived i).obj
      (F 0)))
    (n i : ℕ) :
    flcProperty Y (((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerived i).obj (F n)) := by
  induction n generalizing i with
  | zero => exact h₀ i
  | succ n ih =>
    refine (flcProperty Y).prop_of_iso
      (((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerived i).mapIso (e₂ n)) ?_
    exact flcProperty_rightDerived_lowerStar_X₂ g (hS n)
      (fun j ↦ (flcProperty Y).prop_of_iso
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerived j).mapIso (e₁ n).symm) (h₀ j))
      (fun j ↦ (flcProperty Y).prop_of_iso
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerived j).mapIso (e₃ n).symm) (ih j)) i

end AlgebraicGeometry.Etale
