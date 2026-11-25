/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.RingTheory.LimitModuleLocalizationRingData
import WeilConjectures.RingTheory.LimitModuleModuleDataConstruction
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Descent of a local algebra and a presented module along a given local-ring system

Source: Stacks Project, Algebra, Tags 00QV, 00QX and 00R1
(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system).
-/

@[expose] public section

universe u v p

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

/-- Descend a localization of a finitely presented algebra and a finite module presentation
along the given directed system. Scalar-extension maps are specified on pure tensors; the
module tensors put the new scalar ring first, using tensor symmetry to match the source.

Source: Stacks Project, Algebra, Tags 00QV, 00QX and 00R1
(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system).

Proof:
1. Write `T = B_q`, where `B = A[x₁,...,xₙ]/(f₁,...,fₘ)`. The prime contracts to the
   maximal ideal of `A`. Descend the finitely many coefficients to a common stage and
   localize the resulting algebras at the inverse-image primes. Their contraction to
   each base stage is maximal, so all structure and transition maps are local.
   Use [lem-weil-pbc-localization-of-localization] and
   [lem-weil-pbc-filtered-colimit-algebras-elementwise].
2. Polynomial extension and quotient base change identify the scalar extensions of
   these presentations. Their colimit is `B`: lift finite coefficient sets to a stage;
   relations vanishing in `B` vanish at a later stage after descending their finite
   witnesses. Localizing at the compatible primes gives colimit `T`. The tail is cofinal.
   Use [lem-weil-pbc-polynomial-scalar-extension], [lem-weil-pbc-tensor-quotient-base-change],
   [lem-weil-pbc-filtered-colimit-rings-zero],
   [lemma-quasi-finite-coordinates--1],
   [lem-weil-pbc-colimit-initial-full-subcategory] and
   [lem-weil-pbc-filtered-colimit-modules-criterion].
3. Base change of localization gives an intermediate localization of the polynomial
   quotient at each later stage, then localization at the inverse-image prime gives
   the local stage ring. The same argument applies at the limit. Use
   [lem-weil-pbc-localization-base-change], [lem-weil-pbc-localization-of-localization]
   and [lem-weil-pbc-tensor-quotient-base-change].
4. Descend the finitely many entries of the given `t × s` presentation matrix to one
   common later stage. Define each stage module as its cokernel, with the induced
   compatible semilinear transition maps and maps to `N`. These modules are finite.
   Use [lem-weil-pbc-filtered-colimit-algebras-elementwise] and
   [def-weil-finitely-generated-module].
5. Tensoring these presentations is right exact and carries each matrix to the later
   matrix, so the canonical scalar-extension maps are module isomorphisms, including
   at the limit. Use [lem-weil-pbc-tensor-right-exact] and
   [lem-weil-pbc-module-base-change-universal-property].
6. Every module element is represented by a finite vector and lifts to a common stage.
   A vector becoming zero is a combination of finitely many matrix columns. Descend
   its coefficients and then its coordinate equalities to a later stage. The
   elementwise colimit criterion over `ℤ` proves the abelian-group colimit assertion.
   Use [lem-weil-pbc-filtered-colimit-algebras-elementwise],
   [lem-weil-pbc-filtered-colimit-rings-zero] and
   [lem-weil-pbc-filtered-colimit-modules-criterion].

(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module)
(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-core)
-/
theorem exists_limit_module_essentially_finite_presentation_over_system
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (P : Type p) [CommRing P] [Algebra c.pt P] [Algebra.FinitePresentation c.pt P]
    (W : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap c.pt P) = τ)
    (hT : letI := f.toAlgebra; IsLocalization W T)
    (N : AddCommGrpCat.{max u v}) [Module T N]
    (s t : ℕ) (H : (Fin s → T) →ₗ[T] (Fin t → T))
    (hN : Nonempty (((Fin t → T) ⧸ LinearMap.range H) ≃ₗ[T] N)) :
    ∃ i₀ : I,
      ∃ (B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u}) (β : B ⟶ (Functor.const _).obj T),
        Nonempty (IsColimit (Cocone.mk T β)) ∧
        ∃ (κ : ∀ i : {i : I // i₀ ≤ i}, B.obj i →+* T),
          (∀ i, ∀ x : B.obj i, κ i x = (β.app i).hom x) ∧
          (∀ i, IsLocalRing (B.obj i)) ∧ (∀ i, IsLocalHom (κ i)) ∧
          (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
            IsLocalHom (B.map (homOfLE h)).hom) ∧
          ∃ (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i),
            (∀ i, IsLocalHom (τ₀ i)) ∧ (∀ i, (τ₀ i).EssFiniteType) ∧
            (∀ i, (κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom) ∧
            (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
              (B.map (homOfLE h)).hom.comp (τ₀ i) =
                (τ₀ j).comp (F.map (homOfLE h)).hom) ∧
            ∃ (D : {i : I // i₀ ≤ i} ⥤ AddCommGrpCat.{max u v}) (δ : D ⟶ (Functor.const _).obj N),
              Nonempty (IsColimit (Cocone.mk N δ)) ∧
              ∃ (ν : ∀ i : {i : I // i₀ ≤ i}, D.obj i →+ N)
                (_ : ∀ i : {i : I // i₀ ≤ i}, Module (B.obj i) (D.obj i)),
                (∀ i, ∀ x : D.obj i, ν i x = (δ.app i).hom x) ∧
                (∀ i, ∀ (y : B.obj i) (x : D.obj i), ν i (y • x) = κ i y • ν i x) ∧
                (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j)
                  (y : B.obj i) (x : D.obj i),
                  (D.map (homOfLE h)).hom (y • x) =
                    (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
                (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
                (∀ i, ∃ H₀ : (Fin s → B.obj i) →ₗ[B.obj i] (Fin t → B.obj i),
                  Nonempty (((Fin t → B.obj i) ⧸ LinearMap.range H₀) ≃ₗ[B.obj i] D.obj i)) ∧
                (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
                  letI := (τ₀ i).toAlgebra
                  letI := (F.map (homOfLE h)).hom.toAlgebra
                  (∃ φ : B.obj i ⊗[F.obj i.1] F.obj j.1 →+* B.obj j,
                    (∀ (x : B.obj i) (y : F.obj j.1),
                      φ (x ⊗ₜ[F.obj i.1] y) =
                        (B.map (homOfLE h)).hom x * τ₀ j y) ∧
                    (letI := φ.toAlgebra
                     ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] F.obj j.1),
                       IsLocalization U (B.obj j))) ∧
                  (letI := (B.map (homOfLE h)).hom.toAlgebra
                   ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
                     ∀ (y : B.obj j) (x : D.obj i),
                       e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x)) ∧
                (∀ i : {i : I // i₀ ≤ i},
                  letI := (τ₀ i).toAlgebra
                  letI : Algebra (F.obj i.1) c.pt := (c.ι.app i.1).hom.toAlgebra
                  (∃ φ : B.obj i ⊗[F.obj i.1] c.pt →+* T,
                    (∀ (x : B.obj i) (y : c.pt),
                      φ (x ⊗ₜ[F.obj i.1] y) = κ i x * τ y) ∧
                    (letI := φ.toAlgebra
                     ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] c.pt), IsLocalization U T)) ∧
                  (letI := (κ i).toAlgebra
                   ∃ e : T ⊗[B.obj i] D.obj i ≃ₗ[T] N,
                     ∀ (y : T) (x : D.obj i), e (y ⊗ₜ[B.obj i] x) = y • ν i x)) := by
  obtain ⟨i₀, B, β, hcol, κ, hκ, hBlocal, hκlocal, hBmap, τ₀, hτlocal,
      hτfinite, hτcomp, hτnat, hRingTrans, hRingLimit⟩ :=
    exists_limit_module_localization_ring_data F c hc hF hcLocal T τ P W f hf hT
  have hβlocal : ∀ i, IsLocalHom (β.app i).hom := by
    intro i
    have heq : κ i = (β.app i).hom := by ext x; exact hκ i x
    rw [← heq]
    exact hκlocal i
  obtain ⟨i₁, hi, D, δ, hDcol, ν, hModule, hν, hνsmul, hmap, hfinite,
      hpres, htrans, hlimit⟩ :=
    exists_limit_module_presentation_cokernel_data F c hc hF hcLocal T τ N s t H hN
      i₀ B β hcol hBlocal hβlocal hBmap κ hκ τ₀ hτlocal hτfinite hτcomp hτnat
      hRingTrans hRingLimit
  let ρ : {i : I // i₁ ≤ i} ⥤ {i : I // i₀ ≤ i} :=
    { obj := fun i ↦ ⟨i.1, hi.trans i.2⟩
      map := fun h ↦ homOfLE (leOfHom h) }
  let B₁ := ρ ⋙ B
  let β₁ : B₁ ⟶ (Functor.const _).obj T := Functor.whiskerLeft ρ β
  let κ₁ : ∀ i : {i : I // i₁ ≤ i}, B₁.obj i →+* T := fun i ↦ κ (ρ.obj i)
  let τ₁ := fun i ↦ τ₀ (ρ.obj i)
  let : Nonempty {i : I // i₁ ≤ i} := ⟨⟨i₁, le_rfl⟩⟩
  let : IsDirected {i : I // i₁ ≤ i} (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩⟩
  let : ρ.Final := by
    refine Functor.final_of_exists_of_isFiltered ρ ?_ ?_
    · intro i
      obtain ⟨k, hik, h₁k⟩ := exists_ge_ge i.1 i₁
      exact ⟨⟨k, h₁k⟩, ⟨homOfLE hik⟩⟩
    · intro i j f g
      exact ⟨j, 𝟙 j, Subsingleton.elim _ _⟩
  have hcol₁ : Nonempty (IsColimit (Cocone.mk T β₁)) :=
    ⟨(Functor.Final.isColimitWhiskerEquiv ρ (Cocone.mk T β)).symm hcol.some⟩
  refine ⟨i₁, B₁, β₁, hcol₁, κ₁, ?_, ?_, ?_, ?_, τ₁, ?_, ?_, ?_, ?_,
    D, δ, hDcol, ν, hModule, hν, hνsmul, hmap, hfinite, hpres, ?_, ?_⟩
  · intro i x
    exact hκ (ρ.obj i) x
  · intro i
    exact hBlocal (ρ.obj i)
  · intro i
    exact hκlocal (ρ.obj i)
  · intro i j h
    exact hBmap (ρ.obj i) (ρ.obj j) h
  · intro i
    exact hτlocal (ρ.obj i)
  · intro i
    exact hτfinite (ρ.obj i)
  · intro i
    exact hτcomp (ρ.obj i)
  · intro i j h
    exact hτnat (ρ.obj i) (ρ.obj j) h
  · intro i j h
    exact ⟨hRingTrans (ρ.obj i) (ρ.obj j) h, htrans i j h⟩
  · intro i
    exact ⟨hRingLimit (ρ.obj i), hlimit i⟩

end RingHom
