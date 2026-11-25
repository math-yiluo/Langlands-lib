/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.SixFunctors.ProEtale.Adic.LatticeSections

/-!
# Linear independence of lattice sections by pointwise evaluation

Let `F` be a sheaf of `ℚ̄_ℓ,X`-modules. Global sections `s₁, …, sᵣ` of `F` are linearly
independent over `ℚ̄_ℓ,X(U)` for every `U`, i.e. `(aᵢ) ↦ ∑ aᵢ • sᵢ|_U` is injective (the
injectivity hypothesis of `AlgebraicGeometry.ProEtale.AdicSheaf.isIso_ofSections_of_lattice`), as
soon as they can be *tested pointwise*: for every affine `U` and point `x` of `U` there is
an additive map `Φ_{U,x} : F(U) → V_{U,x}` to a `ℚ̄_ℓ`-vector space with
`Φ(a • s) = a(x) • Φ(s)` (such as the stalk at a geometric point over `x`) under which the
`sᵢ|_U` become linearly independent
(`AlgebraicGeometry.ProEtale.AdicSheaf.sectionsLinearMap_injective_of_eval`). No injectivity of
`Φ` is needed, and only affine `U` matter
(`AlgebraicGeometry.ProEtale.AdicSheaf.sectionsLinearMap_injective_of_isAffine`).

For lattice sections `sᵢ = ψ(bᵢ)` and evaluations `Φ(ψ(m))(x) = j(m(x))` into a fixed space `V`
this reduces to the linear independence of the `j(bᵢ)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.sectionsLinearMap_injective_of_eval_const`); for
`V = ℚ̄_ℓ ⊗_{𝒪_E} M` and `j = 1 ⊗ -`, a basis of `M` modulo torsion has linearly independent
image, `ℚ̄_ℓ` being flat over `𝒪_E` (`LinearIndependent.one_tmul_of_mkQ`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct

/-- Elements linearly independent modulo a submodule `N` (typically the torsion) stay linearly
independent after a flat base change `R → S`. -/
lemma LinearIndependent.one_tmul_of_mkQ {R S M ι : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] [AddCommGroup M] [Module R M] {b : ι → M}
    (N : Submodule R M) (hb : LinearIndependent R (N.mkQ ∘ b)) :
    LinearIndependent S fun i ↦ (1 : S) ⊗ₜ[R] b i :=
  LinearIndependent.of_comp (N.mkQ.baseChange S)
    (Module.Flat.linearIndependent_one_tmul (S := S) hb)

namespace AlgebraicGeometry.ProEtale.AdicSheaf

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}} (F : AdicSheaf l X)

/-- **Injectivity on affine objects**: `(aᵢ) ↦ ∑ aᵢ • sᵢ|_U` is injective for every `U` as soon
as it is injective on families of functions with values in finite subextensions of `ℚ̄_ℓ` over
affine `U`: a locally finite function on `U` is such a function on every affine open of `U`. -/
lemma sectionsLinearMap_injective_of_isAffine {r : ℕ}
    (s : Fin r → F.X.obj.obj (op (proEtTop X)))
    (h : ∀ (U : X.ProEt) [IsAffine U.left]
      (a : Fin r → (adicConstantSheaf l X).obj.obj (op U)),
      (∀ i, (a i).down.1 ∈ finiteIntermediateFieldValued l U.left) →
        sectionsLinearMap F s (op U) a = 0 → a = 0) (U : X.ProEtᵒᵖ) :
    Function.Injective (sectionsLinearMap F s U) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  funext i
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
  obtain ⟨W, hW, hxW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1
    U.unop.left.isBasis_affineOpens) (show x ∈ (⊤ : U.unop.left.Opens) from trivial)
  let ιW := overOpensι (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U.unop W
  have : IsAffine (overOpens (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U.unop W).left := hW
  have : CompactSpace (overOpens (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U.unop W).left :=
    isCompact_iff_compactSpace.1 hW.isCompact
  have h0 := h _ (fun i ↦ (adicConstantSheaf l X).obj.map ιW.op (a i))
    (fun i ↦ mem_finiteIntermediateFieldValued_of_mem_locallyFiniteFunctions
      ((adicConstantSheaf l X).obj.map ιW.op (a i)).down.2)
    (by
      rw [← map_sectionsLinearMap]
      change F.X.obj.map ιW.op (sectionsLinearMap F s U a) = 0
      rw [ha, map_zero])
  exact congrArg (fun b ↦ (b i).down.1 ⟨x, hxW⟩) h0

/-- **Linear independence of global sections by pointwise evaluation**: suppose that for every
affine `U` and every point `x` of `U` there is an additive map `Φ_{U,x} : F(U) → V_{U,x}` to a
`ℚ̄_ℓ`-vector space with `Φ(a • s) = a(x) • Φ(s)` for `a` with values in a finite subextension
of `ℚ̄_ℓ` (e.g. a stalk at a geometric point over `x`), mapping the restrictions `sᵢ|_U` to
linearly independent vectors. Then `(aᵢ) ↦ ∑ aᵢ • sᵢ|_U` is injective for every `U`. -/
theorem sectionsLinearMap_injective_of_eval {r : ℕ} (s : Fin r → F.X.obj.obj (op (proEtTop X)))
    {V : ∀ U : X.ProEt, U.left → Type*} [∀ U x, AddCommGroup (V U x)]
    [∀ U x, Module (PadicAlgCl l) (V U x)]
    (Φ : ∀ (U : X.ProEt) [IsAffine U.left] (x : U.left), F.X.obj.obj (op U) →+ V U x)
    (hΦact : ∀ (U : X.ProEt) [IsAffine U.left] (x : U.left)
      (a : (adicConstantSheaf l X).obj.obj (op U)) (t : F.X.obj.obj (op U)),
      a.down.1 ∈ finiteIntermediateFieldValued l U.left →
        Φ U x (sectionAct F a t) = a.down.1 x • Φ U x t)
    (hΦ : ∀ (U : X.ProEt) [IsAffine U.left] (x : U.left),
      LinearIndependent (PadicAlgCl l) fun i ↦ Φ U x (restrictTop F (s i) (op U)))
    (U : X.ProEtᵒᵖ) : Function.Injective (sectionsLinearMap F s U) := by
  refine sectionsLinearMap_injective_of_isAffine F s (fun U _ a ha0 ha ↦ ?_) U
  funext i
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
  have h0 := congrArg (Φ U x) ha
  simp only [sectionsLinearMap_apply, map_sum, map_zero] at h0
  rw [Finset.sum_congr rfl fun k _ ↦ hΦact U x (a k) _ (ha0 k)] at h0
  exact Fintype.linearIndependent_iff.1 (hΦ U x) (fun k ↦ (a k).down.1 x) h0 i

variable {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  (ψ : ∀ U : X.ProEt, C(U.left, M) →+ F.X.obj.obj (op U))
  (hψ : ∀ ⦃U V : X.ProEt⦄ (f : V ⟶ U) (m : C(U.left, M)),
    ψ V (m.comp f.left.base.hom) = F.X.obj.map f.op (ψ U m))

include hψ in
/-- **Linear independence of lattice sections by pointwise evaluation into a fixed space**: if
the additive maps `Φ_{U,x} : F(U) → V` satisfy, on affine `U`, `Φ_x(ψ(m)) = j(m(x))` and
`Φ_x(a • s) = a(x) • Φ_x(s)`, and the `j(bᵢ)` are linearly independent over `ℚ̄_ℓ`, then
`(aᵢ) ↦ ∑ aᵢ • ψ(bᵢ)|_U` is injective for every `U`. -/
theorem sectionsLinearMap_injective_of_eval_const {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl l) V] (j : M → V)
    (Φ : ∀ (U : X.ProEt) [IsAffine U.left] (_ : U.left), F.X.obj.obj (op U) →+ V)
    (hΦψ : ∀ (U : X.ProEt) [IsAffine U.left] (m : C(U.left, M)) (x : U.left),
      Φ U x (ψ U m) = j (m x))
    (hΦact : ∀ (U : X.ProEt) [IsAffine U.left] (x : U.left)
      (a : (adicConstantSheaf l X).obj.obj (op U)) (t : F.X.obj.obj (op U)),
      a.down.1 ∈ finiteIntermediateFieldValued l U.left →
        Φ U x (sectionAct F a t) = a.down.1 x • Φ U x t)
    {r : ℕ} (b : Fin r → M) (hb : LinearIndependent (PadicAlgCl l) (j ∘ b)) (U : X.ProEtᵒᵖ) :
    Function.Injective (sectionsLinearMap F
      (fun i ↦ ψ (proEtTop X) (ContinuousMap.const _ (b i))) U) := by
  refine sectionsLinearMap_injective_of_eval F _ (V := fun _ _ ↦ V) Φ hΦact
    (fun U _ x ↦ ?_) U
  have hb' (k : Fin r) : restrictTop F (ψ (proEtTop X) (ContinuousMap.const _ (b k))) (op U) =
      ψ U (ContinuousMap.const _ (b k)) :=
    (hψ (toProEtTop U) (ContinuousMap.const _ (b k))).symm
  simp only [hb', hΦψ, ContinuousMap.const_apply]
  exact hb

end AlgebraicGeometry.ProEtale.AdicSheaf
