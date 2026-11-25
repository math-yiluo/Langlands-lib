/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.PuncturedLisse
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.TraceFormula.CurveLocal.Model

/-!

# The cover datum of the prime-to-`ℓ` covers

The construction of blueprint `lemma-tangent-cones-on-cover` is organised around a
*cover datum* (`AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum`): a smooth curve `C` with a
finite morphism `p : C ⟶ X`, a `k`-point `c` over `y` at which `p` has ramification index `e`
prime to `ℓ`, an open neighbourhood `W` of `y` over whose punctured part `W ∖ y` the morphism `p`
is étale, and a finite étale Galois cover of `p⁻¹(W ∖ y)` with group a finite `ℓ`-group
trivializing the terms of flat constructible models of `L` and `K`.

In the blueprint the covers `X' ⟶ X`, `Y' ⟶ Y` of the strictly local traits are obtained by
normalizing the strictly local traits in the fixed fields of `ℓ`-Sylow subgroups; here one global
cover of a neighbourhood of `y` serves for both factors: the `ℓ`-Sylow quotient `V ⟶ W ∖ y` of a
Galois cover trivializing the terms has degree `d` prime to `ℓ`
(`AlgebraicGeometry.Scheme.exists_sylow_galoisCover_trivializing`), its normalization `C` is a
smooth curve finite over `X`, and as the ramification indices of the points over `y` add up to
`d`, one of them is prime to `ℓ`. Taking the same cover on both factors, the degrees agree, so no
equalizing extensions are needed.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

omit [IsAlgClosed k] in
/-- The point `y` of the model is a closed point. -/
lemma isClosed_y : IsClosed ({M.y.base (default : Spec (.of k))} : Set M.X) := by
  have : IsClosedImmersion M.y := by
    have : IsClosedImmersion (M.y ≫ M.f) := by
      rw [M.y_comp]
      infer_instance
    exact IsClosedImmersion.of_comp M.y M.f
  have h := M.y.isClosedEmbedding.isClosed_range
  have hr : Set.range M.y.base = {M.y.base (default : Spec (.of k))} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [Subsingleton.elim w default]
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  rwa [hr] at h

/-- **The cover datum** of blueprint `lemma-tangent-cones-on-cover` for bounded complexes
`PL`, `PK` of sheaves on `X` (flat constructible models of `L` and `K`): a smooth curve `C` finite
over an open neighbourhood `U` of `y`, a `k`-point `c` over `y` with ramification index `e` prime
to `ℓ` (the image of a uniformizer at `y` is a unit times the `e`-th power of a uniformizer at
`c`), an open neighbourhood `W` of `y` over whose punctured part `p` is étale, and a finite étale
Galois cover of `p⁻¹(W ∖ y)` with group a finite `ℓ`-group over which the pullbacks of `PL`,
`PK` are isomorphic, as complexes, to constant complexes on bounded complexes of finite modules
(the lisse models with monodromy through the `ℓ`-group). -/
structure CoverDatum (ℓ : ℕ) {Λ : Type (u + 1)} [CommRing Λ]
    (PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) where
  /-- The cover curve. -/
  C : Scheme.{u}
  /-- Its structure morphism. -/
  fC : C ⟶ Spec (.of k)
  [smoothOfRelativeDimension : SmoothOfRelativeDimension 1 fC]
  [isSeparated : IsSeparated fC]
  /-- The cover. -/
  p : C ⟶ M.X
  /-- An open neighbourhood of `y` over which `p` is finite. -/
  U : M.X.Opens
  mem_U : M.y.base (default : Spec (.of k)) ∈ U
  /-- The finite morphism `C ⟶ U`. -/
  pU : C ⟶ U.toScheme
  [isFinite : IsFinite pU]
  pU_ι : pU ≫ U.ι = p
  p_comp : p ≫ M.f = fC
  /-- The point over `y`. -/
  c : Spec (.of k) ⟶ C
  c_comp : c ≫ p = M.y
  /-- The ramification index at `c`. -/
  e : ℕ
  one_le_e : 1 ≤ e
  not_dvd_e : ¬ ℓ ∣ e
  ramification : ∀ u : M.X.presheaf.stalk (M.y.base (default : Spec (.of k))),
    Ideal.span {u} = IsLocalRing.maximalIdeal _ →
    ∃ w ξ : C.presheaf.stalk (c.base (default : Spec (.of k))), IsUnit w ∧
      Ideal.span {ξ} = IsLocalRing.maximalIdeal _ ∧
      (M.X.presheaf.stalkSpecializes (show p.base (c.base default) ⤳ M.y.base default by
          rw [← c_comp]; rfl) ≫
        p.stalkMap (c.base default)).hom u = w * ξ ^ e
  /-- The neighbourhood of `y` over whose punctured part `p` is étale. -/
  W : M.X.Opens
  mem_W : M.y.base (default : Spec (.of k)) ∈ W
  etale : Etale (p ∣_ (puncturedOpens W _ M.isClosed_y))
  /-- The `ℓ`-group trivializing the terms. -/
  G : Type (u + 1)
  [group : Group G]
  [finite : Finite G]
  isPGroup : IsPGroup ℓ G
  /-- The Galois cover trivializing the terms. -/
  galois : Scheme.GaloisCover G (p ⁻¹ᵁ puncturedOpens W _ M.isClosed_y).toScheme
  trivializes : ∀ P ∈ ({PL, PK} : Set _), ∃ (Cx : CochainComplex (ModuleCat.{u + 1} Λ) ℤ)
    (a b : ℤ) (_ : Cx.IsStrictlyGE a) (_ : Cx.IsStrictlyLE b) (_ : ∀ n, Finite (Cx.X n)),
    Nonempty (((upperStar (ModuleCat.{u + 1} Λ)
      (galois.π ≫ (p ⁻¹ᵁ puncturedOpens W _ M.isClosed_y).ι ≫ p)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅
      ((constantSheaf galois.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Cx)

end AlgebraicGeometry.Etale.CurveLocalModel
