/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# The local Frobenius and the local alternating trace of a Weil complex

Let `K` be a Weil complex on a `k₀`-scheme `X`, with geometric fiber `X̄ = X ×_{k₀} k̄`. A point
`g : Spec K ⟶ X` with values in a finite extension `K` of `k₀` with `qᵐ` elements, together with
an embedding `ι : K ↪ k̄`, gives a geometric point `x̄ : Spec k̄ ⟶ X̄` fixed by the `m`-th power
of the geometric Frobenius up to reparametrisation. The iterated Weil structure then induces the
local Frobenius `F_x^{(m)}` on the stalk `𝓗ʲ(K)_x̄` of every cohomology sheaf of `K`, and the
local alternating trace

`Tr(F_x^{(m)} | K_x̄) = ∑_j (-1)ʲ Tr(F_x^{(m)} | 𝓗ʲ(K)_x̄)`.

The conjugacy class of the local Frobenius does not depend on the embedding `ι`.

## Main definitions

- `AlgebraicGeometry.WeilComplex.stalk` (`definition-trace-function`): the stalk
  `𝓗ʲ(K)_x̄` at a closed point with its local Frobenius `F_x`.
- `AlgebraicGeometry.WeilComplex.stalkAtGeometricFiberPoint` (`definition-trace-function`):
  the stalk `𝓗ʲ(K)_x̄` with the local Frobenius `F_x^{(m)}`, at the geometric point attached to
  a point with values in a field with `qᵐ` elements and an embedding of that field into `k̄`.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_equiv_stalkAtGeometricFiberPoint`
  (`theorem-trace-formula-euler-product--1`): the local Frobenius operators attached to two
  embeddings are conjugate.

## Implementation notes

The blueprint defines `K_x̄ := L x̄^* For(K)` and its trace as the alternating sum of the traces
on the cohomology sheaves. The local alternating trace `Tr(F_x^{(n)} | K_x̄)` of
`definition-trace-function` is `AlgebraicGeometry.WeilComplex.traceFunction`
(`WeilConjectures.WeilSheaf.Stalk`), which takes that alternating sum as the definition: the
derived stalk is not used.

The remark `theorem-trace-formula-euler-product--1` of the blueprint only points to
`AlgebraicGeometry.WeilComplex.nonempty_equiv_stalkAtGeometricFiberPoint`; it is recorded as
`AlgebraicGeometry.WeilComplex.exists_frobeniusEnd_stalkAtGeometricFiberPoint_eq_conj`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {l : ℕ} [Fact l.Prime]
variable {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

variable (F : WeilSheaf k₀ l X)

/-- The stalk `F_x̄` of a Weil sheaf, with the local Frobenius `F_x^{(m)}`, at the geometric point
`x̄ = AlgebraicGeometry.Scheme.Hom.geometricFiberPoint ι g hg` over a point `g : Spec K ⟶ X`
with values in a field `K` with `qᵐ` elements, for an embedding `ι : K ↪ k̄` over `k₀`. -/
noncomputable def stalkAtGeometricFiberPoint {K : Type u} [Field K] [Algebra k₀ K] [Finite K]
    (ι : K →ₐ[k₀] AlgebraicClosure k₀) (g : Spec (.of K) ⟶ X)
    (hg : g ≫ (X ↘ Spec (CommRingCat.of k₀)) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
    (m : ℕ) (hK : Nat.card K = Nat.card k₀ ^ m) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  F.stalkAt _ m (Scheme.Hom.geometricFiberPoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) ι g hg m hK)

/-- Blueprint `theorem-trace-formula-euler-product--1`: Independence of the local Frobenius
operator from the embedding.

For a point `g : Spec K ⟶ X` with values in a field `K` with `qᵐ` elements and two embeddings
`ι, ι' : K ↪ k̄` over `k₀`, the local Frobenius operators `F_x^{(m)}` on the stalks of a Weil
sheaf at the two attached geometric points are conjugate. Both geometric points lie over the
image point of `g`, whose residue field embeds into the finite field `K`, so this is an instance
of `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAt`. -/
theorem nonempty_equiv_stalkAtGeometricFiberPoint {K : Type u} [Field K] [Algebra k₀ K]
    [Finite K] (ι ι' : K →ₐ[k₀] AlgebraicClosure k₀) (g : Spec (.of K) ⟶ X)
    (hg : g ≫ (X ↘ Spec (CommRingCat.of k₀)) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
    (m : ℕ) (hK : Nat.card K = Nat.card k₀ ^ m) :
    Nonempty ((F.stalkAtGeometricFiberPoint ι g hg m hK).Equiv
      (F.stalkAtGeometricFiberPoint ι' g hg m hK)) := by
  have h := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint_comp_geometricFiberProj_base ι g hg
  refine F.nonempty_equiv_stalkAt _ _
    (h.trans ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint_comp_geometricFiberProj_base
      ι' g hg).symm) (h ▸ X.mem_finitePoints.mpr ?_) m _ _
  exact Finite.of_injective _
    (X.descResidueField (Scheme.stalkClosedPointTo g)).hom.injective

end WeilSheaf

namespace WeilComplex

variable (K : WeilComplex k₀ l X)

/-- Blueprint `definition-trace-function`: Local Frobenius and local alternating trace.

The stalk `𝓗ʲ(For K)_x̄` of the `j`-th cohomology sheaf of a Weil complex at the geometric
point over a closed point `x`, with the local Frobenius `F_x`, obtained by iterating the Weil
isomorphism `deg x` times. The geometric point is attached to an embedding `κ(x) ↪ k̄` chosen
by `IsAlgClosed.lift` (`AlgebraicGeometry.WeilSheaf.stalk`). -/
noncomputable def stalk (j : ℤ) (x : X.finitePoints) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((homologySheaf j).obj K).stalk x

/-- Blueprint `definition-trace-function`: Local Frobenius and local alternating trace.

The stalk `𝓗ʲ(For K)_x̄` of the `j`-th cohomology sheaf of a Weil complex with the local
Frobenius `F_x^{(m)}`, at the geometric point attached to a point `g : Spec K ⟶ X` with values in
a field `K` with `qᵐ` elements and an embedding `ι : K ↪ k̄` over `k₀`. -/
noncomputable def stalkAtGeometricFiberPoint (j : ℤ) {K' : Type u} [Field K'] [Algebra k₀ K']
    [Finite K'] (ι : K' →ₐ[k₀] AlgebraicClosure k₀) (g : Spec (.of K') ⟶ X)
    (hg : g ≫ (X ↘ Spec (CommRingCat.of k₀)) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K')))
    (m : ℕ) (hK : Nat.card K' = Nat.card k₀ ^ m) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((homologySheaf j).obj K).stalkAtGeometricFiberPoint ι g hg m hK

/-- Blueprint `theorem-trace-formula-euler-product--1`: Independence of the local Frobenius
operator from the embedding.

For a point `g : Spec K' ⟶ X` with values in a field `K'` with `qᵐ` elements, two embeddings
`ι, ι' : K' ↪ k̄` over `k₀` and `j ∈ ℤ`, the local Frobenius operators `F_x^{(m)}` on the stalks
of the cohomology sheaf `𝓗ʲ(For K)` at the two attached geometric points are conjugate. For a
closed point `x` take `K' = κ(x)` and `m = deg x`. -/
theorem nonempty_equiv_stalkAtGeometricFiberPoint (j : ℤ) {K' : Type u} [Field K']
    [Algebra k₀ K'] [Finite K'] (ι ι' : K' →ₐ[k₀] AlgebraicClosure k₀) (g : Spec (.of K') ⟶ X)
    (hg : g ≫ (X ↘ Spec (CommRingCat.of k₀)) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K')))
    (m : ℕ) (hK : Nat.card K' = Nat.card k₀ ^ m) :
    Nonempty ((K.stalkAtGeometricFiberPoint j ι g hg m hK).Equiv
      (K.stalkAtGeometricFiberPoint j ι' g hg m hK)) :=
  ((homologySheaf j).obj K).nonempty_equiv_stalkAtGeometricFiberPoint ι ι' g hg m hK

/-- Blueprint `theorem-trace-formula-euler-product--1`: Pointer to the properties of the local
Frobenius.

The conjugacy class of the local Frobenius `F_x^{(m)}` on `𝓗ʲ(For K)_x̄` does not depend on the
embedding `ι : K' ↪ k̄` used to build the geometric point: for two embeddings the two operators
are conjugate by a linear isomorphism of the stalks. This independence is
`theorem-trace-formula-euler-product--1`
(`AlgebraicGeometry.WeilComplex.nonempty_equiv_stalkAtGeometricFiberPoint`), not part of the
construction. -/
theorem exists_frobeniusEnd_stalkAtGeometricFiberPoint_eq_conj (j : ℤ) {K' : Type u} [Field K']
    [Algebra k₀ K'] [Finite K'] (ι ι' : K' →ₐ[k₀] AlgebraicClosure k₀) (g : Spec (.of K') ⟶ X)
    (hg : g ≫ (X ↘ Spec (CommRingCat.of k₀)) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K')))
    (m : ℕ) (hK : Nat.card K' = Nat.card k₀ ^ m) :
    ∃ e : (K.stalkAtGeometricFiberPoint j ι g hg m hK).carrier ≃ₗ[PadicAlgCl l]
        (K.stalkAtGeometricFiberPoint j ι' g hg m hK).carrier,
      (K.stalkAtGeometricFiberPoint j ι' g hg m hK).frobeniusEnd =
        e.conj (K.stalkAtGeometricFiberPoint j ι g hg m hK).frobeniusEnd :=
  let ⟨e⟩ := K.nonempty_equiv_stalkAtGeometricFiberPoint j ι ι' g hg m hK
  ⟨e.toLinearEquiv, e.frobeniusEnd_eq_conj⟩

end WeilComplex

end AlgebraicGeometry
