/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Extension.ExtendScalars
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.RingTheory.JacobiZariskiConnectingMapNaturality
import WeilConjectures.RingTheory.SubsingletonH1CotangentOfCharP

/-!
# Residue-field differential injectivity in positive characteristic

Source: Stacks Project, More on Algebra, Proposition Tag 07E5, proof of (3) ⇔ (4)
(blueprint: lem-weil-pbc-h1-injective-differentials-injective-char-p).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
/-- For a Noetherian local `k`-algebra in positive characteristic, injectivity of the
canonical map from first cotangent homology to the maximal ideal's conormal module
implies injectivity of the residue-field base change of the map on prime-field differentials.
Tensor factors are reversed from the source by the canonical tensor commutativity isomorphisms.

Source: Stacks Project, More on Algebra, Proposition Tag 07E5, proof of (3) ⇔ (4).
Proof:
1. Injectivity of `γ` implies injectivity of `H1Cotangent.map k A K K`, by applying
   the conormal equivalence to an equality of its images.
2. The connecting map `∂A` for `𝔽_p → A → K` is injective: prime-field H1 vanishes
   (lem-weil-pbc-field-char-p-h1-cotangent-vanishing), and Mathlib's
   `H1Cotangent.exact_map_δ` identifies its kernel with the image of that zero module
   (lem-weil-pbc-jacobi-zariski-middle-exactness).
3. Connecting-map naturality (lem-weil-pbc-jacobi-zariski-connecting-map-naturality)
   gives `∂A ∘ H1Cotangent.map k A K K = λ ∘ ∂k`. The comparison map supplied there
   equals this statement's tensor lift by its formula on universal differentials.
4. The maps to `Ω[K⁄𝔽_p]` commute with `λ`, as checked on `x ⊗ da` using
   the universal derivation (def-weil-pbc-kahler-differentials).
5. If `λ(x) = 0`, step 4 and Mathlib's `H1Cotangent.exact_δ_mapBaseChange`
   (lem-weil-pbc-jacobi-zariski-middle-exactness) give `x = ∂k(h)`. Step 3 gives
   `∂A(H1Cotangent.map k A K K h) = 0`. Injectivity from steps 2 and 1 gives
   `h = 0`, hence `x = 0`.

(blueprint: lem-weil-pbc-h1-injective-differentials-injective-char-p) -/
theorem differentials_injective_of_h1Cotangent_injective_charP
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP k p] :
    letI := ZMod.algebra k p
    letI := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
    let K := IsLocalRing.ResidueField A
    let P := Extension.ofSurjective (Algebra.ofId A K) IsLocalRing.residue_surjective
    let γ := P.h1CotangentEquivCotangent.toLinearMap.comp (H1Cotangent.map k A K K)
    let lambdaMap := (TensorProduct.isBaseChange k Ω[k⁄ZMod p] K).lift
      (((TensorProduct.mk A K Ω[A⁄ZMod p] 1).restrictScalars k).comp
        (KaehlerDifferential.map (ZMod p) (ZMod p) k A))
    Function.Injective γ → Function.Injective lambdaMap := by
  let := ZMod.algebra k p
  let := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
  let K := IsLocalRing.ResidueField A
  let P := Extension.ofSurjective (Algebra.ofId A K) IsLocalRing.residue_surjective
  let γ := P.h1CotangentEquivCotangent.toLinearMap.comp (H1Cotangent.map k A K K)
  let lambdaMap := (TensorProduct.isBaseChange k Ω[k⁄ZMod p] K).lift
    (((TensorProduct.mk A K Ω[A⁄ZMod p] 1).restrictScalars k).comp
      (KaehlerDifferential.map (ZMod p) (ZMod p) k A))
  change Function.Injective γ → Function.Injective lambdaMap
  intro hγ
  have hmap : Function.Injective (H1Cotangent.map k A K K) := by
    intro x y h
    apply hγ
    change P.h1CotangentEquivCotangent _ = P.h1CotangentEquivCotangent _
    exact congrArg P.h1CotangentEquivCotangent h
  let : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hzero : Subsingleton (H1Cotangent (ZMod p) K) := by
    convert subsingleton_h1Cotangent_of_charP p (Fact.out : p.Prime).pos K using 1
    congr 1
    exact Subsingleton.elim _ _
  let := hzero
  have hδ : Function.Injective (H1Cotangent.δ (ZMod p) A K) := by
    apply LinearMap.ker_eq_bot.mp
    rw [(H1Cotangent.exact_map_δ (ZMod p) A K).linearMap_ker_eq]
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx, map_zero, LinearMap.zero_apply]
  obtain ⟨c, hc, hleft, hquot⟩ :=
    jacobiZariski_connectingMap_naturality (ZMod p) k A (IsLocalRing.maximalIdeal A)
  have hlambda (x : K) (y : Ω[k⁄ZMod p]) :
      lambdaMap (x ⊗ₜ[k] y) =
        x ⊗ₜ[A] KaehlerDifferential.map (ZMod p) (ZMod p) k A y := by
    have hy : lambdaMap (1 ⊗ₜ[k] y) =
        1 ⊗ₜ[A] KaehlerDifferential.map (ZMod p) (ZMod p) k A y :=
      IsBaseChange.lift_eq _ _ y
    calc
      lambdaMap (x ⊗ₜ[k] y) = lambdaMap (x • (1 ⊗ₜ[k] y)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = x • lambdaMap (1 ⊗ₜ[k] y) := map_smul _ _ _
      _ = x ⊗ₜ[A] KaehlerDifferential.map (ZMod p) (ZMod p) k A y := by
        rw [hy, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hc_eq : c = lambdaMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    obtain ⟨f, rfl⟩ := KaehlerDifferential.linearCombination_surjective (ZMod p) k y
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [TensorProduct.tmul_add, hf, hg]
    | single a r =>
      simp only [Finsupp.linearCombination_single, TensorProduct.tmul_smul]
      have hh := hlambda (r • x) (KaehlerDifferential.D (ZMod p) k a)
      simp only [KaehlerDifferential.map_D] at hh
      exact (hc (r • x) a).trans hh.symm
  have hnatural : (H1Cotangent.δ (ZMod p) A K).comp (H1Cotangent.map k A K K) =
      lambdaMap.comp (H1Cotangent.δ (ZMod p) k K) := by
    rw [← LinearMap.comp_assoc, hquot] at hleft
    exact hleft.trans (congrArg (fun f ↦ f.comp (H1Cotangent.δ (ZMod p) k K)) hc_eq)
  have hmiddle : (KaehlerDifferential.mapBaseChange (ZMod p) A K).comp lambdaMap =
      KaehlerDifferential.mapBaseChange (ZMod p) k K := by
    have hm : ((KaehlerDifferential.map (ZMod p) (ZMod p) A K).restrictScalars k).comp
        (KaehlerDifferential.map (ZMod p) (ZMod p) k A) =
        KaehlerDifferential.map (ZMod p) (ZMod p) k K := by
      apply Derivation.liftKaehlerDifferential_unique
      ext a
      change KaehlerDifferential.map (ZMod p) (ZMod p) A K
        (KaehlerDifferential.map (ZMod p) (ZMod p) k A
          (KaehlerDifferential.D (ZMod p) k a)) =
        KaehlerDifferential.map (ZMod p) (ZMod p) k K
          (KaehlerDifferential.D (ZMod p) k a)
      simp only [KaehlerDifferential.map_D]
      rw [← IsScalarTower.algebraMap_apply k A K]
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    simp only [LinearMap.comp_apply, hlambda, KaehlerDifferential.mapBaseChange_tmul]
    exact congrArg (x • ·) (LinearMap.congr_fun hm y)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hw : KaehlerDifferential.mapBaseChange (ZMod p) k K x = 0 := by
    rw [← hmiddle, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨h, rfl⟩ := (H1Cotangent.exact_δ_mapBaseChange (ZMod p) k K x).mp hw
  have hh : h = 0 := hmap (hδ (by
    rw [← LinearMap.comp_apply, hnatural, LinearMap.comp_apply, hx, map_zero, map_zero]))
  rw [hh, map_zero]

end Algebra
