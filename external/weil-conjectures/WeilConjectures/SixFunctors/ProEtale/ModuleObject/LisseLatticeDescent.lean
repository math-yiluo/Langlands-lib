/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeValues

/-!
# Descent of lisse `E`-sheaves to `𝒪_E` from integral transition values

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`, `S` a scheme and `L` a module object over `E_S`
trivialised, `e_k : E_{V_k}ⁿ ≅ f_k^* L`, on a finite pro-étale cover `{f_k : V_k ⟶ S}`. For
`a : W ⟶ V_j` and `b : W ⟶ V_k` with `a ≫ f_j = b ≫ f_k`, the transition morphism from the
pullback of `e_k` to the pullback of `e_j` is a matrix of continuous functions `W → E`; its values
are invertible matrices `T_{jk}(a, b)(x) ∈ GL_n(E)`
(`AlgebraicGeometry.ProEtale.exists_transitionValues`). They

* are continuous in `x`, together with their inverses;
* are compatible with precomposition: `T_{jk}(c ≫ a, c ≫ b)(x) = T_{jk}(a, b)(c x)`;
* satisfy the cocycle condition `T_{jl}(a, c) = T_{jk}(a, b) T_{kl}(b, c)` and `T_{kk}(a, a) = 1`.

If `g_k : V_k → GL_n(E)` are continuous and the conjugates `g_j(p₁ w)⁻¹ T_{jk}(p₁, p₂)(w) g_k(p₂ w)`
on the fibre products `V_j ×_S V_k` and their inverses have integral entries, then `L` descends
to a locally free `𝒪_{E,S}`-module: the trivialisations changed by the `g_k` have transition
matrices with entries in `𝒪_E`, and the descent of
`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_isDefinedOver` applies.

We also show that trivialisations of a locally free `E_S`-module over overlapping charts have the
same rank (`AlgebraicGeometry.ProEtale.rank_eq_of_comp_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

/-- Matrices with two-sided inverses over a field are square. -/
lemma Matrix.eq_of_mul_eq_one_of_mul_eq_one {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin m) K) (hBA : B * A = 1)
    (hAB : A * B = 1) : n = m := by
  have h₁ : n ≤ m := by
    have := (Matrix.rank_mul_le_right B A).trans A.rank_le_height
    rwa [hBA, Matrix.rank_one, Fintype.card_fin] at this
  have h₂ : m ≤ n := by
    have := (Matrix.rank_mul_le_right A B).trans B.rank_le_height
    rwa [hAB, Matrix.rank_one, Fintype.card_fin] at this
  omega

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R]

/-- Evaluation commutes with the matrix of a composite. -/
private lemma finFreeMatrix_map_comp {K : Type*} [Semiring K]
    (ρ : End (regular R) →+* K) {l m n : ℕ}
    (φ : finiteFree R l ⟶ finiteFree R m) (ψ : finiteFree R m ⟶ finiteFree R n) :
    (finFreeMatrix (φ ≫ ψ)).map ρ = (finFreeMatrix ψ).map ρ * (finFreeMatrix φ).map ρ := by
  rw [finFreeMatrix_comp, Matrix.map_mul]

/-- Evaluation sends the matrix of the identity to the identity matrix. -/
private lemma finFreeMatrix_map_id {K : Type*} [Semiring K]
    (ρ : End (regular R) →+* K) (n : ℕ) :
    (finFreeMatrix (𝟙 (finiteFree R n))).map ρ = 1 := by
  rw [finFreeMatrix_id, Matrix.map_one _ (map_zero ρ) (map_one ρ)]

/-- Entries of a product of three matrices evaluate to the product of their evaluations. -/
private lemma finFreeEntry_matrixTriple_eval {K : Type*} [Semiring K]
    (ρ : End (regular R) →+* K) {n : ℕ}
    (A B D : Matrix (Fin n) (Fin n) (End (regular R))) (i j : Fin n) :
    ρ (finFreeEntry (finFreeOfMatrix (A * B * D)) i j) =
      (A.map ρ * B.map ρ * D.map ρ) i j := by
  rw [← finFreeMatrix_apply, finFreeMatrix_finFreeOfMatrix]
  change ((A * B * D).map ρ) i j = _
  rw [Matrix.map_mul, Matrix.map_mul]

/-- Evaluation in a field detects the rank of finite free module objects. -/
private lemma rank_eq_of_finiteFree_iso {K : Type*} [Field K]
    (ρ : End (regular R) →+* K) {m n : ℕ} (e : finiteFree R m ≅ finiteFree R n) :
    m = n := by
  apply Matrix.eq_of_mul_eq_one_of_mul_eq_one
    ((finFreeMatrix e.hom).map ρ) ((finFreeMatrix e.inv).map ρ)
  · rw [← Matrix.map_mul, ← finFreeMatrix_comp, e.hom_inv_id, finFreeMatrix_id,
      Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  · rw [← Matrix.map_mul, ← finFreeMatrix_comp, e.inv_hom_id, finFreeMatrix_id,
      Matrix.map_one _ (map_zero ρ) (map_one ρ)]

/-- Continuous invertible matrices give automorphisms of a finite free module object
when its coefficient endomorphisms are continuous functions. -/
private lemma exists_finFreeIso_of_continuous {X K : Type*} [TopologicalSpace X]
    [TopologicalSpace K] [Ring K] [IsTopologicalRing K]
    (ev : End (regular R) ≃+* C(X, K)) {n : ℕ} (g : X → GL (Fin n) K)
    (hg : ∀ i i', Continuous fun x ↦ (g x : Matrix (Fin n) (Fin n) K) i i')
    (hg' : ∀ i i', Continuous fun x ↦ (((g x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i') :
    ∃ G : finiteFree R n ≅ finiteFree R n,
      ∀ x, (finFreeMatrix G.hom).map (fun t ↦ ev t x) = (g x : Matrix (Fin n) (Fin n) K) ∧
        (finFreeMatrix G.inv).map (fun t ↦ ev t x) =
          (((g x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  classical
  let ρ (x : X) : End (regular R) →+* K :=
    ((Pi.evalRingHom (fun _ : X ↦ K) x).comp ContinuousMap.coeFnRingHom).comp ev.toRingHom
  have hext (M N : Matrix (Fin n) (Fin n) (End (regular R)))
      (h : ∀ x, M.map (ρ x) = N.map (ρ x)) : M = N :=
    Matrix.ext fun i i' ↦ ev.injective (ContinuousMap.ext fun x ↦
      congrFun (congrFun (h x) i) i')
  let A : Matrix (Fin n) (Fin n) (End (regular R)) :=
    Matrix.of fun i i' ↦ ev.symm ⟨fun x ↦ (g x : Matrix (Fin n) (Fin n) K) i i', hg i i'⟩
  let B : Matrix (Fin n) (Fin n) (End (regular R)) :=
    Matrix.of fun i i' ↦ ev.symm
      ⟨fun x ↦ (((g x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i', hg' i i'⟩
  have hA (x : X) : A.map (ρ x) = (g x : Matrix (Fin n) (Fin n) K) :=
    Matrix.ext fun i i' ↦ by simp [A, ρ]
  have hB (x : X) : B.map (ρ x) = (((g x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    Matrix.ext fun i i' ↦ by simp [B, ρ]
  have hAB : A * B = 1 := hext _ _ fun x ↦ by
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  have hBA : B * A = 1 := hext _ _ fun x ↦ by
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  refine ⟨finFreeIsoOfMatrix A B hAB hBA, fun x ↦ ⟨?_, ?_⟩⟩
  · change (finFreeMatrix (finFreeOfMatrix A)).map (ρ x) = _
    rw [finFreeMatrix_finFreeOfMatrix, hA]
  · change (finFreeMatrix (finFreeOfMatrix B)).map (ρ x) = _
    rw [finFreeMatrix_finFreeOfMatrix, hB]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- **Ranks of trivialisations agree on overlaps.** Two trivialisations `E_Vⁿ ≅ f^* L` and
`E_V'ⁿ' ≅ f'^* L` whose pullbacks to a nonempty scheme `W` are comparable have the same rank: the
values at a point of the transition matrices are mutually inverse matrices over `E`. -/
theorem rank_eq_of_comp_eq {S V V' W : Scheme.{u}}
    {L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) S)}
    {f : V ⟶ S} {f' : V' ⟶ S} {n n' : ℕ}
    (e : Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj E) V) n ≅
      (f)^*⟦Profinite.continuousMapRingObj E⟧.obj L)
    (e' : Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj E) V') n' ≅
      (f')^*⟦Profinite.continuousMapRingObj E⟧.obj L)
    (a : W ⟶ V) (b : W ⟶ V') (h : a ≫ f = b ≫ f') (x : W) : n = n' := by
  obtain ⟨ev, -, -⟩ := exists_subfieldEndRingEquiv.{u} ℓ E
  let ρ :=
    ((Pi.evalRingHom (fun _ : W ↦ (E : Type)) x).comp ContinuousMap.coeFnRingHom).comp
      (ev W).toRingHom
  apply Mod.rank_eq_of_finiteFree_iso ρ
  exact (upperStarFiniteFreeIso (Profinite.continuousMapRingObj E) a n).symm ≪≫
    (a)^*⟦Profinite.continuousMapRingObj E⟧.mapIso e ≪≫
    ((CondensedRing.upperStarComp (Profinite.continuousMapRingObj E) a f).app L).symm ≪≫
    (CondensedRing.upperStarCongr (Profinite.continuousMapRingObj E) h).app L ≪≫
    (CondensedRing.upperStarComp (Profinite.continuousMapRingObj E) b f').app L ≪≫
    ((b)^*⟦Profinite.continuousMapRingObj E⟧.mapIso e').symm ≪≫
    upperStarFiniteFreeIso (Profinite.continuousMapRingObj E) b n'

/-- **Transition values of a trivialisation, and descent from integral values.** For a finite
pro-étale cover `{f_k : V_k ⟶ S}` trivialising `L`, `e_k : E_{V_k}ⁿ ≅ f_k^* L`, the values
`Tval j k W a b h x ∈ GL_n(E)` of the transition matrices from the pullback of `e_k` along `b` to
the pullback of `e_j` along `a` are continuous, compatible with precomposition and satisfy the
cocycle condition. If continuous `g_k : V_k → GL_n(E)` make the conjugated values
`g_j(p₁ w)⁻¹ T_{jk}(p₁, p₂)(w) g_k(p₂ w)` on `V_j ×_S V_k` integral, together with their inverses,
then `L ≅ E_S ⊗_{𝒪_{E,S}} L₀` for a locally free `𝒪_{E,S}`-module `L₀`. -/
theorem exists_transitionValues {S : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) S))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S) [Finite 𝒰.I₀] {n : ℕ}
    (e : ∀ k, Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj E) (𝒰.X k)) n ≅
      (𝒰.f k)^*⟦Profinite.continuousMapRingObj E⟧.obj L) :
    ∃ Tval : ∀ (j k : 𝒰.I₀) (W : Scheme.{u}) (a : W ⟶ 𝒰.X j) (b : W ⟶ 𝒰.X k),
        a ≫ 𝒰.f j = b ≫ 𝒰.f k → W → GL (Fin n) E.1,
      (∀ j k W a b h i i', Continuous fun x ↦
        ((Tval j k W a b h x : GL (Fin n) E.1) : Matrix (Fin n) (Fin n) E.1) i i') ∧
      (∀ j k W a b h i i', Continuous fun x ↦
        (((Tval j k W a b h x)⁻¹ : GL (Fin n) E.1) : Matrix (Fin n) (Fin n) E.1) i i') ∧
      (∀ j k (W W' : Scheme.{u}) (c : W' ⟶ W) a b h h' x,
        Tval j k W' (c ≫ a) (c ≫ b) h' x = Tval j k W a b h (c.base x)) ∧
      (∀ j k l W a b c h h' h'' x,
        Tval j l W a c h'' x = Tval j k W a b h x * Tval k l W b c h' x) ∧
      (∀ k W a h x, Tval k k W a a h x = 1) ∧
      ∀ g : ∀ k, 𝒰.X k → GL (Fin n) E.1,
        (∀ k i i', Continuous fun v ↦
          ((g k v : GL (Fin n) E.1) : Matrix (Fin n) (Fin n) E.1) i i') →
        (∀ k i i', Continuous fun v ↦
          (((g k v)⁻¹ : GL (Fin n) E.1) : Matrix (Fin n) (Fin n) E.1) i i') →
        (∀ j k (w : ↥(pullback (𝒰.f j) (𝒰.f k))) i i',
          ‖(((g j ((pullback.fst (𝒰.f j) (𝒰.f k)).base w))⁻¹ *
            Tval j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
              pullback.condition w * g k ((pullback.snd (𝒰.f j) (𝒰.f k)).base w) :
                GL (Fin n) E.1) : Matrix (Fin n) (Fin n) E.1) i i'‖ ≤ 1) →
        (∀ j k (w : ↥(pullback (𝒰.f j) (𝒰.f k))) i i',
          ‖((((g j ((pullback.fst (𝒰.f j) (𝒰.f k)).base w))⁻¹ *
            Tval j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
              pullback.condition w * g k ((pullback.snd (𝒰.f j) (𝒰.f k)).base w))⁻¹ :
                GL (Fin n) E.1) : Matrix (Fin n) (Fin n) E.1) i i'‖ ≤ 1) →
        ∃ L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
            (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) S),
          IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) S) L₀ ∧
            Nonempty ((Mod.extendScalars (padicIntegersToPadicSubfield S ℓ E)).obj L₀ ≅ L) := by
  classical
  obtain ⟨ev, hev, hint⟩ := exists_subfieldEndRingEquiv.{u} ℓ E
  obtain ⟨T, hTtrans, hTself, hTcomp, hTdef⟩ := exists_frameTransitions
    (Profinite.continuousMapRingObj E) (padicIntegersRingObjToContinuousMapRingObj ℓ E) L 𝒰.f e
  -- values at points
  let ρ (W : Scheme.{u}) (x : W) :=
    ((Pi.evalRingHom (fun _ : W ↦ (E : Type)) x).comp ContinuousMap.coeFnRingHom).comp
      (ev W).toRingHom
  let Mv (j k : 𝒰.I₀) (W : Scheme.{u}) (a : W ⟶ 𝒰.X j) (b : W ⟶ 𝒰.X k)
      (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) (x : W) : Matrix (Fin n) (Fin n) E.1 :=
    (Mod.finFreeMatrix (T j k W a b h)).map (ρ W x)
  have hMv_mul (j k l : 𝒰.I₀) (W : Scheme.{u}) (a : W ⟶ 𝒰.X j) (b : W ⟶ 𝒰.X k)
      (c : W ⟶ 𝒰.X l) (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) (h' : b ≫ 𝒰.f k = c ≫ 𝒰.f l)
      (h'' : a ≫ 𝒰.f j = c ≫ 𝒰.f l) (x : W) :
      Mv j k W a b h x * Mv k l W b c h' x = Mv j l W a c h'' x := by
    exact (Mod.finFreeMatrix_map_comp (ρ W x) (T k l W b c h')
      (T j k W a b h)).symm.trans
        (congrArg (fun t ↦ (Mod.finFreeMatrix t).map (ρ W x))
          (hTtrans j k l W a b c h h' h''))
  have hMv_one (k : 𝒰.I₀) (W : Scheme.{u}) (a : W ⟶ 𝒰.X k) (h : a ≫ 𝒰.f k = a ≫ 𝒰.f k)
      (x : W) : Mv k k W a a h x = 1 := by
    exact (congrArg (fun t ↦ (Mod.finFreeMatrix t).map (ρ W x))
      (hTself k W a h)).trans (Mod.finFreeMatrix_map_id (ρ W x) n)
  have hMv_comp (j k : 𝒰.I₀) (W W' : Scheme.{u}) (c : W' ⟶ W) (a : W ⟶ 𝒰.X j)
      (b : W ⟶ 𝒰.X k) (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) (h' : (c ≫ a) ≫ 𝒰.f j = (c ≫ b) ≫ 𝒰.f k)
      (x : W') : Mv j k W' (c ≫ a) (c ≫ b) h' x = Mv j k W a b h (c.base x) := by
    refine (congrArg (fun M ↦ M.map (ρ W' x))
      (hTcomp j k W W' c a b h h')).trans ?_
    exact Matrix.ext fun i i' ↦ hev W' W c _ x
  have hMv_cont (j k : 𝒰.I₀) (W : Scheme.{u}) (a : W ⟶ 𝒰.X j) (b : W ⟶ 𝒰.X k)
      (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) (i i' : Fin n) : Continuous fun x ↦ Mv j k W a b h x i i' :=
    (ev W (Mod.finFreeMatrix (T j k W a b h) i i')).continuous
  -- the values, as invertible matrices
  let Tval (j k : 𝒰.I₀) (W : Scheme.{u}) (a : W ⟶ 𝒰.X j) (b : W ⟶ 𝒰.X k)
      (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) (x : W) : GL (Fin n) E.1 :=
    ⟨Mv j k W a b h x, Mv k j W b a h.symm x,
      (hMv_mul j k j W a b a h h.symm rfl x).trans (hMv_one j W a rfl x),
      (hMv_mul k j k W b a b h.symm h rfl x).trans (hMv_one k W b rfl x)⟩
  refine ⟨Tval, fun j k W a b h i i' ↦ hMv_cont j k W a b h i i',
    fun j k W a b h i i' ↦ hMv_cont k j W b a h.symm i i',
    fun j k W W' c a b h h' x ↦ Units.ext (hMv_comp j k W W' c a b h h' x),
    fun j k l W a b c h h' h'' x ↦ Units.ext (hMv_mul j k l W a b c h h' h'' x).symm,
    fun k W a h x ↦ Units.ext (hMv_one k W a h x), ?_⟩
  intro g hg hg' hint₁ hint₂
  obtain ⟨G, hGv⟩ := Classical.axiomOfChoice fun k ↦
    Mod.exists_finFreeIso_of_continuous (ev (𝒰.X k)) (g k) (hg k) (hg' k)
  have hP (j k : 𝒰.I₀) := IsPullback.of_hasPullback (𝒰.f j) (𝒰.f k)
  -- the restriction of the matrices of the `G k` along a morphism
  have hGres (k : 𝒰.I₀) (P : Scheme.{u}) (p : P ⟶ 𝒰.X k) (x : P) :
      ((Mod.finFreeMatrix (G k).hom).map (restrictEnd (Profinite.continuousMapRingObj E) p)).map
          (ρ P x) = ((g k (p.base x) : GL (Fin n) E.1) : Matrix (Fin n) (Fin n) E.1) ∧
        ((Mod.finFreeMatrix (G k).inv).map (restrictEnd (Profinite.continuousMapRingObj E) p)).map
          (ρ P x) = (((g k (p.base x))⁻¹ : GL (Fin n) E.1) : Matrix (Fin n) (Fin n) E.1) := by
    exact ⟨(Matrix.ext fun i i' ↦ hev P _ p _ x).trans (hGv k (p.base x)).1,
      (Matrix.ext fun i i' ↦ hev P _ p _ x).trans (hGv k (p.base x)).2⟩
  have hdef (j k : 𝒰.I₀) := hTdef G j k (hP j k)
  have hdef' (j k : 𝒰.I₀) := And.intro
    ((hdef j k).1 fun i i' ↦ by
      refine (hint _ _ fun x ↦ ?_).imp fun s hs ↦ hs.symm
      change ‖ρ _ x _‖ ≤ 1
      rw [Mod.finFreeEntry_matrixTriple_eval, (hGres k _ _ x).2, (hGres j _ _ x).1]
      have key := hint₂ j k x i' i
      rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul,
        ← Matrix.mul_assoc] at key
      exact key)
    ((hdef j k).2 fun i i' ↦ by
      refine (hint _ _ fun x ↦ ?_).imp fun s hs ↦ hs.symm
      change ‖ρ _ x _‖ ≤ 1
      rw [Mod.finFreeEntry_matrixTriple_eval, (hGres j _ _ x).2, (hGres k _ _ x).1]
      have key := hint₁ j k x i' i
      rw [Units.val_mul, Units.val_mul] at key
      exact key)
  exact exists_isLocallyFree_extendScalars_iso_of_isDefinedOver
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) L 𝒰 (fun k ↦ G k ≪≫ e k) hP
    (fun k ↦ mono_extendRestrictAdjunction_unit_app_finiteFree_padicIntegers ℓ E _ n) hdef'

end AlgebraicGeometry.ProEtale
