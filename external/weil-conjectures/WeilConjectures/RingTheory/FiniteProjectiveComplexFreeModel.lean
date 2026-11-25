/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite free replacement of bounded above finite projective complexes

Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U, (3) implies (1).
(blueprint: lem-pc-finite-projective-complex-free-model).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex

/-- Split a finite free surjection and use its kernel as a finite projective complement. -/
private theorem exists_complement (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    ∃ C : ModuleCat.{u} R, Module.Finite R C ∧ Module.Projective R C ∧
      Module.Free R (M × C) := by
  obtain ⟨r, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hfg' (m : M) : f (g m) = m := DFunLike.congr_fun hfg m
  let K := LinearMap.ker f
  let k : (Fin r → R) →ₗ[R] K :=
    { toFun v := ⟨v - g (f v), by simp [K, hfg']⟩
      map_add' v w := by ext; simp; abel
      map_smul' a v := by ext; simp [smul_sub] }
  have hk (v : K) : k v = v := by
    ext
    simp [k, K]
  have hksurj : Function.Surjective k := fun v ↦ ⟨v, hk v⟩
  have hfin : Module.Finite R K := Module.Finite.of_surjective k hksurj
  have hproj : Module.Projective R K :=
    Module.Projective.of_split K.subtype k (LinearMap.ext hk)
  let e : (M × K) ≃ₗ[R] (Fin r → R) :=
    { toLinearMap := g.coprod K.subtype
      invFun v := (f v, k v)
      left_inv v := by
        rcases v with ⟨m, z⟩
        apply Prod.ext
        · simp [hfg', K]
        · ext
          simp [k, hfg', K]
      right_inv v := by
        change g (f v) + (v - g (f v)) = v
        abel }
  have hfree : Module.Free R (M × K) := Module.Free.of_equiv e.symm
  exact ⟨ModuleCat.of R K, hfin, hproj, hfree⟩

set_option backward.isDefEq.respectTransparency false in
/-- Add consecutive contractible complement pairs to a natural-number chain complex. -/
private theorem nat_free_model (R : Type u) [CommRing R]
    (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ n : ℕ, Module.Finite R (P.X n))
    (hprojective : ∀ n : ℕ, Module.Projective R (P.X n)) :
    ∃ F : ChainComplex (ModuleCat.{u} R) ℕ,
      (∀ n : ℕ, Module.Free R (F.X n) ∧ Module.Finite R (F.X n)) ∧
      Nonempty (HomotopyEquiv F P) := by
  classical
  let State := {C : ModuleCat.{u} R // Module.Finite R C ∧ Module.Projective R C}
  let next (n : ℕ) (C : State) : State := by
    have := hfinite n
    have := hprojective n
    have := C.property.1
    have := C.property.2
    let h := exists_complement R (ModuleCat.of R (P.X n × C.val))
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1⟩
  let C : ℕ → State := Nat.rec ⟨ModuleCat.of R (Fin 0 → R), inferInstance, inferInstance⟩
    (fun n s ↦ next n s)
  let X (n : ℕ) := ModuleCat.of R ((P.X n × (C n).val) × (C (n + 1)).val)
  let d (n : ℕ) : X (n + 1) ⟶ X n := ModuleCat.ofHom
    { toFun v := ((P.d (n + 1) n v.1.1, 0), v.1.2)
      map_add' v w := by simp
      map_smul' a v := by simp }
  have sq (n : ℕ) : d (n + 1) ≫ d n = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    have hp := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (P.d_comp_d (n + 2) (n + 1) n))
      v.1.1
    change ((P.d (n + 1) n (P.d (n + 2) (n + 1) v.1.1), 0), 0) = ((0, 0), 0)
    apply Prod.ext
    · apply Prod.ext
      · simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero,
          LinearMap.comp_apply, LinearMap.zero_apply] using hp
      · rfl
    · rfl
  let F := ChainComplex.of X d sq
  let f : F ⟶ P := ChainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom ((LinearMap.fst R _ _).comp (LinearMap.fst R _ _)))
    (fun n ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      simp only [F, ChainComplex.of_d]
      change P.d (n + 1) n v.1.1 = P.d (n + 1) n v.1.1
      rfl)
  let g : P ⟶ F := ChainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom
      { toFun p := ((p, 0), 0)
        map_add' v w := by simp
        map_smul' a v := by simp })
    (fun n ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      simp only [F, ChainComplex.of_d]
      change ((P.d (n + 1) n v, 0), 0) = ((P.d (n + 1) n v, 0), 0)
      rfl)
  have hgf : g ≫ f = 𝟙 P := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    rfl
  let h (n : ℕ) : F.X n ⟶ F.X (n + 1) := ModuleCat.ofHom
    { toFun v := ((0, v.2), 0)
      map_add' v w := by simp
      map_smul' a v := by simp }
  let H (i j : ℕ) : F.X i ⟶ F.X j :=
    if hij : j = i + 1 then h i ≫ eqToHom (congrArg F.X hij.symm) else 0
  have homot : Homotopy (𝟙 F) (f ≫ g) :=
    { hom := H
      zero i j hij := by
        have hne : j ≠ i + 1 := fun he ↦ hij he.symm
        simp only [H, dite_eq_right hne]
      comm i := by
        cases i with
        | zero =>
          rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
          simp only [H, dite_eq_left rfl, eqToHom_refl, Category.comp_id, zero_add]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro v
          have hx : v.1.2 = 0 := by
            have : Subsingleton (C 0).val := by dsimp [C]; infer_instance
            exact Subsingleton.elim _ _
          change v = ((P.d 1 0 0, 0), v.2) + ((v.1.1, 0), 0)
          rcases v with ⟨⟨p, x⟩, y⟩
          apply Prod.ext
          · apply Prod.ext
            · change p = P.d 1 0 0 + p
              simp
            · change x = 0 + 0
              simpa using hx
          · change y = y + 0
            simp
        | succ n =>
          rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
          simp only [H, dite_eq_left rfl, eqToHom_refl, Category.comp_id]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro v
          simp only [F, ChainComplex.of_d]
          change v = ((0, v.1.2), 0) + ((P.d (n + 2) (n + 1) 0, 0), v.2) +
            ((v.1.1, 0), 0)
          rcases v with ⟨⟨p, x⟩, y⟩
          apply Prod.ext
          · apply Prod.ext
            · change p = 0 + P.d (n + 2) (n + 1) 0 + p
              simp
            · change x = x + 0 + 0
              simp
          · change y = 0 + y + 0
            simp }
  refine ⟨F, ?_, ⟨⟨f, g, homot.symm, Homotopy.ofEq hgf⟩⟩⟩
  intro n
  have := hfinite n
  have := hprojective n
  have := (C n).property.1
  have := (C n).property.2
  have hfree : Module.Free R (X n) := by
    change Module.Free R ((P.X n × (C n).val) × (next n (C n)).val)
    exact (exists_complement R (ModuleCat.of R (P.X n × (C n).val))).choose_spec.2.2
  have := (C (n + 1)).property.1
  change Module.Free R (X n) ∧ Module.Finite R ((P.X n × (C n).val) × (C (n + 1)).val)
  exact ⟨hfree, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- A bounded above complex of finite projective modules has a finite free replacement
with the same upper bound and a quasi-isomorphism to the original complex.

Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U, (3) implies (1).
(blueprint: lem-pc-finite-projective-complex-free-model).

Proof: Put C^(b+1) = 0. Descending from b, choose a finite projective complement C^n
of P^n ⊕ C^(n + 1) in a finite free module. This is possible because a finite projective
module is a direct summand of a finite free module: choose a finite free surjection,
split it using projectivity, and use its kernel as complement. The kernel is finite
projective because it is a direct summand of that finite free module.
Set F^n = P^n ⊕ C^(n + 1) ⊕ C^n for n ≤ b, and F^n = 0 for n > b. Choose the
complements recursively at n = b-k for k : ℕ; transport the resulting decompositions
to the finite free modules. The differential sends (p, x, y) in degree n to
(d_P(p), 0, x) in degree n+1. At the top it is zero, since P^(b+1) and C^(b+1)
are zero. Its square is zero by the square-zero identity for d_P.
Projection onto P gives a chain map, and inclusion of P is a chain map in the
opposite direction. Their composite on P is the identity. The other composite
differs from the identity by the projection onto the two complement summands.
The degree-minus-one map (p, x, y) ↦ (0, y, 0) contracts these summands, giving
id_F - inclusion ∘ projection = d h + h d. Thus the projection is a homotopy
equivalence and in particular a quasi-isomorphism. All terms are finite free and
zero above b. No lower bound is needed; the recursion continues indefinitely.
For the zero ring or zero complex the same construction works with rank-zero
terms and zero complements. The module universe equals the ring universe, so the
finite free modules and kernels used in the construction fit in it. -/
theorem exists_finiteFree_model_of_finite_projective (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) (hb : P.IsStrictlyLE b)
    (hfinite : ∀ n : ℤ, Module.Finite R (P.X n))
    (hprojective : ∀ n : ℤ, Module.Projective R (P.X n)) :
    ∃ F : CochainComplex (ModuleCat.{u} R) ℤ, F.IsStrictlyLE b ∧
      (∀ n : ℤ, Module.Free R (F.X n) ∧ Module.Finite R (F.X n)) ∧
      ∃ f : F ⟶ P, QuasiIso f := by
  classical
  have := hb
  let e := ComplexShape.embeddingUpIntLE b
  let T := P.truncLE' e
  have hterms (n : ℕ) : Module.Finite R (T.X n) ∧ Module.Projective R (T.X n) := by
    let t := asIso ((P.truncLE'ToRestriction e).f n) ≪≫ P.restrictionXIso e rfl
    have := hfinite (e.f n)
    have := hprojective (e.f n)
    exact ⟨Module.Finite.equiv t.symm.toLinearEquiv,
      Module.Projective.of_equiv t.symm.toLinearEquiv⟩
  obtain ⟨N, hN, ⟨q⟩⟩ := nat_free_model R T (fun n ↦ (hterms n).1)
    (fun n ↦ (hterms n).2)
  let F : CochainComplex (ModuleCat.{u} R) ℤ := N.extend e
  have hfree (i : ℤ) : Module.Free R (F.X i) ∧ Module.Finite R (F.X i) := by
    by_cases hi : ∃ n, e.f n = i
    · obtain ⟨n, hn⟩ := hi
      have := (hN n).1
      have := (hN n).2
      let t := (N.extendXIso e hn).symm.toLinearEquiv
      exact ⟨Module.Free.of_equiv t, Module.Finite.equiv t⟩
    · have : Subsingleton (F.X i) := ModuleCat.subsingleton_of_isZero
        (N.isZero_extend_X e i (by simpa using hi))
      exact ⟨inferInstance, inferInstance⟩
  let f : F ⟶ P := HomologicalComplex.extendMap q.hom e ≫
    (P.truncLEIso e).inv ≫ P.ιTruncLE b
  have : QuasiIso q.hom := inferInstance
  refine ⟨F, inferInstance, hfree, f, ?_⟩
  dsimp only [f]
  infer_instance

end CochainComplex
