/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimitsEventuallyConstant
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Assembly of a degreewise stabilizing finite free tower

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent, final iteration.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A tower with a descending stabilization cutoff and improving localized cohomology
assembles to a bounded above finite free complex. No pseudo-coherence hypothesis is
needed for this assembly statement.

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent, final iteration
(blueprint: lem-sc-stabilized-finite-free-tower).

Proof: Regard the sequence and transitions as the diagram D on the ordered natural
numbers. In each degree i, the evaluated diagram is eventually constant from
k(i)=max(0,b+1-i): induction on l-k(i) shows that all composites of transitions from
k(i) are invertible. Mathlib's eventual-constancy colimit construction provides its
colimit. The homological-complex colimit construction assembles these degreewise
colimits into E, with its differential and square-zero identity. The compatible maps
alpha define a cocone to M, hence a map gamma:E to M by the colimit universal property.
The inclusion from every sufficiently late stage is invertible in degree i. Transport
finite freeness and the upper support bound across this inclusion. For cohomology in
degree i choose k(i-1); the inclusions in i-1,i,i+1 are all invertible, and localization
preserves them. The localized inclusion is therefore a quasi-isomorphism at i by the
short-complex criterion. Its composite with gamma is alpha at this stage by the
colimit factorization identity. Since that stage map is a quasi-isomorphism at i,
cancellation gives that gamma is also one. Empty families impose no condition; zero
rings are included throughout. The colimit object is fixed by its universal property;
no datum is defined using an unproved mere existence statement.
-/
theorem exists_model_of_stabilized_finite_free_tower (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℕ) (f : Fin r → A) (b : ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{u} A) ℤ) (α : ∀ k : ℕ, F k ⟶ M)
    (τ : ∀ k : ℕ, F k ⟶ F (k + 1))
    (hupper : ∀ k : ℕ, (F k).IsStrictlyLE b)
    (hfinite : ∀ k : ℕ, ∀ i : ℤ, Module.Free A ((F k).X i) ∧
      Module.Finite A ((F k).X i))
    (hcomm : ∀ k : ℕ, τ k ≫ α (k + 1) = α k)
    (hstable : ∀ k : ℕ, ∀ i : ℤ, b + 1 - (k : ℤ) ≤ i → IsIso ((τ k).f i))
    (hiso : ∀ k : ℕ, ∀ j : Fin r, ∀ i : ℤ, b + 1 - (k : ℤ) < i → QuasiIsoAt
      ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
        (ComplexShape.up ℤ)).map (α k)) i) :
    ∃ (E : CochainComplex (ModuleCat.{u} A) ℤ), E.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free A (E.X i) ∧ Module.Finite A (E.X i)) ∧
      ∃ γ : E ⟶ M, ∀ j : Fin r, QuasiIso
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
          (ComplexShape.up ℤ)).map γ) := by
  classical
  let D := Functor.ofSequence τ
  have hevent (i : ℤ) (k : ℕ) (hk : b + 1 - (k : ℤ) ≤ i) :
      Functor.IsEventuallyConstantFrom
        (D ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) i) k := by
    intro l φ
    have hkl : k ≤ l := leOfHom φ
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hkl
    induction a with
    | zero =>
        have hφ : φ = 𝟙 k := Subsingleton.elim _ _
        subst hφ
        change IsIso ((D ⋙ HomologicalComplex.eval _ _ i).map (𝟙 k))
        rw [CategoryTheory.Functor.map_id]
        infer_instance
    | succ a ih =>
        let ψ : k ⟶ k + a := homOfLE (by omega)
        let χ : k + a ⟶ k + a + 1 := homOfLE (by omega)
        have hφ : φ = ψ ≫ χ := Subsingleton.elim _ _
        rw [hφ, Functor.map_comp]
        have hiψ : IsIso ((D ⋙ HomologicalComplex.eval _ _ i).map ψ) := ih ψ (by omega)
        have hc : IsIso ((D ⋙ HomologicalComplex.eval
            (ModuleCat.{u} A) (ComplexShape.up ℤ) i).map χ) := by
          change IsIso (((Functor.ofSequence τ).map χ).f i)
          have hχ : χ = homOfLE (Nat.le_add_right (k + a) 1) := Subsingleton.elim _ _
          rw [hχ, Functor.ofSequence_map_homOfLE_succ]
          exact hstable (k + a) i (by omega)
        infer_instance
  let cutoff (i : ℤ) : ℕ := (b + 1 - i).toNat
  have hcut (i : ℤ) : b + 1 - (cutoff i : ℤ) ≤ i := by
    dsimp [cutoff]
    omega
  have (i : ℤ) : HasColimit
      (D ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) i) :=
    (hevent i (cutoff i) (hcut i)).hasColimit
  let E := colimit D
  let γ : E ⟶ M := colimit.desc D
    { pt := M
      ι := NatTrans.ofSequence α (by
        intro k
        simpa [D] using hcomm k) }
  have hι (i : ℤ) (k : ℕ) (hk : b + 1 - (k : ℤ) ≤ i) :
      IsIso ((colimit.ι D k).f i) :=
    (hevent i k hk).isIso_ι_of_isColimit
      (isColimitOfPreserves (HomologicalComplex.eval _ _ i) (colimit.isColimit D))
  have hu : E.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have := hι i (cutoff i) (hcut i)
    have : (F (cutoff i)).IsStrictlyLE b := hupper _
    exact ((F (cutoff i)).isZero_of_isStrictlyLE b i hi).of_iso
      (asIso ((colimit.ι D (cutoff i)).f i)).symm
  have hf (i : ℤ) : Module.Free A (E.X i) ∧ Module.Finite A (E.X i) := by
    have := hι i (cutoff i) (hcut i)
    have : Module.Free A ((D.obj (cutoff i)).X i) := (hfinite _ _).1
    have : Module.Finite A ((D.obj (cutoff i)).X i) := (hfinite _ _).2
    let e := (asIso ((colimit.ι D (cutoff i)).f i)).toLinearEquiv
    exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩
  refine ⟨E, hu, hf, γ, ?_⟩
  intro j
  rw [quasiIso_iff]
  intro i
  let k := cutoff (i - 1)
  have hk : b + 1 - (k : ℤ) ≤ i - 1 := hcut (i - 1)
  let L := Functor.mapHomologicalComplex
    (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
    (ComplexShape.up ℤ)
  have hqi : QuasiIsoAt (L.map (colimit.ι D k)) i := by
    rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    let φ := (HomologicalComplex.shortComplexFunctor' _ _ (i - 1) i (i + 1)).map
      (L.map (colimit.ι D k))
    have h₁ : IsIso φ.τ₁ := by
      have := hι (i - 1) k hk
      change IsIso ((ModuleCat.extendScalars
        (algebraMap A (Localization.Away (f j)))).map ((colimit.ι D k).f (i - 1)))
      infer_instance
    have h₂ : IsIso φ.τ₂ := by
      have := hι i k (by omega)
      change IsIso ((ModuleCat.extendScalars
        (algebraMap A (Localization.Away (f j)))).map ((colimit.ι D k).f i))
      infer_instance
    have h₃ : IsIso φ.τ₃ := by
      have := hι (i + 1) k (by omega)
      change IsIso ((ModuleCat.extendScalars
        (algebraMap A (Localization.Away (f j)))).map ((colimit.ι D k).f (i + 1)))
      infer_instance
    exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ
  have hfac : colimit.ι D k ≫ γ = α k := colimit.ι_desc _ _
  have : QuasiIsoAt (L.map (colimit.ι D k) ≫ L.map γ) i := by
    rw [← L.map_comp, hfac]
    exact hiso k j i (by omega)
  exact quasiIsoAt_of_comp_left (L.map (colimit.ι D k)) (L.map γ) i

end CochainComplex
