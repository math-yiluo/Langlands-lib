/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.ConstantSubsheafStalkBound
import WeilConjectures.Topology.ConstantSubsheafPeelLayer
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-! # Finite filtration of a finitely generated subsheaf of the constant sheaf

Source: Stacks Project, Cohomology, Lemma 0A38
(blueprint: lem-sc-constant-subsheaf-finite-filtration).
-/

private theorem constantSubsheaf_filtration_of_stalk_bound
    (X : TopCat.{u})
    (hqc : ∀ U V : Opens X, IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (C : Sheaf AddCommGrpCat X)
    (hC : Nonempty (C ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))))
    (e : ∀ x : X, TopCat.Presheaf.stalk C.obj x ≅ AddCommGrpCat.of (ULift.{u} ℤ))
    (b : ℕ)
    (K : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g)
    (hb : ∀ x : X, ∃ a : ℕ, a ≤ b ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk K.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) :
    ∃ (m : ℕ) (F : Fin (m + 1) → Sheaf AddCommGrpCat X)
      (f : ∀ i : Fin m, F i.castSucc ⟶ F i.succ)
      (_hf : ∀ i : Fin m, Mono (f i))
      (Q : Fin m → Sheaf AddCommGrpCat X)
      (S : ∀ _i : Fin m, ShortComplex (Sheaf AddCommGrpCat X))
      (_hS : ∀ i : Fin m, (S i).ShortExact)
      (_hQ : ∀ i : Fin m, Nonempty (Q i ≅ cokernel (f i)))
      (_hquot : ∀ i : Fin m, ∃ (U V : Opens X),
        IsCompact (U : Set X) ∧ IsCompact (V : Set X) ∧ V ≤ U ∧
        Nonempty ((S i).X₁ ≅ (abelianOpenExtensionByZero V).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ∧
        Nonempty ((S i).X₂ ≅ (abelianOpenExtensionByZero U).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ∧
        Nonempty ((S i).X₃ ≅ Q i))
      , IsZero (F 0) ∧ Nonempty (F (Fin.last m) ≅ K) := by
  classical
  induction b generalizing K with
  | zero =>
    have hK : IsZero K := by
      apply (isZero_iff_stalkFunctor_obj_isZero K).mpr
      intro x
      obtain ⟨a, ha, hrange⟩ := hb x
      have ha0 : a = 0 := Nat.eq_zero_of_le_zero ha
      subst a
      simp only [Nat.cast_zero] at hrange
      let j := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom ≫ (e x).hom
      have hm : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom) :=
        TopCat.Presheaf.stalk_mono_of_mono ι x
      let := hm
      have hinj : Function.Injective j :=
        (AddCommGrpCat.mono_iff_injective j).mp inferInstance
      have hz (t : ToType (TopCat.Presheaf.stalk K.obj x)) : j t = 0 := by
        have ht : j t ∈ Set.range (fun z : ULift.{u} ℤ ↦ (0 : ℤ) • z) := by
          erw [← hrange]
          exact ⟨t, rfl⟩
        obtain ⟨z, hz⟩ := ht
        simpa using hz.symm
      apply AddCommGrpCat.isZero_iff_subsingleton.mpr
      exact ⟨fun t t' ↦ hinj ((hz t).trans (hz t').symm)⟩
    refine ⟨0, fun _ ↦ K, (fun i ↦ i.elim0), (fun i ↦ i.elim0),
      (fun i ↦ i.elim0), (fun i ↦ i.elim0), (fun i ↦ i.elim0),
      (fun i ↦ i.elim0), (fun i ↦ i.elim0), hK, ⟨Iso.refl K⟩⟩
  | succ b ih =>
    obtain ⟨L, l, hl, hgenL, hbL, T, hT, hquotT⟩ :=
      constantSubsheaf_peel_layer X hqc K C ι hC hgen e b hb
    let := hl
    obtain ⟨m, F, f, hf, Q, S, hS, hQ, hquot, hzero, ⟨eL⟩⟩ :=
      ih L (l ≫ ι) hgenL hbL
    let F' : Fin (m + 1 + 1) → Sheaf AddCommGrpCat X := Fin.snoc F K
    let pLast : F' (Fin.last m).castSucc ≅ L :=
      (eqToIso (by simp only [F', Fin.snoc_castSucc])).trans eL
    let qLast : F' (Fin.last m).succ ≅ K := eqToIso (by simp [F'])
    let pOld (j : Fin m) : F' j.castSucc.castSucc ≅ F j.castSucc :=
      eqToIso (by simp only [F', Fin.snoc_castSucc])
    let qOld (j : Fin m) : F' j.castSucc.succ ≅ F j.succ :=
      eqToIso (by simp only [F', ← Fin.castSucc_succ, Fin.snoc_castSucc])
    let f' : ∀ i : Fin (m + 1), F' i.castSucc ⟶ F' i.succ :=
      Fin.lastCases (pLast.hom ≫ l ≫ qLast.inv)
        (fun j ↦ (pOld j).hom ≫ f j ≫ (qOld j).inv)
    have hf' : ∀ i : Fin (m + 1), Mono (f' i) := by
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [f', Fin.lastCases_last]
        infer_instance
      · simp only [f', Fin.lastCases_castSucc]
        let := hf j
        infer_instance
    let Q' : Fin (m + 1) → Sheaf AddCommGrpCat X := Fin.snoc Q (cokernel l)
    let S' : Fin (m + 1) → ShortComplex (Sheaf AddCommGrpCat X) := Fin.snoc S T
    have hS' : ∀ i : Fin (m + 1), (S' i).ShortExact := by
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa [S'] using hT
      · simpa [S'] using hS j
    have hQ' : ∀ i : Fin (m + 1), Nonempty (Q' i ≅ cokernel (f' i)) := by
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [Q', Fin.snoc_last, f', Fin.lastCases_last]
        exact ⟨(cokernel.mapIso _ l pLast qLast (by simp)).symm⟩
      · simp only [Q', Fin.snoc_castSucc, f', Fin.lastCases_castSucc]
        obtain ⟨ej⟩ := hQ j
        exact ⟨ej.trans (cokernel.mapIso _ (f j) (pOld j) (qOld j) (by simp)).symm⟩
    refine ⟨m + 1, F', f', hf', Q', S', hS', hQ', ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa [S', Q'] using hquotT
      · simpa [S', Q'] using hquot j
    · change IsZero (F' (Fin.castSucc 0))
      simpa only [F', Fin.snoc_castSucc] using hzero
    · exact ⟨by simpa [F'] using Iso.refl K⟩

set_option linter.unusedVariables false in
/-- A finitely generated subsheaf of the constant integer sheaf admits the finite
filtration by extension-by-zero quotients described in Stacks Lemma 0A38.

Proof (Stacks, Lemma 0A38, following the four steps of the node):
1. Write K using finitely many sections on quasi-compact opens. Using the constant-sheaf
   definition `def-weil-pbc-constant-sheaf`, split each open into its finitely many clopen
   fibres so that each generator is an integer n_i. Delete zero generators, change signs
   to make n_i positive, and adjoin all nonempty finite intersections with the gcd of
   their integers. Intersections are quasi-compact by hqc. Bezout's identity shows that
   these additions do not change K, and that each stalk's gcd is attained by a generator.
2. Let K_r be generated by the generators of value at most r, starting with K_0 = 0.
   For large r this is K. Set U_r to the union of opens with value at most r, V_r to
   those with value less than r, and W_r to those with value r; all are quasi-compact.
   Computing gcds gives equal stalks for K_r and K_(r-1) on V_r, quotient stalk r Z
   on U_r minus V_r, and zero outside U_r. Glue the class of r over W_r with zero
   over V_r to a generating section sigma_r of the quotient over U_r. The integer r
   need not itself be a section of K_r over all U_r.
3. The section sigma_r gives j_! Z_(U_r) to K_r/K_(r-1). The inclusion V_r into U_r
   gives j'_! Z_(V_r) to j_! Z_(U_r), and the composite vanishes. Apply
   `TopCat.Sheaf.abelianOpenExtensionByZero_stalks`
   (`lem-sc-topological-extension-by-zero-stalks`): outside U_r all terms vanish;
   on U_r minus V_r the map Z to r Z sends 1 to r and is an isomorphism;
   on V_r the first map is identity on Z and the quotient vanishes. The criterion
   `TopCat.shortExact_iff_stalkFunctor_map_shortExact`
   (`lem-sc-abelian-sheaf-short-exact-stalkwise`) gives the short exact sequence.
4. Delete repeated stages and relabel to obtain the finite filtration with the asserted
   zero and terminal terms and the short exact sequence for every successive quotient.
(blueprint: lem-sc-constant-subsheaf-finite-filtration).
-/
theorem constantSubsheaf_finite_filtration
    (X : TopCat.{u})
    (hqc : ∀ U V : Opens X, IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (K C : Sheaf AddCommGrpCat X)
    (ι : K ⟶ C)
    [Mono ι]
    (hC : Nonempty (C ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g) :
    ∃ (m : ℕ) (F : Fin (m + 1) → Sheaf AddCommGrpCat X)
      (f : ∀ i : Fin m, F i.castSucc ⟶ F i.succ)
      (hf : ∀ i : Fin m, Mono (f i))
      (Q : Fin m → Sheaf AddCommGrpCat X)
      (S : ∀ i : Fin m, ShortComplex (Sheaf AddCommGrpCat X))
      (hS : ∀ i : Fin m, (S i).ShortExact)
      (hQ : ∀ i : Fin m, Nonempty (Q i ≅ cokernel (f i)))
      (hquot : ∀ i : Fin m, ∃ (U V : Opens X),
        IsCompact (U : Set X) ∧ IsCompact (V : Set X) ∧ V ≤ U ∧
        Nonempty ((S i).X₁ ≅ (abelianOpenExtensionByZero V).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ∧
        Nonempty ((S i).X₂ ≅ (abelianOpenExtensionByZero U).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ∧
        Nonempty ((S i).X₃ ≅ Q i))
      , IsZero (F 0) ∧ Nonempty (F (Fin.last m) ≅ K) := by
  obtain ⟨e, b, hb⟩ := constantSubsheaf_stalk_bound X K C ι hC hgen
  exact constantSubsheaf_filtration_of_stalk_bound X hqc C hC e b K ι hgen hb

end TopCat.Sheaf
