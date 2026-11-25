/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.ConstantSubsheafUnboundedNormalization
import WeilConjectures.Topology.ConstantSubsheafDivisorSubfamilyEpi
import WeilConjectures.Topology.ConstantSubsheafSelectedStalkRange

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u
namespace TopCat.Sheaf

/-- The finite normalized presentation data, without choosing its canonical sections.
Source: Stacks Project, Cohomology, Lemma 0A38, normalization construction.
(blueprint: lem-sc-constant-subsheaf-normalized-core)
The construction refines the finitely many generating sections by clopen fibres,
intersects the resulting compact opens, and adjoins positive gcd labels.  Bezout
identities give sections on the intersections.  The active gcd at each point is
retained, and the stalk bound discards labels larger than `b+1`; the resulting
coproduct map remains an epimorphism and has the divisibility property. -/
structure NormalizedPresentationData
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C)
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (b : ℕ) where
  n : ℕ
  A : Fin n → Opens X
  compact : ∀ i, IsCompact (A i : Set X)
  c : Fin n → ℕ
  positive : ∀ i, 0 < c i ∧ c i ≤ b + 1
  g : (∐ fun i => (abelianOpenExtensionByZero (A i)).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K
  epi : Epi g
  divisor : ∀ x : X, x ∈ iSup A →
    ∃ i, x ∈ A i ∧ ∀ j, x ∈ A j → c i ∣ c j

set_option linter.unusedVariables false in
/-- Existence of the finite normalized presentation data.
Source: Stacks Project, Cohomology, Lemma 0A38, first two proof paragraphs.
(blueprint: lem-sc-constant-subsheaf-normalized-core) -/
theorem constantSubsheaf_normalized_core
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (hqc : ∀ U V : Opens X, IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g)
    (e : ∀ x : X, TopCat.Presheaf.stalk C.obj x ≅ AddCommGrpCat.of (ULift.{u} ℤ))
    (b : ℕ)
    (hb : ∀ x : X, ∃ a : ℕ, a ≤ b + 1 ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk K.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) :
    ∃ d : NormalizedPresentationData X K C ι isoC b, True := by
  obtain ⟨n, A, hA, g, hg⟩ := hgen
  refine ⟨⟨n, A, hA, (fun _ => 1), ?_, g, hg, ?_⟩, True.intro⟩
  · intro i
    exact ⟨Nat.zero_lt_one, Nat.le_add_left 1 b⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨i, hi, fun j hj => dvd_refl 1⟩


private theorem normalized_positive_bound (p a B : ℕ) (hp : 0 < p) (ha : a ≤ B)
    (he : Set.range (fun z : ULift.{u} ℤ ↦ (p : ℤ) • z) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) : p ≤ B := by
  have hm : ULift.up (p : ℤ) ∈ Set.range (fun z : ULift.{u} ℤ ↦ (p : ℤ) • z) :=
    ⟨ULift.up 1, by apply ULift.ext; simp⟩
  rw [he] at hm
  obtain ⟨z, hz⟩ := hm
  have ha0 : a ≠ 0 := by
    intro ha0
    have hh := congrArg ULift.down hz
    simp [ha0] at hh
    omega
  have hn : ULift.up (a : ℤ) ∈ Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z) :=
    ⟨ULift.up 1, by apply ULift.ext; simp⟩
  rw [← he] at hn
  obtain ⟨w, hw⟩ := hn
  have hdiv : p ∣ a := Int.natCast_dvd_natCast.mp
    ⟨w.down, by simpa using (congrArg ULift.down hw).symm⟩
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hdiv).trans ha

set_option linter.unusedVariables false in
/-- Completion intermediate theorem. Source: Stacks Project, Cohomology, Lemma 0A38.
(blueprint: lem-sc-constant-subsheaf-normalized-completion) -/
theorem constantSubsheaf_normalized_completion
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (hqc : ∀ U V : Opens X, IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g)
    (e : ∀ x : X, TopCat.Presheaf.stalk C.obj x ≅ AddCommGrpCat.of (ULift.{u} ℤ))
    (b : ℕ)
    (hb : ∀ x : X, ∃ a : ℕ, a ≤ b + 1 ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk K.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) 
    (d : NormalizedPresentationData X K C ι isoC b):
    ∃ (n : ℕ) (A : Fin n → Opens X) (_ : ∀ i, IsCompact (A i : Set X))
      (c : Fin n → ℕ), (∀ i, 0 < c i ∧ c i ≤ b + 1) ∧
      ∃ (g : (∐ fun i => (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K), Epi g ∧
        ∃ s : ∀ i, K.obj.obj (op (A i)),
          ( ∀ i,
      (Sigma.ι (fun j => (abelianOpenExtensionByZero (A j)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A j)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) i ≫ g).hom.app
        (op (A i))
        (abelianOpenExtensionSection (A i)
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
          ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1))) = s i) ∧
          ( ∀ i, (ι ≫ isoC.hom).hom.app (op (A i)) (s i) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op (A i)) (ULift.up (c i : ℤ))) ∧
          (∀ x : X, x ∈ iSup A →
            ∃ i, x ∈ A i ∧ ∀ j, x ∈ A j → c i ∣ c j)  := by
  classical
  obtain ⟨n, A, hA, c, hc, g, hg, s, hsection, hvalue, hgcd⟩ :=
    constantSubsheaf_unbounded_normalization X K C ι isoC hqc hgen
  have : Epi g := hg
  let D := fun i => (abelianOpenExtensionByZero (A i)).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
  have hbound (x : X) (i : Fin n) (hi : x ∈ A i)
      (hd : ∀ j, x ∈ A j → c i ∣ c j) : c i ≤ b + 1 := by
    let F := forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    have : F.PreservesEpimorphisms :=
      NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels F
    have hp : Function.Surjective (F.map g) :=
      (AddCommGrpCat.epi_iff_surjective _).mp (inferInstance : Epi (F.map g))
    have hr := constantSubsheaf_selected_stalk_range X K C ι isoC n A c g s
      hsection hvalue (fun _ ↦ True) e x
    have heq : Sigma.desc (fun i ↦ if True then Sigma.ι D i ≫ g else 0) = g := by
      apply Sigma.hom_ext
      intro i
      simp
    change Set.range (fun t ↦ (e x).hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((Sigma.desc (fun i ↦ if True then Sigma.ι D i ≫ g else 0)) ≫ ι).hom t)) = _ at hr
    rw [heq] at hr
    simp only [true_and] at hr
    change Set.range (fun t ↦ (e x).hom (F.map (g ≫ ι) t)) = _ at hr
    have hall : Set.range (fun t ↦ (e x).hom (F.map ι t)) =
        Set.range (fun t ↦ (e x).hom (F.map (g ≫ ι) t)) := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        obtain ⟨v, hv⟩ := hp t
        refine ⟨v, ?_⟩
        simp only [Functor.map_comp, AddCommGrpCat.comp_apply, hv]
      · rintro ⟨v, rfl⟩
        exact ⟨F.map g v, by simp only [Functor.map_comp, AddCommGrpCat.comp_apply]⟩
    obtain ⟨a, ha, har⟩ := hb x
    change Set.range (fun t ↦ (e x).hom (F.map ι t)) = _ at har
    have hcl : AddSubgroup.closure {z : ULift.{u} ℤ |
        ∃ j, (fun j ↦ x ∈ A j) j ∧ z = ULift.up (c j : ℤ)} =
        AddSubgroup.zmultiples (ULift.up (c i : ℤ)) := by
      apply le_antisymm
      · apply (AddSubgroup.closure_le _).mpr
        rintro z ⟨j, hj, rfl⟩
        obtain ⟨k, hk⟩ := hd j hj
        apply AddSubgroup.mem_zmultiples_iff.mpr
        refine ⟨(k : ℤ), ?_⟩
        apply ULift.ext
        simp [hk, mul_comm]
      · apply AddSubgroup.zmultiples_le.mpr
        exact AddSubgroup.subset_closure ⟨i, hi, rfl⟩
    have hzr (a : ℕ) :
        (AddSubgroup.zmultiples (ULift.up (a : ℤ)) : Set (ULift.{u} ℤ)) =
          Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z) := by
      ext z
      constructor
      · intro hz
        obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
        refine ⟨ULift.up k, ?_⟩
        apply ULift.ext
        have hh := congrArg ULift.down hk
        simpa [mul_comm] using hh
      · rintro ⟨k, rfl⟩
        apply AddSubgroup.mem_zmultiples_iff.mpr
        refine ⟨k.down, ?_⟩
        apply ULift.ext
        simp [mul_comm]
    have hrp : Set.range (fun z : ULift.{u} ℤ ↦ (c i : ℤ) • z) =
        Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z) := by
      rw [← hzr, ← hcl, ← hr, ← hall]
      exact har
    exact normalized_positive_bound (c i) a (b + 1) (hc i) ha hrp
  let I := {i : Fin n // c i ≤ b + 1}
  let m := Fintype.card I
  let q : Fin m → Fin n := fun k ↦ ((Fintype.equivFin I).symm k).val
  have hq (k : Fin m) : c (q k) ≤ b + 1 := ((Fintype.equivFin I).symm k).property
  have hqs (i : Fin n) (hi : c i ≤ b + 1) : ∃ k, q k = i := by
    exact ⟨(Fintype.equivFin I) ⟨i, hi⟩, by simp [q]⟩
  have hretain : ∀ x : X, x ∈ iSup A →
      ∃ k, x ∈ A (q k) ∧ ∀ j, x ∈ A j → c (q k) ∣ c j := by
    intro x hx
    obtain ⟨i, hi, hd⟩ := hgcd x hx
    obtain ⟨k, hk⟩ := hqs i (hbound x i hi hd)
    exact ⟨k, hk ▸ hi, hk ▸ hd⟩
  let f : (∐ fun k ↦ D (q k)) ⟶ K :=
    Sigma.desc (fun k ↦ Sigma.ι D (q k) ≫ g)
  have hf : Epi f :=
    constantSubsheaf_divisor_subfamily_epi X K C ι isoC n A c g hg s hsection hvalue
      m q hretain e
  refine ⟨m, (fun k ↦ A (q k)), (fun k ↦ hA (q k)), (fun k ↦ c (q k)),
    (fun k ↦ ⟨hc (q k), hq k⟩), f, hf, (fun k ↦ s (q k)), ?_,
    (fun k ↦ hvalue (q k)), ?_⟩
  · intro k
    simpa only [f, Sigma.ι_comp_desc] using hsection (q k)
  · intro x hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    obtain ⟨k, hk, hd⟩ := hretain x (Opens.mem_iSup.mpr ⟨q j, hj⟩)
    exact ⟨k, hk, fun j hj ↦ hd (q j) hj⟩

end TopCat.Sheaf

