/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Topology.PointwiseTruncationOpenStabilization
import WeilConjectures.CategoryTheory.DerivedLimitEventuallyIso
import WeilConjectures.Topology.DerivedLimitStalkInjective
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry.RingedSpace

private theorem module_isIso_of_stalk_bijective (X : RingedSpace.{u})
    {F G : SheafOfModules.{u} (moduleRings X)} (f : F ⟶ G)
    (hf : ∀ x : X, Function.Bijective ((moduleStalkFunctor X x).map f).hom) :
    IsIso f := by
  let T := SheafOfModules.toSheaf (moduleRings X)
  have ht : IsIso (T.map f) := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (T.map f)).2
    intro x
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact hf x
  exact isIso_of_reflects_iso f T

private theorem tower_isIso_map_of_successor
    {C : Type*} [Category C] (A : ℕᵒᵖ ⥤ C) (N : ℕ)
    (hA : ∀ n : ℕ, N ≤ n → IsIso (A.map (homOfLE (Nat.le_succ n)).op))
    (n : ℕ) (hn : N ≤ n) : IsIso (A.map (homOfLE hn).op) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using (inferInstance : IsIso (𝟙 (A.obj (Opposite.op N))))
  | succ n hn ih =>
    have := hA n hn
    have := ih
    have he : (homOfLE (show N ≤ n + 1 by omega)).op =
        (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hn).op := Subsingleton.elim _ _
    rw [he, A.map_comp]
    infer_instance

/-- Isomorphism part of pointwise truncation reconstruction
(blueprint: lem-pc-ringed-space-pointwise-truncation-limit-isIso).

Proof: fix a compatible map `c`. For each point and cohomological degree, choose a
truncation index beyond the three local bounds supplied by `hlocal`. The successive
truncation triangle and its long exact cohomology sequence make the transitions in the
two adjacent degrees isomorphisms from that index onward. The Roos abelian-group lemma
then kills the resulting `R¹ lim` term. The derived-limit stalk-injectivity lemma,
together with the derived global-sections/limit comparison, shows that the map induced
by `c` on every stalk cohomology group is injective. Its composite with the truncation
map is the canonical truncation isomorphism, so it is also surjective. Isomorphisms on
all stalk cohomology groups imply `IsIso c` by the derived-category cohomology
criterion. This is the uniqueness half of Stacks, Cohomology, Tag 0D62. -/
theorem pointwise_truncation_limit_isIso (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    (E : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (hlocal : ∀ x : X, ∃ (b : ℤ → ℤ) (B : Set (Opens X)),
      (∀ U ∈ B, x ∈ U) ∧
      (∀ V : Opens X, x ∈ V → ∃ U ∈ B, U ≤ V) ∧
      (∀ (m : ℤ) (p : ℕ) (U : Opens X), U ∈ B → b m < (p : ℤ) →
        IsZero ((openModuleCohomology X p U).obj
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X))
            (m - (p : ℤ))).obj E))))
    [HasProduct (fun n : ℕ => (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E)]
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (π : K ⟶ ∏ᶜ (fun n : ℕ =>
      (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E))
    (δ : (∏ᶜ (fun n : ℕ =>
      (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E)) ⟶ K⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle
      (fun n : ℕ => (DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E) K π δ) :
    (∀ c : E ⟶ K, (∀ n : ℕ,
      c ≫ π ≫ Pi.π (fun n : ℕ =>
        (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) → IsIso c) := by
  intro c hc
  let : HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _
  let t := DerivedCategory.TStructure.t (C := SheafOfModules.{u} (moduleRings X))
  let A : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (moduleRings X)) :=
    Functor.ofOpSequence (X := fun n : ℕ ↦ (t.truncGE (-(n : ℤ))).obj E)
      (fun n : ℕ ↦
        (t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E)
  have hA : IsDerivedLimitTriangle
      (fun n : ℕ ↦ A.map (homOfLE (Nat.le_succ n)).op) K π δ := by
    simpa only [A, Functor.ofOpSequence_map_homOfLE_succ] using hK
  apply (DerivedCategory.isIso_iff _ c).2
  intro m
  apply module_isIso_of_stalk_bijective X
  intro x
  obtain ⟨b, B, hmem, hbasis, hvan⟩ := hlocal x
  obtain ⟨N, hNm, hN⟩ := pointwise_truncation_open_stabilization X E b B hvan m
  have hlim (U : Opens X) (hU : U ∈ B) : IsZero
      ((@Functor.rightDerived _ _ _ _ _
        (@InjectiveResolution.instHasInjectiveResolutions _ _ _ roosTowerEnoughInjectives) _
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) roosLimitAdditive 1).obj
        (A ⋙ openModuleDerivedSections X U ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1))) := by
    apply isZero_firstDerivedLimit_of_eventually_isIso
    refine ⟨N, ?_⟩
    intro n hn
    simpa only [Functor.comp_map, A, Functor.ofOpSequence_map_homOfLE_succ] using
      (hN U hU n hn).1
  have hinj (U : Opens X) (hU : U ∈ B) (n : ℕ) (hn : N ≤ n) :
      Function.Injective
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
          ((openModuleDerivedSections X U).map (A.map (homOfLE hn).op))) := by
    let D := A ⋙ openModuleDerivedSections X U ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} m
    have hstep (k : ℕ) (hk : N ≤ k) :
        IsIso (D.map (homOfLE (Nat.le_succ k)).op) := by
      simpa only [D, Functor.comp_map, A, Functor.ofOpSequence_map_homOfLE_succ] using
        (hN U hU k hk).2
    have := tower_isIso_map_of_successor D N hstep n hn
    exact (ConcreteCategory.bijective_of_isIso (D.map (homOfLE hn).op)).1
  have hp := derivedLimit_stalk_injective X A K π δ hA x m N B hmem hbasis hlim hinj
  let H := DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) m
  let S := moduleStalkFunctor X x
  let p := π ≫ Pi.π (fun n : ℕ ↦ (t.truncGE (-(n : ℤ))).obj E) N
  have hcomp : S.map (H.map c) ≫ S.map (H.map p) =
      S.map (H.map ((t.truncGEπ (-(N : ℤ))).app E)) := by
    rw [← S.map_comp, ← H.map_comp]
    exact congrArg (fun f ↦ S.map (H.map f)) (hc N)
  have : IsIso (H.map ((t.truncGEπ (-(N : ℤ))).app E)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app E (-(N : ℤ)) m hNm
  have hbij := ConcreteCategory.bijective_of_isIso
    (S.map (H.map ((t.truncGEπ (-(N : ℤ))).app E)))
  have hbij' : Function.Bijective (S.map (H.map c) ≫ S.map (H.map p)) := by
    rw [hcomp]
    exact hbij
  change Function.Injective (S.map (H.map p)).hom at hp
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply hbij'.1
    change (S.map (H.map p)) ((S.map (H.map c)) a) =
      (S.map (H.map p)) ((S.map (H.map c)) b)
    rw [hab]
  · intro y
    obtain ⟨z, hz⟩ := hbij'.2 ((S.map (H.map p)) y)
    refine ⟨z, hp ?_⟩
    exact hz

end AlgebraicGeometry.RingedSpace
