/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.ConstantSubsheafPositiveRefinementData
import WeilConjectures.Topology.AbelianIntegerExtensionSections
import WeilConjectures.Topology.AbelianIntegerExtensionHomExt

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Construct the coproduct factorization from a finite signed partition record.
Source: Stacks Project, Cohomology, Lemma 0A38, first proof paragraph, with the
factorization made explicit by gluing on the finite disjoint partition.
https://stacks.math.columbia.edu/tag/0A38
(blueprint: lem-sc-constant-subsheaf-positive-refinement-factor)

Proof: Write P for the coproduct of the extensions on d.A. For each original index i,
cover U i by d.Z i and the d.A j with d.parent j = i, using d.hcover. On d.Z i take
the zero section of P. On d.A j take d.sign j times the canonical unit section of
that extension, followed by its coproduct injection into P. The pieces are pairwise
disjoint by d.hdisjoint and d.hdisjointZ, so these sections agree on all intersections
(the only section of an abelian sheaf on the empty open is zero). Sheaf gluing gives
a section t i of P on U i with precisely these restrictions.

A section t of any abelian sheaf H on U determines a morphism j_U! Z to H: map the
constant integer presheaf on U to H restricted to U by integer multiples of the
restrictions of t, sheafify, apply extension by zero, and compose with the counit.
The resulting morphism sends the canonical unit to t. It is uniquely determined by
this value: maps from the constant integer presheaf are determined by one and
naturality, and both sheafifications and the slice extension preserve this universal
property (a presheaf map is fixed on every direct-sum injection).

Apply this construction to t i and take the coproduct of these morphisms to obtain l.
After composition with Sigma.desc d.f, the restriction of t i on each d.A j is
sign j times the unit image of f j, hence the restriction of d.s i by d.hsigned;
on d.Z i both are zero by d.hzero. Sheaf separation on the cover gives the unit
image d.s i on all of U i. By d.hs this is the unit image of the old component of g.
The uniqueness just established makes the two component morphisms equal. Coproduct
extensionality yields l followed by Sigma.desc d.f = g. Empty partitions and the
case n = 0 use the same gluing argument and force the old unit sections to be zero. -/
theorem positive_refinement_factor
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (m : ℕ) (U : Fin m → Opens X)
    (g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K)
    (d : PositiveRefinementData X K C ι isoC m U g) :
    ∃ l : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶
          (∐ fun i => (abelianOpenExtensionByZero (d.A i)).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (d.A i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))),
      l ≫ Sigma.desc d.f = g := by
  classical
  let E (V : Opens X) := (abelianOpenExtensionByZero V).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
  let one (V : Opens X) : (E V).obj.obj (op V) :=
    abelianOpenExtensionSection V
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) V le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
        ((Functor.const (Opens ((Opens.toTopCat X).obj V))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map V.inclusion').obj V)) (ULift.up 1))
  let P : Sheaf AddCommGrpCat.{u} X := ∐ fun j ↦ E (d.A j)
  have component (i : Fin m) :
      ∃ li : E (U i) ⟶ P, li ≫ Sigma.desc d.f = Sigma.ι _ i ≫ g := by
    let J := {j : Fin d.n // d.parent j = i}
    let V : Option J → Opens X
      | none => d.Z i
      | some j => d.A j.1
    have hVU : ∀ a, V a ≤ U i := by
      intro a
      cases a with
      | none => exact d.hZU i
      | some j => simpa only [V, j.2] using d.hAU j.1
    have cover : U i ≤ iSup V := by
      rw [d.hcover i]
      apply sup_le
      · exact le_iSup V none
      · exact iSup_le fun j ↦ le_iSup V (some j)
    let sf : ∀ a, P.obj.obj (op (V a))
      | none => 0
      | some j => d.sign j.1 • (Sigma.ι (fun j ↦ E (d.A j)) j.1).hom.app
          (op (d.A j.1)) (one (d.A j.1))
    have empty_eq (W : Opens X) (hw : W = ⊥) (a b : P.obj.obj (op W)) : a = b := by
      apply TopCat.Presheaf.section_ext P W a b
      intro x hx
      rw [hw] at hx
      exact False.elim hx
    have compat : TopCat.Presheaf.IsCompatible P.obj V sf := by
      intro a b
      by_cases hab : a = b
      · subst b; rfl
      · apply empty_eq
        cases a with
        | none =>
          cases b with
          | none => exact False.elim (hab rfl)
          | some j => simpa only [V, j.2] using (d.hdisjointZ j.1).symm.eq_bot
        | some j =>
          cases b with
          | none => simpa only [V, j.2] using (d.hdisjointZ j.1).eq_bot
          | some k =>
            have hjk : j.1 ≠ k.1 := by
              intro h
              apply hab
              exact congrArg some (Subtype.ext h)
            exact (d.hdisjoint j.1 k.1 (j.2.trans k.2.symm) hjk).eq_bot
    obtain ⟨t, ht, _⟩ := P.existsUnique_gluing' V (U i)
      (fun a ↦ homOfLE (hVU a)) cover sf compat
    obtain ⟨li, hli⟩ := abelianIntegerExtension_section_lift X P (U i) t
    refine ⟨li, ?_⟩
    apply abelianIntegerExtension_unit_injective X K (U i)
    change (Sigma.desc d.f).hom.app (op (U i)) (li.hom.app (op (U i)) (one (U i))) =
      (Sigma.ι _ i ≫ g).hom.app (op (U i)) (one (U i))
    change li.hom.app (op (U i)) (one (U i)) = t at hli
    rw [hli, ← d.hs i]
    apply K.eq_of_locally_eq' V (U i) (fun a ↦ homOfLE (hVU a)) cover
    intro a
    have hn := (Sigma.desc d.f).hom.naturality (homOfLE (hVU a)).op
    have hn' := congrArg (fun f ↦ f t) hn
    change (Sigma.desc d.f).hom.app (op (V a))
      (P.obj.map (homOfLE (hVU a)).op t) =
      K.obj.map (homOfLE (hVU a)).op ((Sigma.desc d.f).hom.app (op (U i)) t) at hn'
    rw [← hn', ht a]
    cases a with
    | none => simpa only [sf, map_zero] using (d.hzero i).symm
    | some j =>
      change (Sigma.desc d.f).hom.app (op (d.A j.1))
        (d.sign j.1 • (Sigma.ι (fun j ↦ E (d.A j)) j.1).hom.app
          (op (d.A j.1)) (one (d.A j.1))) = _
      rw [map_zsmul]
      have he := congrArg (fun f : E (d.A j.1) ⟶ K ↦
        f.hom.app (op (d.A j.1)) (one (d.A j.1))) (Sigma.ι_comp_desc d.f j.1)
      change (Sigma.desc d.f).hom.app (op (d.A j.1))
        ((Sigma.ι (fun j ↦ E (d.A j)) j.1).hom.app
          (op (d.A j.1)) (one (d.A j.1))) = _ at he
      rw [he]
      rcases j with ⟨j, hj⟩
      subst i
      exact (d.hsigned j).symm
  choose li hli using component
  refine ⟨Sigma.desc li, ?_⟩
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, Sigma.ι_comp_desc]
  exact hli i

end TopCat.Sheaf
