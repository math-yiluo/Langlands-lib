/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Localization detects vanishing of the multiplication tower

Source: Stacks Project, More on Algebra, Tag 091P, equivalence (1) and (3)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
lemma telescope_shortExact {C : Type*} [Category C] [Abelian C]
    (E : ℕ ⥤ C) [HasColimit E] (c : Cofan E.obj) (hc : IsColimit c)
    (d : c.pt ⟶ c.pt) [Mono d]
    (hd : ∀ n, c.inj n ≫ d =
      c.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ c.inj (n + 1)) :
    ∃ (e : c.pt ⟶ colimit E) (he : d ≫ e = 0),
      (ShortComplex.mk d e he).ShortExact := by
  let e := Cofan.IsColimit.desc hc (fun n ↦ colimit.ι E n)
  have he : d ≫ e = 0 := by
    apply Cofan.IsColimit.hom_ext hc
    intro n
    rw [← Category.assoc, hd]
    simp [e, Preadditive.sub_comp, Category.assoc, Cofan.IsColimit.fac, colimit.w]
  let cocone (s : CokernelCofork d) : Cocone E :=
    { pt := s.pt
      ι :=
        { app := fun n ↦ c.inj n ≫ s.π
          naturality := by
            intro n m a
            have hs (k : ℕ) :
                E.map (homOfLE (Nat.le_succ k)) ≫ c.inj (k + 1) ≫ s.π =
                  c.inj k ≫ s.π := by
              have hz := congrArg (fun z ↦ c.inj k ≫ z) s.condition
              rw [← Category.assoc, hd] at hz
              exact (sub_eq_zero.mp (by
                simpa [Preadditive.sub_comp] using hz)).symm
            have hall (m : ℕ) (hnm : n ≤ m) :
                E.map (homOfLE hnm) ≫ c.inj m ≫ s.π = c.inj n ≫ s.π := by
              induction m, hnm using Nat.le_induction with
              | base => simp
              | succ k hnk ih =>
                rw [show homOfLE (Nat.le_trans hnk (Nat.le_succ k)) =
                  homOfLE hnk ≫ homOfLE (Nat.le_succ k) from Subsingleton.elim _ _]
                rw [E.map_comp, Category.assoc, hs k]
                exact ih
            dsimp only [Functor.const]
            rw [Category.comp_id]
            rw [show a = homOfLE (leOfHom a) from Subsingleton.elim _ _]
            exact hall m (leOfHom a) } }
  have hco : IsColimit (CokernelCofork.ofπ e he) := by
    refine Cofork.IsColimit.mk _ (fun s ↦ colimit.desc E (cocone s)) ?_ ?_
    · intro s
      apply Cofan.IsColimit.hom_ext hc
      intro n
      simp [e, cocone, Cofan.IsColimit.fac_assoc]
    · intro s m hm
      apply colimit.hom_ext (F := E)
      intro n
      have hn := congrArg (fun z ↦ c.inj n ≫ z) hm
      simpa [e, cocone, Category.assoc, Cofan.IsColimit.fac_assoc] using hn
  refine ⟨e, he, ?_⟩
  exact
    { exact := ShortComplex.exact_of_g_is_cokernel _ hco
      mono_f := inferInstance
      epi_g := epi_of_isColimit_cofork hco }

namespace DerivedCategory

end DerivedCategory
