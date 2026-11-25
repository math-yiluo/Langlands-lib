/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Module localization as the colimit of multiplication by one element

Source: Stacks Project, Section 10.9 (Tag 00CM), module localization at the powers of an
element (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
/-- (auxiliary; not a blueprint node) Stacks Project, Tag 00CM:
the canonical map from the colimit of `M --f--> M --f--> M --f--> ...` to `M_f` is an
`R`-linear isomorphism, sending the class of `m` at stage `e` to `m / f^e`.

Proof:
1. Index the copies of `M` by the filtered poset of natural numbers; successive maps
   multiply by `f`. The linear maps `m ↦ m / f^e` are compatible, because
   `(f • m) / f^(e+1) = m / f^e`, and induce a map from the colimit by its universal
   property (def-weil-pbc-category-colimit).
2. Every element of the localization is a fraction `m / f^e`, so this map is surjective
   (def-weil-pbc-module-localization-away; lem-weil-pbc-filtered-colimit-modules-elementwise).
3. If `m / f^e = n / f^d`, the localization equality criterion gives some `r` with
   `f^r • (f^d • m - f^e • n) = 0`. At stage `E = e + d + r` the representatives have
   difference `f^(E-e) • m - f^(E-d) • n = 0`. Thus they represent the same colimit element
   (def-weil-pbc-module-localization-away; lem-weil-pbc-filtered-colimit-modules-elementwise).
4. The induced linear map is bijective and hence a linear isomorphism, with the given formula.
-/
theorem localization_away_colimit
    {R : Type u} [CommRing R] (f : R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    let D : ℕ ⥤ ModuleCat.{v} R :=
      Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R M)
        (fun _ : ℕ ↦ ModuleCat.ofHom (LinearMap.lsmul R M f))
    ∃ κ : ↥(colimit D) ≃ₗ[R] LocalizedModule.Away f M,
      ∀ (e : ℕ) (m : M),
        κ ((colimit.ι D e) m) =
          LocalizedModule.mk (S := Submonoid.powers f) m ⟨f ^ e, ⟨e, rfl⟩⟩ := by
  classical
  dsimp only
  let D : ℕ ⥤ ModuleCat.{v} R :=
    Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R M)
      (fun _ : ℕ ↦ ModuleCat.ofHom (LinearMap.lsmul R M f))
  change ∃ κ : ↥(colimit D) ≃ₗ[R] LocalizedModule.Away f M, _
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{v}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{v})
  have : PreservesColimit D (forget (ModuleCat.{v} R)) := by
    rw [← HasForget₂.forget_comp (C := ModuleCat.{v} R) (D := AddCommGrpCat.{v})]
    infer_instance
  have hstep (e : ℕ) : D.map (homOfLE (Nat.le_succ e)) =
      ModuleCat.ofHom (LinearMap.lsmul R M f) :=
    Functor.ofSequence_map_homOfLE_succ _ e
  have hι (e : ℕ) (m : M) :
      (colimit.ι D (e + 1)) (f • m) = (colimit.ι D e) m := by
    have h := ConcreteCategory.congr_hom (colimit.w D (homOfLE (Nat.le_succ e))) m
    change (colimit.ι D (e + 1)) ((D.map (homOfLE (Nat.le_succ e))) m) = _ at h
    rw [hstep] at h
    exact h
  let c : Cocone D :=
    { pt := colimit D
      ι := NatTrans.ofSequence (fun e ↦ colimit.ι D (e + 1)) (by
        intro e
        ext m
        change (colimit.ι D (e + 1 + 1)) ((D.map (homOfLE (Nat.le_succ e))) m) = _
        rw [hstep]
        exact hι (e + 1) m) }
  let t := (colimit.desc D c).hom
  have ht (e : ℕ) (m : M) : t ((colimit.ι D e) m) = (colimit.ι D (e + 1)) m := by
    exact ConcreteCategory.congr_hom (colimit.ι_desc c e) m
  have reps (x : ↥(colimit D)) : ∃ (e : ℕ) (m : M), (colimit.ι D e) m = x := by
    exact Concrete.colimit_exists_rep D x
  have ht₁ (x : ↥(colimit D)) : f • t x = x := by
    obtain ⟨e, m, rfl⟩ := reps x
    rw [ht, ← map_smul (colimit.ι D (e + 1)).hom, hι]
  have ht₂ (x : ↥(colimit D)) : t (f • x) = x := by
    rw [map_smul, ht₁]
  have hf : IsUnit (algebraMap R (Module.End R ↥(colimit D)) f) := by
    rw [Module.End.isUnit_iff]
    exact ⟨fun x y h ↦ by simpa only [Module.algebraMap_end_apply, ht₂] using congrArg t h,
      fun x ↦ ⟨t x, ht₁ x⟩⟩
  have hp (e k : ℕ) (m : M) :
      (colimit.ι D (e + k)) (f ^ k • m) = (colimit.ι D e) m := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', mul_smul, ← Nat.add_assoc, hι, ih]
  have hmap (k : ℕ) (m : M) : D.map (homOfLE (Nat.zero_le k)) m = f ^ k • m := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show homOfLE (Nat.zero_le (k + 1)) =
          homOfLE (Nat.zero_le k) ≫ homOfLE (Nat.le_succ k) from Subsingleton.elim _ _,
          D.map_comp]
        change (D.map (homOfLE (Nat.le_succ k)))
          ((D.map (homOfLE (Nat.zero_le k))) m) = _
        rw [hstep]
        change f • (D.map (homOfLE (Nat.zero_le k))) m = _
        rw [ih, pow_succ', mul_smul]
  have hp₀ (e : ℕ) (m : M) :
      f ^ e • (colimit.ι D e) m = (colimit.ι D 0) m := by
    have h := hp 0 e m
    rw [Nat.zero_add] at h
    change (colimit.ι D e).hom (f ^ e • m) = _ at h
    rw [map_smul] at h
    exact h
  have hloc : IsLocalizedModule (Submonoid.powers f) (colimit.ι D 0).hom :=
    { map_units := by
        rintro ⟨s, e, rfl⟩
        simpa only [map_pow] using hf.pow e
      surj := by
        intro x
        obtain ⟨e, m, rfl⟩ := reps x
        refine ⟨⟨m, ⟨f ^ e, ⟨e, rfl⟩⟩⟩, ?_⟩
        change f ^ e • (colimit.ι D e) m = (colimit.ι D 0) m
        exact hp₀ e m
      exists_of_eq := by
        intro x y h
        obtain ⟨k, a, b, hab⟩ := Concrete.colimit_exists_of_rep_eq D x y h
        refine ⟨⟨f ^ k, ⟨k, rfl⟩⟩, ?_⟩
        have ha : a = homOfLE (Nat.zero_le k) := Subsingleton.elim _ _
        have hb : b = homOfLE (Nat.zero_le k) := Subsingleton.elim _ _
        change f ^ k • x = f ^ k • y
        simpa only [ha, hb, hmap] using hab }
  let := hloc
  refine ⟨(IsLocalizedModule.iso (Submonoid.powers f) (colimit.ι D 0).hom).symm, ?_⟩
  intro e m
  apply IsLocalizedModule.iso_symm_apply'
  change f ^ e • (colimit.ι D e) m = (colimit.ι D 0) m
  exact hp₀ e m

end ModuleCat
