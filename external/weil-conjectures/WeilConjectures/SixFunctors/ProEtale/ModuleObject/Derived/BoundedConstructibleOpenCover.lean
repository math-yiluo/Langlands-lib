/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-!
# Bounded constructibility is local on finite open covers

Let `Λ` be a commutative condensed ring and `X` a scheme with noetherian underlying space, covered
by finitely many opens `Uᵢ`. A complex `K` of module objects over `Λ_X` is bounded constructible
as soon as its restrictions `K|_{Uᵢ}` are
(`ProEtale.CondensedRing.boundedConstructible_of_openCover`). This rests on the open–closed
dévissage: for an open `U` with closed complement `Z`, a module object is zero, respectively
constructible, as soon as its restrictions to `U` and `Z` are
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_of_isCompl`,
`ProEtale.CondensedRing.isConstructibleModuleObject_of_openClosed`, by concatenating
stratifications), and on an induction on the number of opens, as for étale sheaves
(`AlgebraicGeometry.Etale.boundedConstructible_of_openCover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- On an empty scheme every module object over `Λ` is zero: all sections over the (empty)
objects of the pro-étale site are zero. -/
lemma isZero_mod_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsZero M :=
  isZero_of_isZero_X _ (IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) _
    (Functor.isZero _ fun T ↦
      have : IsEmpty T.unop.left := ⟨fun t ↦ IsEmpty.false (α := X) (T.unop.hom.base t)⟩
      (ProEt.isTerminalSectionsOfIsEmpty M.X T.unop).isZero))

/-- The restriction to `i⁻¹ U` of the restriction to `Z` of a module object is the restriction
to `Z ∩ U` of its restriction to `U`. -/
noncomputable def upperStarRestrictIso {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((i ⁻¹ᵁ U).ι)^*⟦Λ⟧.obj ((i)^*⟦Λ⟧.obj M) ≅ (i ∣_ U)^*⟦Λ⟧.obj ((U.ι)^*⟦Λ⟧.obj M) :=
  upperStarSquareIso Λ (a := (i ⁻¹ᵁ U).ι) (b := i ∣_ U) (f := i) (g := U.ι)
    (morphismRestrict_ι i U).symm M

/-- If the restriction of `M` to an open `U` vanishes, so does the restriction to `V = i⁻¹ U` of
`i^* M`. (Stated for any `V` equal to `i⁻¹ U`, to keep the kernel checks cheap.) -/
lemma isZero_upperStar_restrict {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) (V : Z.Opens)
    (hV : V = i ⁻¹ᵁ U)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsZero ((U.ι)^*⟦Λ⟧.obj M)) : IsZero ((V.ι)^*⟦Λ⟧.obj ((i)^*⟦Λ⟧.obj M)) := by
  subst hV
  exact ((upperStar Λ (i ∣_ U)).map_isZero h).of_iso (upperStarRestrictIso Λ i U M)

/-- If the restriction of `M` to an open `U` is constructible, so is the restriction to
`V = i⁻¹ U` of `i^* M`. -/
lemma isConstructibleModuleObject_upperStar_restrict {X Z : Scheme.{u}} (i : Z ⟶ X)
    (U : X.Opens) (V : Z.Opens) (hV : V = i ⁻¹ᵁ U)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsConstructibleModuleObject (condensedRingObj Λ U) ((U.ι)^*⟦Λ⟧.obj M)) :
    IsConstructibleModuleObject (condensedRingObj Λ V) ((V.ι)^*⟦Λ⟧.obj ((i)^*⟦Λ⟧.obj M)) := by
  subst hV
  exact (IsConstructibleModuleObject.upperStar Λ (i ∣_ U) h).of_iso
    (upperStarRestrictIso Λ i U M).symm

/-- The traces on the closed complement `Z` of `U₀` of the remaining members of a finite open
cover cover `Z`. -/
lemma exists_mem_preimage_succ {X Z : Scheme.{u}} {n : ℕ} (U : Fin (n + 1) → X.Opens)
    (hU : ∀ x, ∃ i, x ∈ U i) (i : Z ⟶ X) (hi : Set.range i.base = ((U 0 : Set X))ᶜ) (z : Z) :
    ∃ k : Fin n, z ∈ i ⁻¹ᵁ U k.succ := by
  have hz : i.base z ∉ U 0 := by
    have : i.base z ∈ Set.range i.base := ⟨z, rfl⟩
    rwa [hi] at this
  obtain ⟨k, hk⟩ := hU (i.base z)
  obtain ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ k |>.resolve_left (by rintro rfl; exact hz hk)
  exact ⟨k, hk⟩

/-- A module object on a scheme with noetherian underlying space vanishes as soon as its
restrictions to the members of a finite open cover vanish. -/
theorem isZero_of_openCover : ∀ (n : ℕ) {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (U : Fin n → X.Opens) (_ : ∀ x, ∃ i, x ∈ U i)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (∀ i, IsZero (((U i).ι)^*⟦Λ⟧.obj M)) → IsZero M := by
  intro n
  induction n with
  | zero =>
    intro X _ U hU M _
    have : IsEmpty X := ⟨fun x ↦ by obtain ⟨i, -⟩ := hU x; exact i.elim0⟩
    exact isZero_mod_of_isEmpty Λ M
  | succ n ih =>
    intro X _ U hU M h
    have : TopologicalSpace.NoetherianSpace (U 0) :=
      (U 0).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (U 0).ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    obtain ⟨Z, i, _, hij⟩ : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
        Set.range i.base = ((U 0 : Set X))ᶜ :=
      ⟨_, (U 0).closedComplement, inferInstance, (U 0).range_closedComplement⟩
    have : TopologicalSpace.NoetherianSpace Z := i.isClosedEmbedding.isInducing.noetherianSpace
    have hc : IsCompl (Set.range i.base) (Set.range (U 0).ι.base) := by
      rw [hij, Scheme.Opens.range_ι]
      exact isCompl_compl.symm
    let V : Fin n → Z.Opens := fun k ↦ i ⁻¹ᵁ U k.succ
    exact isZero_of_isZero_upperStar_of_isCompl Λ i (U 0).ι hc M
      (@ih Z _ V (exists_mem_preimage_succ U hU i hij) ((i)^*⟦Λ⟧.obj M)
        (fun k ↦ isZero_upperStar_restrict Λ i (U k.succ) (V k) rfl M (h k.succ))) (h 0)

/-- If the restriction of `j^* M` along `g` is pro-étale locally finitely presented, so is the
restriction of `M` along `g ≫ j`. -/
lemma isLocallyFinitelyPresented_mapMod_comp {W U X : Scheme.{u}} (g : W ⟶ U) (j : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsLocallyFinitelyPresented ((g)^*[Ab.{u + 1}].obj (condensedRingObj Λ U))
      (((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ U)).obj ((j)^*⟦Λ⟧.obj M))) :
    IsLocallyFinitelyPresented ((g ≫ j)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
      (((g ≫ j)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj M) := by
  refine (isLocallyFinitelyPresented_mapMod_iff Λ _ _).2 (IsLocallyFinitelyPresented.of_iso ?_
    ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 h))
  exact ((upperStarComp Λ g j).app _).symm

/-- **Open–closed dévissage of constructibility**: for an open immersion `j` with quasi-compact
range and a closed immersion `i` onto its complement, a module object whose restrictions along `j`
and `i` are constructible is constructible, along the concatenated stratification
(`Scheme.Stratification.openClosed`). -/
theorem isConstructibleModuleObject_of_openClosed {X U Z : Scheme.{u}} (j : U ⟶ X)
    (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hU : IsConstructibleModuleObject (condensedRingObj Λ U) ((j)^*⟦Λ⟧.obj M))
    (hZ : IsConstructibleModuleObject (condensedRingObj Λ Z) ((i)^*⟦Λ⟧.obj M)) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  obtain ⟨SU, hSU⟩ := hU
  obtain ⟨SZ, hSZ⟩ := hZ
  refine ⟨Stratification.openClosed j i hij SU SZ, fun k ↦ ?_⟩
  change IsLocallyFinitelyPresented
      ((Sum.rec (motive := fun s ↦ Sum.elim SU.domain SZ.domain s ⟶ X)
        (fun l ↦ SU.immersion l ≫ j) (fun l ↦ SZ.immersion l ≫ i)
        (finSumFinEquiv.symm k))^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
      (((Sum.rec (motive := fun s ↦ Sum.elim SU.domain SZ.domain s ⟶ X)
        (fun l ↦ SU.immersion l ≫ j) (fun l ↦ SZ.immersion l ≫ i)
        (finSumFinEquiv.symm k))^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj M)
  generalize finSumFinEquiv.symm k = s
  rcases s with l | l
  · exact isLocallyFinitelyPresented_mapMod_comp Λ (SU.immersion l) j M (hSU l)
  · exact isLocallyFinitelyPresented_mapMod_comp Λ (SZ.immersion l) i M (hSZ l)

/-- A module object on a scheme with noetherian underlying space is constructible as soon as its
restrictions to the members of a finite open cover are. -/
theorem isConstructibleModuleObject_of_openCover : ∀ (n : ℕ) {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (U : Fin n → X.Opens) (_ : ∀ x, ∃ i, x ∈ U i)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (∀ i, IsConstructibleModuleObject (condensedRingObj Λ (U i)) (((U i).ι)^*⟦Λ⟧.obj M)) →
      IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  intro n
  induction n with
  | zero =>
    intro X _ U hU M _
    have : IsEmpty X := ⟨fun x ↦ by obtain ⟨i, -⟩ := hU x; exact i.elim0⟩
    exact ProEtale.isConstructibleModuleObject_of_isZero _ (isZero_mod_of_isEmpty Λ M)
  | succ n ih =>
    intro X _ U hU M h
    have : TopologicalSpace.NoetherianSpace (U 0) :=
      (U 0).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (U 0).ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    obtain ⟨Z, i, _, hij⟩ : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
        Set.range i.base = ((U 0 : Set X))ᶜ :=
      ⟨_, (U 0).closedComplement, inferInstance, (U 0).range_closedComplement⟩
    have : TopologicalSpace.NoetherianSpace Z := i.isClosedEmbedding.isInducing.noetherianSpace
    let V : Fin n → Z.Opens := fun k ↦ i ⁻¹ᵁ U k.succ
    exact isConstructibleModuleObject_of_openClosed Λ (U 0).ι i
      (by rw [hij, Scheme.Opens.range_ι]) M (h 0)
      (@ih Z _ V (exists_mem_preimage_succ U hU i hij) ((i)^*⟦Λ⟧.obj M)
        (fun k ↦ isConstructibleModuleObject_upperStar_restrict Λ i (U k.succ) (V k) rfl M
          (h k.succ)))

/-- **Bounded constructibility is local on finite open covers**: a complex of module objects over
`Λ` on a scheme with noetherian underlying space whose restrictions to the members of a finite
open cover are bounded constructible is bounded constructible. -/
theorem boundedConstructible_of_openCover {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h : ∀ i, boundedConstructible (condensedRingObj Λ (U i).toScheme)
      ((L((Scheme.Opens.ι (U i))^*⟦Λ⟧)).obj K)) :
    boundedConstructible (condensedRingObj Λ X) K := by
  -- homology commutes with the restrictions
  have e (i : Fin n) (q : ℤ) := (leftDerivedUpperStarHomologyIso Λ (U i).ι q).app K
  choose a b hab using fun i ↦ ((mem_boundedConstructible_iff _ _).1 (h i)).1
  have hz (q : ℤ) (hq : ∀ i, q < a i ∨ b i < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) :=
    isZero_of_openCover Λ n U hU _ fun i ↦ (hab i q (hq i)).of_iso (e i q)
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨-∑ i, |a i|, ∑ i, |b i|, fun q hq ↦ ?_⟩,
    fun q ↦ ?_⟩
  · refine hz q fun i ↦ ?_
    have h₁ := Finset.single_le_sum (f := fun i ↦ |a i|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    have h₂ := Finset.single_le_sum (f := fun i ↦ |b i|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    have := neg_abs_le (a i)
    have := le_abs_self (b i)
    rcases hq with hq | hq
    · left; lia
    · right; lia
  · exact isConstructibleModuleObject_of_openCover Λ n U hU _ fun i ↦
      (((mem_boundedConstructible_iff _ _).1 (h i)).2 q).of_iso (e i q).symm

end AlgebraicGeometry.ProEtale.CondensedRing
