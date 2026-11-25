/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension

/-!
# zero case of the well-ordered union argument

Source: Stacks Project, Algebra, Lemma 0D1U.
-/

@[expose] public section

universe u v w

namespace ModuleCat

private theorem projective_of_resolution_zero
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (h : HasProjectiveResolutionLE M 0) : CategoryTheory.Projective M := by
  obtain ⟨P, hP⟩ := h
  have hd : P.complex.d 1 0 = 0 := (hP 1 (by omega)).eq_of_src _ _
  have : CategoryTheory.IsIso (P.π.f 0) :=
    CategoryTheory.Limits.CokernelCofork.IsColimit.isIso_π
      P.cokernelCofork P.isColimitCokernelCofork hd
  exact CategoryTheory.Projective.of_iso (CategoryTheory.asIso (P.π.f 0)) (P.projective 0)

private theorem resolution_zero_of_projective
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) [CategoryTheory.Projective M] :
    HasProjectiveResolutionLE M 0 := by
  refine ⟨CategoryTheory.ProjectiveResolution.self M, fun i hi ↦ ?_⟩
  exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

private theorem sections_sum_eq_zero
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {E : Type w} [LinearOrder E] (F : E → Submodule R M) (hF : Monotone F)
    (s : ∀ e, ((F e) ⧸
      ((⨆ i : {i : E // i < e}, F i.val).comap (F e).subtype)) →ₗ[R] F e)
    (hs : ∀ e, ((⨆ i : {i : E // i < e}, F i.val).comap (F e).subtype).mkQ.comp
      (s e) = LinearMap.id)
    (t : Finset E)
    (x : ∀ e, (F e) ⧸ ((⨆ i : {i : E // i < e}, F i.val).comap (F e).subtype))
    (hx : ∑ e ∈ t, ((s e (x e) : F e) : M) = 0) : ∀ e ∈ t, x e = 0 := by
  classical
  induction t using Finset.induction_on_max with
  | empty => simp
  | insert e t hlt ih =>
    have he : e ∉ t := fun h ↦ (hlt e h).false
    rw [Finset.sum_insert he] at hx
    have hprev : (∑ i ∈ t, ((s i (x i) : F i) : M)) ∈
        ⨆ i : {i : E // i < e}, F i.val := by
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.mem_iSup_of_mem ⟨i, hlt i hi⟩ (s i (x i)).property
    have hstage : (∑ i ∈ t, ((s i (x i) : F i) : M)) ∈ F e := by
      apply Submodule.sum_mem
      intro i hi
      exact hF (hlt i hi).le (s i (x i)).property
    have heq : s e (x e) = -(⟨∑ i ∈ t, ((s i (x i) : F i) : M), hstage⟩ : F e) :=
      Subtype.ext (eq_neg_of_add_eq_zero_left hx)
    have hmem : s e (x e) ∈
        (⨆ i : {i : E // i < e}, F i.val).comap (F e).subtype := by
      rw [heq]
      exact Submodule.neg_mem _ hprev
    have hxe : x e = 0 := by
      have hzero := (Submodule.Quotient.mk_eq_zero _).mpr hmem
      have hsec := DFunLike.congr_fun (hs e) (x e)
      exact hsec.symm.trans hzero
    have hrest : ∑ i ∈ t, ((s i (x i) : F i) : M) = 0 := by
      simpa [hxe] using hx
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hxe
    · exact ih hrest i hi

private theorem sections_sum_surjective
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (s : ∀ e, ((F e) ⧸
      ((⨆ i : {i : E // i < e}, F i.val).comap (F e).subtype)) →ₗ[R] F e)
    (hs : ∀ e, ((⨆ i : {i : E // i < e}, F i.val).comap (F e).subtype).mkQ.comp
      (s e) = LinearMap.id) :
    Function.Surjective (DirectSum.toModule R E M
      (fun e ↦ (F e).subtype.comp (s e))) := by
  classical
  let ψ := DirectSum.toModule R E M (fun e ↦ (F e).subtype.comp (s e))
  have hrange : ∀ e, F e ≤ ψ.range := by
    intro e
    induction e using (wellFounded_lt (α := E)).induction with
    | h e ih =>
      intro y hy
      let z : F e := ⟨y, hy⟩
      let U := (⨆ i : {i : E // i < e}, F i.val).comap (F e).subtype
      have hsec : U.mkQ (s e (U.mkQ z)) = U.mkQ z :=
        DFunLike.congr_fun (hs e) (U.mkQ z)
      have hdiff : z - s e (U.mkQ z) ∈ U := by
        apply (Submodule.Quotient.mk_eq_zero U).mp
        change U.mkQ (z - s e (U.mkQ z)) = 0
        rw [map_sub, hsec, sub_self]
      have hprev : (⨆ i : {i : E // i < e}, F i.val) ≤ ψ.range :=
        iSup_le fun i ↦ ih i.val i.property
      have hdiff' : y - ((s e (U.mkQ z) : F e) : M) ∈ ψ.range := hprev hdiff
      have hterm : ((s e (U.mkQ z) : F e) : M) ∈ ψ.range := by
        refine ⟨DirectSum.lof R E _ e (U.mkQ z), ?_⟩
        simp [ψ]
      simpa using ψ.range.add_mem hdiff' hterm
  intro y
  obtain ⟨e, he⟩ := hcover y
  exact hrange e he

/-- Base case of Auslander's well-ordered union argument.
Source: Stacks Project, Algebra, Lemma 0D1U, the case `n = 0`.
(blueprint: lem-weil-pbc-well-ordered-union-zero-step).

Proof: write `U e` for the supremum of the preceding stages, pulled back into `F e`,
and `Q e = F e / U e`. A length-zero projective resolution makes its augmentation
an isomorphism: its degree-one object is zero and its augmentation is a cokernel
of the zero arrow. Thus each `Q e` is a projective object in `ModuleCat.{v} R`.
The quotient projection `F e → Q e` is an epimorphism. Its projectivity supplies
an R-linear section `s e`. Compose this section with the inclusion into `M`.

Define `psi` from the external direct sum of the `Q e` to `M` by the finite sum
of the section maps. For injectivity take a nonzero vector and the largest index
in its finite nonempty support. Its image lies in that stage; projection to that
stage's quotient kills all smaller components and leaves its nonzero component.
For surjectivity use well-founded induction on a stage containing the given
vector `y`. Subtract `s e` of its quotient class. The difference belongs to the
predecessor supremum. Directedness of the nonempty chain of earlier stages
identifies that supremum with their union. Hence the difference is in an earlier
stage and the induction hypothesis applies. At a least stage the predecessor
is zero, so the difference is zero. Add back the section to obtain a preimage.

The direct sum is consequently linearly equivalent to `M`. If `E` lives in a
larger universe, shrink this direct sum along the equivalence before regarding
it as an object of `ModuleCat.{v} R`. To verify its categorical projectivity,
lift a map out of it across an epimorphism by lifting each component using the
categorical projectivity of `Q e`, and sum the lifts on finite supports. This
argument does not require the ring to be small in universe `v`. Transfer
projectivity to `M` and use the identity resolution, concentrated in degree zero.
No choice is used to define library data: the sections only occur in this proof.

Edge cases: an empty `E` is excluded by `hcover` applied to zero. Repeated stages
have zero successive quotients and contribute zero summands. For a single stage
the quotient projection is the identification with the whole module. -/
theorem hasProjectiveResolutionLE_of_wellOrderedUnion_zero
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (hquot : ∀ e : E, HasProjectiveResolutionLE
      (ModuleCat.of R ((F e) ⧸
        ((⨆ e' : {i : E // i < e}, F e'.val).comap (F e).subtype))) 0) :
    HasProjectiveResolutionLE M 0 := by
  classical
  let U (e : E) := (⨆ i : {i : E // i < e}, F i.val).comap (F e).subtype
  let Q (e : E) := (F e) ⧸ U e
  have hQ : ∀ e, CategoryTheory.Projective (ModuleCat.of R (Q e)) :=
    fun e ↦ projective_of_resolution_zero _ (hquot e)
  have hsections : ∀ e, ∃ s : Q e →ₗ[R] F e, (U e).mkQ.comp s = LinearMap.id := by
    intro e
    have : CategoryTheory.Epi (ModuleCat.ofHom (U e).mkQ) :=
      (ModuleCat.epi_iff_surjective _).mpr (U e).mkQ_surjective
    obtain ⟨s, hs⟩ := CategoryTheory.Projective.factors
      (CategoryTheory.CategoryStruct.id (ModuleCat.of R (Q e)))
      (ModuleCat.ofHom (U e).mkQ)
    exact ⟨s.hom, ModuleCat.hom_ext_iff.mp hs⟩
  choose s hs using hsections
  let ψ := DirectSum.toModule R E M (fun e ↦ (F e).subtype.comp (s e))
  have hinj : Function.Injective ψ := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro x hx
    change ψ x = 0 at hx
    have hsum : ∑ e ∈ x.support, ((s e (x e) : F e) : M) = 0 := by
      change (DFinsupp.sumAddHom
        (fun e ↦ ((F e).subtype.comp (s e)).toAddMonoidHom)) x = 0 at hx
      simpa only [DFinsupp.sumAddHom_apply, DFinsupp.sum,
        LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
        Submodule.subtype_apply] using hx
    have hcoeff := sections_sum_eq_zero F hF s hs x.support (fun e ↦ x e) hsum
    change x = 0
    ext e
    change x e = 0
    by_cases he : e ∈ x.support
    · exact hcoeff e he
    · simpa only [DFinsupp.mem_support_iff, not_not] using he
  have hsurj : Function.Surjective ψ := sections_sum_surjective F hcover s hs
  let a := LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have hM : CategoryTheory.Projective M := by
    constructor
    intro X Y f p hp
    have hlifts : ∀ e, ∃ l : Q e →ₗ[R] X,
        p.hom.comp l = f.hom.comp ((F e).subtype.comp (s e)) := by
      intro e
      obtain ⟨l, hl⟩ := CategoryTheory.Projective.factors
        (ModuleCat.ofHom (f.hom.comp ((F e).subtype.comp (s e)))) p
      exact ⟨l.hom, ModuleCat.hom_ext_iff.mp hl⟩
    choose l hl using hlifts
    let χ := DirectSum.toModule R E X l
    have hχ : p.hom.comp χ = f.hom.comp ψ := by
      apply DirectSum.linearMap_ext
      intro e
      apply LinearMap.ext
      intro x
      simpa [χ, ψ] using DFunLike.congr_fun (hl e) x
    refine ⟨ModuleCat.ofHom (χ.comp a.symm.toLinearMap), ?_⟩
    apply ModuleCat.hom_ext
    change p.hom.comp (χ.comp a.symm.toLinearMap) = f.hom
    rw [← LinearMap.comp_assoc, hχ, LinearMap.comp_assoc]
    have ha : ψ.comp a.symm.toLinearMap = LinearMap.id := by
      ext x
      exact a.apply_symm_apply x
    rw [ha, LinearMap.comp_id]
  exact resolution_zero_of_projective M

end ModuleCat
