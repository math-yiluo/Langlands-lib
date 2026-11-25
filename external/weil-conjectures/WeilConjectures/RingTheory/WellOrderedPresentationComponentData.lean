/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Component data for a well-ordered projective presentation

Source: Stacks Project, Algebra, Lemma 0D1U, direct-sum presentation construction,
adapted to supplied projective augmentations and arbitrary index universes.
(blueprint: lem-weil-pbc-well-ordered-presentation-component-data).
-/

@[expose] public section

universe u v w

namespace ModuleCat

open CategoryTheory

private def stageSupport {R : Type u} [CommRing R] {I : Type v} {E : Type w}
    [LinearOrder E] (key : I → E) (Q : I → ModuleCat.{v} R) (e : E) :
    Submodule R (Π₀ i, Q i) where
  carrier := {x | ∀ i, ¬ key i ≤ e → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro r x hx i hi
    simp [hx i hi]

private theorem stageSupport_mono {R : Type u} [CommRing R] {I : Type v} {E : Type w}
    [LinearOrder E] (key : I → E) (Q : I → ModuleCat.{v} R) :
    Monotone (stageSupport key Q) := by
  intro e f hef x hx i hi
  exact hx i (fun h ↦ hi (h.trans hef))

private theorem single_mem_stageSupport {R : Type u} [CommRing R] {I : Type v}
    [DecidableEq I]
    {E : Type w} [LinearOrder E] (key : I → E) (Q : I → ModuleCat.{v} R)
    (i : I) (z : Q i) {e : E} (hi : key i ≤ e) :
    DFinsupp.single i z ∈ stageSupport key Q e := by
  classical
  intro j hj
  have hij : i ≠ j := by
    intro h
    subst j
    exact hj hi
  simp [DFinsupp.single_apply, hij]

private theorem stageSupport_cover {R : Type u} [CommRing R] {I : Type v}
    {E : Type w} [LinearOrder E] [Nonempty E]
    (key : I → E) (Q : I → ModuleCat.{v} R) (x : Π₀ i, Q i) :
    ∃ e, x ∈ stageSupport key Q e := by
  classical
  induction x using DFinsupp.induction with
  | h0 => exact ⟨Classical.arbitrary E, (stageSupport key Q _).zero_mem⟩
  | ha i z x _ _ ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨max (key i) e, (stageSupport key Q _).add_mem ?_ ?_⟩
    · exact single_mem_stageSupport key Q i z (le_max_left _ _)
    · exact stageSupport_mono key Q (le_max_right _ _) he

private theorem strictSupport_mem_predecessors {R : Type u} [CommRing R]
    {I : Type v} {E : Type w} [LinearOrder E]
    (key : I → E) (Q : I → ModuleCat.{v} R) (e : E) (x : Π₀ i, Q i)
    (hx : ∀ i, ¬ key i < e → x i = 0) :
    x ∈ ⨆ j : {j : E // j < e}, stageSupport key Q j.val := by
  classical
  rw [← DFinsupp.sum_single (f := x), DFinsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  have hlt : key i < e := by
    by_contra h
    exact (DFinsupp.mem_support_iff.mp hi) (hx i h)
  exact (le_iSup (fun j : {j : E // j < e} ↦ stageSupport key Q j.val)
    ⟨key i, hlt⟩) (single_mem_stageSupport key Q i (x i) le_rfl)

private theorem stageSupport_inactive {R : Type u} [CommRing R] {I : Type v}
    {E : Type w} [LinearOrder E] (key : I → E) (Q : I → ModuleCat.{v} R)
    (e : E) (he : ∀ i, key i ≠ e) :
    stageSupport key Q e = ⨆ j : {j : E // j < e}, stageSupport key Q j.val := by
  apply le_antisymm
  · intro x hx
    apply strictSupport_mem_predecessors key Q e x
    intro i hi
    apply hx i
    exact fun h ↦ hi (lt_of_le_of_ne h (he i))
  · apply iSup_le
    intro j
    exact stageSupport_mono key Q j.property.le

private theorem stageSupport_projection {R : Type u} [CommRing R] {I : Type v}
    {E : Type w} [LinearOrder E]
    (key : I → E) (Q : I → ModuleCat.{v} R) (hkey : Function.Injective key) (i : I) :
    Function.Surjective ((DFinsupp.lapply i).comp (stageSupport key Q (key i)).subtype) ∧
    ((DFinsupp.lapply i).comp (stageSupport key Q (key i)).subtype).ker =
      (⨆ j : {j : E // j < key i}, stageSupport key Q j.val).comap
        (stageSupport key Q (key i)).subtype := by
  classical
  constructor
  · intro z
    exact ⟨⟨DFinsupp.single i z, single_mem_stageSupport key Q i z le_rfl⟩, by simp⟩
  · apply le_antisymm
    · intro x hx
      change x.val i = 0 at hx
      apply strictSupport_mem_predecessors key Q (key i) x.val
      intro j hj
      by_cases hji : key j ≤ key i
      · have h : j = i := hkey (le_antisymm hji (le_of_not_gt hj))
        subst j
        exact hx
      · exact x.property j hji
    · intro x hx
      change x.val i = 0
      change x.val ∈ ⨆ j : {j : E // j < key i}, stageSupport key Q j.val at hx
      refine Submodule.iSup_induction _ hx (motive := fun y ↦ y i = 0) ?_ ?_ ?_
      · intro j y hy
        exact hy i (not_le_of_gt j.property)
      · rfl
      · intro y z hy hz
        simp [hy, hz]

private theorem stageSupport_image_le {R : Type u} [CommRing R] {I : Type v}
    {E : Type w} [LinearOrder E] [DecidableEq I]
    (key : I → E) (Q : I → ModuleCat.{v} R) (M : ModuleCat.{v} R)
    (F : E → Submodule R M) (hF : Monotone F)
    (t : ∀ i, Q i →ₗ[R] F (key i)) (e : E) :
    (stageSupport key Q e).map
      (DFinsupp.lsum R (fun i ↦ (F (key i)).subtype.comp (t i))) ≤ F e := by
  classical
  rintro _ ⟨x, hx, rfl⟩
  rw [← DFinsupp.sum_single (f := x), DFinsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [DFinsupp.lsum_single]
  have hle : key i ≤ e := by
    by_contra h
    exact (DFinsupp.mem_support_iff.mp hi) (hx i h)
  exact hF hle (t i (x i)).property

private theorem dfinsupp_category_projective {R : Type u} [CommRing R] {I : Type v}
    (Q : I → ModuleCat.{v} R) [∀ i, Projective (Q i)] :
    Projective (ModuleCat.of R (Π₀ i, Q i)) := by
  classical
  constructor
  intro X Y f g hg
  let t : ∀ i, Q i →ₗ[R] X := fun i ↦
    (Projective.factorThru (ModuleCat.ofHom (f.hom.comp (DFinsupp.lsingle i))) g).hom
  refine ⟨ModuleCat.ofHom (DFinsupp.lsum R t), ?_⟩
  apply ModuleCat.hom_ext
  apply DFinsupp.lhom_ext
  intro i z
  have ht := ModuleCat.hom_ext_iff.mp
    (Projective.factorThru_comp (ModuleCat.ofHom (f.hom.comp (DFinsupp.lsingle i))) g)
  change g.hom.comp (t i) = f.hom.comp (DFinsupp.lsingle i) at ht
  change g.hom ((DFinsupp.lsum R t) (DFinsupp.single i z)) = _
  rw [DFinsupp.lsum_single]
  exact LinearMap.congr_fun ht z

/-- Construct the filtered projective middle module and its component maps, before
intersecting with the kernel of the presentation.
Source: Stacks Project, Algebra, Lemma 0D1U, direct-sum presentation construction;
the active-index size reduction is the construction in the parent node.
(blueprint: lem-weil-pbc-well-ordered-presentation-component-data).

Proof: let V_e be the supremum of F_i for i < e, and call e active when
F_e / (V_e.comap F_e.subtype) is nonzero. Choose x_e in F_e outside V_e at each
active index. If e < f, then x_e belongs to V_f whereas x_f does not, so these
choices give an injection of the active indices into M. Hence they are small
in universe v, and their shrunk type can index a direct sum B in universe v.
For each active e, lift the supplied projective degree-zero augmentation
through the quotient epimorphism F_e → F_e / V_e using categorical projectivity.
Define b on each summand by this lift followed by F_e.subtype. Define H_e by
support in indices at most e. These submodules are monotone and exhaustive:
a finite nonempty support has a largest index, and for empty support an index
exists by applying hcover to zero. B is categorically projective by lifting
maps from each summand through an epimorphism and summing the lifts.

Prove map b H_e = F_e by well-founded induction. The inclusion into F_e
follows from monotonicity. For the reverse inclusion, at an active stage lift
the quotient class using surjectivity of the augmentation, subtract the image
of the corresponding summand, and obtain an element of V_e. By induction, each
earlier F_i lies in the image of H_i and hence in the image of H_e. The supremum
universal property therefore puts all of V_e in the image of H_e, including
when the predecessor set is empty. At an inactive stage
F_e = V_e and this induction argument alone suffices.

At an inactive stage no summand is added, so H_e is the predecessor supremum.
At an active stage take p to be the component projection. It is surjective by
the summand inclusion. Its kernel is the vectors supported strictly before e;
finite support identifies this with the predecessor supremum pulled back to
H_e. Take a to be b restricted to H_e with codomain F_e. After quotienting,
every earlier summand vanishes, and the e summand gives the augmentation,
which proves the displayed commuting identity. This also handles repeated
stages (inactive), a least active stage (zero predecessors), and M = 0 (no
active indices). No object is defined by choosing from this unfinished theorem. -/
theorem exists_projective_presentation_component_data
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (P : ∀ e : E, ProjectiveResolution
      (ModuleCat.of R ((F e) ⧸
        ((⨆ i : {j : E // j < e}, F i.val).comap (F e).subtype)))) :
    ∃ (B : ModuleCat.{v} R) (_ : Projective B) (b : B →ₗ[R] M)
      (H : E → Submodule R B),
      Monotone H ∧ (∀ x : B, ∃ e : E, x ∈ H e) ∧
      (∀ e : E, (H e).map b = F e) ∧
      ∀ e : E,
        H e = ⨆ i : {j : E // j < e}, H i.val ∨
        ∃ p : H e →ₗ[R] (P e).complex.X 0,
          Function.Surjective p ∧
          p.ker = (⨆ i : {j : E // j < e}, H i.val).comap (H e).subtype ∧
          ∃ a : H e →ₗ[R] F e,
            (F e).subtype.comp a = b.comp (H e).subtype ∧
            ((P e).π.f 0).hom.comp p =
              ((⨆ i : {j : E // j < e}, F i.val).comap (F e).subtype).mkQ.comp a := by
  classical
  let V : E → Submodule R M := fun e ↦ ⨆ j : {j : E // j < e}, F j.val
  have hVF (e : E) : V e ≤ F e := iSup_le fun j ↦ hF j.property.le
  let A := {e : E // F e ≠ V e}
  have hex (e : A) : ∃ x : F e.val, (x : M) ∉ V e.val := by
    by_contra h
    have hall : ∀ x : F e.val, (x : M) ∈ V e.val := by simpa using h
    exact e.property (le_antisymm (fun x hx ↦ hall ⟨x, hx⟩) (hVF e.val))
  let witness : A → M := fun e ↦ (hex e).choose
  have hw (e : A) : witness e ∈ F e.val ∧ witness e ∉ V e.val :=
    ⟨(hex e).choose.property, (hex e).choose_spec⟩
  have hinj : Function.Injective witness := by
    intro e f hef
    apply Subtype.ext
    rcases lt_trichotomy e.val f.val with h | h | h
    · exact False.elim ((hw f).2 (hef ▸
        (le_iSup (fun j : {j : E // j < f.val} ↦ F j.val) ⟨e.val, h⟩) (hw e).1))
    · exact h
    · exact False.elim ((hw e).2 (hef.symm ▸
        (le_iSup (fun j : {j : E // j < e.val} ↦ F j.val) ⟨f.val, h⟩) (hw f).1))
  let : Small.{v} A := small_of_injective hinj
  let I := Shrink.{v} A
  let α : I ≃ A := (equivShrink A).symm
  let key : I → E := fun i ↦ (α i).val
  have hkey : Function.Injective key := Subtype.val_injective.comp α.injective
  let Q : I → ModuleCat.{v} R := fun i ↦ (P (key i)).complex.X 0
  let q (e : E) := (V e).comap (F e).subtype
  have hepi (e : E) : Epi (ModuleCat.ofHom (q e).mkQ) :=
    (ModuleCat.epi_iff_surjective _).mpr (q e).mkQ_surjective
  let t : ∀ i, Q i →ₗ[R] F (key i) := fun i ↦
    (Projective.factorThru ((P (key i)).π.f 0)
      (ModuleCat.ofHom (q (key i)).mkQ)).hom
  have ht (i : I) : (q (key i)).mkQ.comp (t i) = ((P (key i)).π.f 0).hom := by
    exact ModuleCat.hom_ext_iff.mp
      (Projective.factorThru_comp ((P (key i)).π.f 0)
        (ModuleCat.ofHom (q (key i)).mkQ))
  let B := ModuleCat.of R (Π₀ i, Q i)
  let b : B →ₗ[R] M := DFinsupp.lsum R (fun i ↦ (F (key i)).subtype.comp (t i))
  let H : E → Submodule R B := stageSupport key Q
  have hH : Monotone H := stageSupport_mono key Q
  have hforward (e : E) : (H e).map b ≤ F e :=
    stageSupport_image_le key Q M F hF t e
  have hb_single (i : I) (z : Q i) : b (DFinsupp.single i z) = t i z :=
    DFinsupp.lsum_single R (fun j ↦ (F (key j)).subtype.comp (t j)) i z
  have hstep (e : E) (x : M) (hx : x ∈ F e) :
      ∃ y ∈ H e, x - b y ∈ V e := by
    by_cases he : F e = V e
    · exact ⟨0, (H e).zero_mem, by simpa using he ▸ hx⟩
    · let i : I := α.symm ⟨e, he⟩
      have hi : key i = e := congrArg Subtype.val (α.apply_symm_apply ⟨e, he⟩)
      rw [← hi] at hx ⊢
      obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((P (key i)).π.f 0)).mp
        inferInstance ((q (key i)).mkQ ⟨x, hx⟩)
      refine ⟨DFinsupp.single i z, single_mem_stageSupport key Q i z le_rfl, ?_⟩
      rw [hb_single]
      have ht' := LinearMap.congr_fun (ht i) z
      change (q (key i)).mkQ (t i z) = _ at ht'
      have hq : (q (key i)).mkQ (⟨x, hx⟩ - t i z) = 0 := by
        erw [map_sub, ht', hz, sub_self]
      exact (Submodule.Quotient.mk_eq_zero (q (key i))).mp hq
  have himage : ∀ e : E, (H e).map b = F e := by
    intro e
    have wf : WellFounded (fun a b : E ↦ a < b) := wellFounded_lt
    refine wf.induction (C := fun e ↦ (H e).map b = F e) e ?_
    intro e ih
    apply le_antisymm (hforward e)
    have hprev : V e ≤ (H e).map b := by
      apply iSup_le
      intro j
      rw [← ih j.val j.property]
      exact Submodule.map_mono (hH j.property.le)
    intro x hx
    obtain ⟨y, hy, hr⟩ := hstep e x hx
    have hby : b y ∈ (H e).map b := ⟨y, hy, rfl⟩
    simpa using ((H e).map b).add_mem (hprev hr) hby
  have hB : Projective B := dfinsupp_category_projective Q
  have hE : Nonempty E := ⟨(hcover 0).choose⟩
  let : Nonempty E := hE
  refine ⟨B, hB, b, H, hH, stageSupport_cover key Q, himage, ?_⟩
  intro e
  by_cases he : F e = V e
  · left
    apply stageSupport_inactive key Q e
    intro i hi
    apply (α i).property
    change F (key i) = V (key i)
    rw [hi]
    exact he
  · right
    let i : I := α.symm ⟨e, he⟩
    have hi : key i = e := congrArg Subtype.val (α.apply_symm_apply ⟨e, he⟩)
    rw [← hi]
    let p : H (key i) →ₗ[R] Q i := (DFinsupp.lapply i).comp (H (key i)).subtype
    have hp := stageSupport_projection key Q hkey i
    refine ⟨p, hp.1, hp.2, ?_⟩
    let a : H (key i) →ₗ[R] F (key i) :=
      (b.comp (H (key i)).subtype).codRestrict (F (key i))
        (fun x ↦ hforward (key i) ⟨x, x.property, rfl⟩)
    refine ⟨a, rfl, ?_⟩
    have hprev : (⨆ j : {j : E // j < key i}, H j.val).map b ≤ V (key i) := by
      rw [Submodule.map_iSup]
      apply iSup_le
      intro j
      exact (hforward j.val).trans (le_iSup (fun j : {j : E // j < key i} ↦ F j.val) j)
    apply LinearMap.ext
    intro x
    let y : B := x.val - DFinsupp.single i (x.val i)
    have hyH : y ∈ H (key i) :=
      (H (key i)).sub_mem x.property (single_mem_stageSupport key Q i (x.val i) le_rfl)
    have hyker : (⟨y, hyH⟩ : H (key i)) ∈ p.ker := by
      change y i = 0
      change x.val i - (DFinsupp.single i (x.val i) : Π₀ j, Q j) i = 0
      simp only [DFinsupp.single_eq_same, sub_self]
    rw [hp.2] at hyker
    have hby : b y ∈ V (key i) := hprev ⟨y, hyker, rfl⟩
    change ((P (key i)).π.f 0).hom (x.val i) = (q (key i)).mkQ (a x)
    erw [← LinearMap.congr_fun (ht i) (x.val i)]
    apply (Submodule.Quotient.eq (q (key i))).mpr
    change (t i (x.val i) : M) - b x.val ∈ V (key i)
    rw [← hb_single]
    convert (V (key i)).neg_mem hby using 1
    simp [y, map_sub]

end ModuleCat
