/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.Topology.Sheaves.Cech

/-!
# Vanishing of cohomology from vanishing of Čech cohomology

Let `X` be a topological space, `B` a class of open subsets of `X` containing `X`, and `𝒞` a
class of finite families of open subsets such that all finite intersections of the members of a
family in `𝒞` lie in `B`, and such that every open covering of a member `V` of `B` is refined by
a family in `𝒞` covering `V`. If an abelian sheaf `F` has vanishing higher Čech cohomology on all
the families in `𝒞`, then the higher sheaf cohomology `H^q(X, F)` vanishes.

This is [Stacks, Cohomology, Lemma 20.11.9][stacks-project] (tag `01EV`). The proof is the
usual dimension shifting: embed `F` into an injective sheaf `I` with cokernel `Q`. The vanishing
of the first Čech cohomology of `F` shows that `I(V) → Q(V)` is surjective for every `V` in `B`,
hence that the Čech complexes of `F`, `I` and `Q` on a family in `𝒞` form a short exact sequence.
Since the Čech complexes of `I` are exact in positive degrees, `Q` again has vanishing higher Čech
cohomology on the families in `𝒞`, and `H^{q + 1}(X, F) ≅ H^q(X, Q)` for `q > 0` while
`H^1(X, F)` is the cokernel of `I(X) → Q(X)`.

## Main statements

- `TopCat.Presheaf.surjective_app_of_exactAt_cechComplex_one`: if the first Čech cohomology of
  `F` vanishes on families refining every covering of `V`, then `I(V) → Q(V)` is surjective for
  every short exact sequence `0 → F → I → Q → 0` of abelian sheaves.
- `TopCat.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`: the vanishing criterion.
-/

@[expose] public section

universe u v

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
  {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

/-- The composite of the two maps of a short complex of abelian sheaves vanishes on sections. -/
lemma app_g_app_f (W : (Opens X)ᵒᵖ) (x : S.X₁.obj.obj W) :
    S.g.hom.app W (S.f.hom.app W x) = 0 :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congr_arg (fun φ ↦ φ.hom) S.zero) W) x

/-- In a short exact sequence of abelian sheaves, the first map is injective on sections. -/
lemma injective_app_f (hS : S.ShortExact) (W : (Opens X)ᵒᵖ) :
    Function.Injective (S.f.hom.app W) := by
  have := hS.mono_f
  exact (AddCommGrpCat.mono_iff_injective _).1
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj W).map_mono S.f)

/-- A short exact sequence of abelian sheaves is left exact on sections. -/
lemma exists_app_f_eq (hS : S.ShortExact) (W : (Opens X)ᵒᵖ) (x : S.X₂.obj.obj W)
    (hx : S.g.hom.app W x = 0) : ∃ y, S.f.hom.app W y = x := by
  have := hS.mono_f
  exact (ShortComplex.ab_exact_iff _).1 (hS.exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj W) inferInstance inferInstance) x hx

/-- In a short exact sequence of abelian sheaves, a section of the third sheaf over `V`
lifts locally around every point of `V`. -/
lemma exists_app_g_eq_map (hS : S.ShortExact) (V : Opens X) (s : S.X₃.obj.obj (op V)) (x : X)
    (hx : x ∈ V) : ∃ (W : Opens X) (h : W ≤ V) (t : S.X₂.obj.obj (op W)),
      S.g.hom.app _ t = S.X₃.obj.map (homOfLE h).op s ∧ x ∈ W := by
  have := hS.epi_g
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) S.g.hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} S.g).2 this
  obtain ⟨W, f, hf, hxW⟩ :=
    (Opens.mem_grothendieckTopology X).1 (Presheaf.imageSieve_mem _ S.g.hom s) x hx
  obtain ⟨t, ht⟩ := hf
  exact ⟨W, f.le, t, ht, hxW⟩

end TopCat.Sheaf

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X)

/-- `TopCat.Presheaf.cechComplex_map_f_apply`, for elements of the objects of the complex. -/
lemma cechComplex_map_f_apply' {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (k : ℕ)
    (c : ((cechComplex U).obj P).X k) (y : Fin (k + 1) → ι) :
    ((cechComplex U).map φ).f k c y = φ.app _ (c y) :=
  cechComplex_map_f_apply U φ k c y

/-- The zero Čech cochain vanishes termwise. -/
lemma cechComplex_zero_apply (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (k : ℕ)
    (y : Fin (k + 1) → ι) : (0 : ((cechComplex U).obj P).X k) y = 0 :=
  rfl

/-- `TopCat.Presheaf.exactAt_cechComplex_iff`, for elements of the objects of the complex. -/
lemma exactAt_cechComplex_iff' (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (q : ℕ) :
    ((cechComplex U).obj P).ExactAt (q + 1) ↔
      ∀ c : ((cechComplex U).obj P).X (q + 1), ((cechComplex U).obj P).d (q + 1) (q + 2) c = 0 →
        ∃ b : ((cechComplex U).obj P).X q, ((cechComplex U).obj P).d q (q + 1) b = c :=
  exactAt_cechComplex_iff U P q

/-- A morphism of presheaves commutes with the Čech differentials. -/
lemma cechComplex_map_f_d_apply {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (k : ℕ)
    (c : ((cechComplex U).obj P).X k) :
    ((cechComplex U).map φ).f (k + 1) (((cechComplex U).obj P).d k (k + 1) c) =
      ((cechComplex U).obj Q).d k (k + 1) (((cechComplex U).map φ).f k c) :=
  (ConcreteCategory.congr_hom (((cechComplex U).map φ).comm k (k + 1)) c).symm

/-- The composite of two Čech differentials vanishes. -/
lemma cechComplex_d_d_apply (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (k : ℕ)
    (c : ((cechComplex U).obj P).X k) :
    ((cechComplex U).obj P).d (k + 1) (k + 2) (((cechComplex U).obj P).d k (k + 1) c) = 0 :=
  ConcreteCategory.congr_hom (((cechComplex U).obj P).d_comp_d k (k + 1) (k + 2)) c

/-- A sectionwise injective morphism of presheaves induces injections on Čech cochains. -/
lemma cechComplex_map_f_injective {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    (hf : ∀ W, Function.Injective (f.app W)) (k : ℕ) :
    Function.Injective (((cechComplex U).map f).f k) := fun a b h ↦ by
  funext y
  exact hf _ (by simpa only [cechComplex_map_f_apply'] using congr_fun h y)

/-- If `P₁ → P₂ → P₃` is sectionwise exact at `P₂`, then so are the Čech cochains. -/
lemma exists_cechComplex_map_f_eq {P₁ P₂ P₃ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃) (hfg : ∀ W x, g.app W x = 0 → ∃ y, f.app W y = x) (k : ℕ)
    (a : ((cechComplex U).obj P₂).X k) (ha : ((cechComplex U).map g).f k a = 0) :
    ∃ e, ((cechComplex U).map f).f k e = a := by
  have (y : Fin (k + 1) → ι) := hfg _ (a y) (by
    simpa only [cechComplex_map_f_apply', cechComplex_zero_apply] using congr_fun ha y)
  choose e he using this
  exact ⟨e, funext fun y ↦ (cechComplex_map_f_apply U f k e y).trans (he y)⟩

/-- If the composite `P₁ → P₂ → P₃` vanishes sectionwise, then it vanishes on Čech cochains. -/
lemma cechComplex_map_f_map_f_eq_zero {P₁ P₂ P₃ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃) (hfg : ∀ W x, g.app W (f.app W x) = 0) (k : ℕ)
    (b : ((cechComplex U).obj P₁).X k) :
    ((cechComplex U).map g).f k (((cechComplex U).map f).f k b) = 0 := by
  funext y
  rw [cechComplex_map_f_apply', cechComplex_map_f_apply', cechComplex_zero_apply]
  exact hfg _ _

/-- Let `P₁ → P₂ → P₃` be morphisms of presheaves which are sectionwise left exact, and such
that `P₂ → P₃` is surjective on the sections over the finite intersections of the family `U`.
If the Čech complexes of `P₁` and `P₂` are exact in degrees `q + 2` and `q + 1`, then the Čech
complex of `P₃` is exact in degree `q + 1`. -/
theorem exactAt_cechComplex_of_sectionwise {P₁ P₂ P₃ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃) (hfg : ∀ W x, g.app W (f.app W x) = 0)
    (hf : ∀ W, Function.Injective (f.app W))
    (hfg' : ∀ W x, g.app W x = 0 → ∃ y, f.app W y = x)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι), Function.Surjective (g.app (op (⨅ l, U (y l)))))
    (q : ℕ) (h₁ : ((cechComplex U).obj P₁).ExactAt (q + 2))
    (h₂ : ((cechComplex U).obj P₂).ExactAt (q + 1)) :
    ((cechComplex U).obj P₃).ExactAt (q + 1) := by
  have hinj := cechComplex_map_f_injective U f hf
  have hker := exists_cechComplex_map_f_eq U f g hfg'
  have hzero := cechComplex_map_f_map_f_eq_zero U f g hfg
  rw [exactAt_cechComplex_iff'] at h₁ h₂ ⊢
  intro c hc
  obtain ⟨a, hac⟩ : ∃ a : ((cechComplex U).obj P₂).X (q + 1),
      ((cechComplex U).map g).f (q + 1) a = c := by
    choose a ha using fun y ↦ hg (q + 1) y (c y)
    exact ⟨a, funext fun y ↦ (cechComplex_map_f_apply U g _ a y).trans (ha y)⟩
  obtain ⟨e, he⟩ := hker _ (((cechComplex U).obj P₂).d (q + 1) (q + 2) a) (by
    rw [cechComplex_map_f_d_apply, hac, hc])
  obtain ⟨b, hb⟩ := h₁ e (hinj _ (by
    rw [cechComplex_map_f_d_apply, he, map_zero, cechComplex_d_d_apply]))
  obtain ⟨a', ha'⟩ := h₂ (a - ((cechComplex U).map f).f (q + 1) b) (by
    rw [map_sub, ← cechComplex_map_f_d_apply, hb, he, sub_self])
  refine ⟨((cechComplex U).map g).f q a', ?_⟩
  rw [← cechComplex_map_f_d_apply, ha', map_sub, hzero, sub_zero, hac]

/-- Subtraction of Čech cochains is termwise. -/
lemma cechComplex_sub_apply (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (k : ℕ)
    (a b : ((cechComplex U).obj P).X k) (y : Fin (k + 1) → ι) : (a - b) y = a y - b y :=
  rfl

/-- The restrictions of the members of a family of sections with equal indices agree. -/
lemma map_homOfLE_apply_of_eq (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) {ι : Type*}
    (V : ι → Opens X) (t : ∀ z, P.obj (op (V z))) {z z' : ι} (h : z = z') {W : Opens X}
    (h₁ : W ≤ V z) (h₂ : W ≤ V z') :
    P.map (homOfLE h₁).op (t z) = P.map (homOfLE h₂).op (t z') := by
  subst h
  rfl

/-- The Čech differential of the restrictions of a single section vanishes. -/
lemma cechComplex_d_zero_restrict (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) {V : Opens X}
    (s : P.obj (op V)) (h : ∀ z : Fin 1 → ι, ⨅ l, U (z l) ≤ V) :
    ((cechComplex U).obj P).d 0 1
      (fun z ↦ P.map (homOfLE (h z)).op s : ((cechComplex U).obj P).X 0) = 0 := by
  funext y
  refine (cechComplex_d_apply U P 0 _ y).trans ?_
  simp [Fin.sum_univ_two, map_homOfLE_map_homOfLE_apply, cechComplex_zero_apply]

/-- A Čech `0`-cocycle is compatible: its members agree on the overlaps. -/
lemma map_inf_eq_of_cechComplex_d_zero (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (c : ((cechComplex U).obj P).X 0) (hc : ((cechComplex U).obj P).d 0 1 c = 0)
    (z z' : Fin 1 → ι) :
    P.map (homOfLE (inf_le_left : (⨅ l, U (z l)) ⊓ ⨅ l, U (z' l) ≤ _)).op (c z) =
      P.map (homOfLE (inf_le_right : (⨅ l, U (z l)) ⊓ ⨅ l, U (z' l) ≤ _)).op (c z') := by
  have hle : (⨅ l, U (z l)) ⊓ ⨅ l, U (z' l) ≤ ⨅ l, U (![z 0, z' 0] l) := by
    refine le_iInf fun l ↦ ?_
    fin_cases l
    · exact inf_le_left.trans (iInf_le _ 0)
    · exact inf_le_right.trans (iInf_le _ 0)
  have h := congr_arg (P.map (homOfLE hle).op) (congr_fun hc ![z 0, z' 0])
  rw [cechComplex_zero_apply, map_zero] at h
  replace h := (congr_arg (P.map (homOfLE hle).op) (cechComplex_d_apply U P 0 c _)).symm.trans h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_zsmul, add_zero,
    map_homOfLE_map_homOfLE_apply] at h
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ, Fin.val_zero,
    zero_add, pow_one, neg_smul, one_smul] at h
  rw [← sub_eq_add_neg, sub_eq_zero] at h
  have h₀ : ![z 0, z' 0] ∘ Fin.succ = z' := by
    funext l
    fin_cases l
    rfl
  have h₁ : ![z 0, z' 0] ∘ Fin.succAbove 1 = z := by
    funext l
    fin_cases l
    rfl
  exact (map_homOfLE_apply_of_eq P (fun z : Fin 1 → ι ↦ ⨅ l, U (z l)) c h₁.symm _ _).trans
    (h.symm.trans (map_homOfLE_apply_of_eq P (fun z : Fin 1 → ι ↦ ⨅ l, U (z l)) c h₀ _ _))

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves and `V` an open subset
such that every open covering of `V` is refined by a finite family `U` covering `V` on which the
first Čech cohomology of `F` vanishes. Then `I(V) → Q(V)` is surjective. -/
theorem surjective_app_of_exactAt_cechComplex_one
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) {V : Opens X}
    (hV : ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) → ∃ (n : ℕ) (U : Fin n → Opens X),
      iSup U = V ∧ (∀ i, ∃ x, U i ≤ W x) ∧ ((cechComplex U).obj S.X₁.obj).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op V)) := by
  intro s
  choose W hWV t ht hxW using TopCat.Sheaf.exists_app_g_eq_map hS V s
  obtain ⟨m, U, hUV, hUW, hU⟩ := hV (fun x ↦ W x.1 x.2) (fun x ↦ hxW x.1 x.2)
  choose ι hι using hUW
  have hW (z : Fin 1 → Fin m) : ⨅ l, U (z l) ≤ W (ι (z 0)).1 (ι (z 0)).2 :=
    (iInf_le _ 0).trans (hι _)
  have hV' (z : Fin 1 → Fin m) : ⨅ l, U (z l) ≤ V := (hW z).trans (hWV _ _)
  let a : ((cechComplex U).obj S.X₂.obj).X 0 := fun z ↦
    S.X₂.obj.map (homOfLE (hW z)).op (t _ _)
  have ha : ((cechComplex U).map S.g.hom).f 0 a =
      fun z ↦ S.X₃.obj.map (homOfLE (hV' z)).op s := by
    funext z
    rw [cechComplex_map_f_apply', NatTrans.naturality_apply, ht, map_homOfLE_map_homOfLE_apply]
  obtain ⟨e, he⟩ := exists_cechComplex_map_f_eq U S.f.hom S.g.hom
    (TopCat.Sheaf.exists_app_f_eq hS) _ (((cechComplex U).obj S.X₂.obj).d 0 1 a) (by
      rw [cechComplex_map_f_d_apply, ha, cechComplex_d_zero_restrict])
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff' U _ 0).1 hU e
    (cechComplex_map_f_injective U _ (TopCat.Sheaf.injective_app_f hS) _ (by
      rw [cechComplex_map_f_d_apply, he, map_zero, cechComplex_d_d_apply]))
  have hda : ((cechComplex U).obj S.X₂.obj).d 0 1
      (a - ((cechComplex U).map S.f.hom).f 0 b) = 0 := by
    rw [map_sub, ← cechComplex_map_f_d_apply, hb, he, sub_self]
  have hcov : V ≤ iSup fun z : Fin 1 → Fin m ↦ ⨅ l, U (z l) := by
    rw [← hUV]
    exact iSup_le fun i ↦ (le_iInf fun _ ↦ le_rfl).trans
      (le_iSup (fun z : Fin 1 → Fin m ↦ ⨅ l, U (z l)) fun _ ↦ i)
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.X₂
    (fun z : Fin 1 → Fin m ↦ ⨅ l, U (z l)) V (fun z ↦ homOfLE (hV' z)) hcov _
    (map_inf_eq_of_cechComplex_d_zero U _ _ hda)
  refine ⟨σ, TopCat.Sheaf.eq_of_locally_eq' S.X₃ (fun z : Fin 1 → Fin m ↦ ⨅ l, U (z l)) V
    (fun z ↦ homOfLE (hV' z)) hcov _ _ fun z ↦ ?_⟩
  rw [← NatTrans.naturality_apply, hσ, cechComplex_sub_apply, map_sub, cechComplex_map_f_apply',
    TopCat.Sheaf.app_g_app_f, sub_zero, ← cechComplex_map_f_apply' U S.g.hom]
  exact congr_fun ha z

end TopCat.Presheaf

namespace TopCat.Sheaf

open Presheaf Abelian

variable {X : TopCat.{u}}

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves with `I` injective. If
the connecting map `H^q(Q) → H^{q + 1}(F)` vanishes, then `H^{q + 1}(F) = 0`. -/
lemma subsingleton_H_succ_of_comp_extClass
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (h : ∀ y : CategoryTheory.Sheaf.H S.X₃ q, y.comp hS.extClass rfl = 0) :
    Subsingleton (CategoryTheory.Sheaf.H S.X₁ (q + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim _ _) rfl
  exact h y

/-- If `I(X) → Q(X)` is surjective, then the connecting map `H^0(Q) → H^1(F)` vanishes. -/
lemma comp_extClass_eq_zero_of_surjective
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (h : Function.Surjective (S.g.hom.app (op ⊤)))
    (y : CategoryTheory.Sheaf.H S.X₃ 0) : y.comp hS.extClass rfl = 0 := by
  obtain ⟨t, ht⟩ := h (CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop y)
  obtain rfl : y = CategoryTheory.Sheaf.H.map S.g 0
      ((CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop).symm t) := by
    rw [CategoryTheory.Sheaf.H.equiv₀_symm_naturality, ht, AddEquiv.symm_apply_apply]
  rw [CategoryTheory.Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
    Ext.comp_zero]

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves. If every open covering
of a member `V` of `B` is refined by a finite family covering `V` on which the first Čech
cohomology of `F` vanishes, then `I(V) → Q(V)` is surjective for every `V` in `B`. -/
lemma surjective_app_of_exactAt_cechComplex
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (B : Opens X → Prop) (𝒞 : ∀ {n : ℕ}, (Fin n → Opens X) → Prop)
    (hcov : ∀ V, B V → ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) → ∃ (n : ℕ) (U : Fin n → Opens X),
      𝒞 U ∧ iSup U = V ∧ ∀ i, ∃ x, U i ≤ W x)
    (hF : ∀ {n : ℕ} (U : Fin n → Opens X), 𝒞 U → ((cechComplex U).obj S.X₁.obj).ExactAt 1)
    (V : Opens X) (hV : B V) : Function.Surjective (S.g.hom.app (op V)) :=
  surjective_app_of_exactAt_cechComplex_one hS fun W hW ↦ by
    obtain ⟨n, U, hU, hUV, hUW⟩ := hcov V hV W hW
    exact ⟨n, U, hUV, hUW, hF U hU⟩

/-- **The Čech criterion for the vanishing of cohomology.** Let `B` be a class of open subsets of
`X` containing `X` and `𝒞` a class of finite families of open subsets such that the finite
intersections of the members of a family in `𝒞` lie in `B`, and such that every open covering of
a member `V` of `B` is refined by a family in `𝒞` covering `V`. If the Čech complexes of the
abelian sheaf `F` on the families in `𝒞` are exact in positive degrees, then `H^q(X, F) = 0` for
`q > 0`. -/
@[stacks 01EV]
theorem subsingleton_H_succ_of_exactAt_cechComplex
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Opens X → Prop) (𝒞 : ∀ {n : ℕ}, (Fin n → Opens X) → Prop) (hB : B ⊤)
    (h𝒞 : ∀ {n : ℕ} (U : Fin n → Opens X), 𝒞 U → ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      B (⨅ l, U (y l)))
    (hcov : ∀ V, B V → ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) → ∃ (n : ℕ) (U : Fin n → Opens X),
      𝒞 U ∧ iSup U = V ∧ ∀ i, ∃ x, U i ≤ W x)
    (hF : ∀ {n : ℕ} (U : Fin n → Opens X), 𝒞 U → ∀ q : ℕ,
      ((cechComplex U).obj F.obj).ExactAt (q + 1))
    (q : ℕ) : Subsingleton (CategoryTheory.Sheaf.H F (q + 1)) := by
  induction q generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    exact subsingleton_H_succ_of_comp_extClass hS 0 (comp_extClass_eq_zero_of_surjective hS
      (surjective_app_of_exactAt_cechComplex hS B 𝒞 hcov (fun U hU ↦ hF U hU 0) ⊤ hB))
  | succ q ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hsurj := surjective_app_of_exactAt_cechComplex hS B 𝒞 hcov fun U hU ↦ hF U hU 0
    have := ih S.X₃ fun U hU q ↦ exactAt_cechComplex_of_sectionwise U S.f.hom S.g.hom
      app_g_app_f (injective_app_f hS) (exists_app_f_eq hS)
      (fun k y ↦ hsurj _ (h𝒞 U hU k y)) q (hF U hU (q + 1))
      (exactAt_cechComplex_of_injective U S.X₂ q)
    exact subsingleton_H_succ_of_comp_extClass hS (q + 1) fun y ↦ by
      rw [Subsingleton.elim y 0, Ext.zero_comp]

end TopCat.Sheaf
